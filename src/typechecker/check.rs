use super::*;

impl TypeChecker {
    /// Check all statements in `block` and return the type of the final
    /// (tail) expression, or `Type::Void` if there is none.
    ///
    /// `ret_ty` is the expected return type of the enclosing function, forwarded
    /// to `check_stmt` for `return` statement validation.
    pub(crate) fn check_block(
        &mut self,
        block: &Block,
        mut env: TypeEnv,
        ret_ty: Option<&Type>,
    ) -> Type {
        for stmt in &block.stmts {
            self.check_stmt(stmt, &mut env, ret_ty);
        }
        match &block.tail {
            Some(tail) => self.infer_expr(tail, &env),
            None => Type::Void,
        }
    }

    /// Check a labelled block (used by loops and trailing closure args).
    pub(crate) fn check_labelled_block(
        &mut self,
        lb: &LabelledBlock,
        env: &TypeEnv,
        ret_ty: Option<&Type>,
    ) -> Type {
        let child = env.snapshot_child();
        self.check_block(&lb.block, child, ret_ty)
    }

    /// Check a single statement, mutating `env` with any new bindings.
    ///
    /// `ret_ty` is forwarded for `return` validation.
    pub(crate) fn check_stmt(&mut self, stmt: &Stmt, env: &mut TypeEnv, ret_ty: Option<&Type>) {
        match stmt {
            Stmt::Let(let_stmt) => {
                for binding in &let_stmt.bindings {
                    self.check_local_binding(binding, env, ret_ty);
                }
            }

            Stmt::Const(const_stmt) => {
                for binding in &const_stmt.bindings {
                    self.check_local_binding(binding, env, ret_ty);
                }
            }

            Stmt::Def(def_stmt) => {
                // Local `def` - handle each binding.
                for binding in &def_stmt.bindings {
                    match binding {
                        DefBinding::Value { pattern, init, .. } => {
                            let init_ty = self.infer_expr(init, env);
                            bind_pattern_names(pattern, init_ty, env);
                        }
                        DefBinding::FuncDef {
                            name,
                            params,
                            body,
                            return_type,
                            ..
                        } => {
                            // Register the local function name as Func type.
                            let param_types: Vec<Type> = params
                                .iter()
                                .map(|p| {
                                    p.ty.as_ref()
                                        .map(|te| self.resolve_type_expr(te))
                                        .unwrap_or(Type::Any)
                                })
                                .collect();
                            let ret_type = return_type
                                .as_ref()
                                .map(|te| self.resolve_type_expr(te))
                                .unwrap_or(Type::Any);
                            let func_type = Type::Func {
                                params: param_types,
                                ret: Box::new(ret_type),
                            };
                            env.bindings.insert(name.clone(), func_type);
                            // Also check the body (best-effort).
                            let child = env.snapshot_child();
                            let _ = self.check_block(body, child, None);
                        }
                        DefBinding::TypeAlias { name, .. } => {
                            // Local type aliases are not registered in the binding env.
                            let _ = name;
                        }
                    }
                }
            }

            Stmt::Return(ret_stmt) => {
                let value_ty = match &ret_stmt.value {
                    Some(v) => self.infer_expr(v, env),
                    None => Type::Void,
                };
                if let Some(expected) = ret_ty {
                    if !self.is_assignable(&value_ty, expected) {
                        self.error(
                            format!(
                                "return type mismatch: expected {}, got {}",
                                expected.display_name(),
                                value_ty.display_name()
                            ),
                            ret_stmt.span,
                        );
                    }
                }
            }

            Stmt::Break(brk) => {
                if let Some(v) = &brk.value {
                    self.infer_expr(v, env);
                }
            }

            Stmt::Continue(_) => {}

            Stmt::Expr(expr_stmt) => {
                self.infer_expr(&expr_stmt.expr, env);
            }
        }
    }

    /// Check a single `let`/`const` binding, register the bound name(s) in `env`.
    fn check_local_binding(
        &mut self,
        binding: &LocalBinding,
        env: &mut TypeEnv,
        ret_ty: Option<&Type>,
    ) {
        let init_ty = self.infer_expr(&binding.init, env);

        // Check annotation if present
        let declared_ty = binding.ty.as_ref().map(|te| self.resolve_type_expr(te));

        let effective_ty = if let Some(ref decl) = declared_ty {
            if !self.is_assignable(&init_ty, decl) {
                self.error(
                    format!(
                        "type annotation mismatch: expected {}, got {}",
                        decl.display_name(),
                        init_ty.display_name()
                    ),
                    binding.span,
                );
            }
            decl.clone()
        } else {
            init_ty
        };

        // Register name(s) into env
        bind_pattern_names(&binding.pattern, effective_ty, env);

        // Check any nested stmts referenced via the init (already handled in
        // infer_expr; nothing extra needed here).
        let _ = ret_ty; // forwarded but not used at this level
    }

    /// Check all function bodies in the program (fourth pass).
    pub(crate) fn check_all_bodies(&mut self, program: &Program) {
        // Collect FuncDef bindings to avoid borrow conflicts - we need &mut self inside
        // the loop but program is already borrowed.
        let func_defs: Vec<_> = program
            .items
            .iter()
            .filter_map(|item| {
                if let Item::Decl(decl) = item {
                    if let DeclKind::Def(def_decl) = &decl.kind {
                        let funcs: Vec<_> = def_decl
                            .bindings
                            .iter()
                            .filter_map(|b| {
                                if let DefBinding::FuncDef {
                                    receiver,
                                    name,
                                    type_params,
                                    params,
                                    return_type,
                                    body,
                                    span,
                                } = b
                                {
                                    // Convert to legacy DefnDecl for reuse of check_defn_body.
                                    Some(crate::ast::DefnDecl {
                                        receiver: receiver.clone(),
                                        name: name.clone(),
                                        type_params: type_params.clone(),
                                        params: params.clone(),
                                        return_type: return_type.clone(),
                                        body: body.clone(),
                                        span: *span,
                                    })
                                } else {
                                    None
                                }
                            })
                            .collect();
                        return Some(funcs);
                    }
                }
                None
            })
            .flatten()
            .collect();

        for defn in func_defs {
            self.check_defn_body(&defn);
        }
    }

    /// Type-check the body of a single `defn` declaration.
    ///
    /// Creates a child environment with:
    /// - type parameters bound as `TypeVar`
    /// - parameters bound to their resolved types
    ///
    /// Then checks the body block and validates the tail type against the
    /// declared return type.
    fn check_defn_body(&mut self, defn: &crate::ast::DefnDecl) {
        // Build a child env with type params and params
        let mut child = self.env.snapshot_child();

        // Bind type parameters
        for tp in &defn.type_params {
            child
                .type_params
                .insert(tp.name.clone(), Type::TypeVar(tp.name.clone()));
        }

        // Bind parameters with their resolved types
        for param in &defn.params {
            let ty = match &param.ty {
                Some(te) => self.resolve_type_expr(te),
                None => Type::Any, // already errored in register_functions
            };
            child.bindings.insert(param.internal.clone(), ty);
        }

        // Resolve declared return type
        let ret_ty = defn
            .return_type
            .as_ref()
            .map(|te| self.resolve_type_expr(te));

        let actual_ty = self.check_block(&defn.body, child, ret_ty.as_ref());

        // If the body has a tail expression, check it against the return type
        if defn.body.tail.is_some() {
            if let Some(ref expected) = ret_ty {
                if !self.is_assignable(&actual_ty, expected) {
                    self.error(
                        format!(
                            "function `{}` returns {}, but declared return type is {}",
                            defn.name,
                            actual_ty.display_name(),
                            expected.display_name()
                        ),
                        defn.body.span,
                    );
                }
            }
        }
    }
}
