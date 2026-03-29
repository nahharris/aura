use super::*;

impl TypeChecker {
    pub(crate) fn infer_expr(&mut self, expr: &Expr, env: &TypeEnv) -> Type {
        match expr {
            Expr::Int(..) => Type::Int,
            Expr::Float(..) => Type::Float,
            Expr::Str(..) => Type::String,
            Expr::Char(..) => Type::Char,
            Expr::Ident(name, span) => {
                if let Some(ty) = env.lookup_binding(name) {
                    ty.clone()
                } else if let Some(ty) = env.lookup_function(name) {
                    ty.clone()
                } else {
                    self.error(format!("unknown identifier `{name}`"), *span);
                    Type::Any
                }
            }
            Expr::DotIdent(..) => Type::Any,
            Expr::Builtin { .. } => Type::Any,
            Expr::Binary { op, lhs, rhs, span } => self.infer_binary(*op, lhs, rhs, *span, env),
            Expr::Unary {
                op,
                expr: inner,
                span,
            } => {
                let ty = self.infer_expr(inner, env);
                match op {
                    UnOp::Neg => {
                        if !matches!(ty, Type::Int | Type::Float | Type::Any) {
                            self.error(
                                format!(
                                    "unary `-` requires Int or Float, got {}",
                                    ty.display_name()
                                ),
                                *span,
                            );
                        }
                        ty
                    }
                    UnOp::Not => {
                        if !matches!(ty, Type::Bool | Type::Any) {
                            self.error(
                                format!("unary `!` requires Bool, got {}", ty.display_name()),
                                *span,
                            );
                        }
                        Type::Bool
                    }
                }
            }
            Expr::Assign {
                target,
                value,
                span,
            } => {
                let target_ty = self.infer_expr(target, env);
                let value_ty = self.infer_expr(value, env);
                if !self.is_assignable(&value_ty, &target_ty) {
                    self.error(
                        format!(
                            "cannot assign {} to {}",
                            value_ty.display_name(),
                            target_ty.display_name()
                        ),
                        *span,
                    );
                }
                value_ty
            }
            Expr::FieldAccess {
                object,
                field,
                span,
            } => {
                let obj_ty = self.infer_expr(object, env);
                self.infer_field_access(&obj_ty, field, *span)
            }
            Expr::Index {
                object,
                index,
                span,
            } => {
                let obj_ty = self.infer_expr(object, env);
                let idx_ty = self.infer_expr(index, env);
                self.infer_index(&obj_ty, &idx_ty, *span)
            }
            Expr::SafeNav {
                object,
                field,
                span,
            } => {
                let obj_ty = self.infer_expr(object, env);
                let inner_ty = match &obj_ty {
                    Type::Union(members) => {
                        let non_null: Vec<_> = members
                            .iter()
                            .filter(|t| !matches!(t, Type::Null))
                            .cloned()
                            .collect();
                        if non_null.len() == 1 {
                            non_null.into_iter().next().unwrap()
                        } else if non_null.is_empty() {
                            Type::Null
                        } else {
                            Type::Union(non_null)
                        }
                    }
                    other => other.clone(),
                };
                let field_ty = self.infer_field_access(&inner_ty, field, *span);
                Type::Union(vec![field_ty, Type::Null])
            }
            Expr::ForceUnwrap { expr: inner, .. } => {
                let ty = self.infer_expr(inner, env);
                match ty {
                    Type::Union(members) => {
                        let non_null: Vec<_> = members
                            .into_iter()
                            .filter(|t| !matches!(t, Type::Null))
                            .collect();
                        if non_null.len() == 1 {
                            non_null.into_iter().next().unwrap()
                        } else if non_null.is_empty() {
                            Type::Null
                        } else {
                            Type::Union(non_null)
                        }
                    }
                    other => other,
                }
            }
            Expr::PostIncrement { target, span } | Expr::PostDecrement { target, span } => {
                let ty = self.infer_expr(target, env);
                if !matches!(ty, Type::Int | Type::Float | Type::Any) {
                    self.error(
                        format!("++ / -- requires Int or Float, got {}", ty.display_name()),
                        *span,
                    );
                }
                ty
            }
            Expr::Cast { expr, ty, span } => {
                let from_ty = self.infer_expr(expr, env);
                let to_ty = self.resolve_type_expr(ty);
                self.check_cast(&from_ty, &to_ty, *span);
                to_ty
            }
            Expr::Elvis { left, right, .. } => {
                let l = self.infer_expr(left, env);
                let r = self.infer_expr(right, env);
                if l == r {
                    l
                } else {
                    Type::Union(vec![l, r])
                }
            }
            Expr::Range {
                start,
                end: end_expr,
                span,
            } => {
                let s = self.infer_expr(start, env);
                let e = self.infer_expr(end_expr, env);
                if !matches!(s, Type::Int | Type::Any) {
                    self.error(
                        format!("range start must be Int, got {}", s.display_name()),
                        *span,
                    );
                }
                if !matches!(e, Type::Int | Type::Any) {
                    self.error(
                        format!("range end must be Int, got {}", e.display_name()),
                        *span,
                    );
                }
                Type::List(Box::new(Type::Int))
            }
            Expr::Call {
                callee,
                args,
                trailing,
                span,
            } => self.infer_call(callee, args, trailing, *span, env),
            Expr::List { items, .. } => {
                if items.is_empty() {
                    return Type::List(Box::new(Type::Any));
                }
                let first_ty = {
                    let item = &items[0];
                    let mut child = env.snapshot_child();
                    for stmt in &item.stmts {
                        self.check_stmt(stmt, &mut child, None);
                    }
                    self.infer_expr(&item.value, &child)
                };
                for item in items.iter().skip(1) {
                    let mut child = env.snapshot_child();
                    for stmt in &item.stmts {
                        self.check_stmt(stmt, &mut child, None);
                    }
                    let ty = self.infer_expr(&item.value, &child);
                    if !self.is_assignable(&ty, &first_ty) && !self.is_assignable(&first_ty, &ty) {
                        return Type::List(Box::new(Type::Any));
                    }
                }
                Type::List(Box::new(first_ty))
            }
            Expr::Dict { entries, .. } => {
                if entries.is_empty() {
                    return Type::Dict(Box::new(Type::Any), Box::new(Type::Any));
                }
                let key_ty = self.infer_expr(&entries[0].key, env);
                let val_ty = self.infer_expr(&entries[0].value, env);
                Type::Dict(Box::new(key_ty), Box::new(val_ty))
            }
            Expr::Tuple { items, .. } => {
                if items.is_empty() {
                    return Type::Void;
                }
                let elems: Vec<Type> = items
                    .iter()
                    .map(|item| {
                        let mut child = env.snapshot_child();
                        for stmt in &item.stmts {
                            self.check_stmt(stmt, &mut child, None);
                        }
                        self.infer_expr(&item.value, &child)
                    })
                    .collect();
                Type::Tuple(elems)
            }
            Expr::Struct { fields, .. } => {
                let resolved: Vec<(std::string::String, Type)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), self.infer_expr(&f.value, env)))
                    .collect();
                Type::Struct {
                    name: None,
                    fields: resolved,
                }
            }
            Expr::ArrayLiteral { items, span } => {
                if items.is_empty() {
                    return Type::Array {
                        elem: Box::new(Type::Any),
                        len: 0,
                    };
                }
                let first_ty = {
                    let item = &items[0];
                    let mut child = env.snapshot_child();
                    for stmt in &item.stmts {
                        self.check_stmt(stmt, &mut child, None);
                    }
                    self.infer_expr(&item.value, &child)
                };
                for item in items.iter().skip(1) {
                    let mut child = env.snapshot_child();
                    for stmt in &item.stmts {
                        self.check_stmt(stmt, &mut child, None);
                    }
                    let ty = self.infer_expr(&item.value, &child);
                    if !self.is_assignable(&ty, &first_ty) && !self.is_assignable(&first_ty, &ty) {
                        self.error("array literal elements must have compatible types", *span);
                        break;
                    }
                }
                Type::Array {
                    elem: Box::new(first_ty),
                    len: items.len(),
                }
            }
            Expr::SetLiteral { items, span } => {
                if items.is_empty() {
                    return Type::Set(Box::new(Type::Any));
                }
                let first_ty = {
                    let item = &items[0];
                    let mut child = env.snapshot_child();
                    for stmt in &item.stmts {
                        self.check_stmt(stmt, &mut child, None);
                    }
                    self.infer_expr(&item.value, &child)
                };
                for item in items.iter().skip(1) {
                    let mut child = env.snapshot_child();
                    for stmt in &item.stmts {
                        self.check_stmt(stmt, &mut child, None);
                    }
                    let ty = self.infer_expr(&item.value, &child);
                    if !self.is_assignable(&ty, &first_ty) && !self.is_assignable(&first_ty, &ty) {
                        self.error("set literal elements must have compatible types", *span);
                        break;
                    }
                }
                Type::Set(Box::new(first_ty))
            }
            Expr::Closure(closure) => self.infer_closure(closure, env),
            Expr::Block(block) => {
                let child = env.snapshot_child();
                self.check_block(block, child, None)
            }
            Expr::If(if_expr) => {
                let cond_ty = self.infer_expr(&if_expr.condition, env);
                if !matches!(cond_ty, Type::Bool | Type::Any) {
                    self.error(
                        format!("if condition must be Bool, got {}", cond_ty.display_name()),
                        if_expr.condition.span(),
                    );
                }
                let then_ty = self.check_block(&if_expr.then_block, env.snapshot_child(), None);
                match &if_expr.else_block {
                    Some(else_block) => {
                        let else_ty = self.check_block(else_block, env.snapshot_child(), None);
                        if then_ty == else_ty {
                            then_ty
                        } else {
                            Type::Union(vec![then_ty, else_ty])
                        }
                    }
                    None => Type::Void,
                }
            }
            Expr::Cases(cases) => {
                let mut arm_types: Vec<Type> = Vec::new();
                for arm in &cases.arms {
                    let guard_ty = self.infer_expr(&arm.guard, env);
                    if !matches!(guard_ty, Type::Bool | Type::Any) {
                        self.error(
                            format!("cases guard must be Bool, got {}", guard_ty.display_name()),
                            arm.guard.span(),
                        );
                    }
                    let ty = self.infer_expr(&arm.body, env);
                    arm_types.push(ty);
                }
                unify_types(arm_types)
            }
            Expr::Loop(loop_expr) => {
                if let Some(cond) = &loop_expr.condition {
                    let cond_ty = self.check_block(cond, env.snapshot_child(), None);
                    if !matches!(cond_ty, Type::Bool | Type::Void | Type::Any) {
                        self.error(
                            format!(
                                "loop condition must be Bool, got {}",
                                cond_ty.display_name()
                            ),
                            cond.span,
                        );
                    }
                }
                self.check_labelled_block(&loop_expr.body, env, None);
                Type::Void
            }
        }
    }

    pub(crate) fn infer_binary(
        &mut self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
        env: &TypeEnv,
    ) -> Type {
        let l = self.infer_expr(lhs, env);
        let r = self.infer_expr(rhs, env);

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                if op == BinOp::Add && matches!((&l, &r), (Type::String, Type::String)) {
                    return Type::String;
                }
                let numeric = |t: &Type| matches!(t, Type::Int | Type::Float | Type::Any);
                if !numeric(&l) {
                    self.error(
                        format!(
                            "left operand of `{op}` must be numeric, got {}",
                            l.display_name()
                        ),
                        span,
                    );
                }
                if !numeric(&r) {
                    self.error(
                        format!(
                            "right operand of `{op}` must be numeric, got {}",
                            r.display_name()
                        ),
                        span,
                    );
                }
                if matches!(l, Type::Float) || matches!(r, Type::Float) {
                    Type::Float
                } else {
                    Type::Int
                }
            }
            BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                let ordered =
                    |t: &Type| matches!(t, Type::Int | Type::Float | Type::String | Type::Any);
                if !ordered(&l) {
                    self.error(
                        format!(
                            "left operand of `{op}` must be Int, Float, or String, got {}",
                            l.display_name()
                        ),
                        span,
                    );
                }
                if !ordered(&r) {
                    self.error(
                        format!(
                            "right operand of `{op}` must be Int, Float, or String, got {}",
                            r.display_name()
                        ),
                        span,
                    );
                }
                Type::Bool
            }
            BinOp::Eq | BinOp::Ne => Type::Bool,
            BinOp::And | BinOp::Or => {
                if !matches!(l, Type::Bool | Type::Any) {
                    self.error(
                        format!(
                            "left operand of `{op}` must be Bool, got {}",
                            l.display_name()
                        ),
                        span,
                    );
                }
                if !matches!(r, Type::Bool | Type::Any) {
                    self.error(
                        format!(
                            "right operand of `{op}` must be Bool, got {}",
                            r.display_name()
                        ),
                        span,
                    );
                }
                Type::Bool
            }
        }
    }

    pub(crate) fn infer_field_access(&mut self, obj_ty: &Type, field: &str, span: Span) -> Type {
        match obj_ty {
            Type::Module { path, exports } => {
                if let Some(ty) = exports.get(field) {
                    ty.clone()
                } else {
                    self.error(format!("module `{path}` has no export `{field}`"), span);
                    Type::Any
                }
            }
            Type::Struct { fields, .. } => {
                if let Some((_, ty)) = fields.iter().find(|(n, _)| n == field) {
                    ty.clone()
                } else {
                    self.error(
                        format!("type {} has no field `{field}`", obj_ty.display_name()),
                        span,
                    );
                    Type::Any
                }
            }
            _ => Type::Any,
        }
    }

    pub(crate) fn infer_index(&mut self, obj_ty: &Type, idx_ty: &Type, span: Span) -> Type {
        match obj_ty {
            Type::List(elem) => {
                if !matches!(idx_ty, Type::Int | Type::Any) {
                    self.error(
                        format!("list index must be Int, got {}", idx_ty.display_name()),
                        span,
                    );
                }
                *elem.clone()
            }
            Type::Dict(key, val) => {
                if !self.is_assignable(idx_ty, key) {
                    self.error(
                        format!(
                            "dict key type is {}, cannot index with {}",
                            key.display_name(),
                            idx_ty.display_name()
                        ),
                        span,
                    );
                }
                *val.clone()
            }
            Type::Tuple(elems) => unify_types(elems.clone()),
            Type::Array { elem, .. } => {
                if !matches!(idx_ty, Type::Int | Type::Any) {
                    self.error(
                        format!("array index must be Int, got {}", idx_ty.display_name()),
                        span,
                    );
                }
                *elem.clone()
            }
            _ => Type::Any,
        }
    }

    pub(crate) fn infer_call(
        &mut self,
        callee: &Expr,
        args: &[crate::ast::Arg],
        trailing: &[crate::ast::TrailingArg],
        span: Span,
        env: &TypeEnv,
    ) -> Type {
        let arg_tys: Vec<Type> = args
            .iter()
            .map(|a| self.infer_expr(&a.value, env))
            .collect();
        for targ in trailing {
            self.check_labelled_block(&targ.block, env, None);
        }

        let callee_ty = match callee {
            Expr::Ident(name, _) => env
                .lookup_function(name)
                .or_else(|| env.lookup_binding(name))
                .cloned(),
            Expr::FieldAccess {
                object,
                field,
                span: field_span,
            } => {
                let obj_ty = self.infer_expr(object, env);
                match &obj_ty {
                    Type::Module { .. } => {
                        Some(self.infer_field_access(&obj_ty, field, *field_span))
                    }
                    _ => {
                        let qualified = format!("{}.{}", obj_ty.display_name(), field);
                        env.lookup_function(&qualified).cloned()
                    }
                }
            }
            Expr::Closure(closure) => {
                let closure_ty = self.infer_closure_with_subject(closure, env, &arg_tys);
                Some(closure_ty)
            }
            _ => {
                self.infer_expr(callee, env);
                None
            }
        };

        match callee_ty {
            Some(Type::Func { params, ret }) => {
                let total_args = args.len() + trailing.len();
                if total_args != params.len() && (trailing.is_empty() || total_args > params.len())
                {
                    self.error(
                        format!("expected {} argument(s), got {total_args}", params.len()),
                        span,
                    );
                }
                for (i, arg) in args.iter().enumerate() {
                    if let Some(expected) = params.get(i) {
                        let actual = if let Expr::Closure(closure) = &arg.value {
                            let subject_tys: Vec<Type> = match expected {
                                Type::Func {
                                    params: closure_params,
                                    ..
                                } => closure_params.clone(),
                                _ => vec![],
                            };
                            let closure_ty =
                                self.infer_closure_with_subject(closure, env, &subject_tys);
                            if subject_tys.len() == 1 {
                                self.check_exhaustiveness(
                                    &closure.arms,
                                    &subject_tys[0],
                                    closure.span,
                                );
                            }
                            closure_ty
                        } else {
                            self.infer_expr(&arg.value, env)
                        };
                        if !self.is_assignable(&actual, expected) {
                            self.error(
                                format!(
                                    "argument {} has type {}, expected {}",
                                    i + 1,
                                    actual.display_name(),
                                    expected.display_name()
                                ),
                                arg.span,
                            );
                        }
                    }
                }
                *ret
            }
            Some(other) if !other.is_any() => {
                self.error(
                    format!("cannot call value of type {}", other.display_name()),
                    span,
                );
                Type::Any
            }
            _ => Type::Any,
        }
    }

    pub(crate) fn infer_closure(&mut self, closure: &crate::ast::Closure, env: &TypeEnv) -> Type {
        self.infer_closure_with_subject(closure, env, &[])
    }

    pub(crate) fn infer_closure_with_subject(
        &mut self,
        closure: &crate::ast::Closure,
        env: &TypeEnv,
        subject_tys: &[Type],
    ) -> Type {
        if closure.arms.is_empty() {
            return Type::Func {
                params: vec![],
                ret: Box::new(Type::Void),
            };
        }

        let mut ret_types: Vec<Type> = Vec::new();
        for arm in &closure.arms {
            let ty = self.infer_closure_arm(arm, env, subject_tys);
            ret_types.push(ty);
        }

        let ret = unify_types(ret_types);
        let first_arm = &closure.arms[0];
        let params = first_arm
            .patterns
            .iter()
            .enumerate()
            .map(|(i, _)| subject_tys.get(i).cloned().unwrap_or(Type::Any))
            .collect();
        Type::Func {
            params,
            ret: Box::new(ret),
        }
    }

    pub(crate) fn infer_closure_arm(
        &mut self,
        arm: &ClosureArm,
        env: &TypeEnv,
        subject_tys: &[Type],
    ) -> Type {
        let mut child = env.snapshot_child();
        for (i, pat) in arm.patterns.iter().enumerate() {
            let subject_ty = subject_tys.get(i).cloned().unwrap_or(Type::Any);
            self.check_pattern(pat, &subject_ty, &mut child);
        }
        if let Some(guard) = &arm.guard {
            self.infer_expr(guard, &child);
        }
        self.infer_expr(&arm.body, &child)
    }
}
