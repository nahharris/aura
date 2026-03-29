use super::*;

impl TypeChecker {
    pub(crate) fn register_type_aliases_for_exports(&mut self, program: &Program) {
        self.register_type_aliases(program);
    }

    pub(crate) fn bind_type_param_for_exports(&mut self, name: &str) {
        self.env
            .type_params
            .insert(name.to_string(), Type::TypeVar(name.to_string()));
    }

    pub(crate) fn unbind_type_param_for_exports(&mut self, name: &str) {
        self.env.type_params.remove(name);
    }

    pub(crate) fn resolve_params_for_exports(
        &mut self,
        params: &[Param],
        fn_span: Span,
    ) -> Vec<Type> {
        self.resolve_params(params, fn_span)
    }

    pub(crate) fn resolve_type_expr_for_exports(&mut self, ty: &TypeExpr) -> Type {
        self.resolve_type_expr(ty)
    }

    pub(crate) fn export_errors(&self) -> &[TypeError] {
        &self.errors
    }

    pub(crate) fn strict_export_value_type(
        &mut self,
        module_path: &str,
        export_name: &str,
        init: &Expr,
    ) -> Result<Type, String> {
        match init {
            Expr::Int(..) => Ok(Type::Int),
            Expr::Float(..) => Ok(Type::Float),
            Expr::Str(..) => Ok(Type::String),
            Expr::Char(..) => Ok(Type::Char),
            Expr::Ident(name, _) if name == "true" || name == "false" => Ok(Type::Bool),
            Expr::Ident(name, _) if name == "null" => Ok(Type::Null),
            Expr::Builtin { name, .. } => Self::kernel_builtin_signature(name).ok_or_else(|| {
                format!(
                    "{module_path}: export `{export_name}` references unknown builtin `{name}`"
                )
            }),
            _ => Err(format!(
                "{module_path}: export `{export_name}` must have an explicit type shape or builtin-backed binding"
            )),
        }
    }

    pub(crate) fn kernel_builtin_signature(name: &str) -> Option<Type> {
        let list_any = || Type::List(Box::new(Type::Any));
        let f = |params: Vec<Type>, ret: Type| Type::Func {
            params,
            ret: Box::new(ret),
        };
        match name {
            "io_write" => Some(f(vec![Type::Int, Type::String], Type::Void)),
            "to_str" => Some(f(vec![Type::Any], Type::String)),

            "str_len" => Some(f(vec![Type::String], Type::Int)),
            "str_upper" | "str_lower" | "str_trim" => Some(f(vec![Type::String], Type::String)),
            "str_contains" | "str_starts_with" | "str_ends_with" => {
                Some(f(vec![Type::String, Type::String], Type::Bool))
            }
            "str_split" => Some(f(vec![Type::String, Type::String], list_any())),
            "str_join" => Some(f(vec![Type::String, list_any()], Type::String)),
            "str_replace" => Some(f(
                vec![Type::String, Type::String, Type::String],
                Type::String,
            )),
            "str_slice" => Some(f(vec![Type::String, Type::Int, Type::Int], Type::String)),
            "str_parse_int" | "str_parse_float" => Some(f(vec![Type::String], Type::Any)),

            "list_len" => Some(f(vec![list_any()], Type::Int)),
            "list_push" => Some(f(vec![list_any(), Type::Any], Type::Void)),
            "list_pop" => Some(f(vec![list_any()], Type::Any)),
            "list_contains" => Some(f(vec![list_any(), Type::Any], Type::Bool)),
            "list_slice" => Some(f(vec![list_any(), Type::Int, Type::Int], list_any())),
            "list_concat" => Some(f(vec![list_any(), list_any()], list_any())),
            "list_reverse" => Some(f(vec![list_any()], list_any())),
            "list_index_of" => Some(f(vec![list_any(), Type::Any], Type::Int)),

            _ => None,
        }
    }
}
