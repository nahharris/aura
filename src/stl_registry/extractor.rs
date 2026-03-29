use crate::ast::{DeclKind, DefBinding, Item, Pattern, Program};
use crate::stl_registry::StlModuleExports;
use crate::typechecker::{Type, TypeChecker};

pub(crate) fn extract_module_exports_strict(
    module_path: &str,
    program: &Program,
) -> Result<StlModuleExports, String> {
    let mut checker = TypeChecker::new();
    checker.register_type_aliases_for_exports(program);

    let mut exports = StlModuleExports::new();
    for item in &program.items {
        let Item::Decl(decl) = item else { continue };
        let DeclKind::Def(def_decl) = &decl.kind else {
            continue;
        };

        for binding in &def_decl.bindings {
            match binding {
                DefBinding::FuncDef {
                    receiver,
                    name,
                    type_params,
                    params,
                    return_type,
                    span,
                    ..
                } => {
                    for tp in type_params {
                        checker.bind_type_param_for_exports(&tp.name);
                    }
                    let param_types = checker.resolve_params_for_exports(params, *span);
                    let ret_type = match return_type {
                        Some(rt) => checker.resolve_type_expr_for_exports(rt),
                        None => {
                            return Err(format!(
                                "{module_path}: export `{name}` is missing a return type"
                            ))
                        }
                    };
                    for tp in type_params {
                        checker.unbind_type_param_for_exports(&tp.name);
                    }

                    let full_name = match receiver {
                        Some(recv) => format!("{recv}.{name}"),
                        None => name.clone(),
                    };
                    exports.insert(
                        full_name,
                        Type::Func {
                            params: param_types,
                            ret: Box::new(ret_type),
                        },
                    );
                }
                DefBinding::TypeAlias {
                    name,
                    type_params,
                    ty,
                    ..
                } => {
                    for tp in type_params {
                        checker.bind_type_param_for_exports(&tp.name);
                    }

                    let resolved = checker.resolve_type_expr_for_exports(ty);
                    for tp in type_params {
                        checker.unbind_type_param_for_exports(&tp.name);
                    }

                    exports.insert(name.clone(), resolved);
                }
                DefBinding::Value { pattern, init, .. } => {
                    let Pattern::Bind(name, _) = pattern else {
                        return Err(format!(
                            "{module_path}: unsupported exported binding pattern `{:?}`",
                            pattern
                        ));
                    };
                    let value_ty = checker.strict_export_value_type(module_path, name, init)?;
                    exports.insert(name.clone(), value_ty);
                }
            }
        }
    }

    if !checker.export_errors().is_empty() {
        return Err(format!(
            "{module_path}: signature extraction errors: {:?}",
            checker
                .export_errors()
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        ));
    }

    Ok(exports)
}
