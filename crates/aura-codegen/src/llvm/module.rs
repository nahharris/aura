use aura_typecheck::CheckedModule;
#[cfg(feature = "llvm-backend")]
use aura_typecheck::Ty;
#[cfg(feature = "llvm-backend")]
use std::collections::HashSet;

use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
use super::expr::classify_expr_kind;
#[cfg(feature = "llvm-backend")]
use super::expr::lower_expr;

#[cfg(feature = "llvm-backend")]
use inkwell::context::Context;

#[cfg(feature = "llvm-backend")]
use super::{
    context::CodegenContext,
    function::{declare_function, declare_global_stub},
};

#[cfg(feature = "llvm-backend")]
pub fn emit_module_stub(
    module_name: &str,
    checked: &CheckedModule,
) -> Result<String, CodegenError> {
    let context = Context::create();
    let cg = CodegenContext::new(&context, module_name, checked);

    let function_names = checked
        .ir
        .declarations
        .iter()
        .filter_map(|decl| {
            let ty = checked.types.get(decl.ty)?;
            if matches!(ty, Ty::Func { .. }) {
                return Some(decl.name.clone());
            }
            None
        })
        .collect::<HashSet<_>>();

    for decl in &checked.ir.declarations {
        let Some(ty) = checked.types.get(decl.ty) else {
            return Err(CodegenError::InvalidTypeId(decl.ty.0));
        };

        if matches!(ty, Ty::Func { .. }) {
            declare_function(&cg, decl)?;
        } else {
            declare_global_stub(&cg, decl)?;
        }
    }

    for decl in &checked.ir.declarations {
        if !function_names.contains(&decl.name) {
            continue;
        }

        let function = cg
            .module
            .get_function(&decl.name)
            .ok_or(CodegenError::InvalidFunctionType(decl.name.clone()))?;
        let entry = cg.context.append_basic_block(function, "entry");
        cg.builder.position_at_end(entry);

        let lowered = lower_expr(&cg, &decl.value)
            .map_err(|_| CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value)))?;

        if function.get_type().get_return_type().is_some() {
            cg.builder.build_return(Some(&lowered)).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        } else {
            cg.builder.build_return(None).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        }
    }

    Ok(cg.module.print_to_string().to_string())
}

#[cfg(not(feature = "llvm-backend"))]
pub fn emit_module_stub(
    _module_name: &str,
    _checked: &CheckedModule,
) -> Result<String, CodegenError> {
    Err(CodegenError::BackendDisabled)
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "llvm-backend"))]
    use aura_frontend::Parser;
    #[cfg(not(feature = "llvm-backend"))]
    use aura_typecheck::check_module;

    #[cfg(not(feature = "llvm-backend"))]
    use super::emit_module_stub;

    #[cfg(not(feature = "llvm-backend"))]
    #[test]
    fn backend_disabled_without_feature() {
        let program = Parser::parse_source("def x = 1;").expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let err = emit_module_stub("test", &module).expect_err("backend disabled");
        assert_eq!(
            err.to_string(),
            "LLVM backend is disabled; enable feature `llvm-backend`"
        );
    }
}
