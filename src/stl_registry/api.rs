use std::sync::OnceLock;

use crate::stl_registry::{builder::build_stl_registry, StlModuleExports, StlRegistry};
use crate::typechecker::Type;

pub(crate) fn stl_module_exports(path: &str) -> Result<Option<StlModuleExports>, String> {
    match stl_registry() {
        Ok(reg) => Ok(reg.get(path).cloned()),
        Err(err) => Err(err.clone()),
    }
}

pub(crate) fn stl_module_type(path: &str) -> Result<Option<Type>, String> {
    Ok(stl_module_exports(path)?.map(|exports| Type::Module {
        path: path.to_string(),
        exports,
    }))
}

pub(crate) fn stl_registry() -> &'static Result<StlRegistry, String> {
    static REGISTRY: OnceLock<Result<StlRegistry, String>> = OnceLock::new();
    REGISTRY.get_or_init(build_stl_registry)
}
