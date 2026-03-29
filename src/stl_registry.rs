use std::collections::HashMap;
use std::sync::OnceLock;

use crate::typechecker::{Type, TypeChecker};

pub(crate) type StlModuleExports = HashMap<String, Type>;
pub(crate) type StlRegistry = HashMap<String, StlModuleExports>;

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

fn build_stl_registry() -> Result<StlRegistry, String> {
    let modules: [(&str, &str); 8] = [
        ("@stl/core", include_str!("../stl/core.aura")),
        ("@stl/io", include_str!("../stl/io.aura")),
        ("@stl/string", include_str!("../stl/string.aura")),
        ("@stl/list", include_str!("../stl/list.aura")),
        ("@stl/collections", include_str!("../stl/collections.aura")),
        ("@stl/bool", include_str!("../stl/bool.aura")),
        ("@stl/option", include_str!("../stl/option.aura")),
        ("@stl/result", include_str!("../stl/result.aura")),
    ];

    let mut registry = HashMap::new();
    for (path, src) in modules {
        let (tokens, lex_errs) = crate::lexer::lex(src);
        if !lex_errs.is_empty() {
            return Err(format!("failed to lex {path}: {lex_errs:?}"));
        }
        let (program, parse_errs) = crate::parser::parse_tokens(tokens);
        if !parse_errs.is_empty() {
            return Err(format!("failed to parse {path}: {parse_errs:?}"));
        }

        let mut checker = TypeChecker::new();
        let exports = checker.extract_module_exports_strict(path, &program)?;
        registry.insert(path.to_string(), exports);
    }

    Ok(registry)
}
