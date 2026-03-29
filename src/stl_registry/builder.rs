use std::collections::HashMap;

use crate::stl_registry::{extractor, StlRegistry};

pub(crate) fn build_stl_registry() -> Result<StlRegistry, String> {
    let mut registry = HashMap::new();
    for path in crate::stl_sources::STL_SIGNATURE_PATHS {
        let Some(src) = crate::stl_sources::stl_source(path) else {
            return Err(format!("missing embedded source for {path}"));
        };
        let (tokens, lex_errs) = crate::lexer::lex(src);
        if !lex_errs.is_empty() {
            return Err(format!("failed to lex {path}: {lex_errs:?}"));
        }
        let (program, parse_errs) = crate::parser::parse_tokens(tokens);
        if !parse_errs.is_empty() {
            return Err(format!("failed to parse {path}: {parse_errs:?}"));
        }

        let exports = extractor::extract_module_exports_strict(path, &program)?;
        registry.insert(path.to_string(), exports);
    }

    Ok(registry)
}
