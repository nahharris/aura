pub mod aliases;
pub mod builtins;
pub mod checked_ir;
pub mod checker;
pub mod diagnostics;
pub mod generics;
pub mod interfaces;
pub mod modules;
pub mod numeric;
pub mod patterns;
pub mod resolver;
pub mod symbols;
pub mod types;
pub mod unify;

use aura_frontend::ast::Program;
use std::collections::HashMap;

use checker::TypeChecker;
pub use diagnostics::{Diagnostic, Severity};
pub use resolver::Resolver;
pub use symbols::{ScopeId, SymbolId, SymbolKind};
pub use types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone)]
pub struct CheckedModule {
    pub symbols: resolver::ResolvedSymbols,
    pub value_types: HashMap<String, TyId>,
    pub types: TyInterner,
    pub ir: checked_ir::CheckedIr,
}

#[derive(Debug, Clone)]
pub struct CheckResult {
    pub module: Option<CheckedModule>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check_module(ast: &Program) -> CheckResult {
    let mut resolver = Resolver::new();
    let symbols = resolver.resolve_program(ast);
    let mut diagnostics = resolver.into_diagnostics();

    let mut checker = TypeChecker::new();
    let value_types = checker.check_program(ast);
    let (types, checker_diagnostics, ir) = checker.into_parts();
    diagnostics.extend(checker_diagnostics);

    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return CheckResult {
            module: None,
            diagnostics,
        };
    }

    CheckResult {
        module: Some(CheckedModule {
            symbols,
            value_types,
            types,
            ir,
        }),
        diagnostics,
    }
}
