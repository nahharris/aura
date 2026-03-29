pub mod aliases;
pub mod diagnostics;
pub mod resolver;
pub mod symbols;
pub mod types;

use aura_frontend::ast::Program;

pub use diagnostics::{Diagnostic, Severity};
pub use resolver::Resolver;
pub use symbols::{ScopeId, SymbolId, SymbolKind};
pub use types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone)]
pub struct CheckedModule {
    pub symbols: resolver::ResolvedSymbols,
}

#[derive(Debug, Clone)]
pub struct CheckResult {
    pub module: Option<CheckedModule>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check_module(ast: &Program) -> CheckResult {
    let mut resolver = Resolver::new();
    let symbols = resolver.resolve_program(ast);
    let diagnostics = resolver.into_diagnostics();

    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return CheckResult {
            module: None,
            diagnostics,
        };
    }

    CheckResult {
        module: Some(CheckedModule { symbols }),
        diagnostics,
    }
}
