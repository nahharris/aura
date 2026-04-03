use std::collections::HashMap;

use aura_diagnostics::{Diagnostic, Issue, Stage};
use aura_frontend::ast::{Decl, Program};

use crate::symbols::{ScopeId, Symbol, SymbolId, SymbolKind};

#[derive(Debug, Clone, Default)]
pub struct ResolvedSymbols {
    pub symbols: Vec<Symbol>,
    pub by_name: HashMap<(ScopeId, String), SymbolId>,
}

#[derive(Debug, Clone)]
struct Scope {
    parent: Option<ScopeId>,
}

#[derive(Debug, Clone)]
pub struct Resolver {
    scopes: Vec<Scope>,
    current_scope: ScopeId,
    next_symbol_id: usize,
    resolved: ResolvedSymbols,
    diagnostics: Vec<Diagnostic>,
}

impl Resolver {
    pub fn new() -> Self {
        let root = Scope { parent: None };
        Self {
            scopes: vec![root],
            current_scope: ScopeId(0),
            next_symbol_id: 0,
            resolved: ResolvedSymbols::default(),
            diagnostics: Vec::new(),
        }
    }

    pub fn resolve_program(&mut self, program: &Program) -> ResolvedSymbols {
        for decl in &program.declarations {
            match decl {
                Decl::Assign { name, .. } => self.declare(name, SymbolKind::Value),
                Decl::Macro(m) => self.declare(&m.name, SymbolKind::Function),
                Decl::Function(f) => self.declare(&f.name, SymbolKind::Function),
                Decl::Use(u) => self.declare(&u.target, SymbolKind::Module),
            }
        }

        self.resolved.clone()
    }

    pub fn into_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    fn declare(&mut self, name: &str, kind: SymbolKind) {
        let key = (self.current_scope, name.to_string());
        if self.resolved.by_name.contains_key(&key) {
            self.diagnostics.push(
                Diagnostic::error(Issue::ResolveDuplicate)
                    .with_stage(Stage::Resolver)
                    .with_hint("rename one declaration or remove the duplicate"),
            );
            return;
        }

        let symbol_id = SymbolId(self.next_symbol_id);
        self.next_symbol_id += 1;

        self.resolved.symbols.push(Symbol {
            id: symbol_id,
            name: name.to_string(),
            kind,
            scope: self.current_scope,
        });
        self.resolved.by_name.insert(key, symbol_id);
    }

    #[allow(dead_code)]
    fn push_scope(&mut self) {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope {
            parent: Some(self.current_scope),
        });
        self.current_scope = id;
    }

    #[allow(dead_code)]
    fn pop_scope(&mut self) {
        let parent = self.scopes[self.current_scope.0].parent;
        if let Some(parent) = parent {
            self.current_scope = parent;
        }
    }
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use aura_frontend::ast::{Decl, Expr, Program};

    use crate::check_module;

    #[test]
    fn resolver_reports_duplicate_symbols() {
        let program = Program {
            declarations: vec![
                Decl::Assign { doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign { doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("2".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_RESOLVE_DUP"));
    }

    #[test]
    fn resolver_collects_distinct_symbols() {
        let program = Program {
            declarations: vec![
                Decl::Assign { doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign { doc: None,
                    name: "y".to_string(),
                    value: Expr::Int("2".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(checked.diagnostics.is_empty());
    }
}
