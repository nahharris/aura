use std::collections::HashMap;

use aura_frontend::ast::{Decl, Program};

use crate::diagnostics::Diagnostic;

#[derive(Debug, Clone, Default)]
pub struct ModuleImports {
    pub namespaces: HashMap<String, String>,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleChecker {
    imports: ModuleImports,
    diagnostics: Vec<Diagnostic>,
}

impl ModuleChecker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn check_program(&mut self, program: &Program) {
        for decl in &program.declarations {
            if let Decl::Use(use_decl) = decl {
                if self.imports.namespaces.contains_key(&use_decl.target) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            "E_USE_DUPLICATE",
                            format!("duplicate use target '{}'", use_decl.target),
                        )
                        .with_hint("rename one import target or remove duplicate import"),
                    );
                    continue;
                }

                self.imports
                    .namespaces
                    .insert(use_decl.target.clone(), use_decl.target.clone());
            }
        }
    }

    pub fn imports(&self) -> &ModuleImports {
        &self.imports
    }

    pub fn into_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }
}

#[cfg(test)]
mod tests {
    use aura_frontend::ast::{Decl, Program, UseDecl};

    use crate::modules::ModuleChecker;

    #[test]
    fn duplicate_use_targets_are_rejected() {
        let program = Program {
            declarations: vec![
                Decl::Use(UseDecl {
                    target: "io".to_string(),
                }),
                Decl::Use(UseDecl {
                    target: "io".to_string(),
                }),
            ],
        };

        let mut checker = ModuleChecker::new();
        checker.check_program(&program);
        let diagnostics = checker.into_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "E_USE_DUPLICATE");
    }
}
