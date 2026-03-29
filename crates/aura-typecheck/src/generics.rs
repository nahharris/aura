use aura_frontend::ast::{StaticArg, TypeExpr};

use crate::diagnostics::Diagnostic;
use crate::interfaces::InterfaceRegistry;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericConstraint {
    Interface(String),
    Static(TypeExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericParam {
    pub name: String,
    pub constraints: Vec<GenericConstraint>,
}

#[derive(Debug, Default, Clone)]
pub struct GenericChecker {
    interfaces: InterfaceRegistry,
}

impl GenericChecker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn validate_constraints(&self, params: &[GenericParam]) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        for param in params {
            for constraint in &param.constraints {
                if let GenericConstraint::Interface(name) = constraint {
                    if !self.interfaces.contains(name) {
                        diagnostics.push(
                            Diagnostic::error(
                                "E_UNKNOWN_INTERFACE",
                                format!("unknown interface constraint '{name}'"),
                            )
                            .with_hint("declare the interface or use a known prelude interface"),
                        );
                    }
                }
            }
        }
        diagnostics
    }

    pub fn validate_static_args(
        &self,
        constraints: &[GenericConstraint],
        args: &[StaticArg],
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        for (idx, constraint) in constraints.iter().enumerate() {
            if let GenericConstraint::Static(expected) = constraint {
                let Some(arg) = args.get(idx) else {
                    diagnostics.push(
                        Diagnostic::error(
                            "E_STATIC_ARG_MISSING",
                            "missing static argument for constrained generic parameter",
                        )
                        .with_hint("provide all constrained static arguments"),
                    );
                    continue;
                };

                match arg {
                    StaticArg::Value(_) => {}
                    StaticArg::Type(actual_ty) => {
                        diagnostics.push(
                            Diagnostic::error(
                                "E_STATIC_ARG_KIND",
                                format!(
                                    "expected compile-time value for static constraint {:?}, got type argument {:?}",
                                    expected, actual_ty
                                ),
                            )
                            .with_hint("replace type argument with a compile-time-known value"),
                        );
                    }
                }
            }
        }
        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use aura_frontend::ast::{StaticArg, StaticValueExpr, TypeExpr};

    use crate::generics::{GenericChecker, GenericConstraint, GenericParam};

    #[test]
    fn unknown_interface_constraint_is_rejected() {
        let checker = GenericChecker::new();
        let params = vec![GenericParam {
            name: "T".to_string(),
            constraints: vec![GenericConstraint::Interface("Mystery".to_string())],
        }];

        let diagnostics = checker.validate_constraints(&params);
        assert!(!diagnostics.is_empty());
        assert_eq!(diagnostics[0].code, "E_UNKNOWN_INTERFACE");
    }

    #[test]
    fn static_constraints_require_value_arguments() {
        let checker = GenericChecker::new();
        let constraints = vec![GenericConstraint::Static(TypeExpr::Named {
            name: "Int".to_string(),
            args: Vec::new(),
        })];

        let bad = checker.validate_static_args(
            &constraints,
            &[StaticArg::Type(TypeExpr::Named {
                name: "Int".to_string(),
                args: Vec::new(),
            })],
        );
        assert!(!bad.is_empty());
        assert_eq!(bad[0].code, "E_STATIC_ARG_KIND");

        let ok = checker.validate_static_args(
            &constraints,
            &[StaticArg::Value(StaticValueExpr::Int("4".to_string()))],
        );
        assert!(ok.is_empty());
    }
}
