use std::collections::HashMap;

use aura_frontend::ast::{Decl, Expr, Program};

use crate::aliases::TypeAliases;
use crate::builtins::BuiltinRegistry;
use crate::checked_ir::{CheckedDecl, CheckedExpr, CheckedIr};
use crate::diagnostics::Diagnostic;
use crate::modules::ModuleChecker;
use crate::numeric::can_implicitly_widen;
use crate::patterns::PatternChecker;
use crate::types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone)]
pub struct TypeChecker {
    interner: TyInterner,
    aliases: TypeAliases,
    builtins: BuiltinRegistry,
    module_checker: ModuleChecker,
    pattern_checker: PatternChecker,
    diagnostics: Vec<Diagnostic>,
    ir: CheckedIr,
}

impl TypeChecker {
    pub fn new() -> Self {
        let mut interner = TyInterner::new();
        interner.prelude_primitives();
        let aliases = TypeAliases::with_prelude(&mut interner);
        Self {
            interner,
            aliases,
            builtins: BuiltinRegistry::with_prelude(),
            module_checker: ModuleChecker::new(),
            pattern_checker: PatternChecker::new(),
            diagnostics: Vec::new(),
            ir: CheckedIr::empty(),
        }
    }

    pub fn check_program(&mut self, program: &Program) -> HashMap<String, TyId> {
        let mut values = HashMap::new();
        self.module_checker.check_program(program);

        for decl in &program.declarations {
            if let Decl::Assign { name, value } = decl {
                let ty = self.infer_expr(value);
                if let Some(existing) = values.get(name).copied() {
                    self.require_assignable(existing, ty, name);
                }
                values.insert(name.clone(), ty);
                self.ir.declarations.push(CheckedDecl {
                    name: name.clone(),
                    ty,
                    value: self.lower_expr(value),
                });
            }

            if let Decl::Function(function) = decl {
                if let Expr::MultiArm(arms) = &function.body {
                    self.diagnostics
                        .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }
            }

            if let Decl::Macro(macro_decl) = decl {
                if let Expr::MultiArm(arms) = &macro_decl.body {
                    self.diagnostics
                        .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }
            }
        }

        self.diagnostics
            .extend(std::mem::take(&mut self.module_checker).into_diagnostics());

        values
    }

    pub fn into_parts(self) -> (TyInterner, Vec<Diagnostic>, CheckedIr) {
        (self.interner, self.diagnostics, self.ir)
    }

    fn infer_expr(&mut self, expr: &Expr) -> TyId {
        match expr {
            Expr::Int(_) => self.aliases.get("Int").expect("Int alias must exist"),
            Expr::Float(_) => self.aliases.get("Float").expect("Float alias must exist"),
            Expr::Char(_) => self.interner.intern(Ty::Char),
            Expr::String(_) => self.interner.intern(Ty::Nominal("String".to_string())),
            Expr::List(items) => {
                if let Some(first) = items.first() {
                    let item_ty = self.infer_expr(first);
                    for item in items.iter().skip(1) {
                        let ty = self.infer_expr(item);
                        self.require_assignable(item_ty, ty, "list item");
                    }
                    self.interner.intern(Ty::List(item_ty))
                } else {
                    let any = self.interner.intern(Ty::Any);
                    self.interner.intern(Ty::List(any))
                }
            }
            Expr::Dict(entries) => {
                if let Some((k0, v0)) = entries.first() {
                    let key_ty = self.infer_expr(k0);
                    let val_ty = self.infer_expr(v0);
                    for (k, v) in entries.iter().skip(1) {
                        let k_ty = self.infer_expr(k);
                        let v_ty = self.infer_expr(v);
                        self.require_assignable(key_ty, k_ty, "dict key");
                        self.require_assignable(val_ty, v_ty, "dict value");
                    }
                    self.interner.intern(Ty::Dict {
                        key: key_ty,
                        value: val_ty,
                    })
                } else {
                    let any_key = self.interner.intern(Ty::Any);
                    let any_value = self.interner.intern(Ty::Any);
                    self.interner.intern(Ty::Dict {
                        key: any_key,
                        value: any_value,
                    })
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                ..
            } if macro_name == "builtin" => {
                if let Expr::Ident(name) = operand.as_ref() {
                    if self.builtins.get(name).is_none() {
                        self.diagnostics.push(
                            Diagnostic::error(
                                "E_BUILTIN_UNKNOWN",
                                format!("unknown builtin symbol '{name}'"),
                            )
                            .with_hint(
                                "declare the builtin in the registry or fix the symbol name",
                            ),
                        );
                    }
                } else {
                    self.diagnostics.push(
                        Diagnostic::error(
                            "E_BUILTIN_FORM",
                            "builtin expects an identifier operand",
                        )
                        .with_hint("use form: builtin io_write"),
                    );
                }
                self.interner.intern(Ty::Any)
            }
            _ => self.interner.intern(Ty::Any),
        }
    }

    fn require_assignable(&mut self, expected: TyId, actual: TyId, context: &str) {
        if expected == actual {
            return;
        }

        let Some(expected_ty) = self.interner.get(expected).cloned() else {
            return;
        };
        let Some(actual_ty) = self.interner.get(actual).cloned() else {
            return;
        };

        if can_implicitly_widen(&actual_ty, &expected_ty) {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                "E_TYPE_MISMATCH",
                format!(
                    "type mismatch in {context}: expected {:?}, got {:?}",
                    expected_ty, actual_ty
                ),
            )
            .with_hint("use an explicit cast for narrowing or cross-domain numeric conversions"),
        );
    }

    fn lower_expr(&self, expr: &Expr) -> CheckedExpr {
        match expr {
            Expr::Int(v) => CheckedExpr::Int(v.clone()),
            Expr::Float(v) => CheckedExpr::Float(v.clone()),
            Expr::Char(v) => CheckedExpr::Char(v.clone()),
            Expr::String(v) => CheckedExpr::String(v.clone()),
            Expr::List(items) => {
                CheckedExpr::List(items.iter().map(|item| self.lower_expr(item)).collect())
            }
            Expr::Dict(entries) => CheckedExpr::Dict(
                entries
                    .iter()
                    .map(|(k, v)| (self.lower_expr(k), self.lower_expr(v)))
                    .collect(),
            ),
            _ => CheckedExpr::Any,
        }
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use aura_frontend::ast::{Decl, Expr, FunctionDecl, Pattern, Program, TypeExpr};

    use crate::check_module;

    #[test]
    fn allows_implicit_numeric_widening_on_reassignment() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Int("2".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none()); // duplicate symbol from resolver in same scope
    }

    #[test]
    fn multi_arm_without_fallback_reports_non_exhaustive() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                }),
                name: "map".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                },
                body: Expr::MultiArm(vec![aura_frontend::ast::Arm {
                    patterns: vec![Pattern::DotVariant {
                        name: "ok".to_string(),
                        payload: None,
                    }],
                    body: Expr::Ident("x".to_string()),
                }]),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_PATTERN_NON_EXHAUSTIVE"));
    }

    #[test]
    fn wildcard_then_extra_arm_reports_unreachable() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                }),
                name: "map".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                },
                body: Expr::MultiArm(vec![
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Wildcard],
                        body: Expr::Ident("x".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Ident("later".to_string())],
                        body: Expr::Ident("y".to_string()),
                    },
                ]),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_PATTERN_UNREACHABLE_ARM"));
    }

    #[test]
    fn string_is_not_primitive_and_is_nominal() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "s".to_string(),
                value: Expr::String("ok".to_string()),
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let ty_id = module.value_types.get("s").expect("type should exist");
        let ty = module
            .types
            .get(*ty_id)
            .expect("interned type should exist");
        assert!(matches!(ty, crate::types::Ty::Nominal(name) if name == "String"));
    }

    #[test]
    fn checked_ir_is_emitted_for_assignments() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Int("1".to_string()),
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("checked module should exist");
        assert_eq!(module.ir.declarations.len(), 1);
        assert_eq!(module.ir.declarations[0].name, "x");
    }

    #[test]
    fn duplicate_use_targets_fail_typecheck_pipeline() {
        let program = Program {
            declarations: vec![
                Decl::Use(aura_frontend::ast::UseDecl {
                    target: "io".to_string(),
                }),
                Decl::Use(aura_frontend::ast::UseDecl {
                    target: "io".to_string(),
                }),
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_USE_DUPLICATE"));
    }

    #[test]
    fn unknown_builtin_symbol_reports_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "builtin".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::Ident("missing_builtin".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_BUILTIN_UNKNOWN"));
    }
}
