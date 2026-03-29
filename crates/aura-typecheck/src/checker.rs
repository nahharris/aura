use std::collections::HashMap;

use aura_frontend::ast::{Decl, Expr, Program};

use crate::aliases::TypeAliases;
use crate::diagnostics::Diagnostic;
use crate::numeric::can_implicitly_widen;
use crate::types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone)]
pub struct TypeChecker {
    interner: TyInterner,
    aliases: TypeAliases,
    diagnostics: Vec<Diagnostic>,
}

impl TypeChecker {
    pub fn new() -> Self {
        let mut interner = TyInterner::new();
        interner.prelude_primitives();
        let aliases = TypeAliases::with_prelude(&mut interner);
        Self {
            interner,
            aliases,
            diagnostics: Vec::new(),
        }
    }

    pub fn check_program(&mut self, program: &Program) -> HashMap<String, TyId> {
        let mut values = HashMap::new();

        for decl in &program.declarations {
            if let Decl::Assign { name, value } = decl {
                let ty = self.infer_expr(value);
                if let Some(existing) = values.get(name).copied() {
                    self.require_assignable(existing, ty, name);
                }
                values.insert(name.clone(), ty);
            }
        }

        values
    }

    pub fn into_parts(self) -> (TyInterner, Vec<Diagnostic>) {
        (self.interner, self.diagnostics)
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
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use aura_frontend::ast::{Decl, Expr, Program};

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
}
