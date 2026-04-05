use std::collections::HashMap;

use crate::types::{Ty, TyId, TyInterner};
use aura_diagnostics::{Diagnostic, Issue};

#[derive(Debug, Clone, Default)]
pub struct Substitutions {
    pub map: HashMap<TyId, TyId>,
}

#[derive(Debug, Clone, Default)]
pub struct Unifier {
    subs: Substitutions,
}

impl Unifier {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn substitutions(&self) -> &Substitutions {
        &self.subs
    }

    pub fn unify(
        &mut self,
        interner: &mut TyInterner,
        lhs: TyId,
        rhs: TyId,
        _context: &str,
    ) -> Result<TyId, Box<Diagnostic>> {
        let lhs = self.resolve(lhs);
        let rhs = self.resolve(rhs);

        if lhs == rhs {
            return Ok(lhs);
        }

        let lhs_ty = interner.get(lhs).cloned();
        let rhs_ty = interner.get(rhs).cloned();

        match (lhs_ty, rhs_ty) {
            (Some(Ty::Any), Some(_)) => Ok(rhs),
            (Some(_), Some(Ty::Any)) => Ok(lhs),
            (Some(Ty::GenericParam(a)), Some(Ty::GenericParam(b))) if a == b => Ok(lhs),
            (Some(Ty::InferVar(_)), Some(_)) => {
                if self.occurs(interner, lhs, rhs) {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyOccurs)
                            .with_related("infinite type would be created", None)
                            .with_hint(
                                "introduce explicit annotation to break recursive inference",
                            ),
                    ));
                }
                self.bind(lhs, rhs);
                Ok(rhs)
            }
            (Some(_), Some(Ty::InferVar(_))) => {
                if self.occurs(interner, rhs, lhs) {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyOccurs)
                            .with_related("infinite type would be created", None)
                            .with_hint(
                                "introduce explicit annotation to break recursive inference",
                            ),
                    ));
                }
                self.bind(rhs, lhs);
                Ok(lhs)
            }
            (Some(Ty::List(a)), Some(Ty::List(b))) => {
                if self.occurs(interner, lhs, b) || self.occurs(interner, rhs, a) {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyOccurs)
                            .with_related("infinite type would be created", None)
                            .with_hint(
                                "introduce explicit annotation to break recursive inference",
                            ),
                    ));
                }
                let item = self.unify(interner, a, b, _context)?;
                Ok(interner.intern(Ty::List(item)))
            }
            (Some(Ty::Ptr(a)), Some(Ty::Ptr(b))) => {
                let item = self.unify(interner, a, b, _context)?;
                Ok(interner.intern(Ty::Ptr(item)))
            }
            (Some(Ty::Slice(a)), Some(Ty::Slice(b))) => {
                let item = self.unify(interner, a, b, _context)?;
                Ok(interner.intern(Ty::Slice(item)))
            }
            (Some(Ty::Dict { key: ka, value: va }), Some(Ty::Dict { key: kb, value: vb })) => {
                if self.occurs(interner, lhs, kb) || self.occurs(interner, rhs, ka) {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyOccurs)
                            .with_related("infinite type would be created", None)
                            .with_hint(
                                "introduce explicit annotation to break recursive inference",
                            ),
                    ));
                }
                let key = self.unify(interner, ka, kb, _context)?;
                let value = self.unify(interner, va, vb, _context)?;
                Ok(interner.intern(Ty::Dict { key, value }))
            }
            (Some(Ty::Set(a)), Some(Ty::Set(b))) => {
                let item = self.unify(interner, a, b, _context)?;
                Ok(interner.intern(Ty::Set(item)))
            }
            (
                Some(Ty::Array {
                    item: item_a,
                    size: size_a,
                }),
                Some(Ty::Array {
                    item: item_b,
                    size: size_b,
                }),
            ) => {
                if size_a != size_b {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyMismatch)
                            .with_related("array length is part of the type", None)
                            .with_hint("use matching array sizes or an explicit conversion path"),
                    ));
                }
                let item = self.unify(interner, item_a, item_b, _context)?;
                Ok(interner.intern(Ty::Array { item, size: size_a }))
            }
            (
                Some(Ty::Func {
                    params: params_a,
                    ret: ret_a,
                }),
                Some(Ty::Func {
                    params: params_b,
                    ret: ret_b,
                }),
            ) => {
                if params_a.len() != params_b.len() {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyMismatch)
                            .with_related("function parameter count differs", None)
                            .with_hint("pass a callable with matching arity"),
                    ));
                }

                let mut params = Vec::with_capacity(params_a.len());
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    params.push(self.unify(interner, *a, *b, _context)?);
                }
                let ret = self.unify(interner, ret_a, ret_b, _context)?;
                Ok(interner.intern(Ty::Func { params, ret }))
            }
            (Some(Ty::Tuple(items_a)), Some(Ty::Tuple(items_b))) => {
                if items_a.len() != items_b.len() {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyMismatch)
                            .with_related("tuple length is part of the type", None)
                            .with_hint("use tuples with matching element counts"),
                    ));
                }

                let mut items = Vec::with_capacity(items_a.len());
                for (a, b) in items_a.iter().zip(items_b.iter()) {
                    items.push(self.unify(interner, *a, *b, _context)?);
                }
                Ok(interner.intern(Ty::Tuple(items)))
            }
            (Some(Ty::Struct(fields_a)), Some(Ty::Struct(fields_b))) => {
                if fields_a.len() != fields_b.len() {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyMismatch)
                            .with_related("struct field count differs", None)
                            .with_hint("align struct field sets before unification"),
                    ));
                }

                let mut fields = Vec::with_capacity(fields_a.len());
                for ((name_a, ty_a), (name_b, ty_b)) in fields_a.iter().zip(fields_b.iter()) {
                    if name_a != name_b {
                        return Err(Box::new(
                            Diagnostic::error(Issue::UnifyMismatch)
                                .with_related("struct field names must match positionally", None)
                                .with_hint(
                                    "ensure both struct shapes use the same field names/order",
                                ),
                        ));
                    }
                    let field_ty = self.unify(interner, *ty_a, *ty_b, _context)?;
                    fields.push((name_a.clone(), field_ty));
                }

                Ok(interner.intern(Ty::Struct(fields)))
            }
            (Some(Ty::Union(items_a)), Some(Ty::Union(items_b))) => {
                if items_a.len() != items_b.len() {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyMismatch)
                            .with_related("union member count differs", None)
                            .with_hint("ensure both union types have the same members"),
                    ));
                }
                let mut items = Vec::with_capacity(items_a.len());
                for (a, b) in items_a.iter().zip(items_b.iter()) {
                    items.push(self.unify(interner, *a, *b, _context)?);
                }
                Ok(interner.intern(Ty::Union(items)))
            }
            (Some(Ty::Enum(variants_a)), Some(Ty::Enum(variants_b))) => {
                if variants_a.len() != variants_b.len() {
                    return Err(Box::new(
                        Diagnostic::error(Issue::UnifyMismatch)
                            .with_related("enum variant count differs", None)
                            .with_hint("ensure both enum types define same variants"),
                    ));
                }

                let mut variants = Vec::with_capacity(variants_a.len());
                for ((name_a, payload_a), (name_b, payload_b)) in
                    variants_a.iter().zip(variants_b.iter())
                {
                    if name_a != name_b {
                        return Err(Box::new(
                            Diagnostic::error(Issue::UnifyMismatch)
                                .with_related("enum variant names must match positionally", None)
                                .with_hint("ensure both enum variants match by name/order"),
                        ));
                    }

                    let payload = match (payload_a, payload_b) {
                        (Some(a), Some(b)) => Some(self.unify(interner, *a, *b, _context)?),
                        (None, None) => None,
                        _ => {
                            return Err(Box::new(
                                Diagnostic::error(Issue::UnifyMismatch)
                                    .with_related("enum variant payload presence differs", None)
                                    .with_hint(
                                        "ensure matching payload arity for each enum variant",
                                    ),
                            ))
                        }
                    };

                    variants.push((name_a.clone(), payload));
                }

                Ok(interner.intern(Ty::Enum(variants)))
            }
            (Some(a), Some(b)) if a == b => Ok(lhs),
            (Some(Ty::Nominal(_)), Some(_)) | (Some(_), Some(Ty::Nominal(_))) => Ok(lhs),
            (Some(_a), Some(_b)) => Err(Box::new(
                Diagnostic::error(Issue::UnifyMismatch)
                    .with_related("type equality constraint failed", None)
                    .with_hint("add an explicit cast or adjust declaration type annotations"),
            )),
            _ => Err(Box::new(Diagnostic::error(Issue::UnifyUnknown))),
        }
    }

    pub fn resolve(&self, id: TyId) -> TyId {
        let mut current = id;
        while let Some(next) = self.subs.map.get(&current).copied() {
            if next == current {
                break;
            }
            current = next;
        }
        current
    }

    fn bind(&mut self, var: TyId, to: TyId) {
        self.subs.map.insert(var, to);
    }

    fn occurs(&self, interner: &TyInterner, var: TyId, within: TyId) -> bool {
        let within = self.resolve(within);
        if var == within {
            return true;
        }
        match interner.get(within) {
            Some(Ty::List(item)) => self.occurs(interner, var, *item),
            Some(Ty::Ptr(item)) => self.occurs(interner, var, *item),
            Some(Ty::Slice(item)) => self.occurs(interner, var, *item),
            Some(Ty::Dict { key, value }) => {
                self.occurs(interner, var, *key) || self.occurs(interner, var, *value)
            }
            Some(Ty::Func { params, ret }) => {
                params.iter().any(|p| self.occurs(interner, var, *p))
                    || self.occurs(interner, var, *ret)
            }
            Some(Ty::Tuple(items)) => items.iter().any(|t| self.occurs(interner, var, *t)),
            Some(Ty::Struct(fields)) => fields.iter().any(|(_, t)| self.occurs(interner, var, *t)),
            Some(Ty::Union(items)) => items.iter().any(|t| self.occurs(interner, var, *t)),
            Some(Ty::Enum(variants)) => variants
                .iter()
                .any(|(_, payload)| payload.is_some_and(|t| self.occurs(interner, var, t))),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::types::{Ty, TyInterner};
    use crate::unify::Unifier;

    #[test]
    fn infer_var_unifies_with_concrete_type() {
        let mut interner = TyInterner::new();
        let mut next = 0;
        let mut unifier = Unifier::new();

        let var = interner.fresh_infer_var(&mut next);
        let int = interner.intern(Ty::Int32);

        let unified = unifier
            .unify(&mut interner, var, int, "test")
            .expect("unify should succeed");
        assert_eq!(unifier.resolve(var), int);
        assert_eq!(unified, int);
    }

    #[test]
    fn incompatible_types_fail_unification() {
        let mut interner = TyInterner::new();
        let mut unifier = Unifier::new();
        let int = interner.intern(Ty::Int32);
        let float = interner.intern(Ty::Float64);

        let err = unifier
            .unify(&mut interner, int, float, "call argument")
            .expect_err("unification should fail");
        assert_eq!(err.code_str(), "E_UNIFY_MISMATCH");
    }

    #[test]
    fn occurs_check_rejects_infinite_type() {
        let mut interner = TyInterner::new();
        let mut next = 0;
        let mut unifier = Unifier::new();
        let var = interner.fresh_infer_var(&mut next);
        let list_of_var = interner.intern(Ty::List(var));

        let err = unifier
            .unify(&mut interner, var, list_of_var, "occurs test")
            .expect_err("occurs check must fail");
        assert_eq!(err.code_str(), "E_UNIFY_OCCURS");
    }

    #[test]
    fn function_types_unify_structurally() {
        let mut interner = TyInterner::new();
        let mut next = 0;
        let mut unifier = Unifier::new();

        let infer_param = interner.fresh_infer_var(&mut next);
        let infer_ret = interner.fresh_infer_var(&mut next);
        let left = interner.intern(Ty::Func {
            params: vec![infer_param],
            ret: infer_ret,
        });

        let int = interner.intern(Ty::Int32);
        let float = interner.intern(Ty::Float32);
        let right = interner.intern(Ty::Func {
            params: vec![int],
            ret: float,
        });

        let unified = unifier
            .unify(&mut interner, left, right, "fn unify")
            .expect("function unification should succeed");

        assert_eq!(unifier.resolve(infer_param), int);
        assert_eq!(unifier.resolve(infer_ret), float);
        let ty = interner.get(unified).expect("type should exist");
        assert!(matches!(ty, Ty::Func { .. }));
    }

    #[test]
    fn tuple_length_mismatch_fails_unification() {
        let mut interner = TyInterner::new();
        let mut unifier = Unifier::new();
        let int = interner.intern(Ty::Int32);

        let t2 = interner.intern(Ty::Tuple(vec![int, int]));
        let t1 = interner.intern(Ty::Tuple(vec![int]));

        let err = unifier
            .unify(&mut interner, t2, t1, "tuple mismatch")
            .expect_err("tuple lengths should mismatch");
        assert_eq!(err.code_str(), "E_UNIFY_MISMATCH");
    }

    #[test]
    fn array_size_mismatch_fails_unification() {
        let mut interner = TyInterner::new();
        let mut unifier = Unifier::new();
        let int = interner.intern(Ty::Int32);

        let a4 = interner.intern(Ty::Array { item: int, size: 4 });
        let a8 = interner.intern(Ty::Array { item: int, size: 8 });

        let err = unifier
            .unify(&mut interner, a4, a8, "array mismatch")
            .expect_err("array size mismatch should fail");
        assert_eq!(err.code_str(), "E_UNIFY_MISMATCH");
    }
}
