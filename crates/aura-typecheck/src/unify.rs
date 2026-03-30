use std::collections::HashMap;

use crate::diagnostics::Diagnostic;
use crate::types::{Ty, TyId, TyInterner};

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
        context: &str,
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
            (Some(Ty::InferVar(_)), Some(_)) => {
                self.bind(lhs, rhs);
                Ok(rhs)
            }
            (Some(_), Some(Ty::InferVar(_))) => {
                self.bind(rhs, lhs);
                Ok(lhs)
            }
            (Some(Ty::List(a)), Some(Ty::List(b))) => {
                let item = self.unify(interner, a, b, context)?;
                Ok(interner.intern(Ty::List(item)))
            }
            (Some(Ty::Dict { key: ka, value: va }), Some(Ty::Dict { key: kb, value: vb })) => {
                let key = self.unify(interner, ka, kb, context)?;
                let value = self.unify(interner, va, vb, context)?;
                Ok(interner.intern(Ty::Dict { key, value }))
            }
            (Some(a), Some(b)) if a == b => Ok(lhs),
            (Some(a), Some(b)) => Err(Box::new(
                Diagnostic::error(
                    "E_UNIFY_MISMATCH",
                    format!("cannot unify {a:?} with {b:?} in {context}"),
                )
                .with_related("type equality constraint failed", None)
                .with_hint("add an explicit cast or adjust declaration type annotations"),
            )),
            _ => Err(Box::new(Diagnostic::error(
                "E_UNIFY_UNKNOWN",
                "internal unify failure: missing type in interner",
            ))),
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
        assert_eq!(err.code, "E_UNIFY_MISMATCH");
    }
}
