use super::*;

impl TypeChecker {
    /// Check whether `from` is assignable to `to` (widening only).
    ///
    /// # Rules (in order)
    ///
    /// 1. Identity: `from == to → true`
    /// 2. `Never → anything → true` (bottom type)
    /// 3. `anything → Any → true` (top type)
    /// 4. `T → Interface { methods }`: structural subtyping — `T` must expose
    ///    every method in the interface with a compatible type.
    /// 5. `T → Union(members)`: widening — `T` must be assignable to at least
    ///    one member.
    /// 6. `Union(from_members) → Union(to)`: each from-member must be
    ///    assignable to some to-member.
    /// 7. `Struct ↔ Struct`: same name (or both anonymous) → field-wise check;
    ///    different names → false.
    /// 8. `Tuple ↔ Tuple`: element-wise, same length.
    /// 9. `Tuple ↔ Struct → false` (incompatible structural kinds).
    /// 10. All else → false.
    pub(crate) fn is_assignable(&self, from: &Type, to: &Type) -> bool {
        if from == to {
            return true;
        }
        if matches!(from, Type::Never) {
            return true;
        }
        if to.is_any() {
            return true;
        }
        if from.is_any() {
            return true;
        }

        match (from, to) {
            (
                _,
                Type::Interface {
                    methods: to_methods,
                    ..
                },
            ) => to_methods
                .iter()
                .all(|(name, expected_ty)| self.type_has_method(from, name, expected_ty)),

            (_, Type::Union(members)) => members.iter().any(|m| self.is_assignable(from, m)),

            (Type::Union(from_members), _) => {
                from_members.iter().all(|fm| self.is_assignable(fm, to))
            }

            (
                Type::Struct {
                    name: from_name,
                    fields: from_fields,
                },
                Type::Struct {
                    name: to_name,
                    fields: to_fields,
                },
            ) => {
                match (from_name, to_name) {
                    (Some(a), Some(b)) if a != b => return false,
                    _ => {}
                }
                if from_fields.len() != to_fields.len() {
                    return false;
                }
                from_fields.iter().all(|(fname, fty)| {
                    to_fields
                        .iter()
                        .find(|(n, _)| n == fname)
                        .is_some_and(|(_, tty)| self.is_assignable(fty, tty))
                })
            }

            (Type::Tuple(from_elems), Type::Tuple(to_elems)) => {
                from_elems.len() == to_elems.len()
                    && from_elems
                        .iter()
                        .zip(to_elems.iter())
                        .all(|(f, t)| self.is_assignable(f, t))
            }

            (Type::Array { elem: e1, len: n1 }, Type::Array { elem: e2, len: n2 }) => {
                let len_ok = *n2 == 0 || *n1 == 0 || n1 == n2;
                len_ok && self.is_assignable(e1, e2)
            }

            (Type::Set(e1), Type::Set(e2)) => self.is_assignable(e1, e2),

            (Type::Tuple(_), Type::Struct { .. }) | (Type::Struct { .. }, Type::Tuple(_)) => false,

            _ => false,
        }
    }

    fn type_has_method(&self, ty: &Type, name: &str, expected: &Type) -> bool {
        match ty {
            Type::Interface { methods, .. } => methods
                .iter()
                .find(|(n, _)| n == name)
                .is_some_and(|(_, t)| self.is_assignable(t, expected)),
            _ if ty.is_any() => true,
            _ => false,
        }
    }

    pub(crate) fn check_cast(&mut self, from_ty: &Type, to_ty: &Type, span: Span) {
        if from_ty == to_ty {
            return;
        }
        if matches!(from_ty, Type::Never) {
            return;
        }
        if to_ty.is_any() || matches!(to_ty, Type::Interface { .. }) {
            return;
        }
        if matches!(to_ty, Type::Union(_)) {
            return;
        }
        if from_ty.is_any()
            || matches!(from_ty, Type::Union(_))
            || matches!(from_ty, Type::Interface { .. })
        {
            return;
        }
        if matches!(
            (from_ty, to_ty),
            (Type::Int, Type::Float) | (Type::Float, Type::Int)
        ) {
            return;
        }
        if matches!(
            (from_ty, to_ty),
            (Type::Tuple(_), Type::Struct { .. }) | (Type::Struct { .. }, Type::Tuple(_))
        ) {
            self.error(
                format!(
                    "cannot cast between tuple and struct types ({} : {})",
                    from_ty.display_name(),
                    to_ty.display_name()
                ),
                span,
            );
            return;
        }
        if let (Type::Struct { name: Some(a), .. }, Type::Struct { name: Some(b), .. }) =
            (from_ty, to_ty)
        {
            if a != b {
                self.error(
                    format!("cannot cast between distinct named types `{a}` and `{b}`"),
                    span,
                );
                return;
            }
        }
        if let (Type::Struct { .. }, Type::Struct { .. }) = (from_ty, to_ty) {
            return;
        }
        if let (Type::Tuple(_), Type::Tuple(_)) = (from_ty, to_ty) {
            return;
        }
        if let (
            Type::Array {
                elem: e_arr,
                len: n_arr,
            },
            Type::Tuple(elems),
        ) = (from_ty, to_ty)
        {
            if (*n_arr == 0 || elems.len() == *n_arr)
                && elems.iter().all(|t| self.is_assignable(e_arr, t))
            {
                return;
            }
        }
        if let (
            Type::Tuple(elems),
            Type::Array {
                elem: e_arr,
                len: n_arr,
            },
        ) = (from_ty, to_ty)
        {
            if (*n_arr == 0 || elems.len() == *n_arr)
                && elems.iter().all(|t| self.is_assignable(t, e_arr))
            {
                return;
            }
        }
        if self.is_assignable(from_ty, to_ty) {
            return;
        }
        self.error(
            format!(
                "invalid cast: cannot cast `{}` to `{}`",
                from_ty.display_name(),
                to_ty.display_name()
            ),
            span,
        );
    }
}
