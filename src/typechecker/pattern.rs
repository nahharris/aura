use super::*;

impl TypeChecker {
    /// Check `pat` against `subject_ty`, populate `env` with typed bindings,
    /// and emit errors for type mismatches.
    ///
    /// Returns the *narrowed* type that the pattern matches (useful for binding
    /// names to more-specific types in the arm body).
    pub(crate) fn check_pattern(
        &mut self,
        pat: &Pattern,
        subject_ty: &Type,
        env: &mut TypeEnv,
    ) -> Type {
        match pat {
            // -- Wildcard: no binding, no check
            Pattern::Wildcard(_) => subject_ty.clone(),

            // -- Bind: bind name to subject type
            Pattern::Bind(name, _) => {
                env.bindings.insert(name.clone(), subject_ty.clone());
                subject_ty.clone()
            }

            // -- Literal: verify literal type is compatible
            Pattern::Literal(lit_expr) => {
                let lit_ty = self.infer_expr(lit_expr, env);
                if !self.is_assignable(&lit_ty, subject_ty) && !subject_ty.is_any() {
                    self.error(
                        format!(
                            "literal pattern type {} is not compatible with subject type {}",
                            lit_ty.display_name(),
                            subject_ty.display_name()
                        ),
                        lit_expr.span(),
                    );
                }
                lit_ty
            }

            // -- TypeCheck: bind name to the checked (narrowed) type
            Pattern::TypeCheck { name, ty, span } => {
                let checked_ty = self.resolve_type_expr(ty);
                env.bindings.insert(name.clone(), checked_ty.clone());
                let _ = span;
                checked_ty
            }

            // -- Tuple: check arity and recurse into elements
            Pattern::Tuple(pats, span) => {
                let elems: Vec<Type> = match subject_ty {
                    Type::Tuple(elems) => {
                        if elems.len() != pats.len() {
                            self.error(
                                format!(
                                    "tuple pattern has {} elements but subject has {}",
                                    pats.len(),
                                    elems.len()
                                ),
                                *span,
                            );
                        }
                        elems.clone()
                    }
                    _ if subject_ty.is_any() => vec![Type::Any; pats.len()],
                    other => {
                        self.error(
                            format!(
                                "tuple pattern cannot match subject of type {}",
                                other.display_name()
                            ),
                            *span,
                        );
                        vec![Type::Any; pats.len()]
                    }
                };
                let resolved_elems: Vec<Type> = pats
                    .iter()
                    .zip(elems.into_iter().chain(std::iter::repeat(Type::Any)))
                    .map(|(sub_pat, elem_ty)| self.check_pattern(sub_pat, &elem_ty, env))
                    .collect();
                Type::Tuple(resolved_elems)
            }

            // -- Struct: check field names exist and recurse
            Pattern::Struct { fields, span } => {
                let field_types: Vec<(String, Type)> = match subject_ty {
                    Type::Struct {
                        fields: src_fields, ..
                    } => src_fields.clone(),
                    _ if subject_ty.is_any() => vec![],
                    other => {
                        self.error(
                            format!(
                                "struct pattern cannot match subject of type {}",
                                other.display_name()
                            ),
                            *span,
                        );
                        vec![]
                    }
                };
                for spf in fields {
                    let field_ty = field_types
                        .iter()
                        .find(|(n, _)| n == &spf.name)
                        .map_or_else(
                            || {
                                if !subject_ty.is_any() {
                                    self.error(
                                        format!(
                                            "struct pattern references unknown field `{}`",
                                            spf.name
                                        ),
                                        spf.span,
                                    );
                                }
                                Type::Any
                            },
                            |(_, t)| t.clone(),
                        );
                    let binding_name = spf.binding.as_ref().unwrap_or(&spf.name).clone();
                    env.bindings.insert(binding_name, field_ty);
                }
                subject_ty.clone()
            }

            // -- Variant: check against Enum type, bind inner
            Pattern::Variant { name, inner, span } => {
                let inner_ty = match subject_ty {
                    Type::Enum { variants, .. } => variants
                        .iter()
                        .find(|(vname, _)| vname == name)
                        .map_or_else(
                            || {
                                self.error(
                                    format!(
                                        "variant `.{}` does not exist in enum type {}",
                                        name,
                                        subject_ty.display_name()
                                    ),
                                    *span,
                                );
                                Type::Any
                            },
                            |(_, payload)| payload.clone().unwrap_or(Type::Void),
                        ),
                    _ if subject_ty.is_any() => Type::Any,
                    other => {
                        self.error(
                            format!(
                                "variant pattern `.{}` cannot match subject of type {}",
                                name,
                                other.display_name()
                            ),
                            *span,
                        );
                        Type::Any
                    }
                };
                if let Some(inner_pat) = inner {
                    self.check_pattern(inner_pat, &inner_ty, env);
                }
                inner_ty
            }

            // -- Constructor: look up named type, bind inner
            Pattern::Constructor {
                type_name,
                inner,
                span,
            } => {
                let alias_ty = self.env.lookup_alias(type_name).cloned();
                match alias_ty {
                    Some(Type::Struct { fields, .. }) => {
                        let reconstructed = Type::Struct {
                            name: Some(type_name.clone()),
                            fields,
                        };
                        self.check_pattern(inner, &reconstructed, env);
                        reconstructed
                    }
                    Some(Type::Tuple(elems)) => {
                        let reconstructed = Type::Tuple(elems);
                        self.check_pattern(inner, &reconstructed, env);
                        reconstructed
                    }
                    Some(other) => {
                        self.check_pattern(inner, &other, env);
                        other
                    }
                    None => {
                        let _ = span;
                        self.check_pattern(inner, &Type::Any, env);
                        Type::Any
                    }
                }
            }

            // -- Rest: bind name to List<subject>
            Pattern::Rest { name, .. } => {
                let list_ty = Type::List(Box::new(subject_ty.clone()));
                if let Some(n) = name {
                    env.bindings.insert(n.clone(), list_ty.clone());
                }
                list_ty
            }
        }
    }

    /// Check closure-arm exhaustiveness for known subject types.
    pub(crate) fn check_exhaustiveness(
        &mut self,
        arms: &[ClosureArm],
        subject_ty: &Type,
        span: Span,
    ) {
        let has_catch_all = arms.iter().any(|arm| {
            arm.guard.is_none()
                && arm
                    .patterns
                    .first()
                    .is_some_and(|p| matches!(p, Pattern::Wildcard(_) | Pattern::Bind(_, _)))
        });
        if has_catch_all {
            return;
        }

        match subject_ty {
            Type::Bool => {
                let has_true = arms.iter().any(|arm| {
                    arm.patterns.first().is_some_and(
                        |p| matches!(p, Pattern::Literal(Expr::Ident(s, _)) if s == "true"),
                    )
                });
                let has_false = arms.iter().any(|arm| {
                    arm.patterns.first().is_some_and(
                        |p| matches!(p, Pattern::Literal(Expr::Ident(s, _)) if s == "false"),
                    )
                });
                if !has_true {
                    self.error(
                        "non-exhaustive pattern match: missing `true` case for Bool",
                        span,
                    );
                }
                if !has_false {
                    self.error(
                        "non-exhaustive pattern match: missing `false` case for Bool",
                        span,
                    );
                }
            }
            Type::Enum { variants, .. } => {
                for (vname, _) in variants {
                    let covered = arms.iter().any(|arm| {
                        arm.patterns.first().is_some_and(|p| match p {
                            Pattern::Variant { name, .. } => name == vname,
                            _ => false,
                        })
                    });
                    if !covered {
                        self.error(
                            format!(
                                "non-exhaustive pattern match: variant `.{}` is not covered",
                                vname
                            ),
                            span,
                        );
                    }
                }
            }
            Type::Union(members) => {
                for member in members {
                    self.check_exhaustiveness(arms, member, span);
                }
            }
            _ => {}
        }
    }
}
