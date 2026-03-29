use aura_frontend::ast::{Arm, Pattern};

use crate::diagnostics::Diagnostic;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PatternFamily {
    Unknown,
    Variant,
    BoolLike,
}

#[derive(Debug, Clone, Default)]
pub struct PatternChecker;

impl PatternChecker {
    pub fn new() -> Self {
        Self
    }

    pub fn validate_multi_arm_exhaustiveness(&self, arms: &[Arm]) -> Vec<Diagnostic> {
        if arms.is_empty() {
            return vec![Diagnostic::error(
                "E_PATTERN_EMPTY_ARMS",
                "multi-arm expression must contain at least one arm",
            )
            .with_hint("add at least one pattern arm")];
        }

        if has_wildcard_fallback(arms) {
            return Vec::new();
        }

        let family = classify_family(arms);
        let mut diagnostics = Vec::new();
        match family {
            PatternFamily::Variant => {
                diagnostics.push(
                    Diagnostic::error(
                        "E_PATTERN_NON_EXHAUSTIVE",
                        "non-exhaustive variant patterns: wildcard or full variant coverage required",
                    )
                    .with_hint("add `_ -> ...` or include the missing variant patterns"),
                );
            }
            PatternFamily::BoolLike => {
                diagnostics.push(
                    Diagnostic::error(
                        "E_PATTERN_NON_EXHAUSTIVE",
                        "non-exhaustive boolean-like patterns",
                    )
                    .with_hint("cover both true and false, or add a wildcard arm"),
                );
            }
            PatternFamily::Unknown => {
                diagnostics.push(
                    Diagnostic::error(
                        "E_PATTERN_NON_EXHAUSTIVE",
                        "cannot prove multi-arm expression is exhaustive",
                    )
                    .with_hint("add a wildcard fallback arm (`_ -> ...`)"),
                );
            }
        }

        diagnostics
    }

    pub fn validate_redundancy(&self, arms: &[Arm]) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut seen_fallback = false;
        for (idx, arm) in arms.iter().enumerate() {
            let Some(first) = arm.patterns.first() else {
                continue;
            };

            if seen_fallback {
                diagnostics.push(
                    Diagnostic::error(
                        "E_PATTERN_UNREACHABLE_ARM",
                        format!("arm {idx} is unreachable because a previous wildcard matches all values"),
                    )
                    .with_hint("remove the unreachable arm or reorder patterns"),
                );
                continue;
            }

            if matches!(first, Pattern::Wildcard) {
                seen_fallback = true;
            }
        }

        diagnostics
    }
}

fn has_wildcard_fallback(arms: &[Arm]) -> bool {
    arms.iter()
        .any(|arm| matches!(arm.patterns.first(), Some(Pattern::Wildcard)))
}

fn classify_family(arms: &[Arm]) -> PatternFamily {
    let mut saw_variant = false;
    let mut saw_bool_like = false;
    let mut saw_unknown = false;

    for arm in arms {
        let Some(first) = arm.patterns.first() else {
            saw_unknown = true;
            continue;
        };

        match first {
            Pattern::DotVariant { .. } => saw_variant = true,
            Pattern::Ident(name) if name == "true" || name == "false" => saw_bool_like = true,
            Pattern::Wildcard => {}
            _ => saw_unknown = true,
        }
    }

    if saw_variant && !saw_unknown && !saw_bool_like {
        PatternFamily::Variant
    } else if saw_bool_like && !saw_unknown && !saw_variant {
        PatternFamily::BoolLike
    } else {
        PatternFamily::Unknown
    }
}

#[cfg(test)]
mod tests {
    use aura_frontend::ast::{Arm, Expr, Pattern};

    use crate::patterns::PatternChecker;

    fn mk_arm(pattern: Pattern) -> Arm {
        Arm {
            patterns: vec![pattern],
            body: Expr::Ident("x".to_string()),
        }
    }

    #[test]
    fn non_exhaustive_variant_arms_are_reported() {
        let checker = PatternChecker::new();
        let arms = vec![mk_arm(Pattern::DotVariant {
            name: "ok".to_string(),
            payload: Some(Box::new(Pattern::Ident("v".to_string()))),
        })];

        let diagnostics = checker.validate_multi_arm_exhaustiveness(&arms);
        assert!(!diagnostics.is_empty());
        assert_eq!(diagnostics[0].code, "E_PATTERN_NON_EXHAUSTIVE");
    }

    #[test]
    fn wildcard_fallback_makes_arms_exhaustive() {
        let checker = PatternChecker::new();
        let arms = vec![
            mk_arm(Pattern::DotVariant {
                name: "ok".to_string(),
                payload: None,
            }),
            mk_arm(Pattern::Wildcard),
        ];

        let diagnostics = checker.validate_multi_arm_exhaustiveness(&arms);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn arms_after_wildcard_are_unreachable() {
        let checker = PatternChecker::new();
        let arms = vec![
            mk_arm(Pattern::Wildcard),
            mk_arm(Pattern::Ident("anything".to_string())),
        ];

        let diagnostics = checker.validate_redundancy(&arms);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "E_PATTERN_UNREACHABLE_ARM");
    }
}
