pub mod issue;
pub mod type_ref;
pub mod typing_context;

use miette::MietteDiagnostic;

pub use issue::Issue;
pub use type_ref::{PrimitiveType, TypeRef};
pub use typing_context::TypingContext;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    Lexer,
    Parser,
    Resolver,
    Typecheck,
    Ir,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedLabel {
    pub label: String,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub issue: Issue,
    pub stage: Stage,
    pub severity: Severity,
    pub message: String,
    pub span: Option<Span>,
    pub hint: Option<String>,
    pub related: Vec<RelatedLabel>,
    pub obligations: Vec<String>,
}

impl Diagnostic {
    pub fn error(issue: Issue) -> Self {
        let hint = issue.default_hint().map(str::to_string);
        Self {
            issue: issue.clone(),
            stage: Stage::Typecheck,
            severity: Severity::Error,
            message: issue.message(),
            span: None,
            hint,
            related: Vec::new(),
            obligations: Vec::new(),
        }
    }

    pub fn warning(issue: Issue) -> Self {
        let hint = issue.default_hint().map(str::to_string);
        Self {
            issue: issue.clone(),
            stage: Stage::Typecheck,
            severity: Severity::Warning,
            message: issue.message(),
            span: None,
            hint,
            related: Vec::new(),
            obligations: Vec::new(),
        }
    }

    pub fn code_str(&self) -> &'static str {
        self.issue.code()
    }

    pub fn to_miette(&self) -> MietteDiagnostic {
        MietteDiagnostic {
            message: self.message.clone(),
            code: Some(self.issue.code().to_string()),
            severity: Some(match self.severity {
                Severity::Error => miette::Severity::Error,
                Severity::Warning => miette::Severity::Warning,
            }),
            help: self.hint.clone(),
            labels: None,
            url: None,
        }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn with_span_opt(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    pub fn with_stage(mut self, stage: Stage) -> Self {
        self.stage = stage;
        self
    }

    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hint = Some(hint.into());
        self
    }

    pub fn with_related(mut self, label: impl Into<String>, span: Option<Span>) -> Self {
        self.related.push(RelatedLabel {
            label: label.into(),
            span,
        });
        self
    }

    pub fn with_obligations(mut self, obligations: &[String]) -> Self {
        self.obligations.extend(obligations.iter().cloned());
        self
    }
}

impl PartialEq<&str> for Issue {
    fn eq(&self, other: &&str) -> bool {
        self.code() == *other
    }
}

#[cfg(test)]
mod tests {
    use super::{Diagnostic, Issue, PrimitiveType, Severity, Span, Stage, TypeRef, TypingContext};

    #[test]
    fn shared_diagnostic_builder_supports_core_fields() {
        let diagnostic = Diagnostic::error(Issue::TypeMismatch {
            context: TypingContext::Assignment,
            expected: TypeRef::Primitive(PrimitiveType::Int32),
            actual: TypeRef::Primitive(PrimitiveType::Float64),
        })
        .with_stage(Stage::Typecheck)
        .with_span(Span {
            start: 0,
            end: 1,
            line: 1,
            column: 1,
        })
        .with_hint("hint")
        .with_related("related context", None)
        .with_obligations(&["while checking call argument".to_string()]);

        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(diagnostic.related.len(), 1);
        assert_eq!(diagnostic.related[0].label, "related context");
        assert_eq!(diagnostic.obligations.len(), 1);
        assert_eq!(diagnostic.stage, Stage::Typecheck);
        assert!(diagnostic.span.is_some());
    }
}
