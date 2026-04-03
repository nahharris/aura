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
    pub code: &'static str,
    pub stage: Stage,
    pub severity: Severity,
    pub message: String,
    pub span: Option<Span>,
    pub hint: Option<String>,
    pub related: Vec<RelatedLabel>,
    pub obligations: Vec<String>,
}

impl Diagnostic {
    pub fn error(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            stage: Stage::Typecheck,
            severity: Severity::Error,
            message: message.into(),
            span: None,
            hint: None,
            related: Vec::new(),
            obligations: Vec::new(),
        }
    }

    pub fn warning(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            stage: Stage::Typecheck,
            severity: Severity::Warning,
            message: message.into(),
            span: None,
            hint: None,
            related: Vec::new(),
            obligations: Vec::new(),
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

#[cfg(test)]
mod tests {
    use super::{Diagnostic, Severity, Span, Stage};

    #[test]
    fn shared_diagnostic_builder_supports_core_fields() {
        let diagnostic = Diagnostic::error("E_TEST", "base")
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
