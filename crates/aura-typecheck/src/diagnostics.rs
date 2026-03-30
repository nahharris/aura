use aura_frontend::token::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedLabel {
    pub label: String,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: &'static str,
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
            severity: Severity::Error,
            message: message.into(),
            span: None,
            hint: None,
            related: Vec::new(),
            obligations: Vec::new(),
        }
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
    use crate::diagnostics::{Diagnostic, Severity};

    #[test]
    fn diagnostic_can_attach_related_labels() {
        let diagnostic = Diagnostic::error("E_TEST", "base")
            .with_hint("hint")
            .with_related("related context", None)
            .with_obligations(&["while checking call argument".to_string()]);

        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(diagnostic.related.len(), 1);
        assert_eq!(diagnostic.related[0].label, "related context");
        assert_eq!(diagnostic.obligations.len(), 1);
    }
}
