use aura_diagnostics::Severity;
use aura_frontend::Parser;

fn render(diag: &aura_diagnostics::Diagnostic) -> String {
    let sev = match diag.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
    };
    let stage = format!("{:?}", diag.stage).to_lowercase();
    let span = diag
        .span
        .map(|s| format!("{}:{}", s.line, s.column))
        .unwrap_or_else(|| "-".to_string());
    format!(
        "{sev}|{stage}|{}|{}|{}",
        diag.code_str(),
        diag.message,
        span
    )
}

#[test]
fn snapshot_lexer_unterminated_string_diagnostic() {
    let err = Parser::parse_source("x = \"hello").expect_err("should fail");
    let got = render(&err);
    let expected = "error|lexer|E_LEX_STRING_UNTERMINATED|unterminated string literal|1:5";
    assert_eq!(got, expected);
}

#[test]
fn snapshot_parser_missing_macro_operand_diagnostic() {
    let err = Parser::parse_source("def x = macro_name[T]").expect_err("should fail");
    let got = render(&err);
    assert!(got.contains("error|parser|E_PARSE_UNEXPECTED_TOKEN|"));
    assert!(got.contains("expected '('") || got.contains("missing operand"));
    assert!(got.contains("|1:"));
}

#[test]
fn snapshot_parser_malformed_static_arg_list_diagnostic() {
    let err = Parser::parse_source("defmacro[T,,] m(node: Expr[T]) -> Expr[T] { node }")
        .expect_err("should fail");
    let got = render(&err);
    assert!(got.contains("error|parser|E_PARSE_UNEXPECTED_TOKEN|"));
    assert!(got.contains("expected:") && got.contains("found:"));
}
