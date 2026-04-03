use aura_diagnostics::Severity;
use aura_frontend::Parser;
use aura_typecheck::check_module;

fn render(diag: &aura_diagnostics::Diagnostic) -> String {
    let sev = match diag.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
    };
    let stage = format!("{:?}", diag.stage).to_lowercase();
    let obligations = if diag.obligations.is_empty() {
        "-".to_string()
    } else {
        diag.obligations.join(" > ")
    };
    format!(
        "{sev}|{stage}|{}|{}|{}",
        diag.code, diag.message, obligations
    )
}

#[test]
fn snapshot_unresolved_identifier_warning_shape() {
    let parsed = Parser::parse_source("def x = y").expect("parse should succeed");
    let checked = check_module(&parsed);
    let diag = checked
        .diagnostics
        .iter()
        .find(|d| d.code == "W_UNRESOLVED_IDENT")
        .expect("expected unresolved identifier warning");

    let got = render(diag);
    assert!(got.contains("warning|typecheck|W_UNRESOLVED_IDENT|"));
    assert!(got.contains("unresolved identifier 'y'"));
    assert!(got.contains("checking declaration 'x'"));
}

#[test]
fn snapshot_static_bound_kind_error_shape() {
    let src = "def[n: static Int] f(x: Int) -> Int { x }; def y = f[Int](1)";
    let parsed = Parser::parse_source(src).expect("parse should succeed");
    let checked = check_module(&parsed);
    let diag = checked
        .diagnostics
        .iter()
        .find(|d| d.code == "E_STATIC_ARG_KIND")
        .expect("expected static arg kind diagnostic");

    let got = render(diag);
    let expected_prefix =
        "error|typecheck|E_STATIC_ARG_KIND|expected compile-time static value for constraint Named { name: \"Int\", args: [] } in generic call 'f' for 'n'|checking declaration 'y' > checking call expression";
    assert!(got.starts_with(expected_prefix));
}

#[test]
fn snapshot_interface_bound_unsatisfied_shape() {
    let src = "def[T: Iterable] f(x: T) -> T { x }; def y = f[Int](1)";
    let parsed = Parser::parse_source(src).expect("parse should succeed");
    let checked = check_module(&parsed);
    let diag = checked
        .diagnostics
        .iter()
        .find(|d| d.code == "E_INTERFACE_BOUND_UNSAT")
        .expect("expected interface bound unsatisfied diagnostic");

    let got = render(diag);
    assert!(got.contains("error|typecheck|E_INTERFACE_BOUND_UNSAT|"));
    assert!(got.contains("does not satisfy interface bound 'Iterable'"));
    assert!(got.contains("checking declaration 'y'"));
    assert!(got.contains("checking call expression"));
}

#[test]
fn snapshot_type_mismatch_return_shape() {
    let src = "def f(x: Int) -> Int { \"bad\" }";
    let parsed = Parser::parse_source(src).expect("parse should succeed");
    let checked = check_module(&parsed);
    let diag = checked
        .diagnostics
        .iter()
        .find(|d| d.code == "E_TYPE_MISMATCH")
        .expect("expected type mismatch diagnostic");

    let got = render(diag);
    assert!(got.contains("error|typecheck|E_TYPE_MISMATCH|"));
    assert!(
        got.contains("type mismatch in bidirectional expected type")
            || got.contains("type mismatch in function return")
    );
    assert!(got.contains("checking function 'f'"));
}

#[test]
fn snapshot_operator_arity_error_shape() {
    let src = "def x = \"a\" + \"b\"";
    let parsed = Parser::parse_source(src).expect("parse should succeed");
    let checked = check_module(&parsed);
    let diag = checked
        .diagnostics
        .iter()
        .find(|d| d.code == "E_OP_NON_NUMERIC")
        .expect("expected non-numeric operator diagnostic");

    let got = render(diag);
    assert!(got.contains("error|typecheck|E_OP_NON_NUMERIC|"));
    assert!(got.contains("numeric operator requires numeric operands"));
}

#[test]
fn snapshot_cast_invalid_shape() {
    let src = "def x = \"a\": Int";
    let parsed = Parser::parse_source(src).expect("parse should succeed");
    let checked = check_module(&parsed);
    let diag = checked
        .diagnostics
        .iter()
        .find(|d| d.code == "E_CAST_INVALID")
        .expect("expected cast invalid diagnostic");

    let got = render(diag);
    assert!(got.contains("error|typecheck|E_CAST_INVALID|"));
    assert!(got.contains("invalid cast from"));
    assert!(got.contains("invalid cast from"));
}

#[test]
fn all_typecheck_diagnostics_include_related_context_label() {
    let src = "def f(x: Int) -> Int { \"bad\" }; def y = \"a\" + \"b\"";
    let parsed = Parser::parse_source(src).expect("parse should succeed");
    let checked = check_module(&parsed);
    for d in checked
        .diagnostics
        .iter()
        .filter(|d| format!("{:?}", d.stage) == "Typecheck")
    {
        assert!(
            !d.related.is_empty(),
            "expected related labels on diagnostic code {}",
            d.code
        );
    }
}
