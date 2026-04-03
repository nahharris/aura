use aura_frontend::Parser;
use aura_typecheck::check_module;
use aura_typecheck::checked_ir::{BinaryOpKind, CheckedExpr};

#[test]
fn arithmetic_operator_lowers_to_typed_binary_op() {
    let parsed = Parser::parse_source("def x = 1 + 2").expect("parse should succeed");
    let checked = check_module(&parsed);
    let module = checked.module.expect("module should exist");
    let decl = module
        .ir
        .declarations
        .iter()
        .find(|d| d.name == "x")
        .expect("x declaration should exist");

    assert!(matches!(
        decl.value,
        CheckedExpr::BinaryOp {
            op: BinaryOpKind::Add,
            ..
        }
    ));
}

#[test]
fn logical_operator_lowers_to_typed_binary_op() {
    let parsed = Parser::parse_source("def x = true && false").expect("parse should succeed");
    let checked = check_module(&parsed);
    let module = checked.module.expect("module should exist");
    let decl = module
        .ir
        .declarations
        .iter()
        .find(|d| d.name == "x")
        .expect("x declaration should exist");

    assert!(matches!(
        decl.value,
        CheckedExpr::BinaryOp {
            op: BinaryOpKind::And,
            ..
        }
    ));
}

#[test]
fn semantically_checked_ir_has_no_any_nodes_for_core_operator_path() {
    let parsed = Parser::parse_source("def x = 1 > 2").expect("parse should succeed");
    let checked = check_module(&parsed);
    let module = checked.module.expect("module should exist");

    fn contains_any(expr: &CheckedExpr) -> bool {
        match expr {
            CheckedExpr::Any => true,
            CheckedExpr::DotIdent { payload, .. } => {
                payload.as_ref().map(|p| contains_any(p)).unwrap_or(false)
            }
            CheckedExpr::List(items) => items.iter().any(contains_any),
            CheckedExpr::Dict(entries) => entries
                .iter()
                .any(|(k, v)| contains_any(k) || contains_any(v)),
            CheckedExpr::Call { callee, args } => {
                contains_any(callee) || args.iter().any(contains_any)
            }
            CheckedExpr::BinaryOp { lhs, rhs, .. } => contains_any(lhs) || contains_any(rhs),
            CheckedExpr::MacroApply { operand, .. } => contains_any(operand),
            CheckedExpr::Label { expr, .. } => contains_any(expr),
            CheckedExpr::MultiArm(arms) => arms.iter().any(contains_any),
            CheckedExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                contains_any(condition)
                    || contains_any(then_branch)
                    || else_branch
                        .as_ref()
                        .map(|e| contains_any(e))
                        .unwrap_or(false)
            }
            CheckedExpr::Cases { arms } => arms.iter().any(contains_any),
            CheckedExpr::Return { value } => contains_any(value),
            CheckedExpr::Break { value } => {
                value.as_ref().map(|v| contains_any(v)).unwrap_or(false)
            }
            CheckedExpr::Coerce { expr, .. } => contains_any(expr),
            CheckedExpr::Cast { expr, .. } => contains_any(expr),
            CheckedExpr::Continue
            | CheckedExpr::Ident(_)
            | CheckedExpr::Int(_)
            | CheckedExpr::Float(_)
            | CheckedExpr::Char(_)
            | CheckedExpr::String(_)
            | CheckedExpr::Closure { .. } => false,
        }
    }

    assert!(!module
        .ir
        .declarations
        .iter()
        .any(|d| contains_any(&d.value)));
}
