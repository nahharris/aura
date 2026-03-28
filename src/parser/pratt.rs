//! Binding powers for Pratt expression parsing and token → [`BinOp`] mapping.

use crate::ast::BinOp;
use crate::token::TokenKind;

/// Return `(left_bp, right_bp)` for an infix/postfix token.
///
/// For pure postfix operators, `right_bp` is `None` (they have no right operand).
/// For infix operators, both are `Some`.
/// Returns `(0, None)` for tokens that are not infix/postfix operators (which
/// causes the Pratt loop to exit).
pub(crate) fn infix_binding_power(kind: &TokenKind) -> (u8, Option<u8>) {
    match kind {
        // Right-associative assignment — l_bp must be LESS than r_bp.
        TokenKind::Eq => (1, Some(2)),
        // Elvis ?:
        TokenKind::QuestionColon => (3, Some(4)),
        // Logical OR
        TokenKind::PipePipe => (5, Some(6)),
        // Logical AND
        TokenKind::AmpAmp => (7, Some(8)),
        // Equality
        TokenKind::EqEq | TokenKind::BangEq => (9, Some(10)),
        // Comparison
        TokenKind::Lt | TokenKind::Gt | TokenKind::LtEq | TokenKind::GtEq => (11, Some(12)),
        // Range
        TokenKind::DotDot => (13, Some(14)),
        // Additive
        TokenKind::Plus | TokenKind::Minus => (15, Some(16)),
        // Multiplicative
        TokenKind::Star | TokenKind::Slash | TokenKind::Percent => (17, Some(18)),
        // Cast `:` — postfix, no right operand in the expression sense (type follows).
        TokenKind::Colon => (19, None),
        // Post-increment / decrement — postfix.
        TokenKind::PlusPlus | TokenKind::MinusMinus => (21, None),
        // Force unwrap `!!` — postfix.
        TokenKind::BangBang => (23, None),
        // Safe navigation `?.` — postfix.
        TokenKind::QuestionDot => (25, None),
        // Field access `.` — postfix.
        TokenKind::Dot => (27, None),
        // Method call via DotIdent `.method(...)` — postfix.
        TokenKind::DotIdent(_) => (27, None),
        // Call `()` and index `[]` — postfix, highest precedence.
        TokenKind::LParen | TokenKind::LBracket => (29, None),
        // Everything else is not an infix/postfix operator.
        _ => (0, None),
    }
}

/// Map an infix token kind to a [`BinOp`].
/// Panics if the token is not a binary operator (caller must ensure correctness).
pub(crate) fn token_to_binop(kind: &TokenKind) -> BinOp {
    match kind {
        TokenKind::PipePipe => BinOp::Or,
        TokenKind::AmpAmp => BinOp::And,
        TokenKind::EqEq => BinOp::Eq,
        TokenKind::BangEq => BinOp::Ne,
        TokenKind::Lt => BinOp::Lt,
        TokenKind::Gt => BinOp::Gt,
        TokenKind::LtEq => BinOp::Le,
        TokenKind::GtEq => BinOp::Ge,
        TokenKind::Plus => BinOp::Add,
        TokenKind::Minus => BinOp::Sub,
        TokenKind::Star => BinOp::Mul,
        TokenKind::Slash => BinOp::Div,
        TokenKind::Percent => BinOp::Rem,
        _ => panic!("token_to_binop called on non-binary-op token: {kind:?}"),
    }
}
