use core::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypingContext {
    Assignment,
    ReturnType,
    IfCondition,
    IfBranch,
    CasesArm,
    CallArgument,
    CastExpression,
    BinaryOperation,
    GenericConstraint,
    Custom(String),
}

impl fmt::Display for TypingContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Assignment => f.write_str("assignment"),
            Self::ReturnType => f.write_str("function return type"),
            Self::IfCondition => f.write_str("if condition"),
            Self::IfBranch => f.write_str("if branch"),
            Self::CasesArm => f.write_str("cases arm"),
            Self::CallArgument => f.write_str("call argument"),
            Self::CastExpression => f.write_str("cast expression"),
            Self::BinaryOperation => f.write_str("binary operation"),
            Self::GenericConstraint => f.write_str("generic constraint"),
            Self::Custom(text) => f.write_str(text),
        }
    }
}
