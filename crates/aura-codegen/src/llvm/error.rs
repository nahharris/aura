use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenError {
    BackendDisabled,
    InvalidTypeId(usize),
    UnsupportedType(String),
    UnsupportedExpression(&'static str),
    InvalidFunctionType(String),
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CodegenError::BackendDisabled => {
                write!(f, "LLVM backend is disabled; enable feature `llvm-backend`")
            }
            CodegenError::InvalidTypeId(id) => write!(f, "invalid Aura type id: {id}"),
            CodegenError::UnsupportedType(ty) => write!(f, "unsupported type lowering for `{ty}`"),
            CodegenError::UnsupportedExpression(kind) => {
                write!(f, "unsupported expression lowering for `{kind}`")
            }
            CodegenError::InvalidFunctionType(name) => {
                write!(f, "declaration `{name}` does not lower to a function type")
            }
        }
    }
}

impl std::error::Error for CodegenError {}
