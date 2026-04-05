use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenError {
    BackendDisabled,
    InvalidTypeId(usize),
    UnsupportedType(String),
    UnsupportedExpression(&'static str),
    InvalidFunctionType(String),
    NativeTargetInit,
    NativeTargetMachineUnavailable,
    ModuleVerification(String),
    ObjectEmit(String),
    MainLowering(String),
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
            CodegenError::NativeTargetInit => {
                write!(f, "failed to initialize native LLVM target")
            }
            CodegenError::NativeTargetMachineUnavailable => {
                write!(f, "failed to create native LLVM target machine")
            }
            CodegenError::ModuleVerification(detail) => {
                write!(f, "LLVM module verification failed: {detail}")
            }
            CodegenError::ObjectEmit(detail) => {
                write!(f, "failed to emit object file: {detail}")
            }
            CodegenError::MainLowering(detail) => {
                write!(f, "failed to lower main entrypoint: {detail}")
            }
        }
    }
}

impl std::error::Error for CodegenError {}
