pub mod ast;
pub mod parser;

#[derive(thiserror::Error, Debug)]
pub enum AuraError {
    #[error("Parse error: {0}")]
    ParseError(#[from] pest::error::Error<parser::Rule>),
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

pub type AuraResult<T> = Result<T, AuraError>;

