use thiserror::Error;

#[derive(Debug, Error)]
pub enum JitError {
    #[error("parse error: {0}")]
    Parse(String),
    #[error("unknown identifier: {0}")]
    UnknownIdent(String),
    #[error("unknown function: {name}/{arity}")]
    UnknownFunction { name: String, arity: u8 },
    #[error("function already exists: {name}/{arity}")]
    FunctionExists { name: String, arity: u8 },
    #[error("compiled expression invalidated (freed)")]
    Invalidated,
    #[error("jit internal error: {0}")]
    Internal(String),
    #[error("values length mismatch: expected at least {expected}, got {got}")]
    ValuesLen { expected: usize, got: usize },
}

#[derive(Debug)]
pub enum VarResolveError {
    Unknown(String),
    Invalid(String),
}
