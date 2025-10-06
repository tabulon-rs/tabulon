use thiserror::Error;

/// The primary error type for the `tabulon` crate.
#[derive(Debug, Error)]
pub enum JitError {
    /// An error occurred while parsing the expression string.
    #[error("parse error: {0}")]
    Parse(String),
    /// The expression contained an identifier (variable) that was not recognized by the resolver.
    #[error("unknown identifier: {0}")]
    UnknownIdent(String),
    /// The expression tried to call a function that was not registered with the engine.
    #[error("unknown function: {name}/{arity}")]
    UnknownFunction { name: String, arity: u8 },
    /// An attempt was made to register a function with a name and arity that already exists.
    #[error("function already exists: {name}/{arity}")]
    FunctionExists { name: String, arity: u8 },
    /// An attempt was made to evaluate an expression after the underlying JIT memory was freed.
    /// Call `Tabula::free_memory` invalidates all previously compiled expressions.
    #[error("compiled expression invalidated (freed)")]
    Invalidated,
    /// An unexpected internal error occurred within the JIT compiler or engine.
    /// These errors often indicate a bug in `tabulon` itself.
    #[error("jit internal error: {0}")]
    Internal(String),
    /// The number of values provided for evaluation did not match the number of variables in the expression.
    #[error("values length mismatch: expected at least {expected}, got {got}")]
    ValuesLen { expected: usize, got: usize },
}

/// An error type returned by a `VarResolver` when it fails to resolve an identifier.
#[derive(Debug)]
pub enum VarResolveError {
    /// The variable name is unknown.
    Unknown(String),
    /// The variable name is known but is invalid in the current context.
    Invalid(String),
}
