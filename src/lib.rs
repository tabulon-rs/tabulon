#![doc = include_str!("../README.md")]

mod ast;
mod codegen;
mod collect;
mod engine;
mod error;
mod lexer;
mod optimizer;
mod parser;
mod registry;
mod resolver;
mod rt_types;

pub use engine::{CompiledExpr, CompiledExprRef, Tabula};

pub use error::{JitError, VarResolveError};
pub use registry::FnMeta;
pub use resolver::{IdentityResolver, VarResolver};
pub use rt_types::{Fn0, Fn1, Fn2, Fn3, JitFn, RegisteredFn};

// Re-export inventory and the #[function] macro for user crates
pub use inventory;
pub use tabulon_macros::function;
