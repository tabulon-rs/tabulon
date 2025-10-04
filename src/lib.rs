mod error;
mod resolver;
mod rt_types;
mod registry;
mod ast;
mod lexer;
mod parser;
mod collect;
mod codegen;
mod optimizer;
mod engine;
mod macros;

pub use error::{JitError, VarResolveError};
pub use resolver::{VarResolver, IdentityResolver};
pub use rt_types::{JitFn, Fn0, Fn1, Fn2, Fn3, RegisteredFn};
pub use registry::FnMeta;

// Re-export inventory and the #[function] macro for user crates
pub use inventory;
pub use macros::function;

pub use engine::{Tabula, CompiledExpr};
