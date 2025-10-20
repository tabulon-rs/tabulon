#![doc = include_str!("../README.md")]

mod ast;
mod codegen;
mod collect;
mod engine;
mod error;
mod lexer;
mod optimizer;
mod parser;
mod prepared;
mod registry;
mod resolver;
mod rt_types;
mod analysis;

pub use engine::{CompiledExpr, CompiledExprRef, Tabula, VarAccessStrategy, GetVarFn};
pub use parser::Parser;
pub use prepared::PreparedExpr;

pub use error::{JitError, VarResolveError};
pub use registry::{FnMeta, HasCtx, FunctionForEngineCtx, ResolverForEngineCtx, SameAs};
pub use resolver::{IdentityResolver, VarResolver};
pub use rt_types::{CtxPtr, Fn0, Fn1, Fn2, Fn3, JitFn, RegisteredFn};

// Re-export inventory and the #[function] and #[resolver] macros for user crates
pub use inventory;
pub use tabulon_macros::{function, resolver};

#[doc = r#"
Compile-time context checking example (this snippet intentionally fails to compile to demonstrate safety):

```compile_fail
use tabulon::{Tabula, IdentityResolver, function};

#[derive(Debug)] struct Ctx;
#[derive(Debug)] struct OtherCtx;

#[function]
fn needs_other(a: f64, ctx: &OtherCtx) -> f64 { a }

fn main() {
    let mut eng = Tabula::<Ctx>::new_ctx();
    // Fails to compile: engine Ctx differs from function's context type
    eng.register_typed::<__tabulon_marker_needs_other>().unwrap();
}
```
"#]
pub mod __tabulon_typed_registration_docs {}

#[doc = r#"
Typed registration macro example:

```rust
use tabulon::{Tabula, IdentityResolver, function, register_functions_typed};

#[derive(Debug)] struct Ctx { bias: f64 }

#[function]
fn add_bias(a: f64, ctx: &Ctx) -> f64 { a + ctx.bias }

fn main() {
    let mut eng = Tabula::<Ctx>::new_ctx();
    // Prefer the typed registration path for compile-time context safety
    register_functions_typed!(eng, __tabulon_marker_add_bias).unwrap();

    let e = eng.compile_ref("add_bias(A)").unwrap();
    let a = 5.0;
    let mut ctx = Ctx { bias: 1.5 };
    let out = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert!((out - 6.5).abs() < 1e-12);
}
```

A mismatched context will fail to compile when using the typed registration API:

```compile_fail
use tabulon::{Tabula, IdentityResolver, function, register_functions_typed};

#[derive(Debug)] struct Ctx;
#[derive(Debug)] struct OtherCtx;

#[function]
fn needs_other(a: f64, ctx: &OtherCtx) -> f64 { a }

fn main() {
    let mut eng = Tabula::<String, IdentityResolver, Ctx>::new_ctx();
    // Fails to compile: engine Ctx differs from function's context type
    register_functions_typed!(eng, __tabulon_marker_needs_other).unwrap();
}
```
"#]
pub mod __tabulon_typed_registration_macro_docs {}
