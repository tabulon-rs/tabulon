# tabulon

[![crates.io](https://img.shields.io/crates/v/tabulon.svg)](https://crates.io/crates/tabulon)
[![docs.rs](https://docs.rs/tabulon/badge.svg)](https://docs.rs/tabulon)
[![License](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

A high-performance, JIT-compiled expression evaluation engine for Rust, built on Cranelift.

`tabulon` parses simple arithmetic and boolean expressions and compiles them to native machine code at runtime. It is designed for applications like game servers, configuration scripts, or anywhere you need to safely and repeatedly evaluate user-provided expressions with maximum performance.

## Features

- **High-Performance JIT Compilation**: Expressions are compiled to native machine code for near-native performance, powered by [Cranelift](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift).
- **Rich Operator Support**: Full support for arithmetic (`+`, `-`, `*`, `/`), comparison (`==`, `!=`, `<`, `<=`, `>`, `>=`), and logical (`&&`, `||`) operators.
- **Efficient & Safe**:
    - Short-circuiting for `if(...)`, `&&`, and `||` operators avoids unnecessary computation.
    - AST-level optimizations like constant folding are performed automatically.
    - All execution is sandboxed within the JIT engine.
- **Extensible**: Register your own custom Rust functions to be called from within an expression.
- **Flexible**: Use custom resolvers to map variables to your application's specific data structures.

## Quick Start

1.  Add `tabulon` to your `Cargo.toml`:

    ```toml
    [dependencies]
    tabulon = "0.1.0"
    ```

2.  Use the engine to compile and evaluate an expression:

    ```rust
    use tabulon::Tabula;

    fn main() -> Result<(), Box<dyn std::error::Error>> {
        // Create a new engine instance
        let mut engine = Tabula::new();

        // Compile an expression
        let expr = engine.compile("power > 9000 && is_angry * 10")?;

        // `ordered_vars` shows the order variables must be supplied in.
        // Here it would be: ["power", "is_angry"]
        assert_eq!(expr.vars(), &["power", "is_angry"]);

        // Prepare variables for evaluation
        let power_level = 9001.0;
        let is_angry_val = 1.0; // Use 1.0 for true, 0.0 for false

        // `eval` takes a slice of pointers to your f64 variables
        let result = expr.eval(&[&power_level, &is_angry_val])?;

        // The expression "(9001 > 9000) && (1.0 * 10)" is true, so the result is 1.0.
        assert_eq!(result, 1.0);
        println!("It's over 9000! Result: {}", result);

        Ok(())
    }
    ```

## Custom Functions

You can easily register your own Rust functions to be used in expressions.

```rust
use tabulon::{Tabula, function, register_functions};

// Use the `#[function]` attribute to make a function discoverable.
#[function]
pub fn custom_max(a: f64, b: f64) -> f64 {
    if a > b { a } else { b }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut engine = Tabula::new();

    // Register the function with the engine instance.
    register_functions!(engine, custom_max)?;

    let expr = engine.compile("custom_max(player_score, high_score) * 1.1")?;
    
    let player_score = 120.0;
    let high_score = 150.0;

    let result = expr.eval(&[&player_score, &high_score])?;

    assert_eq!(result, 165.0);
    println!("Potential new high score: {}", result);

    Ok(())
}
```

## Performance

`tabulon` is designed for speed. By compiling expressions down to a few simple machine instructions, it can evaluate them orders of magnitude faster than a tree-walking interpreter. Benchmarks are included in the repository (`cargo bench`).

## License

This project is licensed under the MIT License.