use tabulon::{
    IdentityResolver, Parser, PreparedExpr, Tabula, VarAccessStrategy, register_resolver_typed,
    resolver,
};

#[repr(C)]
struct MacroCtx {
    values: Vec<f64>,
    cached: Vec<f64>,
    hit: Vec<u8>,
}

impl MacroCtx {
    fn with_values(values: Vec<f64>) -> Self {
        let n = values.len();
        Self {
            values,
            cached: vec![0.0; n],
            hit: vec![0; n],
        }
    }
}

// Define a resolver without writing extern "C" using the #[resolver] macro.
// This order (index first, &Ctx second) is supported.
#[resolver]
fn my_resolver(idx: u32, ctx: &mut MacroCtx) -> f64 {
    let i = idx as usize;
    if ctx.hit[i] != 0 {
        return ctx.cached[i];
    }
    let v = ctx.values[i];
    ctx.cached[i] = v;
    ctx.hit[i] = 1;
    v
}

#[test]
fn resolver_macro_basic_and_short_circuit() {
    let parser = Parser::new("A && if(B > 0, C, D)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut eng = Tabula::<MacroCtx>::new_ctx();
    // Register via typed helper macro; this calls engine.set_var_getter_typed::<marker>() under the hood.
    register_resolver_typed!(eng, __tabulon_resolver_marker_my_resolver).unwrap();

    // Compile with ResolverCall; symbol is the resolver function name by default.
    let compiled = eng
        .compile_prepared_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "my_resolver",
            },
        )
        .unwrap();

    // Arrange: A = 0 to short-circuit the AND; only A should be fetched.
    let vals = vec![0.0, 123.0, 456.0, 789.0];
    let mut ctx = MacroCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!(out.abs() < 1e-12);
}

#[resolver]
fn name_first_ctx_then_idx(ctx: &MacroCtx, idx: u32) -> f64 {
    // Demonstrate reversed param order works too
    ctx.values[idx as usize]
}

#[test]
fn resolver_macro_reversed_params_works() {
    let parser = Parser::new("A + B").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut eng = Tabula::<MacroCtx>::new_ctx();
    register_resolver_typed!(eng, __tabulon_resolver_marker_name_first_ctx_then_idx).unwrap();
    let compiled = eng
        .compile_prepared_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "name_first_ctx_then_idx",
            },
        )
        .unwrap();

    let vals = vec![2.5, 3.5];
    let mut ctx = MacroCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 6.0).abs() < 1e-12);
}
