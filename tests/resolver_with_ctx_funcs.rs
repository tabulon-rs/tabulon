use tabulon::{Parser, PreparedExpr, Tabula, IdentityResolver, VarAccessStrategy};

#[repr(C)]
struct MixedCtx {
    // Resolver-side storage
    values: Vec<f64>,
    cached: Vec<f64>,
    hit: Vec<u8>, // 0/1
    call_counts: Vec<u32>,
    miss_counts: Vec<u32>,
    // Custom function-side state
    bias: f64,
    factor: f64,
}

impl MixedCtx {
    fn new(values: Vec<f64>, bias: f64, factor: f64) -> Self {
        let n = values.len();
        Self {
            values,
            cached: vec![0.0; n],
            hit: vec![0; n],
            call_counts: vec![0; n],
            miss_counts: vec![0; n],
            bias,
            factor,
        }
    }
}

// Resolver that uses the same ctx as custom functions, defined via macro
#[tabulon::resolver]
fn get_var_both(idx: u32, ctx: &mut MixedCtx) -> f64 {
    let i = idx as usize;
    ctx.call_counts[i] = ctx.call_counts[i].saturating_add(1);
    if ctx.hit[i] != 0 {
        return ctx.cached[i];
    }
    ctx.miss_counts[i] = ctx.miss_counts[i].saturating_add(1);
    let v = ctx.values[i];
    ctx.cached[i] = v;
    ctx.hit[i] = 1;
    v
}

// Custom functions that consume ctx
#[tabulon::function]
fn add_bias(x: f64, ctx: &MixedCtx) -> f64 {
    x + ctx.bias
}

#[tabulon::function]
fn mul_fac(x: f64, ctx: &MixedCtx) -> f64 {
    x * ctx.factor
}

#[test]
fn resolver_and_custom_fn_share_ctx() {
    // Expression uses both resolver-fetched variables and ctx-consuming custom functions
    let parser = Parser::new("add_bias(A) + mul_fac(B) + C").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    // Build name->index map for assertions
    let mut idx_of = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        idx_of.insert(k.as_str(), i);
    }
    let gi = |name: &str| *idx_of.get(name).expect("var present");

    // Engine with MixedCtx
    let mut eng = Tabula::<MixedCtx>::new_ctx();
    // Register resolver and custom functions via macros (typed)
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_both).unwrap();
    tabulon::register_functions_typed!(eng, __tabulon_marker_add_bias, __tabulon_marker_mul_fac).unwrap();

    let compiled = eng
        .compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: "get_var_both" })
        .unwrap();

    // Values: A=2, B=3, C=5; ctx: bias=10, factor=4
    let mut ctx = MixedCtx::new(vec![0.0; prepared.ordered_vars.len()], 10.0, 4.0);
    ctx.values[gi("A")] = 2.0;
    ctx.values[gi("B")] = 3.0;
    ctx.values[gi("C")] = 5.0;

    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();

    // add_bias(2) = 12, mul_fac(3) = 12, + C(5) = 29
    assert!((out - 29.0).abs() < 1e-12);

    // Resolver called exactly once per variable used
    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[gi("A")] = 1;
    expected_calls[gi("B")] = 1;
    expected_calls[gi("C")] = 1;
    expected_misses[gi("A")] = 1;
    expected_misses[gi("B")] = 1;
    expected_misses[gi("C")] = 1;
    assert_eq!(ctx.call_counts, expected_calls);
    assert_eq!(ctx.miss_counts, expected_misses);

    // Modify ctx and re-evaluate to ensure both resolver and custom functions see the same ctx
    ctx.bias = 1.5;
    ctx.factor = 2.0;
    // Change only B to verify resolver fetch on a fresh generation; keep cache logic simple by clearing hits
    ctx.hit.fill(0);
    let out2 = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    // add_bias(2) = 3.5, mul_fac(3) = 6.0, + C(5) = 14.5
    assert!((out2 - 14.5).abs() < 1e-12);
}
