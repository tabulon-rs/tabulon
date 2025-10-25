use tabulon::{IdentityResolver, Parser, PreparedExpr, Tabula, VarAccessStrategy};

#[repr(C)]
struct RefCtx {
    values: Vec<f64>,
    cached: Vec<f64>,
    hit: Vec<u8>,
    call_counts: Vec<u32>,
}

impl RefCtx {
    fn with_values(values: Vec<f64>) -> Self {
        let n = values.len();
        Self {
            values,
            cached: vec![0.0; n],
            hit: vec![0; n],
            call_counts: vec![0; n],
        }
    }
}

#[tabulon::resolver]
fn ref_mode_resolver(idx: u32, ctx: &mut RefCtx) -> f64 {
    let i = idx as usize;
    ctx.call_counts[i] = ctx.call_counts[i].saturating_add(1);
    if ctx.hit[i] != 0 {
        return ctx.cached[i];
    }
    let v = ctx.values[i];
    ctx.cached[i] = v;
    ctx.hit[i] = 1;
    v
}

#[test]
fn resolver_ref_eval_basic() {
    // Compile using the reference-based API with resolver access; no values pointer should be required at eval time.
    let parser = Parser::new("(A + B) * C").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    // Build name->index map
    let mut idx_of = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        idx_of.insert(k.as_str(), i);
    }
    let gi = |n: &str| *idx_of.get(n).unwrap();

    let mut eng = Tabula::<RefCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_ref_mode_resolver).unwrap();

    // Compile ref variant with ResolverCall
    let compiled_ref = eng
        .compile_prepared_ref_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "ref_mode_resolver",
            },
        )
        .unwrap();

    // Set values and evaluate via eval_resolver_ctx (no &f64 slice or pointer array required)
    let mut ctx = RefCtx::with_values(vec![0.0; prepared.ordered_vars.len()]);
    ctx.values[gi("A")] = 2.0;
    ctx.values[gi("B")] = 3.0;
    ctx.values[gi("C")] = 4.0;

    let out = compiled_ref.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 20.0).abs() < 1e-12);

    // Each variable should be fetched exactly once
    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[gi("A")] = 1;
    expected_calls[gi("B")] = 1;
    expected_calls[gi("C")] = 1;
    assert_eq!(ctx.call_counts, expected_calls);
}
