use tabulon::{Parser, PreparedExpr, Tabula, IdentityResolver, VarAccessStrategy};

#[repr(C)]
struct EvalCtx {
    values: Vec<f64>,
    cached: Vec<f64>,
    hit: Vec<u8>, // 0/1
    call_counts: Vec<u32>,
    miss_counts: Vec<u32>,
}

impl EvalCtx {
    fn with_values(values: Vec<f64>) -> Self {
        let n = values.len();
        Self { values, cached: vec![0.0; n], hit: vec![0; n], call_counts: vec![0; n], miss_counts: vec![0; n] }
    }
}

#[tabulon::resolver]
fn get_var_counting(idx: u32, ctx: &mut EvalCtx) -> f64 {
    let i = idx as usize;
    ctx.call_counts[i] = ctx.call_counts[i].saturating_add(1);
    if ctx.hit[i] != 0 { return ctx.cached[i]; }
    ctx.miss_counts[i] = ctx.miss_counts[i].saturating_add(1);
    let v = ctx.values[i];
    ctx.cached[i] = v;
    ctx.hit[i] = 1;
    v
}

#[test]
fn if_carry_shared_var_then_branch() {
    // if(A, B + C, C + D) — shared variable C should be resolved only once
    let parser = Parser::new("if(A + B, B + C, C + D)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut idx = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() { idx.insert(k.as_str(), i); }
    let gi = |n: &str| *idx.get(n).unwrap();

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_counting).unwrap();
    let compiled = eng
        .compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: "get_var_counting" })
        .unwrap();

    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    vals[gi("A")] = 1.0; // take then branch => B + C
    vals[gi("B")] = 10.0;
    vals[gi("C")] = 2.0;
    vals[gi("D")] = 5.0; // unused

    let mut ctx = EvalCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 12.0).abs() < 1e-12);

    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[gi("A")] = 1; expected_misses[gi("A")] = 1;
    expected_calls[gi("B")] = 1; expected_misses[gi("B")] = 1;
    expected_calls[gi("C")] = 1; expected_misses[gi("C")] = 1; // shared var
    assert_eq!(ctx.call_counts, expected_calls, "calls: {:?}", ctx.call_counts);
    assert_eq!(ctx.miss_counts, expected_misses, "misses: {:?}", ctx.miss_counts);
}

#[test]
fn if_carry_shared_var_else_branch() {
    // if(A, B + C, C + D) — shared variable C should be resolved only once
    let parser = Parser::new("if(A + C, B + C, C + D)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut idx = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() { idx.insert(k.as_str(), i); }
    let gi = |n: &str| *idx.get(n).unwrap();

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_counting).unwrap();
    let compiled = eng
        .compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: "get_var_counting" })
        .unwrap();

    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    vals[gi("A")] = 0.0; // take else branch => C + D
    vals[gi("B")] = 10.0; // unused
    vals[gi("C")] = 0.0;
    vals[gi("D")] = 7.0;

    let mut ctx = EvalCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 7.0).abs() < 1e-12);

    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[gi("A")] = 1; expected_misses[gi("A")] = 1;
    expected_calls[gi("C")] = 1; expected_misses[gi("C")] = 1; // shared var
    expected_calls[gi("D")] = 1; expected_misses[gi("D")] = 1;
    assert_eq!(ctx.call_counts, expected_calls, "calls: {:?}", ctx.call_counts);
    assert_eq!(ctx.miss_counts, expected_misses, "misses: {:?}", ctx.miss_counts);
}
