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
        Self {
            values,
            cached: vec![0.0; n],
            hit: vec![0; n],
            call_counts: vec![0; n],
            miss_counts: vec![0; n],
        }
    }
}

#[tabulon::resolver]
fn get_var_test(idx: u32, ctx: &mut EvalCtx) -> f64 {
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

#[test]
fn resolver_basic_eval() {
    // (A + B) * C with ResolverCall
    let parser = Parser::new("(A + B) * C").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();
    assert_eq!(prepared.ordered_vars, vec!["A", "B", "C"].into_iter().map(String::from).collect::<Vec<_>>());

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    // Register the test resolver via macro (typed)
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_test).unwrap();

    let compiled = eng
        .compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: "get_var_test" })
        .unwrap();

    // Values for A,B,C
    let vals = vec![2.0, 3.0, 4.0];
    let mut ctx = EvalCtx::with_values(vals);

    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 20.0).abs() < 1e-9);

    // Expect one cache miss per variable and one call per reference
    assert_eq!(ctx.miss_counts, vec![1, 1, 1]);
    assert_eq!(ctx.call_counts, vec![1, 1, 1]);
}

#[test]
fn resolver_short_circuit_and_if_skips_unneeded_vars() {
    // Expression with short-circuiting: A && B && if((D+E) < 3, F, G)
    let parser = Parser::new("A && B && if((D + E) < 3, F, G)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    // Build name->index map for assertions
    let mut idx_of = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        idx_of.insert(k.as_str(), i);
    }
    let idx = |name: &str| *idx_of.get(name).expect("var present");

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_test).unwrap();
    let compiled = eng
        .compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: "get_var_test" })
        .unwrap();

    // Arrange values: A = 0 causes first AND to short-circuit → no other vars should be fetched.
    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    // Set some arbitrary non-zero values for others; they should not be touched.
    for v in vals.iter_mut() { *v = 42.0; }
    vals[idx("A")] = 0.0;

    let mut ctx = EvalCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    
    // Result should be 0.0 due to short-circuit
    assert!(out.abs() < 1e-12);

    // Only A should have been requested.
    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[idx("A")] = 1;
    expected_misses[idx("A")] = 1;

    assert_eq!(ctx.call_counts, expected_calls, "unexpected resolver call pattern: {:?}", ctx.call_counts);
    assert_eq!(ctx.miss_counts, expected_misses, "unexpected resolver miss pattern: {:?}", ctx.miss_counts);
}

#[test]
fn resolver_nested_if_memoizes_across_multiple_uses() {
    // if(A+B>0, A, if(B+C, C, B+D))
    let parser = Parser::new("if(A + B > 0, A, if(B + C, C, B + D))").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut name_to_idx = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        name_to_idx.insert(k.as_str(), i);
    }
    let gi = |n: &str| *name_to_idx.get(n).expect("present");

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_test).unwrap();
    let compiled = eng
        .compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: "get_var_test" })
        .unwrap();

    // Choose values to take the else-then path:
    // cond1: A + B > 0 -> (-2) + 1 = -1 => false → else
    // cond2: B + C -> 1 + 7 = 8 => true → then returns C
    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    let ia = gi("A");
    let ib = gi("B");
    let ic = gi("C");
    let id = gi("D");
    vals[ia] = -2.0;
    vals[ib] = 1.0;
    vals[ic] = 7.0;
    vals[id] = 100.0;

    let mut ctx = EvalCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();

    // Should return C
    assert!((out - 7.0).abs() < 1e-12);

    // Access pattern along this path:
    // cond1 uses A and B (1 miss each)
    // cond2 uses B and C (B already cached => miss 0 additional, C miss 1)
    // then2 returns C (C already cached => no additional miss)
    // Callback calls occur at each Var occurrence, but misses happen once per var.

    // With SSA block-local cache + branch carry, each variable is resolved at most once per evaluation.
    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[ia] = 1;
    expected_calls[ib] = 1;
    expected_calls[ic] = 1;

    // Misses: A 1, B 1, C 1, D 0
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_misses[ia] = 1;
    expected_misses[ib] = 1;
    expected_misses[ic] = 1;

    assert_eq!(ctx.call_counts, expected_calls, "call counts: {:?}", ctx.call_counts);
    assert_eq!(ctx.miss_counts, expected_misses, "miss counts: {:?}", ctx.miss_counts);
}
