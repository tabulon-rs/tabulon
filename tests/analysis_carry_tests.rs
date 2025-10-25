use tabulon::{IdentityResolver, Parser, PreparedExpr, Tabula, VarAccessStrategy};

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
fn get_var_counting(idx: u32, ctx: &mut EvalCtx) -> f64 {
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
fn or_short_circuit_resolver() {
    let parser = Parser::new("A || B").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut name_to_idx = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        name_to_idx.insert(k.as_str(), i);
    }
    let gi = |n: &str| *name_to_idx.get(n).unwrap();

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_counting).unwrap();

    let compiled = eng
        .compile_prepared_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "get_var_counting",
            },
        )
        .unwrap();

    // Case 1: A != 0 → RHS should not be fetched
    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    vals[gi("A")] = 1.0;
    vals[gi("B")] = 123.0;

    let mut ctx = EvalCtx::with_values(vals.clone());
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 1.0).abs() < 1e-12);

    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[gi("A")] = 1;
    expected_misses[gi("A")] = 1;
    assert_eq!(ctx.call_counts, expected_calls, "calls");
    assert_eq!(ctx.miss_counts, expected_misses, "misses");

    // Case 2: A == 0 → RHS B must be evaluated
    let mut ctx2 = EvalCtx::with_values(vals);
    ctx2.values[gi("A")] = 0.0;
    let out2 = compiled.eval_resolver_ctx(&mut ctx2).unwrap();
    assert!(
        (out2
            - (if ctx2.values[gi("B")] != 0.0 {
                ctx2.values[gi("B")]
            } else {
                0.0
            }))
        .abs()
            < 1e-12
    );
    // We don't assert exact calls here because it depends on both A and B; ensure at least one call to B when A==0
    assert!(
        ctx2.call_counts[gi("B")] >= 1,
        "B should be fetched when A==0"
    );
}

#[test]
fn ifs_carry_resolver_counts() {
    // ifs(A, B + C, D, C + E, C)
    let parser = Parser::new("ifs(A, B + C, D, C + E, C)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut name_to_idx = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        name_to_idx.insert(k.as_str(), i);
    }
    let gi = |n: &str| *name_to_idx.get(n).unwrap();

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_counting).unwrap();
    let compiled = eng
        .compile_prepared_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "get_var_counting",
            },
        )
        .unwrap();

    // Case 1: A true → take then1 (B + C). Carry set should prefetch C once.
    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    vals[gi("A")] = 1.0; // true
    vals[gi("B")] = 10.0;
    vals[gi("C")] = 2.0;
    vals[gi("D")] = 0.0; // don't care
    vals[gi("E")] = 5.0; // don't care
    let mut ctx = EvalCtx::with_values(vals);
    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 12.0).abs() < 1e-12);

    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[gi("A")] = 1;
    expected_misses[gi("A")] = 1;
    expected_calls[gi("B")] = 1;
    expected_misses[gi("B")] = 1;
    expected_calls[gi("C")] = 1;
    expected_misses[gi("C")] = 1;
    assert_eq!(
        ctx.call_counts, expected_calls,
        "case1 calls: {:?}",
        ctx.call_counts
    );
    assert_eq!(
        ctx.miss_counts, expected_misses,
        "case1 misses: {:?}",
        ctx.miss_counts
    );

    // Case 2: A false, D true → take then2 (C + E). C is shared (carry) and should be resolved once overall.
    let mut vals2 = vec![0.0; prepared.ordered_vars.len()];
    vals2[gi("A")] = 0.0; // false
    vals2[gi("B")] = 10.0; // unused
    vals2[gi("C")] = 3.0;
    vals2[gi("D")] = 1.0; // true for second condition
    vals2[gi("E")] = 7.0;
    let mut ctx2 = EvalCtx::with_values(vals2);
    let out2 = compiled.eval_resolver_ctx(&mut ctx2).unwrap();
    assert!((out2 - 10.0).abs() < 1e-12);

    // Expected along this path: A, D, C, E are fetched once; B not fetched.
    let mut expected_calls2 = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses2 = vec![0u32; prepared.ordered_vars.len()];
    expected_calls2[gi("A")] = 1;
    expected_misses2[gi("A")] = 1;
    expected_calls2[gi("D")] = 1;
    expected_misses2[gi("D")] = 1;
    expected_calls2[gi("C")] = 1;
    expected_misses2[gi("C")] = 1;
    expected_calls2[gi("E")] = 1;
    expected_misses2[gi("E")] = 1;
    assert_eq!(
        ctx2.call_counts, expected_calls2,
        "case2 calls: {:?}",
        ctx2.call_counts
    );
    assert_eq!(
        ctx2.miss_counts, expected_misses2,
        "case2 misses: {:?}",
        ctx2.miss_counts
    );

    // Case 3: A false, D false → else returns C (carry should still ensure C resolved once).
    let mut vals3 = vec![0.0; prepared.ordered_vars.len()];
    vals3[gi("A")] = 0.0;
    vals3[gi("B")] = 9.0;
    vals3[gi("C")] = 4.5;
    vals3[gi("D")] = 0.0;
    vals3[gi("E")] = 8.0;
    let mut ctx3 = EvalCtx::with_values(vals3);
    let out3 = compiled.eval_resolver_ctx(&mut ctx3).unwrap();
    assert!((out3 - 4.5).abs() < 1e-12);

    let mut expected_calls3 = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses3 = vec![0u32; prepared.ordered_vars.len()];
    expected_calls3[gi("A")] = 1;
    expected_misses3[gi("A")] = 1;
    expected_calls3[gi("D")] = 1;
    expected_misses3[gi("D")] = 1;
    expected_calls3[gi("C")] = 1;
    expected_misses3[gi("C")] = 1;
    assert_eq!(
        ctx3.call_counts, expected_calls3,
        "case3 calls: {:?}",
        ctx3.call_counts
    );
    assert_eq!(
        ctx3.miss_counts, expected_misses3,
        "case3 misses: {:?}",
        ctx3.miss_counts
    );
}
