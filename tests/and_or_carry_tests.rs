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
fn and_shared_var_resolved_once() {
    // (A > 0) && (A + B > 0) should fetch A only once even though used in both sides
    let parser = Parser::new("(A > 0) && (A + B > 0)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    // Map name -> index
    let mut idx_of = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        idx_of.insert(k.as_str(), i);
    }
    let ia = *idx_of.get("A").unwrap();
    let ib = *idx_of.get("B").unwrap();

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_test).unwrap();

    let compiled = eng
        .compile_prepared_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "get_var_test",
            },
        )
        .unwrap();

    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    vals[ia] = 1.0; // true so RHS evaluated
    vals[ib] = 2.0;
    let mut ctx = EvalCtx::with_values(vals);

    let out = compiled.eval_resolver_ctx(&mut ctx).unwrap();
    assert!((out - 1.0).abs() < 1e-12 || (out - 3.0).abs() < 1e-12 || out.is_finite());

    // Expect exactly one miss for A and one for B
    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[ia] = 1;
    expected_misses[ia] = 1;
    expected_calls[ib] = 1;
    expected_misses[ib] = 1;

    assert_eq!(
        ctx.call_counts, expected_calls,
        "AND shared var A should be resolved once; calls={:?}",
        ctx.call_counts
    );
    assert_eq!(
        ctx.miss_counts, expected_misses,
        "AND shared var A should miss once; misses={:?}",
        ctx.miss_counts
    );
}

#[test]
fn or_shared_var_and_short_circuit() {
    // Case 1: A == 0 -> LHS false, RHS evaluated; A used in both LHS and RHS, should be fetched once
    let parser = Parser::new("A || (A + B)").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();

    let mut idx_of = std::collections::HashMap::new();
    for (i, k) in prepared.ordered_vars.iter().enumerate() {
        idx_of.insert(k.as_str(), i);
    }
    let ia = *idx_of.get("A").unwrap();
    let ib = *idx_of.get("B").unwrap();

    let mut eng = Tabula::<EvalCtx>::new_ctx();
    tabulon::register_resolver_typed!(eng, __tabulon_resolver_marker_get_var_test).unwrap();
    let compiled = eng
        .compile_prepared_with(
            &prepared,
            VarAccessStrategy::ResolverCall {
                symbol: "get_var_test",
            },
        )
        .unwrap();

    // A = 0.0 so RHS runs; A appears in both -> only once
    let mut vals = vec![0.0; prepared.ordered_vars.len()];
    vals[ia] = 0.0;
    vals[ib] = 5.0;
    let mut ctx = EvalCtx::with_values(vals);
    let _ = compiled.eval_resolver_ctx(&mut ctx).unwrap();

    let mut expected_calls = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses = vec![0u32; prepared.ordered_vars.len()];
    expected_calls[ia] = 1;
    expected_misses[ia] = 1;
    expected_calls[ib] = 1;
    expected_misses[ib] = 1;
    assert_eq!(
        ctx.call_counts, expected_calls,
        "OR shared var A should be resolved once when RHS runs; calls={:?}",
        ctx.call_counts
    );
    assert_eq!(
        ctx.miss_counts, expected_misses,
        "OR shared var A should miss once when RHS runs; misses={:?}",
        ctx.miss_counts
    );

    // Case 2: A != 0 -> LHS true, RHS skipped; B untouched
    let mut vals2 = vec![0.0; prepared.ordered_vars.len()];
    vals2[ia] = 7.0;
    vals2[ib] = 9.0;
    let mut ctx2 = EvalCtx::with_values(vals2);
    let _ = compiled.eval_resolver_ctx(&mut ctx2).unwrap();

    let mut expected_calls2 = vec![0u32; prepared.ordered_vars.len()];
    let mut expected_misses2 = vec![0u32; prepared.ordered_vars.len()];
    expected_calls2[ia] = 1;
    expected_misses2[ia] = 1; // A evaluated once
    // B should remain zero
    assert_eq!(
        ctx2.call_counts, expected_calls2,
        "OR short-circuit should avoid B; calls={:?}",
        ctx2.call_counts
    );
    assert_eq!(
        ctx2.miss_counts, expected_misses2,
        "OR short-circuit should avoid B; misses={:?}",
        ctx2.miss_counts
    );
}
