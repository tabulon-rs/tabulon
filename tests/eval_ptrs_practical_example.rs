use tabulon::{JitError, Tabula};

// A practical, non-ECS example that demonstrates how to reuse a stable array of values
// and build raw pointers right before calling `eval_ptrs`.
//
// This pattern keeps memory addresses stable and avoids caching pointers long-term.
// It also shows how to update values in place and re-evaluate without reallocations.
#[test]
fn eval_ptrs_with_stable_boxed_slice_and_rebuilt_ptrs() -> Result<(), JitError> {
    let mut engine = Tabula::new();
    let compiled = engine.compile_ref("a + b * 2")?;

    // Fixed-size set of variables -> store them in Box<[f64]> so addresses are stable.
    let mut values: Box<[f64]> = vec![3.0, 4.5].into_boxed_slice();

    // Build pointers just-in-time for the call based on compiled.vars() order.
    let ptrs: Vec<*const f64> = (0..compiled.vars().len())
        .map(|i| &values[i] as *const f64)
        .collect();
    let out1 = compiled.eval_ptrs(&ptrs)?;
    assert!((out1 - (3.0 + 4.5 * 2.0)).abs() < 1e-12);

    // Update values in place to keep addresses stable.
    values[0] = 5.0; // a
    values[1] = 10.0; // b

    // Rebuild pointers just before the second evaluation.
    let ptrs2: Vec<*const f64> = (0..compiled.vars().len())
        .map(|i| &values[i] as *const f64)
        .collect();
    let out2 = compiled.eval_ptrs(&ptrs2)?;
    assert!((out2 - (5.0 + 10.0 * 2.0)).abs() < 1e-12);

    Ok(())
}

// Pointer safety tips when using eval_ptrs (summary):
// - Build pointers right before calling eval_ptrs; avoid caching long-term.
// - If you must cache, keep values in Box<f64>/Box<[f64]> (or an arena) and update in place.
// - Do not use pointers after freeing/invalidation (see Tabula::free_memory).
