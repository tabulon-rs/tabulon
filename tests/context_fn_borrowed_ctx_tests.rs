use tabulon::{Tabula, function, register_functions};

#[derive(Debug)]
struct BorrowCtx<'a> {
    bias: &'a f64,
}

#[derive(Debug)]
struct BorrowSliceCtx<'a> {
    slice: &'a [i64],
}

#[function]
fn add_with_borrowed_bias<'a>(a: f64, ctx: &BorrowCtx<'a>) -> f64 {
    a + *ctx.bias
}

#[function]
fn idx_from_borrowed_slice<'a>(i: f64, ctx: &BorrowSliceCtx<'a>) -> f64 {
    ctx.slice[i as usize] as f64
}

#[test]
fn context_borrowed_field_read_only() {
    let bias_val = 7.5;
    let mut eng = Tabula::<BorrowCtx<'static>>::new_ctx();
    register_functions!(eng, add_with_borrowed_bias).unwrap();

    let a = 2.5;
    let mut ctx = BorrowCtx { bias: &bias_val };

    let e = eng.compile_ref("add_with_borrowed_bias(A)").unwrap();
    let out = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert!((out - 10.0).abs() < 1e-12);

    // uses_ctx flag should be true
    assert!(e.uses_ctx(), "expected uses_ctx() to be true for borrowed ctx");
}

#[test]
fn context_borrowed_slice_read_only() {
    let backing = [10i64, 20, 30, 40];
    let mut eng = Tabula::<BorrowSliceCtx<'static>>::new_ctx();
    register_functions!(eng, idx_from_borrowed_slice).unwrap();

    let mut ctx = BorrowSliceCtx { slice: &backing[..] };
    let e = eng.compile("idx_from_borrowed_slice(A)").unwrap();

    let out0 = e.eval_with_ctx(&[0f64], &mut ctx).unwrap();
    assert_eq!(out0, 10.0);

    let out2 = e.eval_with_ctx(&[2f64], &mut ctx).unwrap();
    assert_eq!(out2, 30.0);

    // uses_ctx flag check on ref-compiled variant too
    let e_ref = eng.compile_ref("idx_from_borrowed_slice(A)").unwrap();
    assert!(e_ref.uses_ctx());
}

#[test]
fn mismatched_borrowed_context_registration_error() {
    // Engine expects BorrowCtx, but function expects BorrowSliceCtx -> should error
    let mut eng = Tabula::<BorrowCtx<'_>>::new_ctx();
    let err = register_functions!(eng, idx_from_borrowed_slice).unwrap_err();
    match err {
        tabulon::JitError::Internal(msg) => assert!(msg.contains("context type mismatch"), "unexpected message: {}", msg),
        _ => panic!("expected Internal error for context type mismatch"),
    }
}
