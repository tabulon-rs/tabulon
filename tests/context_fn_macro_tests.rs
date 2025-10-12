use tabulon::{Tabula, function, register_functions};

#[derive(Debug)]
struct Ctx {
    bias: f64,
    count: usize,
}

#[derive(Debug)]
struct VecCtx {
    vec: Vec<i64>,
}

#[function]
fn get_vec_ctx(a: f64, ctx: &VecCtx) -> f64 {
    ctx.vec[a as usize] as f64
}

#[function]
fn add_bias(a: f64, ctx: &Ctx) -> f64 {
    a + ctx.bias
}

#[function]
fn bias_add_ctx_first(ctx: &Ctx, a: f64, b: f64) -> f64 {
    a + b + ctx.bias
}

#[function]
fn count_and_add(a: f64, ctx: &mut Ctx) -> f64 {
    ctx.count += 1;
    a + ctx.bias
}

#[function]
fn identity(a: f64) -> f64 {
    a
}

#[test]
fn context_read_only_param() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    register_functions!(eng, add_bias, identity).unwrap();

    let a = 5.0;
    let mut ctx = Ctx { bias: 10.0, count: 0 };

    let e = eng.compile_ref("add_bias(A)").unwrap();
    let out = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert_eq!(out, 15.0);

    let e2 = eng.compile_ref("identity(A)").unwrap();
    let out2 = e2.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert_eq!(out2, 5.0);
}

#[test]
fn context_param_first_position() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    register_functions!(eng, bias_add_ctx_first).unwrap();

    let a = 3.0;
    let b = 4.0;
    let mut ctx = Ctx { bias: 2.5, count: 0 };

    let e = eng.compile_ref("bias_add_ctx_first(A, B)").unwrap();
    let out = e.eval_with_ctx(&[&a, &b], &mut ctx).unwrap();
    assert!((out - (3.0 + 4.0 + 2.5)).abs() < 1e-12);
}

#[test]
fn context_mut_param_modifies_state() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    register_functions!(eng, count_and_add).unwrap();

    let a = 1.0;
    let mut ctx = Ctx { bias: 2.0, count: 0 };

    let e = eng.compile_ref("count_and_add(A)").unwrap();
    let out1 = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert_eq!(out1, 3.0);
    assert_eq!(ctx.count, 1);

    let out2 = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert_eq!(out2, 3.0);
    assert_eq!(ctx.count, 2);
}

#[test]
fn context_param_vec_state() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, VecCtx>::new_ctx();
    register_functions!(eng, get_vec_ctx).unwrap();

    let e = eng.compile("get_vec_ctx(A)").unwrap();
    let mut ctx = VecCtx{vec: vec![1,2,3]};

    let out1 = e.eval_with_ctx(&[0f64], &mut ctx).unwrap();
    assert_eq!(out1, 1.0);
    let out2 = e.eval_with_ctx(&[1f64], &mut ctx).unwrap();
    assert_eq!(out2, 2.0);
    let out3 = e.eval_with_ctx(&[2f64], &mut ctx).unwrap();
    assert_eq!(out3, 3.0);
}

#[test]
fn mismatched_context_registration_error() {
    // Engine expects Ctx, but function get_vec_ctx requires VecCtx. Should error.
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    let err = register_functions!(eng, get_vec_ctx).unwrap_err();
    match err {
        tabulon::JitError::Internal(msg) => assert!(msg.contains("context type mismatch"), "unexpected message: {}", msg),
        _ => panic!("expected Internal error for context type mismatch"),
    }
}

#[test]
fn uses_ctx_flags() {
    // add_bias uses &Ctx
    let mut eng1 = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    register_functions!(eng1, add_bias).unwrap();
    let e1 = eng1.compile_ref("add_bias(A)").unwrap();
    assert!(e1.uses_ctx(), "expected uses_ctx() to be true for add_bias");

    // count_and_add uses &mut Ctx
    let mut eng2 = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    register_functions!(eng2, count_and_add).unwrap();
    let e2 = eng2.compile_ref("count_and_add(A)").unwrap();
    assert!(e2.uses_ctx(), "expected uses_ctx() to be true for count_and_add");

    // get_vec_ctx with VecCtx engine
    let mut eng3 = Tabula::<String, tabulon::IdentityResolver, VecCtx>::new_ctx();
    register_functions!(eng3, get_vec_ctx).unwrap();
    let e3 = eng3.compile_ref("get_vec_ctx(A)").unwrap();
    assert!(e3.uses_ctx(), "expected uses_ctx() to be true for get_vec_ctx");

    // Context-free expression should report false
    let mut eng4 = Tabula::new();
    let e4 = eng4.compile_ref("A + B * 2").unwrap();
    assert!(!e4.uses_ctx(), "expected uses_ctx() to be false for context-free expr");
}
