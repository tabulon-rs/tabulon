use tabulon::{CtxPtr, Tabula, function, register_functions};

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

#[test]
fn context_read_only_param() {
    let mut eng = Tabula::new();
    register_functions!(eng, add_bias).unwrap();

    let a = 5.0;
    let mut ctx = Ctx { bias: 10.0, count: 0 };
    let ctx_ptr = (&mut ctx as *mut Ctx) as CtxPtr;

    let e = eng.compile_ref("add_bias(A)").unwrap();
    let out = e.eval_with_ctx_ptr(&[&a], ctx_ptr).unwrap();
    assert_eq!(out, 15.0);
}

#[test]
fn context_param_first_position() {
    let mut eng = Tabula::new();
    register_functions!(eng, bias_add_ctx_first).unwrap();

    let a = 3.0;
    let b = 4.0;
    let mut ctx = Ctx { bias: 2.5, count: 0 };
    let ctx_ptr = (&mut ctx as *mut Ctx) as CtxPtr;

    let e = eng.compile_ref("bias_add_ctx_first(A, B)").unwrap();
    let out = e.eval_with_ctx_ptr(&[&a, &b], ctx_ptr).unwrap();
    assert!((out - (3.0 + 4.0 + 2.5)).abs() < 1e-12);
}

#[test]
fn context_mut_param_modifies_state() {
    let mut eng = Tabula::new();
    register_functions!(eng, count_and_add).unwrap();

    let a = 1.0;
    let mut ctx = Ctx { bias: 2.0, count: 0 };
    let ctx_ptr = (&mut ctx as *mut Ctx) as CtxPtr;

    let e = eng.compile_ref("count_and_add(A)").unwrap();
    let out1 = e.eval_with_ctx_ptr(&[&a], ctx_ptr).unwrap();
    assert_eq!(out1, 3.0);
    assert_eq!(ctx.count, 1);

    let out2 = e.eval_with_ctx_ptr(&[&a], ctx_ptr).unwrap();
    assert_eq!(out2, 3.0);
    assert_eq!(ctx.count, 2);
}

#[test]
fn context_param_vec_state() {
    let mut eng = Tabula::new();
    register_functions!(eng, get_vec_ctx).unwrap();

    let e = eng.compile("get_vec_ctx(A)").unwrap();
    let ctx = VecCtx{vec: vec![1,2,3]};

    let out1 = e.eval_with_ctx(&[0f64], &ctx).unwrap();
    assert_eq!(out1, 1.0);
    let out2 = e.eval_with_ctx(&[1f64], &ctx).unwrap();
    assert_eq!(out2, 2.0);
    let out3 = e.eval_with_ctx(&[2f64], &ctx).unwrap();
    assert_eq!(out3, 3.0);
}