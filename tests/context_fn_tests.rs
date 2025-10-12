use tabulon::Tabula;

#[repr(C)]
struct Ctx { bias: f64 }

// Context-using unary function: returns x + ctx.bias
extern "C" fn add_bias(ctx: *mut std::ffi::c_void, x: f64) -> f64 {
    if ctx.is_null() { return f64::NAN; }
    let c = unsafe { &*(ctx as *const Ctx) };
    x + c.bias
}

// Context-using binary function: scales and adds with bias held in ctx
extern "C" fn scale_add(ctx: *mut std::ffi::c_void, a: f64, b: f64) -> f64 {
    if ctx.is_null() { return f64::NAN; }
    let c = unsafe { &*(ctx as *const Ctx) };
    a * c.bias + b
}

#[test]
fn unary_ctx_function_eval_with_ctx_ptr() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    eng.register_unary("add_bias", add_bias, true).unwrap();

    let expr = eng.compile_ref("add_bias(A)").unwrap();
    let a = 5.0;

    let mut ctx = Ctx { bias: 10.0 };
    let out = expr.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert_eq!(out, 15.0);
}

#[test]
fn binary_ctx_function_eval_with_ctx() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    eng.register_binary("scale_add", scale_add, true).unwrap();

    // expression: scale_add(x, y) with bias=2.0 => 3 * 2 + 4 = 10
    let expr = eng.compile_ref("scale_add(X, Y)").unwrap();
    let x = 3.0;
    let y = 4.0;

    let mut ctx = Ctx { bias: 2.0 };
    let out = expr.eval_with_ctx(&[&x, &y], &mut ctx).unwrap();
    assert_eq!(out, 10.0);
}
