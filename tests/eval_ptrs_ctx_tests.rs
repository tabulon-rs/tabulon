use tabulon::Tabula;

#[repr(C)]
struct Ctx { bias: f64 }

// Context-using unary function: returns x + ctx.bias
extern "C" fn add_bias(ctx: *mut std::ffi::c_void, x: f64) -> f64 {
    if ctx.is_null() { return f64::NAN; }
    let c = unsafe { &*(ctx as *const Ctx) };
    x + c.bias
}

#[test]
fn eval_ptrs_with_ctx_unary() {
    let mut eng = Tabula::<String, tabulon::IdentityResolver, Ctx>::new_ctx();
    eng.register_unary("add_bias", add_bias, true).unwrap();

    let e = eng.compile_ref("add_bias(A)").unwrap();
    let x = 7.0;
    let mut ctx = Ctx { bias: 3.0 };

    let ptrs: [*const f64; 1] = [&x as *const f64];
    let out = e.eval_ptrs_with_ctx(&ptrs, &mut ctx).unwrap();
    assert_eq!(out, 10.0);
}
