use tabulon::{JitError, Tabula};

// Manual direct-call registration using the new ctx-first ABI (Fn2)
extern "C" fn mul_ctx(_ctx: *mut std::ffi::c_void, a: f64, b: f64) -> f64 {
    a * b
}

#[test]
fn manual_direct_call_binary() {
    let mut eng = Tabula::new();
    eng.register_binary("mul_ctx", mul_ctx, false).unwrap();

    let e = eng.compile_ref("mul_ctx(3, 4)").unwrap();
    let out = e.eval(&[]).unwrap();
    assert_eq!(out, 12.0);
}

#[test]
fn register_after_module_created_should_fail() {
    let mut eng = Tabula::new();
    // Trigger JIT module creation by compiling once
    let _ = eng.compile_ref("A + B").unwrap();

    // Further registrations must fail
    extern "C" fn id_fn(_ctx: *mut std::ffi::c_void, x: f64) -> f64 {
        x
    }
    let err = eng.register_unary("id", id_fn, false).unwrap_err();
    match err {
        JitError::Internal(msg) => {
            assert!(msg.contains("cannot register functions after JIT module is created"))
        }
        _ => panic!("expected Internal error"),
    }
}
