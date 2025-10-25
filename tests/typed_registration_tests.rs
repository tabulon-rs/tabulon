use tabulon::{Tabula, function};

#[derive(Debug)]
struct Ctx {
    bias: f64,
}

#[function]
fn add_bias(a: f64, ctx: &Ctx) -> f64 {
    a + ctx.bias
}

#[function]
fn sqr(x: f64) -> f64 {
    x * x
}

#[test]
fn register_typed_with_matching_ctx() {
    let mut eng = Tabula::<Ctx>::new_ctx();
    // Register using the typed, compile-time-checked API via the generated marker type
    eng.register_typed::<__tabulon_marker_add_bias>().unwrap();

    let e = eng.compile_ref("add_bias(A)").unwrap();
    let a = 5.0;
    let mut ctx = Ctx { bias: 1.5 };
    let out = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert!((out - 6.5).abs() < 1e-12);
}

#[test]
fn register_typed_no_ctx_function_on_unit_engine() {
    let mut eng = Tabula::new();
    eng.register_typed::<__tabulon_marker_sqr>().unwrap();

    let e = eng.compile_ref("sqr(A)").unwrap();
    let a = 4.0;
    let out = e.eval(&[&a]).unwrap();
    assert_eq!(out, 16.0);
}
