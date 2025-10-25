use tabulon::{Tabula, function, register_functions_typed};

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
fn typed_macro_with_matching_ctx() {
    let mut eng = Tabula::<Ctx>::new_ctx();
    // Use the typed macro with the generated marker type
    register_functions_typed!(eng, __tabulon_marker_add_bias).unwrap();

    let e = eng.compile_ref("add_bias(A)").unwrap();
    let a = 2.0;
    let mut ctx = Ctx { bias: 0.5 };
    let out = e.eval_with_ctx(&[&a], &mut ctx).unwrap();
    assert!((out - 2.5).abs() < 1e-12);
}

#[test]
fn typed_macro_no_ctx_function_on_unit_engine() {
    let mut eng = Tabula::new();
    register_functions_typed!(eng, __tabulon_marker_sqr).unwrap();

    let e = eng.compile_ref("sqr(A)").unwrap();
    let a = 4.0;
    let out = e.eval(&[&a]).unwrap();
    assert_eq!(out, 16.0);
}
