use tabulon::{Tabula, function, register_functions};

#[function]
pub fn min(a: f64, b: f64) -> f64 {
    if a < b { a } else { b }
}

#[function]
pub fn one() -> f64 {
    1.0
}

#[function]
pub fn pow2(x: f64) -> f64 {
    x * x
}

#[test]
fn custom_min_binary() {
    let mut eng = Tabula::new();
    register_functions!(eng, min).unwrap();

    let compiled = eng.compile_ref("min(A, B)").unwrap();
    let a = 3.0;
    let b = 5.0;
    assert_eq!(compiled.vars(), &["A", "B"]);
    assert_eq!(compiled.eval(&[&a, &b]).unwrap(), 3.0);
}

#[test]
fn custom_zero_arity_and_unary() {
    let mut eng = Tabula::new();
    register_functions!(eng, one, pow2).unwrap();

    // Use both registered functions
    let compiled = eng.compile_ref("one() + pow2(A)").unwrap();
    let a = 4.0;
    assert_eq!(compiled.vars(), &["A"]);
    assert_eq!(compiled.eval(&[&a]).unwrap(), 1.0 + 16.0);
}
