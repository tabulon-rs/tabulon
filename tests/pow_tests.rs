use tabulon::Tabula;

#[test]
fn pow_basic() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("2 ^ 3").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), 8.0);
}

#[test]
fn pow_right_associative() {
    let mut eng = Tabula::new();
    // 2^(3^2) = 2^9 = 512
    let e = eng.compile_ref("2 ^ 3 ^ 2").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), 512.0);
}

#[test]
fn pow_precedence_with_unary() {
    let mut eng = Tabula::new();
    // - (2^2) = -4
    let e1 = eng.compile_ref("-2^2").unwrap();
    assert_eq!(e1.eval(&[]).unwrap(), -4.0);

    // (-2)^2 = 4
    let e2 = eng.compile_ref("(-2)^2").unwrap();
    assert_eq!(e2.eval(&[]).unwrap(), 4.0);
}

#[test]
fn pow_precedence_with_mul() {
    let mut eng = Tabula::new();
    let e1 = eng.compile_ref("2^3*2").unwrap();
    assert_eq!(e1.eval(&[]).unwrap(), 16.0);

    let e2 = eng.compile_ref("2*2^3").unwrap();
    assert_eq!(e2.eval(&[]).unwrap(), 16.0);
}

#[test]
fn pow_with_variables() {
    let mut eng = Tabula::new();
    let a = 3.0;
    let e = eng.compile_ref("a ^ 2").unwrap();
    assert_eq!(e.eval(&[&a]).unwrap(), 9.0);
}

#[test]
fn pow_fractional_exponent() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("9 ^ 0.5").unwrap();
    let out = e.eval(&[]).unwrap();
    assert!((out - 3.0).abs() < 1e-12);
}
