use tabulon::Tabula;

#[test]
fn not_basic() {
    let mut eng = Tabula::new();
    let c = eng.compile_ref("!0").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 1.0);

    let c = eng.compile_ref("!1").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 0.0);
}

#[test]
fn not_with_eq() {
    let mut eng = Tabula::new();
    let c = eng.compile_ref("!(1 == 1)").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 0.0);

    let c = eng.compile_ref("!(1 == 2)").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 1.0);
}

#[test]
fn not_chaining_and_unary_minus() {
    let mut eng = Tabula::new();
    let c = eng.compile_ref("!!1").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 1.0);

    let x = 2.0;
    let c = eng.compile_ref("!-x").unwrap();
    assert_eq!(c.eval(&[&x]).unwrap(), 0.0);
}

#[test]
fn not_zero_edge_cases() {
    let mut eng = Tabula::new();
    let zp = 0.0f64; // +0.0
    let c = eng.compile_ref("!x").unwrap();
    assert_eq!(c.eval(&[&zp]).unwrap(), 1.0);

    let zn = -0.0f64; // -0.0도 0으로 취급
    assert_eq!(c.eval(&[&zn]).unwrap(), 1.0);
}
