use tabulon::Tabula;

#[test]
fn arithmetic_precedence_mul_before_add() {
    // 1 + 2 * 3 = 7 (mul before add)
    let mut eng = Tabula::new();
    let c = eng.compile_ref("1 + 2 * 3").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 7.0);
}

#[test]
fn parentheses_override() {
    // (1 + 2) * 3 = 9 (parentheses override)
    let mut eng = Tabula::new();
    let c = eng.compile_ref("(1 + 2) * 3").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 9.0);
}

#[test]
fn unary_minus_precedence() {
    // -A * B == (-A) * B
    let mut eng = Tabula::new();
    let c = eng.compile_ref("-A * B").unwrap();
    let a = 2.0;
    let b = 3.0;
    assert_eq!(c.eval(&[&a, &b]).unwrap(), -6.0);
}

#[test]
fn left_associativity_sub() {
    // A - B - C = (A - B) - C
    let mut eng = Tabula::new();
    let c = eng.compile_ref("A - B - C").unwrap();
    let a = 10.0;
    let b = 2.0;
    let d = 3.0;
    assert_eq!(c.eval(&[&a, &b, &d]).unwrap(), 5.0);
}

#[test]
fn relational_vs_equality_precedence() {
    // Relational binds tighter than equality: A == (B < C)
    // Choose values to distinguish parsing: with A=0, B=2, C=3
    // (B < C) -> 1.0; A == 1.0 -> 0.0
    // If parsed as (A == B) < C it would be (0==2)->0 < 3 -> 1, which differs.
    let mut eng = Tabula::new();
    let c = eng.compile_ref("A == B < C").unwrap();
    let a = 0.0;
    let b = 2.0;
    let d = 3.0;
    assert_eq!(c.eval(&[&a, &b, &d]).unwrap(), 0.0);
}

#[test]
fn and_has_higher_precedence_than_or() {
    // && binds tighter than ||: 1 || (0 && 0) = 1
    let mut eng = Tabula::new();
    let c = eng.compile_ref("1 || 0 && 0").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 1.0);

    // Parentheses change grouping: (1 || 0) && 0 = 0
    let c2 = eng.compile_ref("(1 || 0) && 0").unwrap();
    assert_eq!(c2.eval(&[]).unwrap(), 0.0);
}

#[test]
fn call_primary_with_max_against_mul() {
    // Function calls are primary; test with built-in max
    let mut eng = Tabula::new();
    let c = eng.compile_ref("max(1, 2) + 3 * 4").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 14.0); // 2 + (3*4)

    let c2 = eng.compile_ref("(max(1, 2) + 3) * 4").unwrap();
    assert_eq!(c2.eval(&[]).unwrap(), 20.0); // (2 + 3) * 4
}
