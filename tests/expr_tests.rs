use tabulon::Tabula;

#[test]
fn expr_mul_add() {
    let expr = "A + B";
    let mut eng = Tabula::new();
    let compiled = eng.compile_ref(expr).unwrap();
    let str_v = 100.0;
    let bonus_str = 20.0;
    let out = compiled.eval(&[&str_v, &bonus_str]).unwrap();
    assert_eq!(out, 120.0);
}

#[test]
fn expr_eq() {
    let expr = "A == B";
    let mut eng = Tabula::new();
    let compiled = eng.compile_ref(expr).unwrap();
    let a = 100.0;
    let b = 100.0;
    let c = 200.0;
    let out1 = compiled.eval(&[&a, &b]).unwrap();
    let out2 = compiled.eval(&[&a, &c]).unwrap();
    assert_eq!(out1, 1.0);
    assert_eq!(out2, 0.0);
}

#[test]
fn expr_complex() {
    let expr = "A / 0.10 + 10 + B";
    let mut eng = Tabula::new();
    let compiled = eng.compile_ref(expr).unwrap();
    let wis = 30.0;
    let bonus = 5.0;
    let out = compiled.eval(&[&wis, &bonus]).unwrap(); // 30/0.1 + 10 + 5 = 300 + 15 = 315
    assert_eq!(out, 315.0);
}

#[test]
fn expr_duplicated_var() {
    let expr = "A + A";
    let mut eng = Tabula::new();
    let compiled = eng.compile_ref(expr).unwrap();
    let str_v = 100.0;
    let out = compiled.eval(&[&str_v]).unwrap();
    assert_eq!(out, 200.0);
}

#[test]
fn expr_relations_constants_and_vars() {
    let mut eng = Tabula::new();
    let a = 1.0;
    // A < 2 => true
    let c = eng.compile_ref("A < 2").unwrap();
    assert_eq!(c.eval(&[&a]).unwrap(), 1.0);

    // A <= 1 => true
    let c = eng.compile_ref("A <= 1").unwrap();
    assert_eq!(c.eval(&[&a]).unwrap(), 1.0);

    // A > 1 => false
    let c = eng.compile_ref("A > 1").unwrap();
    assert_eq!(c.eval(&[&a]).unwrap(), 0.0);

    // A >= 1 => true
    let c = eng.compile_ref("A >= 1").unwrap();
    assert_eq!(c.eval(&[&a]).unwrap(), 1.0);

    // A != 2 => true
    let c = eng.compile_ref("A != 2").unwrap();
    assert_eq!(c.eval(&[&a]).unwrap(), 1.0);
}

#[test]
fn expr_logical_ops() {
    let mut eng = Tabula::new();
    let a = 5.0;
    let b = 3.0;
    let c = 10.0;
    // (A > B) && (B < C) => true
    let cmp = eng.compile_ref("(A > B) && (B < C)").unwrap();
    assert_eq!(cmp.eval(&[&a, &b, &c]).unwrap(), 1.0);

    // X || Y with 0 and non-zero
    let x0 = 0.0;
    let y2 = 2.0;
    let or = eng.compile_ref("X || Y").unwrap();
    assert_eq!(or.eval(&[&x0, &y2]).unwrap(), 1.0);

    // X && Y with non-zero and zero
    let x2 = 2.0;
    let y0 = 0.0;
    let and = eng.compile_ref("X && Y").unwrap();
    assert_eq!(and.eval(&[&x2, &y0]).unwrap(), 0.0);
}

#[test]
fn expr_precedence_mix() {
    let mut eng = Tabula::new();
    // (A + 2) > 2 && 0 || 1  with A=1 -> 3>2 true -> true && 0 -> false -> false || 1 -> true
    let a = 1.0;
    let e = eng.compile_ref("(A + 2) > 2 && 0 || 1").unwrap();
    assert_eq!(e.eval(&[&a]).unwrap(), 1.0);
}

#[test]
fn expr_if_builtin_constants() {
    let mut eng = Tabula::new();
    let e1 = eng.compile_ref("if(1, 1, 2)").unwrap();
    assert_eq!(e1.eval(&[]).unwrap(), 1.0);

    let e2 = eng.compile_ref("if(0, 1, 2)").unwrap();
    assert_eq!(e2.eval(&[]).unwrap(), 2.0);

    let e3 = eng.compile_ref("if(2, 1, 2)").unwrap();
    assert_eq!(e3.eval(&[]).unwrap(), 1.0);
}

#[test]
fn expr_builtin_max_constants() {
    let mut eng = Tabula::new();
    let e1 = eng.compile_ref("max(1, 2) == 2").unwrap();
    assert_eq!(e1.eval(&[]).unwrap(), 1.0);

    let e2 = eng.compile_ref("max(-1, 0) == 0").unwrap();
    assert_eq!(e2.eval(&[]).unwrap(), 1.0);

    let e3 = eng
        .compile_ref("max(1.1111111111111, 1.1111111111112) == 1.1111111111112")
        .unwrap();
    assert_eq!(e3.eval(&[]).unwrap(), 1.0);
}

#[test]
fn expr_many_vars() {
    let mut eng = Tabula::new();
    let a = 1.0;
    let b = 2.0;
    let c = 3.0;
    let d = 4.0;
    let e = 5.0;
    let f = 6.0;
    let g = 7.0;
    let h = 8.0;
    let e1 = eng.compile_ref("A + B + C + D + E + F + G + H").unwrap();
    assert_eq!(e1.eval(&[&a, &b, &c, &d, &e, &f, &g, &h]).unwrap(), 36.0);
}
