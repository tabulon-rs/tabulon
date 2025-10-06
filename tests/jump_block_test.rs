use tabulon::Tabula;

#[test]
fn test_jump_block_if() {
    let expr = "if(a+b>c, a+1, b+2)+if(a>b+c, a+1, b+2)";
    let mut engine = Tabula::new();
    let compiled = engine.compile(expr).unwrap();

    let a = 1.0;
    let b = 2.0;
    let c = 3.0;

    let result = compiled.eval(&[a, b, c]).unwrap();

    assert_eq!(result, 8.0);

    let a = 2.0;
    let b = 3.0;
    let c = 1.0;

    let result = compiled.eval(&[a, b, c]).unwrap();

    assert_eq!(result, 8.0);
}

#[test]
fn test_jump_block_or() {
    let expr = "(a+b) || (a+d)";
    let mut engine = Tabula::new();
    let compiled = engine.compile(expr).unwrap();

    let a = 1.0;
    let b = -1.0;
    let c = 3.0;
    let d = 4.0;

    let result = compiled.eval(&[a, b, c, d]).unwrap();
    assert_eq!(result, 1.0);
}
