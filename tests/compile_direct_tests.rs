use tabulon::{JitError, Tabula};

#[test]
fn variable_order_and_eval_compile() -> Result<(), JitError> {
    let mut engine = Tabula::new();
    let compiled = engine.compile("(Str + BonusStr) * MulStr")?;
    assert_eq!(compiled.vars(), &["Str", "BonusStr", "MulStr"]);

    let out = compiled.eval(&[100.0, 20.0, 1.5])?;
    assert!((out - 180.0).abs() < 1e-9);
    Ok(())
}

#[test]
fn values_len_error_compile() {
    let mut engine = Tabula::new();
    let compiled = engine.compile("A + B + C").unwrap();
    let err = compiled.eval(&[1.0, 2.0]).unwrap_err();
    match err {
        JitError::ValuesLen { expected, got } => {
            assert_eq!(expected, 3);
            assert_eq!(got, 2);
        }
        _ => panic!("expected ValuesLen error"),
    }
}

#[test]
fn if_semantics_compile_threshold() -> Result<(), JitError> {
    let mut engine = Tabula::new();
    // if(a, 10, 20): per current semantics, cond >= 1.0 is true
    let compiled = engine.compile("if(a, 10, 20)")?;

    // a = 0.5 -> false => else branch
    let out1 = compiled.eval(&[0.5])?;
    assert!((out1 - 20.0).abs() < 1e-9);

    // a = 1.0 -> true => then branch
    let out2 = compiled.eval(&[1.0])?;
    assert!((out2 - 10.0).abs() < 1e-9);

    // a = 2.0 -> true (>= 1.0)
    let out3 = compiled.eval(&[2.0])?;
    assert!((out3 - 10.0).abs() < 1e-9);

    Ok(())
}
