use tabulon::{JitError, Tabula};

#[test]
fn values_len_error_on_ref_eval() {
    let mut eng = Tabula::new();
    let expr = eng.compile_ref("A + B + C").unwrap();
    let a = 1.0;
    let b = 2.0;
    let err = expr.eval(&[&a, &b]).unwrap_err();
    match err {
        JitError::ValuesLen { expected, got } => {
            assert_eq!(expected, 3);
            assert_eq!(got, 2);
        }
        other => panic!("unexpected error: {:?}", other),
    }
}

#[test]
fn unknown_function_error_on_compile() {
    let mut eng = Tabula::new();
    let err = eng.compile_ref("no_such_fn(1)").unwrap_err();
    match err {
        JitError::UnknownFunction { name, arity } => {
            assert_eq!(name, "no_such_fn");
            assert_eq!(arity, 1);
        }
        other => panic!("unexpected error: {:?}", other),
    }
}

#[test]
fn invalidated_after_free_memory() {
    let mut eng = Tabula::new();
    let expr = eng.compile_ref("X + 1").unwrap();
    let x = 41.0;
    assert_eq!(expr.eval(&[&x]).unwrap(), 42.0);

    eng.free_memory();

    let err = expr.eval(&[&x]).unwrap_err();
    match err {
        JitError::Invalidated => {}
        other => panic!("expected Invalidated, got {:?}", other),
    }
}
