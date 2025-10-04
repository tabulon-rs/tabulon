use tabulon::{Tabula, register_functions, function, JitError};

#[function]
pub fn mock_min(a: f64, b: f64) -> f64 { if a < b { a } else { b } }

#[test]
fn register_after_compile_requires_free_then_succeeds() {
    let mut eng = Tabula::new();

    // First compile something to force-create the JIT module
    let c = eng.compile("1 + 2").unwrap();
    assert_eq!(c.eval(&[]).unwrap(), 3.0);

    // Trying to register after module creation should fail
    let err = register_functions!(eng, mock_min).unwrap_err();
    match err {
        JitError::Internal(msg) => {
            assert!(msg.contains("cannot register functions"), "unexpected message: {}", msg);
        }
        other => panic!("expected Internal error, got: {other:?}"),
    }

    // Free JIT memory and reset module, then registration should work
    eng.free_memory();
    register_functions!(eng, mock_min).unwrap();

    // Now we can compile expressions that call the newly registered function
    let compiled = eng.compile("mock_min(A, B)").unwrap();
    let a = 3.0; let b = 5.0;
    assert_eq!(compiled.eval(&[&a, &b]).unwrap(), 3.0);
}

#[test]
fn clearing_functions_prevents_calls_until_reregistered() {
    let mut eng = Tabula::new();
    register_functions!(eng, mock_min).unwrap();

    // Works before clearing
    let compiled = eng.compile("mock_min(A,B)").unwrap();
    let a = 1.0; let b = 2.0;
    assert_eq!(compiled.eval(&[&a, &b]).unwrap(), 1.0);

    // Free compiled code and clear registry
    eng.free_memory();
    eng.clear_registered_functions();

    // Compiling calls to previously registered function should now fail with UnknownFunction
    match eng.compile("mock_min(1,2)") {
        Err(JitError::UnknownFunction { name, arity }) => {
            assert_eq!(name, "mock_min");
            assert_eq!(arity, 2);
        }
        Ok(_) => panic!("expected UnknownFunction, got Ok(_)"),
        Err(other) => panic!("expected UnknownFunction, got: {other:?}"),
    }

    // Free the (empty) module created by the failed compile, then re-register and compile again
    eng.free_memory();
    register_functions!(eng, min).unwrap();
    let compiled2 = eng.compile("min(1,2)").unwrap();
    assert_eq!(compiled2.eval(&[]).unwrap(), 1.0);
}

#[test]
fn eval_after_free_returns_invalidated_error() {
    let mut eng = Tabula::new();
    let compiled = eng.compile("A + B").unwrap();
    let a = 1.0; let b = 2.0;
    assert_eq!(compiled.eval(&[&a, &b]).unwrap(), 3.0);
    // Free JIT memory; the old compiled must be invalid now
    eng.free_memory();
    match compiled.eval(&[&a, &b]) {
        Err(JitError::Invalidated) => {}
        other => panic!("expected Invalidated, got: {:?}", other),
    }
}
