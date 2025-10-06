use std::sync::Arc;
use std::thread;
use tabulon::{JitError, Tabula};

#[test]
fn compiled_expr_is_send_and_sync() -> Result<(), JitError> {
    let mut engine = Tabula::new();
    let compiled = engine.compile("a + b")?;

    // Wrap the compiled expression in an Arc to share it across threads.
    // This only compiles if CompiledExpr is Send + Sync.
    let shared_expr = Arc::new(compiled);

    let mut handles = vec![];

    // Spawn 10 threads
    for i in 0..10 {
        let expr_clone = Arc::clone(&shared_expr);

        let handle = thread::spawn(move || {
            // Each thread has its own independent variable values.
            let a = i as f64;
            let b = (i * 2) as f64;

            // Run eval 100 times in each thread.
            for _ in 0..100 {
                let result = expr_clone.eval(&[a, b]).unwrap();
                assert_eq!(result, a + b);
            }
        });
        handles.push(handle);
    }

    // Wait for all threads to complete
    for handle in handles {
        handle.join().unwrap();
    }

    Ok(())
}
