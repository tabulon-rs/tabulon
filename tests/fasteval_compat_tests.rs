use fasteval::{Compiler, Evaler, Parser, Slab, eval_compiled_ref};
use rand::Rng;
use std::collections::HashMap;
use tabulon::Tabula;

const EPS: f64 = 1e-9;

fn eval_with_fasteval(expr: &str, vars: &HashMap<String, f64>) -> Result<f64, fasteval::Error> {
    let mut slab = Slab::new();
    let parser = Parser::new();
    let compiled = parser
        .parse(expr, &mut slab.ps)
        .unwrap()
        .from(&slab.ps)
        .compile(&slab.ps, &mut slab.cs);

    // Namespace closure implementing variables and built-ins: if, max
    // Note: we implement Tabulon semantics for if: cond >= 1.0 is true, else false
    let mut ns = |name: &str, args: Vec<f64>| -> Option<f64> {
        match name {
            "if" => {
                if args.len() != 3 {
                    return Some(f64::NAN);
                }
                if args[0] >= 1.0 {
                    Some(args[1])
                } else {
                    Some(args[2])
                }
            }
            "max" => {
                if args.len() != 2 {
                    return Some(f64::NAN);
                }
                Some(args[0].max(args[1]))
            }
            // Variables
            _ => {
                if !args.is_empty() {
                    return Some(f64::NAN);
                }
                vars.get(name).copied()
            }
        }
    };

    Ok(eval_compiled_ref!(&compiled, &slab, &mut ns))
}

#[test]
fn tabulon_matches_fasteval_on_random_inputs() {
    // Expressions limited to features supported by both: arithmetic, comparisons, if, max.
    let expressions = vec![
        "a + b",
        "a * b + c",
        "(a + b) * c - 3.5",
        "a / 0.1 + 10 + c",
        "a == b",
        "a != b",
        "a < b",
        "a <= b",
        "a > b",
        "a >= b",
        "max(a, b)",
        "if(a > b, a, b)",
        "max(a*2, b/3 + c)",
        "(max(a,b) + if(a < b, b - a, a - b)) / (c + 1)",
        "if(max(a,b) == a, a - b, b - a)",
    ];

    // Compile Tabulon for each expression once.
    let mut compiled_tabulon = Vec::new();
    for expr in &expressions {
        let mut eng = Tabula::new();
        let compiled = eng.compile_ref(expr).unwrap();
        compiled_tabulon.push((expr.to_string(), compiled));
    }

    // Randomized trials per expression
    let trials = 200usize;
    let mut rng = rand::thread_rng();

    for (expr, compiled) in compiled_tabulon.into_iter() {
        for _ in 0..trials {
            // Generate stable set of variable values
            let mut vars: HashMap<String, f64> = HashMap::new();
            // Keep the range moderate to avoid extreme FP values; ensure c != -1 to keep (c+1) away from zero
            let a: f64 = rng.gen_range(-100.0..100.0);
            let b: f64 = rng.gen_range(-100.0..100.0);
            let mut c: f64 = rng.gen_range(-100.0..100.0);
            if (c + 1.0).abs() < 1e-6 {
                c += 2.0;
            }
            vars.insert("a".to_string(), a);
            vars.insert("b".to_string(), b);
            vars.insert("c".to_string(), c);

            // Evaluate with fasteval
            let fe_out = eval_with_fasteval(&expr, &vars).unwrap();

            // Evaluate with tabulon using ordered_vars
            let ordered_values: Vec<&f64> = compiled
                .vars()
                .iter()
                .map(|name| vars.get(name).unwrap_or(&0.0))
                .collect();
            let tab_out = compiled.eval(&ordered_values).unwrap();

            if fe_out.is_nan() && tab_out.is_nan() {
                continue; // both NaN, consider equal
            }
            // Allow tiny numerical differences
            let diff = (fe_out - tab_out).abs();
            assert!(
                diff <= EPS,
                "expr='{}' fasteval={} tabulon={} diff={} vars={:?}",
                expr,
                fe_out,
                tab_out,
                diff,
                vars
            );
        }
    }
}
