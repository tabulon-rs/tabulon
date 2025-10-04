use crate::ast::Ast;

// Safe, semantics-preserving optimizer. Treats Call as impure (no folding).
pub(crate) fn optimize(ast: Ast) -> Ast {
    fixpoint(ast, 2) // two passes are enough for our simple rules
}

fn fixpoint(mut ast: Ast, max_rounds: usize) -> Ast {
    for _ in 0..max_rounds {
        let curr_dbg = ast.clone();
        let next = fold(ast);
        if next == curr_dbg {
            return next;
        }
        ast = next;
    }
    ast
}

fn fold(ast: Ast) -> Ast {
    match ast {
        Ast::Num(_) | Ast::Var(_) => ast,
        Ast::Neg(x) => {
            let x = Box::new(fold(*x));
            match *x {
                Ast::Num(v) => Ast::Num(-v),
                Ast::Neg(inner) => *inner,
                other => Ast::Neg(Box::new(other)),
            }
        }
        Ast::Add(a, b) => fold_add(*a, *b),
        Ast::Sub(a, b) => {
            // normalize to Add(a, Neg(b)) then fold
            let a = fold(*a);
            let b = fold(*b);
            fold_add(a, Ast::Neg(Box::new(b)))
        }
        Ast::Mul(a, b) => fold_mul(*a, *b),
        Ast::Div(a, b) => {
            let a = fold(*a);
            let b = fold(*b);
            match (a, b) {
                (Ast::Num(x), Ast::Num(y)) => Ast::Num(x / y),
                (x, Ast::Num(1.0)) => x,
                (x, y) => Ast::Div(Box::new(x), Box::new(y)),
            }
        }
        Ast::Eq(a, b) => cmp_fold(*a, *b, |x, y| (x == y) as i32 as f64, |a, b| Ast::Eq(Box::new(a), Box::new(b))),
        Ast::Ne(a, b) => cmp_fold(*a, *b, |x, y| (x != y) as i32 as f64, |a, b| Ast::Ne(Box::new(a), Box::new(b))),
        Ast::Lt(a, b) => cmp_fold(*a, *b, |x, y| (x < y) as i32 as f64, |a, b| Ast::Lt(Box::new(a), Box::new(b))),
        Ast::Le(a, b) => cmp_fold(*a, *b, |x, y| (x <= y) as i32 as f64, |a, b| Ast::Le(Box::new(a), Box::new(b))),
        Ast::Gt(a, b) => cmp_fold(*a, *b, |x, y| (x > y) as i32 as f64, |a, b| Ast::Gt(Box::new(a), Box::new(b))),
        Ast::Ge(a, b) => cmp_fold(*a, *b, |x, y| (x >= y) as i32 as f64, |a, b| Ast::Ge(Box::new(a), Box::new(b))),
        Ast::And(a, b) => {
            let a = fold(*a);
            let b = fold(*b);
            match (a, b) {
                (Ast::Num(x), Ast::Num(y)) => Ast::Num(((x != 0.0) && (y != 0.0)) as i32 as f64),
                (Ast::Num(0.0), _) => Ast::Num(0.0),
                (_, Ast::Num(0.0)) => Ast::Num(0.0),
                (x, y) => Ast::And(Box::new(x), Box::new(y)),
            }
        }
        Ast::Or(a, b) => {
            let a = fold(*a);
            let b = fold(*b);
            match (a, b) {
                (Ast::Num(x), Ast::Num(y)) => Ast::Num(((x != 0.0) || (y != 0.0)) as i32 as f64),
                (Ast::Num(x), _) if x != 0.0 => Ast::Num(1.0),
                (_, Ast::Num(y)) if y != 0.0 => Ast::Num(1.0),
                (x, y) => Ast::Or(Box::new(x), Box::new(y)),
            }
        }
        Ast::If(c, t, e) => {
            let c = fold(*c);
            let t = fold(*t);
            let e = fold(*e);
            match c {
                Ast::Num(x) if x >= 1.0 => t,
                Ast::Num(0.0) => e,
                c => Ast::If(Box::new(c), Box::new(t), Box::new(e)),
            }
        }
        Ast::Max(a, b) => {
            let a = fold(*a);
            let b = fold(*b);
            match (a, b) {
                (Ast::Num(x), Ast::Num(y)) => Ast::Num(x.max(y)),
                (x, y) => Ast::Max(Box::new(x), Box::new(y)),
            }
        }
        Ast::Min(a, b) => {
            let a = fold(*a);
            let b = fold(*b);
            match (a, b) {
                (Ast::Num(x), Ast::Num(y)) => Ast::Num(x.min(y)),
                (x, y) => Ast::Min(Box::new(x), Box::new(y)),
            }
        }
        Ast::Call { name, args } => {
            // Treat as impure: only recurse into args; no folding at node level.
            let args = args.into_iter().map(fold).collect();
            Ast::Call { name, args }
        }
    }
}

fn cmp_fold<F, R>(a: Ast, b: Ast, eval: F, rebuild: R) -> Ast
where
    F: Fn(f64, f64) -> f64,
    R: Fn(Ast, Ast) -> Ast,
{
    let a = fold(a);
    let b = fold(b);
    match (a, b) {
        (Ast::Num(x), Ast::Num(y)) => Ast::Num(eval(x, y)),
        (x, y) => rebuild(x, y),
    }
}

fn fold_add(a: Ast, b: Ast) -> Ast {
    let a = fold(a);
    let b = fold(b);
    match (a, b) {
        (Ast::Num(x), Ast::Num(y)) => Ast::Num(x + y),
        (x, Ast::Num(0.0)) => x,
        (Ast::Num(0.0), y) => y,
        (x, y) => Ast::Add(Box::new(x), Box::new(y)),
    }
}

fn fold_mul(a: Ast, b: Ast) -> Ast {
    let a = fold(a);
    let b = fold(b);
    match (a, b) {
        (Ast::Num(x), Ast::Num(y)) => Ast::Num(x * y),
        (x, Ast::Num(1.0)) => x,
        (Ast::Num(1.0), y) => y,
        (x, y) => Ast::Mul(Box::new(x), Box::new(y)),
    }
}
