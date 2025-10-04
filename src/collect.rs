use std::collections::HashSet;
use crate::ast::Ast;

pub(crate) fn collect_vars(ast: &Ast) -> Vec<String> {
    fn walk(node: &Ast, seen: &mut HashSet<String>, out: &mut Vec<String>) {
        match node {
            Ast::Num(_) => {}
            Ast::Var(name) => {
                if !seen.contains(name) {
                    seen.insert(name.clone());
                    out.push(name.clone());
                }
            }
            Ast::Neg(a) => walk(a, seen, out),
            Ast::Add(a, b)
            | Ast::Sub(a, b)
            | Ast::Mul(a, b)
            | Ast::Div(a, b)
            | Ast::Eq(a, b)
            | Ast::Ne(a, b)
            | Ast::Lt(a, b)
            | Ast::Le(a, b)
            | Ast::Gt(a, b)
            | Ast::Ge(a, b)
            | Ast::And(a, b)
            | Ast::Or(a, b)
            | Ast::Min(a, b)
            | Ast::Max(a, b) => {
                walk(a, seen, out);
                walk(b, seen, out);
            }
            Ast::If(c, t, e) => {
                walk(c, seen, out);
                walk(t, seen, out);
                walk(e, seen, out);
            }
            Ast::Call { args, .. } => {
                for a in args { walk(a, seen, out); }
            }
        }
    }
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    walk(ast, &mut seen, &mut out);
    out
}
