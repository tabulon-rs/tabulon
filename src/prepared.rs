use crate::analysis::Analysis;
use crate::ast::Ast;
use crate::collect::collect_vars;
use crate::error::JitError;
use crate::optimizer::optimize;
use crate::resolver::VarResolver;
use std::collections::HashMap;
use std::hash::Hash;

fn compute_ast_flags(ast: &Ast) -> (bool, bool, bool, bool) {
    // Returns (needs_bool_consts, has_if_like, has_logical_ops, has_comparisons)
    use crate::ast::Ast::*;
    match ast {
        Num(_) | Var(_) => (false, false, false, false),
        Neg(x) => compute_ast_flags(x),
        Not(x) => {
            let (_, i, _, c) = compute_ast_flags(x);
            (true, i, true, c)
        }
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) | Pow(a, b) | Max(a, b) | Min(a, b) => {
            let (n1, i1, l1, c1) = compute_ast_flags(a);
            let (n2, i2, l2, c2) = compute_ast_flags(b);
            (n1 || n2, i1 || i2, l1 || l2, c1 || c2)
        }
        Eq(a, b) | Ne(a, b) | Lt(a, b) | Le(a, b) | Gt(a, b) | Ge(a, b) => {
            let (_, i1, l1, _) = compute_ast_flags(a);
            let (_, i2, l2, _) = compute_ast_flags(b);
            (true, i1 || i2, l1 || l2, true)
        }
        And(a, b) | Or(a, b) => {
            let (_, i1, _, c1) = compute_ast_flags(a);
            let (_, i2, _, c2) = compute_ast_flags(b);
            (true, i1 || i2, true, c1 || c2)
        }
        If(cnd, t, e) => {
            let (_, _, l1, c1) = compute_ast_flags(cnd);
            let (_, _, l2, c2) = compute_ast_flags(t);
            let (_, _, l3, c3) = compute_ast_flags(e);
            (true, true, l1 || l2 || l3, c1 || c2 || c3)
        }
        Ifs(list) => {
            let mut n = true; // Ifs implies boolean context for conditions
            let mut i = true; // has_if_like
            let mut l = false;
            let mut c = false;
            for sub in list {
                let (sn, si, sl, sc) = compute_ast_flags(sub);
                n = n || sn;
                i = i || si;
                l = l || sl;
                c = c || sc;
            }
            (n, i, l, c)
        }
        Call { args, .. } => {
            // Calls themselves don't create boolean needs; aggregate from args
            let mut n = false;
            let mut i = false;
            let mut l = false;
            let mut c = false;
            for a in args {
                let (an, ai, al, ac) = compute_ast_flags(a);
                n = n || an;
                i = i || ai;
                l = l || al;
                c = c || ac;
            }
            (n, i, l, c)
        }
    }
}

/// An immutable, front-end preparation output that bundles the parsed AST
/// with variable ordering and indexing metadata.
#[derive(Clone, Debug)]
pub struct PreparedExpr<K> {
    pub ast: Box<Ast>, // optimized AST pinned on heap for stable analysis keys
    /// Variables in left-to-right first-appearance order. The identifiers are
    /// resolved to a user-provided key type `K` via a VarResolver.
    pub ordered_vars: Vec<K>,
    /// Map from source variable name to its index into `ordered_vars`.
    /// Used by codegen to load variable values by position.
    pub var_index: HashMap<String, usize>,
    /// Cached analysis flags derived purely from the AST.
    /// Whether codegen may need boolean constants (1.0/0.0) available.
    pub needs_bool_consts: bool,
    /// Whether the AST contains any if/ifs constructs.
    pub has_if_like: bool,
    /// Whether the AST contains logical operators (not/and/or).
    pub has_logical_ops: bool,
    /// Whether the AST contains comparison operators.
    pub has_comparisons: bool,
    /// Optional front-end analysis for codegen; reused by resolver path.
    pub analysis: Option<Analysis>,
}

impl<K> PreparedExpr<K>
where
    K: Eq + Hash + Clone,
{
    /// Build a PreparedExpr from an AST and a VarResolver, resolving variable names to keys `K`.
    pub(crate) fn from_ast_with_resolver<R>(
        ast: Ast,
        resolver: &R,
    ) -> Result<PreparedExpr<K>, JitError>
    where
        R: VarResolver<K>,
    {
        let raw_vars = collect_vars(&ast);
        let mut ordered_vars: Vec<K> = Vec::new();
        let mut k_to_index: HashMap<K, usize> = HashMap::new();
        let mut var_index: HashMap<String, usize> = HashMap::new();

        for name in raw_vars.iter() {
            let k = match resolver.resolve(name) {
                Ok(v) => v,
                Err(_) => return Err(JitError::UnknownIdent(name.clone())),
            };
            if let Some(&idx) = k_to_index.get(&k) {
                var_index.insert(name.clone(), idx);
            } else {
                let idx = ordered_vars.len();
                k_to_index.insert(k.clone(), idx);
                ordered_vars.push(k);
                var_index.insert(name.clone(), idx);
            }
        }

        // Optimize once and compute flags/analysis on the optimized AST
        let opt_ast = optimize(ast);
        // Pin the optimized AST on heap so node pointer keys remain stable across moves
        let boxed_ast = Box::new(opt_ast);
        let (needs_bool_consts, has_if_like, has_logical_ops, has_comparisons) =
            compute_ast_flags(&boxed_ast);
        let analysis = Analysis::compute(&boxed_ast, &var_index);

        Ok(PreparedExpr {
            ast: boxed_ast,
            ordered_vars,
            var_index,
            needs_bool_consts,
            has_if_like,
            has_logical_ops,
            has_comparisons,
            analysis: Some(analysis),
        })
    }
}
