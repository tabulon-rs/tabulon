use crate::ast::Ast;
use crate::collect::collect_vars;
use crate::error::JitError;
use crate::resolver::VarResolver;
use std::collections::HashMap;
use std::hash::Hash;

/// An immutable, front-end preparation output that bundles the parsed AST
/// with variable ordering and indexing metadata.
#[derive(Clone, Debug)]
pub struct PreparedExpr<K> {
    pub ast: Ast,
    /// Variables in left-to-right first-appearance order. The identifiers are
    /// resolved to a user-provided key type `K` via a VarResolver.
    pub ordered_vars: Vec<K>,
    /// Map from source variable name to its index into `ordered_vars`.
    /// Used by codegen to load variable values by position.
    pub var_index: HashMap<String, usize>,
}

impl<K> PreparedExpr<K>
where
    K: Eq + Hash + Clone,
{
    /// Build a PreparedExpr from an AST and a VarResolver, resolving variable names to keys `K`.
    pub(crate) fn from_ast_with_resolver<R>(ast: Ast, resolver: &R) -> Result<PreparedExpr<K>, JitError>
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

        Ok(PreparedExpr { ast, ordered_vars, var_index })
    }
}
