use std::collections::HashMap;
use tabulon::{Tabula, VarAccessStrategy, VarResolveError, Parser, VarResolver, Resolver, RESOLVER_TRAMPOLINE_SYMBOL, resolve_var_tramp};

// Trait-based resolvers
struct DataSourceA { vars: HashMap<u32, f64> }
impl Resolver for DataSourceA {
    fn resolve(&mut self, index: u32) -> f64 {
        self.vars.get(&index).copied().unwrap_or(0.0) * 10.0
    }
}

struct DataSourceB { vars: Vec<f64> }
impl Resolver for DataSourceB {
    fn resolve(&mut self, index: u32) -> f64 {
        self.vars.get(index as usize).copied().unwrap_or(0.0) + 1.0
    }
}

// Helper to adapt a closure to VarResolver<K>
struct FnResolver<F>(F);
impl<F, K> VarResolver<K> for FnResolver<F>
where
    F: Fn(&str) -> Result<K, VarResolveError>,
{
    fn resolve(&self, ident: &str) -> Result<K, VarResolveError> { (self.0)(ident) }
}

#[test]
fn trait_resolver_dynamic_switch() {
    let mut eng = Tabula::<()>::new_ctx();
    // Register the built-in trampoline symbol once
    eng.set_var_getter(RESOLVER_TRAMPOLINE_SYMBOL, resolve_var_tramp).unwrap();

    // Prepare expression with a name->index resolver
    let expr_str = "A + B";
    let resolver_fn = |ident: &str| -> Result<u32, VarResolveError> {
        match ident { "A" => Ok(0), "B" => Ok(1), _ => Err(VarResolveError::Unknown(ident.to_string())), }
    };
    let resolver = FnResolver(resolver_fn);
    let parser = Parser::new(expr_str).unwrap();
    let prepared = parser.parse_with_var_resolver(&resolver).unwrap();
    let expr = eng.compile_prepared_with(&prepared, VarAccessStrategy::ResolverCall { symbol: RESOLVER_TRAMPOLINE_SYMBOL }).unwrap();

    // First evaluation with DataSourceA
    let mut source_a = DataSourceA { vars: HashMap::new() };
    source_a.vars.insert(0, 5.0); // A=5
    source_a.vars.insert(1, 10.0); // B=10
    let out_a = expr.eval_with_resolver(&mut source_a).unwrap();
    assert_eq!(out_a, 150.0); // (5*10)+(10*10)

    // Second evaluation with DataSourceB
    let mut source_b = DataSourceB { vars: vec![5.0, 10.0] };
    let out_b = expr.eval_with_resolver(&mut source_b).unwrap();
    assert_eq!(out_b, 17.0); // (5+1)+(10+1)

    // Update source_a and re-evaluate
    source_a.vars.insert(0, 6.0);
    let out_a2 = expr.eval_with_resolver(&mut source_a).unwrap();
    assert_eq!(out_a2, 160.0);
}
