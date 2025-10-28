use tabulon::{Tabula, JitError, VarAccessStrategy, Parser, VarResolver, VarResolveError};
use tabulon::rt_types::UnifiedContext;
use tabulon::trait_resolver::Resolver;

// Helper to adapt a closure to VarResolver<K>
struct FnResolver<F>(F);
impl<F, K> VarResolver<K> for FnResolver<F>
    where
        F: Fn(&str) -> Result<K, VarResolveError>,
{
    fn resolve(&self, ident: &str) -> Result<K, VarResolveError> { (self.0)(ident) }
}

#[derive(Default)]
struct MyContext {
    offset: f64,
}

struct MyResolver {
    values: Vec<f64>,
}

impl Resolver for MyResolver {
    fn resolve(&mut self, index: u32) -> f64 {
        *self.values.get(index as usize).unwrap_or(&f64::NAN)
    }
}

extern "C" fn add_offset_fn(ctx: *mut std::ffi::c_void, val: f64) -> f64 {
    let uctx = unsafe { &mut *(ctx as *mut UnifiedContext<MyContext>) };
    let my_ctx = &mut *uctx.user_ctx;
    val + my_ctx.offset
}

#[test]
fn test_eval_with_resolver_and_ctx() -> Result<(), JitError> {
    let mut engine = Tabula::<MyContext>::new_ctx();

    // Register the context-aware function
    engine.register_unary("add_offset", add_offset_fn, true)?;

    // Enable the trait resolver
    // This will set the var_getter to RESOLVER_TRAMPOLINE_SYMBOL
    // But we need RESOLVER_AND_CTX_TRAMPOLINE_SYMBOL for unified context
    // So we need to set it manually or create a new enable_unified_trait_resolver
    // For now, let's manually set it in compile_prepared_with
    // engine.enable_trait_resolver()?;

    // Compile an expression that uses a variable and the context-aware function
    let expr_str = "x + add_offset(y)";
    let resolver_fn = |ident: &str| -> Result<u32, VarResolveError> {
        match ident {
            "x" => Ok(0),
            "y" => Ok(1),
            _ => Err(VarResolveError::Unknown(ident.to_string())),
        }
    };
    let resolver = FnResolver(resolver_fn);
    let parser = Parser::new(expr_str)?;
    let prepared = parser.parse_with_var_resolver(&resolver)?;

    let expr = engine.compile_prepared_with(
        &prepared,
        VarAccessStrategy::ResolverAndCtxCall { symbol: tabulon::trait_resolver::RESOLVER_AND_CTX_TRAMPOLINE_SYMBOL }
    )?;

    let mut my_ctx = MyContext { offset: 5.0 };
    let mut my_resolver = MyResolver { values: vec![10.0, 20.0] };

    let result = expr.eval_with_resolver_and_ctx(&mut my_resolver, &mut my_ctx)?;

    // Expected: x (10.0) + add_offset(y (20.0) + offset (5.0)) = 10.0 + 25.0 = 35.0
    assert_eq!(result, 35.0);

    Ok(())
}