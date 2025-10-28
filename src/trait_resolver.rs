use core::ffi::c_void;
use crate::rt_types::UnifiedContext;

/// Public trait for runtime variable resolution by index.
///
/// Implement this trait to provide values for variables on-demand at evaluation time.
/// The JIT will only call the resolver for variables that are actually used along
/// the executed path (short-circuit branches will not resolve their unused side).
pub trait Resolver {
    fn resolve(&mut self, index: u32) -> f64;
}

/// Opaque context passed to the trampoline, wrapping a trait object.
#[repr(C)]
pub struct ResolverCtx<'a> {
    pub resolver: &'a mut dyn Resolver,
}

/// Name of the resolver trampoline symbol exported by this library.
pub const RESOLVER_TRAMPOLINE_SYMBOL: &str = "resolve_var_tramp";

/// Name of the unified resolver and context trampoline symbol exported by this library.
pub const RESOLVER_AND_CTX_TRAMPOLINE_SYMBOL: &str = "resolve_var_tramp_unified";

/// Trampoline function that the JIT calls to resolve a variable by index.
///
/// Signature must match engine::GetVarFn and the Cranelift-declared (ctx, i32/u32) calling convention.
pub extern "C" fn resolve_var_tramp(ctx: *mut c_void, index: u32) -> f64 {
    if ctx.is_null() {
        return f64::NAN;
    }
    // SAFETY: The engine constructs this context just for the duration of the call.
    let rctx = unsafe { &mut *(ctx as *mut ResolverCtx) };
    rctx.resolver.resolve(index)
}

/// Trampoline function that the JIT calls to resolve a variable by index when a UnifiedContext is used.
///
/// Signature must match engine::GetVarFn and the Cranelift-declared (ctx, i32/u32) calling convention.
pub extern "C" fn resolve_var_tramp_unified<Ctx>(ctx: *mut c_void, index: u32) -> f64 {
    if ctx.is_null() {
        return f64::NAN;
    }
    // SAFETY: The engine constructs this context just for the duration of the call.
    let uctx = unsafe { &mut *(ctx as *mut UnifiedContext<Ctx>) };
    uctx.resolver.resolve(index)
}

impl <T: FnMut(u32)->f64>Resolver for T {
    fn resolve(&mut self, index: u32) -> f64 {
        self(index)
    }
}
