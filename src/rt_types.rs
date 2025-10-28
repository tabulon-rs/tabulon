use crate::trait_resolver::Resolver;

pub type CtxPtr = *mut std::ffi::c_void;

/// A unified context struct that can hold both a variable resolver and a user-defined context.
/// This is used when an expression needs to resolve variables via a Resolver trait and also
/// call registered functions that require a user context.
#[repr(C)]
pub struct UnifiedContext<'a, Ctx> {
    pub resolver: &'a mut dyn Resolver,
    pub user_ctx: &'a mut Ctx,
}

pub type JitFn = unsafe extern "C" fn(*const f64, CtxPtr) -> f64;
pub type JitFnRef = unsafe extern "C" fn(*const *const f64, CtxPtr) -> f64;

pub type Fn0 = extern "C" fn(CtxPtr) -> f64;
pub type Fn1 = extern "C" fn(CtxPtr, f64) -> f64;
pub type Fn2 = extern "C" fn(CtxPtr, f64, f64) -> f64;
pub type Fn3 = extern "C" fn(CtxPtr, f64, f64, f64) -> f64;

#[derive(Clone, Copy)]
pub enum RegisteredFn {
    Nullary { f: Fn0, uses_ctx: bool },
    Unary { f: Fn1, uses_ctx: bool },
    Binary { f: Fn2, uses_ctx: bool },
    Ternary { f: Fn3, uses_ctx: bool },
}

impl RegisteredFn {
    pub fn uses_ctx(&self) -> bool {
        match self {
            RegisteredFn::Nullary { uses_ctx, .. } => *uses_ctx,
            RegisteredFn::Unary { uses_ctx, .. } => *uses_ctx,
            RegisteredFn::Binary { uses_ctx, .. } => *uses_ctx,
            RegisteredFn::Ternary { uses_ctx, .. } => *uses_ctx,
        }
    }
}
