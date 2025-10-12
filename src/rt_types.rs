pub type CtxPtr = *mut std::ffi::c_void;

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
