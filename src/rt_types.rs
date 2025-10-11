pub type CtxPtr = *mut std::ffi::c_void;

pub type JitFn = unsafe extern "C" fn(*const f64, CtxPtr) -> f64;
pub type JitFnRef = unsafe extern "C" fn(*const *const f64, CtxPtr) -> f64;

pub type Fn0 = extern "C" fn(CtxPtr) -> f64;
pub type Fn1 = extern "C" fn(CtxPtr, f64) -> f64;
pub type Fn2 = extern "C" fn(CtxPtr, f64, f64) -> f64;
pub type Fn3 = extern "C" fn(CtxPtr, f64, f64, f64) -> f64;

#[derive(Clone, Copy)]
pub enum RegisteredFn {
    Nullary(Fn0),
    Unary(Fn1),
    Binary(Fn2),
    Ternary(Fn3),
}
