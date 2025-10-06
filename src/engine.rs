use crate::collect::collect_vars;
use crate::codegen::{codegen_expr, VarLoadMode};
use crate::error::JitError;
use crate::parser::Parser;
use crate::resolver::{IdentityResolver, VarResolver};
use crate::rt_types::{Fn0, Fn1, Fn2, Fn3, JitFn, JitFnRef, RegisteredFn};
use crate::ast::Ast;
use cranelift::prelude::*;
use cranelift::codegen::settings;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use cranelift_native as native;
use std::collections::HashMap;
use std::sync::{atomic::{AtomicUsize, Ordering}, Arc};
use uuid::Uuid;
#[cfg(feature= "optimize")]
use crate::optimizer::optimize;

#[derive(Clone)]
pub(crate) struct VarCache {
    values: Vec<Option<Value>>, // idx → 이미 로드된 SSA Value
}
impl VarCache {
    pub fn new(n: usize) -> Self { Self { values: vec![None; n] } }
    pub fn get(&self, i: usize) -> Option<Value> { self.values[i] }
    pub fn set(&mut self, i: usize, v: Value) { self.values[i] = Some(v); }
}


pub struct Tabula<K = String, R = IdentityResolver> {
    pub(crate) resolver: R,
    pub(crate) _phantom: std::marker::PhantomData<K>,
    pub(crate) funcs: HashMap<(String, u8), RegisteredFn>,
    pub(crate) module: Option<JITModule>,
    pub(crate) generation: Arc<AtomicUsize>,
}

impl Tabula<String, IdentityResolver> {
    pub fn new() -> Self {
        Self {
            resolver: IdentityResolver,
            _phantom: std::marker::PhantomData,
            funcs: HashMap::new(),
            module: None,
            generation: Arc::new(AtomicUsize::new(0)),
        }
    }
}

impl<K, R> Tabula<K, R>
where
    K: Clone + Eq + std::hash::Hash + Send + Sync + 'static,
    R: VarResolver<K>,
{
    /// Create an Engine with a custom variable key resolver.
    pub fn with_resolver(resolver: R) -> Self {
        Self {
            resolver,
            _phantom: std::marker::PhantomData,
            funcs: HashMap::new(),
            module: None,
            generation: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn register_nullary(&mut self, name: &str, f: Fn0) -> Result<(), JitError> {
        if self.module.is_some() { return Err(JitError::Internal("cannot register functions after JIT module is created; create a new Engine".into())); }
        let key = (name.to_string(), 0);
        if self.funcs.contains_key(&key) { return Err(JitError::FunctionExists { name: name.to_string(), arity: 0 }); }
        self.funcs.insert(key, RegisteredFn::Nullary(f));
        Ok(())
    }
    pub fn register_unary(&mut self, name: &str, f: Fn1) -> Result<(), JitError> {
        if self.module.is_some() { return Err(JitError::Internal("cannot register functions after JIT module is created; create a new Engine".into())); }
        let key = (name.to_string(), 1);
        if self.funcs.contains_key(&key) { return Err(JitError::FunctionExists { name: name.to_string(), arity: 1 }); }
        self.funcs.insert(key, RegisteredFn::Unary(f));
        Ok(())
    }
    pub fn register_binary(&mut self, name: &str, f: Fn2) -> Result<(), JitError> {
        if self.module.is_some() { return Err(JitError::Internal("cannot register functions after JIT module is created; create a new Engine".into())); }
        let key = (name.to_string(), 2);
        if self.funcs.contains_key(&key) { return Err(JitError::FunctionExists { name: name.to_string(), arity: 2 }); }
        self.funcs.insert(key, RegisteredFn::Binary(f));
        Ok(())
    }
    pub fn register_ternary(&mut self, name: &str, f: Fn3) -> Result<(), JitError> {
        if self.module.is_some() { return Err(JitError::Internal("cannot register functions after JIT module is created; create a new Engine".into())); }
        let key = (name.to_string(), 3);
        if self.funcs.contains_key(&key) { return Err(JitError::FunctionExists { name: name.to_string(), arity: 3 }); }
        self.funcs.insert(key, RegisteredFn::Ternary(f));
        Ok(())
    }

    // --- Common helpers shared by compile and compile_ref ---
    fn parse_and_resolve(&self, expr: &str) -> Result<(Ast, Vec<K>, HashMap<String, usize>), JitError> {
        // Parse to AST
        let parser = Parser::new(expr)?;
        let ast = parser.parse()?;
        #[cfg(feature = "optimize")]
        let ast = optimize(ast);

        // Infer variables and resolve to key type K using the resolver
        let raw_vars = collect_vars(&ast);
        let mut ordered_vars: Vec<K> = Vec::new();
        let mut k_to_index: HashMap<K, usize> = HashMap::new();
        let mut var_index: HashMap<String, usize> = HashMap::new();
        for name in raw_vars.iter() {
            let k = match self.resolver.resolve(name) {
                Ok(v) => v,
                Err(_) => { return Err(JitError::UnknownIdent(name.clone())); }
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
        Ok((ast, ordered_vars, var_index))
    }

    fn ensure_module_and_register(&mut self) -> Result<(), JitError> {
        if self.module.is_none() {
            // Build ISA with opt_level = speed
            let mut flag_builder = settings::builder();
            flag_builder
                .set("opt_level", "speed")
                .map_err(|e| JitError::Internal(format!("settings error: {}", e)))?;
            let isa_builder = native::builder().map_err(|e| JitError::Internal(e.to_string()))?;
            let isa = isa_builder
                .finish(settings::Flags::new(flag_builder))
                .map_err(|e| JitError::Internal(e.to_string()))?;

            let mut jb = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
            // Register all known functions as symbols once
            for ((name, arity), func) in &self.funcs {
                let sym = format!("{}#{}", name, arity);
                let addr: *const u8 = match func {
                    RegisteredFn::Nullary(f) => *f as *const u8,
                    RegisteredFn::Unary(f) => *f as *const u8,
                    RegisteredFn::Binary(f) => *f as *const u8,
                    RegisteredFn::Ternary(f) => *f as *const u8,
                };
                jb.symbol(sym.as_str(), addr);
            }
            self.module = Some(JITModule::new(jb));
        }
        Ok(())
    }


    fn build_and_finalize(
        &mut self,
        var_index: &HashMap<String, usize>,
        ast: &Ast,
        ordered_len: usize,
        load_mode: LoadMode,
    ) -> Result<*const u8, JitError> {
        self.ensure_module_and_register()?;
        let module = self.module.as_mut().unwrap();

        // Common signature: one pointer param, one f64 return
        let mut sig = module.make_signature();
        let ptr_ty = module.target_config().pointer_type();
        sig.params.push(AbiParam::new(ptr_ty));
        sig.returns.push(AbiParam::new(types::F64));
        let func_name = format!("expr_{}", Uuid::new_v4());
        let func_id = module
            .declare_function(&func_name, Linkage::Local, &sig)
            .map_err(|e| JitError::Internal(e.to_string()))?;

        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut fb_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.seal_block(block);

            let vars_ptr = builder.block_params(block)[0];

            // Lazy variable loads: build values on-demand in codegen_expr
            let mut mf = MemFlags::new();
            mf.set_readonly();
            mf.set_aligned();
            let mut cache = VarCache::new(ordered_len);
            let load_mode2 = match load_mode { LoadMode::DirectF64 => VarLoadMode::DirectF64, LoadMode::IndirectPtr => VarLoadMode::IndirectPtr };
            let val = codegen_expr(
                module,
                &self.funcs,
                &mut builder,
                var_index,
                vars_ptr,
                ptr_ty,
                mf,
                &mut cache,
                ast,
                types::F64,
                load_mode2,
            )?;
            builder.ins().return_(&[val]);
            builder.finalize();
        }

        module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::Internal(e.to_string()))?;
        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::Internal(e.to_string()))?;

        let code = module.get_finalized_function(func_id);
        Ok(code)
    }

    pub fn compile(&mut self, expr: &str) -> Result<CompiledExpr<K>, JitError> {
        let (ast, ordered_vars, var_index) = self.parse_and_resolve(expr)?;
        let code = self.build_and_finalize(&var_index, &ast, ordered_vars.len(), LoadMode::DirectF64)?;
        let func_ptr: JitFn = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExpr::<K> { func_ptr, ordered_vars, gen_token: self.generation.clone(), gen_at_compile: gen_at })
    }

    pub fn compile_ref(&mut self, expr: &str) -> Result<CompiledExprRef<K>, JitError> {
        let (ast, ordered_vars, var_index) = self.parse_and_resolve(expr)?;
        let code = self.build_and_finalize(&var_index, &ast, ordered_vars.len(), LoadMode::IndirectPtr)?;
        let func_ptr: JitFnRef = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExprRef::<K> { func_ptr, ordered_vars, gen_token: self.generation.clone(), gen_at_compile: gen_at })
    }

    /// Free all JIT-allocated memory for compiled expressions and reset the JIT module.
    /// After calling this, previously compiled CompiledExpr pointers become invalid and must not be used.
    /// You can register functions again and recompile expressions.
    pub fn free_memory(&mut self) {
        if let Some(module) = self.module.take() {
            unsafe { module.free_memory(); }
        }
        // bump generation to invalidate previously compiled expressions
        self.generation.fetch_add(1, Ordering::Relaxed);
    }

    /// Clear the custom function registry. Call `free_memory` first if a module exists.
    /// This allows re-registering a different function set before recompiling expressions.
    pub fn clear_registered_functions(&mut self) {
        self.funcs.clear();
    }
}

pub struct CompiledExpr<K = String> {
    pub(crate) func_ptr: JitFn,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
}

impl <K> CompiledExpr<K> {
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

    pub fn eval(&self, values: &[f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(values.as_ptr() as *const f64) };
        Ok(out)
    }

}

impl <K> GenToken for CompiledExpr<K> {
    fn gen_token(&self) -> usize {
        self.gen_token.load(Ordering::Relaxed)
    }

    fn gen_at_compile(&self) -> usize {
        self.gen_at_compile
    }
}

#[derive(Clone)]
pub struct CompiledExprRef<K = String> {
    pub(crate) func_ptr: JitFnRef,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
}

impl<K> CompiledExprRef<K> {
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

    pub fn eval(&self, values: &[&f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(values.as_ptr() as *const *const f64) };
        Ok(out)
    }

    /// Evaluates this compiled expression using raw pointers to `f64` inputs.
    ///
    /// This API is intended for integration scenarios (e.g., ECS or FFI) where caching Rust
    /// references across boundaries is inconvenient or impossible. You can keep
    /// stable addresses to your values (for example, by storing them in `Box<f64>` or an
    /// arena) and pass those addresses here as `*const f64`.
    ///
    /// Compared to [`eval`](#method.eval), this avoids holding `&f64` references; the JIT
    /// only reads from the pointed-to values and never writes to them.
    ///
    /// Length requirements:
    /// - `ptrs.len()` must be at least `self.vars().len()`. Extra pointers (if any) are ignored.
    ///
    /// Errors:
    /// - [`JitError::ValuesLen`] if not enough pointers are provided.
    /// - [`JitError::Invalidated`] if the underlying JIT memory was freed via [`Tabula::free_memory`].
    ///
    /// Safety:
    /// - WARNING: This method accepts raw pointers and therefore bypasses Rust's lifetime/borrow
    ///   checking. The compiler cannot verify correctness here; misuse can cause undefined behavior,
    ///   including crashes or memory corruption. Treat pointer construction as an unsafe boundary.
    /// - Each pointer in `ptrs` must be non-null, properly aligned, and point to a valid `f64`.
    /// - The pointed-to memory must remain alive and unmoved for the entire duration of this call.
    ///   In practice, prefer storing values in `Box<f64>`, `Box<[f64]>`, or another allocation with a
    ///   stable address, and update them in place instead of replacing the allocation.
    /// - Do not call this method after the engine has invalidated compiled code (see [`Tabula::free_memory`]).
    ///
    /// Pointer safety checklist
    /// - Prefer not to cache pointers long-term; build them right before calling `eval_ptrs`.
    /// - If you must cache, ensure addresses are stable (e.g., store values in `Box<f64>` and update in place).
    /// - Avoid storing addresses in integer types; keep them as `*const f64` (or `NonNull<f64>` in your code) to make intent clear.
    /// - If using a `Vec<f64>`, avoid reallocation while pointers are in use (e.g., reserve upfront); or use `Box<[f64]>` for a fixed-size set.
    ///
    /// Example (simple)
    /// ----------------
    /// ```
    /// use tabulon::{Tabula, JitError};
    /// # fn main() -> Result<(), JitError> {
    /// let mut engine = Tabula::new();
    /// let compiled = engine.compile_ref("a + b * 2")?;
    /// let a = 3.0;
    /// let b = 4.5;
    /// let ptrs: [*const f64; 2] = [&a as *const f64, &b as *const f64];
    /// let out = compiled.eval_ptrs(&ptrs)?;
    /// assert!((out - (3.0 + 4.5 * 2.0)).abs() < 1e-12);
    /// # Ok(()) }
    /// ```
    ///
    /// Example (practical: reuse a stable array and rebuild pointers per call)
    /// ----------------------------------------------------------------------
    /// This pattern avoids caching pointers by keeping values in a fixed-size `Box<[f64]>` and
    /// rebuilding a `Vec<*const f64>` right before each evaluation. The order matches
    /// `compiled.vars()`.
    /// ```
    /// use tabulon::{Tabula, JitError};
    /// # fn main() -> Result<(), JitError> {
    /// let mut engine = Tabula::new();
    /// let compiled = engine.compile_ref("a + b * 2")?;
    /// let mut values: Box<[f64]> = vec![3.0, 4.5].into_boxed_slice();
    /// // Build pointers just-in-time for the call
    /// let ptrs: Vec<*const f64> = (0..compiled.vars().len())
    ///     .map(|i| &values[i] as *const f64)
    ///     .collect();
    /// let out1 = compiled.eval_ptrs(&ptrs)?;
    /// assert!((out1 - (3.0 + 4.5 * 2.0)).abs() < 1e-12);
    /// // Update values in place and evaluate again
    /// values[0] = 5.0; // a
    /// values[1] = 10.0; // b
    /// let ptrs2: Vec<*const f64> = (0..compiled.vars().len())
    ///     .map(|i| &values[i] as *const f64)
    ///     .collect();
    /// let out2 = compiled.eval_ptrs(&ptrs2)?;
    /// assert!((out2 - (5.0 + 10.0 * 2.0)).abs() < 1e-12);
    /// # Ok(()) }
    /// ```
    ///
    /// See also: [`eval`](#method.eval), [`vars`](#method.vars).
    pub fn eval_ptrs(&self, ptrs: &[*const f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(ptrs, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(ptrs.as_ptr() as *const *const f64) };
        Ok(out)
    }
}

impl <K> GenToken for CompiledExprRef<K>{
    fn gen_token(&self) -> usize {
        self.gen_token.load(Ordering::Relaxed)
    }

    fn gen_at_compile(&self) -> usize {
        self.gen_at_compile
    }
}

trait GenToken {
    fn gen_token(&self) -> usize;
    fn gen_at_compile(&self) -> usize;
}

impl <G> CheckGen for G
where G: GenToken {
    fn check_gen<T>(&self, arr: &[T], needed: usize) -> Result<(), JitError> {
        if arr.len() < needed {
            return Err(JitError::ValuesLen { expected: needed, got: arr.len() });
        }
        if self.gen_token() != self.gen_at_compile() {
            return Err(JitError::Invalidated);
        }

        Ok(())
    }

}

trait CheckGen {
    fn check_gen<T>(&self, arr: &[T], needed: usize) -> Result<(), JitError>;
}



#[derive(Copy, Clone)]
enum LoadMode { DirectF64, IndirectPtr }
