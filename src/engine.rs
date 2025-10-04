use crate::collect::collect_vars;
use crate::codegen::codegen_expr;
use crate::error::JitError;
use crate::parser::Parser;
use crate::resolver::{IdentityResolver, VarResolver};
use crate::rt_types::{Fn0, Fn1, Fn2, Fn3, JitFn, RegisteredFn};
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

    pub fn compile(&mut self, expr: &str) -> Result<CompiledExpr<K>, JitError> {
        // Parse
        let parser = Parser::new(expr)?;
        let ast = parser.parse()?;

        #[cfg(feature= "optimize")]
        let ast = optimize(ast);

        // Infer variables (names) and resolve to key type K using the resolver.
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

        // Lazily create and then reuse a single JITModule per Engine
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
        let module = self.module.as_mut().unwrap();

        // Signature: fn(*const *const f64) -> f64
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
            let ptr_bytes: i32 = if ptr_ty == types::I64 { 8 } else { 4 };

            // Preload variable values once (two-step load: pointer -> f64)
            let mf = MemFlags::new();
            let mut var_vals: Vec<Value> = Vec::with_capacity(ordered_vars.len());
            for idx in 0..ordered_vars.len() {
                let offset = (idx as i32) * ptr_bytes;
                let ptr_to_val = builder.ins().load(ptr_ty, mf, vars_ptr, offset);
                let val = builder.ins().load(types::F64, mf, ptr_to_val, 0);
                var_vals.push(val);
            }

            let val = codegen_expr(module, &self.funcs, &mut builder, &var_index, &var_vals, &ast, types::F64)?;
            builder.ins().return_(&[val]);
            builder.finalize();
        }

        module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::Internal(e.to_string()))?;
        module.clear_context(&mut ctx);
        module.finalize_definitions().map_err(|e| JitError::Internal(e.to_string()))?;

        let code = module.get_finalized_function(func_id);
        let func_ptr: JitFn = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExpr::<K> { func_ptr, ordered_vars, gen_token: self.generation.clone(), gen_at_compile: gen_at })
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

#[derive(Clone)]
pub struct CompiledExpr<K = String> {
    pub(crate) func_ptr: JitFn,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
}

impl<K> CompiledExpr<K> {
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

    pub fn eval(&self, values: &[&f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        if values.len() < needed {
            return Err(JitError::ValuesLen { expected: needed, got: values.len() });
        }
        // Invalidation guard: prevent use-after-free on JIT memory
        if self.gen_token.load(Ordering::Relaxed) != self.gen_at_compile {
            return Err(JitError::Invalidated);
        }
        let f = self.func_ptr;
        let out = unsafe { f(values.as_ptr() as *const *const f64) };
        Ok(out)
    }
}
