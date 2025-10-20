use crate::ast::Ast;
use crate::codegen::{F64Consts, codegen_expr, codegen_expr_with_access, VarAccessIR};
use crate::error::JitError;
use crate::parser::Parser;
use crate::prepared::PreparedExpr;
use crate::resolver::IdentityResolver;
use crate::rt_types::{Fn0, Fn1, Fn2, Fn3, JitFn, JitFnRef, RegisteredFn};
use cranelift::codegen::settings;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use cranelift_native as native;
use log::debug;
use std::collections::HashMap;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use uuid::Uuid;

pub extern "C" fn tabulon_pow_f64(base: f64, exp: f64) -> f64 {
    base.powf(exp)
}

#[allow(unused_variables)]
pub extern "C" fn tabulon_pow_f64_ctx(_ctx: *mut std::ffi::c_void, base: f64, exp: f64) -> f64 {
    tabulon_pow_f64(base, exp)
}

/// External variable getter function type for resolver-based access.
pub type GetVarFn = extern "C" fn(ctx: *mut std::ffi::c_void, index: u32) -> f64;

/// Strategy for how variables are accessed by the compiled code.
#[derive(Debug, Clone, Copy)]
pub enum VarAccessStrategy {
    /// Read variables from a contiguous f64 slice; legacy fast path.
    DirectF64,
    /// Read variables via a slice of pointers/references to f64; legacy ref path.
    IndirectPtr,
    /// Call an external resolver function with (ctx, idx) to obtain each variable lazily.
    ResolverCall { symbol: &'static str },
}

/// The main JIT compilation and evaluation engine.
///
/// `Tabula` is the entry point for parsing, compiling, and evaluating expressions.
/// It holds the JIT compiler context, registered functions, and a variable resolver.
///
/// The type parameters `K` and `R` define the variable key type and the resolver logic,
/// respectively. By default, it uses `String` keys.
///
/// # Examples
///
/// ```
/// use tabulon::Tabula;
///
/// let mut engine = Tabula::new();
/// let expr = engine.compile("a + b").unwrap();
/// let result = expr.eval(&[10.0, 20.0]).unwrap();
/// assert_eq!(result, 30.0);
/// ```
pub struct Tabula<Ctx = ()> {
    pub(crate) _phantom_ctx: std::marker::PhantomData<Ctx>,
    pub(crate) funcs: HashMap<(String, u8), RegisteredFn>,
    pub(crate) module: Option<JITModule>,
    pub(crate) generation: Arc<AtomicUsize>,
    pub(crate) var_getter: Option<(&'static str, GetVarFn)>,
}

impl Default for Tabula<()> {
    fn default() -> Self {
        Self::new()
    }
}

impl Tabula<()> {
    /// Creates a new `Tabula` engine with the default configuration.
    pub fn new() -> Self {
        Self {
            _phantom_ctx: std::marker::PhantomData,
            funcs: HashMap::new(),
            module: None,
            generation: Arc::new(AtomicUsize::new(0)),
            var_getter: None,
        }
    }
}



fn ast_uses_ctx(ast: &Ast, funcs: &HashMap<(String, u8), RegisteredFn>) -> bool {
    use crate::ast::Ast::*;
    match ast {
        Num(_) | Var(_) => false,
        Neg(x) | Not(x) => ast_uses_ctx(x, funcs),
        Add(a, b)
        | Sub(a, b)
        | Mul(a, b)
        | Div(a, b)
        | Pow(a, b)
        | Max(a, b)
        | Min(a, b)
        | Eq(a, b)
        | Ne(a, b)
        | Lt(a, b)
        | Le(a, b)
        | Gt(a, b)
        | Ge(a, b)
        | And(a, b)
        | Or(a, b) => ast_uses_ctx(a, funcs) || ast_uses_ctx(b, funcs),
        If(c, t, e) => ast_uses_ctx(c, funcs) || ast_uses_ctx(t, funcs) || ast_uses_ctx(e, funcs),
        Ifs(list) => list.iter().any(|sub| ast_uses_ctx(sub, funcs)),
        Call { name, args } => {
            let arity = args.len() as u8;
            let this_uses = funcs
                .get(&(name.clone(), arity))
                .map(|rf| match rf {
                    RegisteredFn::Nullary { uses_ctx, .. }
                    | RegisteredFn::Unary { uses_ctx, .. }
                    | RegisteredFn::Binary { uses_ctx, .. }
                    | RegisteredFn::Ternary { uses_ctx, .. } => *uses_ctx,
                })
                .unwrap_or(false);
            this_uses || args.iter().any(|a| ast_uses_ctx(a, funcs))
        }
    }
}

impl<Ctx> Tabula<Ctx> {
    /// Set the variable getter symbol/function for ResolverCall strategy.
    pub fn set_var_getter(&mut self, symbol: &'static str, f: GetVarFn) -> Result<(), JitError> {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot set var getter after JIT module is created; create a new Engine".into(),
            ));
        }
        self.var_getter = Some((symbol, f));
        Ok(())
    }

    /// Sets the variable getter using a #[resolver]-generated marker type tied to this engine's Ctx.
    pub fn set_var_getter_typed<F>(&mut self) -> Result<(), JitError>
    where
        F: crate::registry::ResolverForEngineCtx<Ctx>,
    {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot set var getter after JIT module is created; create a new Engine".into(),
            ));
        }
        let name = F::NAME;
        // SAFETY: addr points to extern "C" shim with correct ABI generated by #[resolver]
        let fptr: GetVarFn = unsafe { std::mem::transmute::<*const u8, GetVarFn>(F::addr()) };
        self.var_getter = Some((name, fptr));
        Ok(())
    }

    /// Registers a nullary (0-argument) function with the engine.
    ///
    /// Functions must be registered before any expressions are compiled.
    pub fn register_nullary(&mut self, name: &str, f: Fn0, uses_ctx: bool) -> Result<(), JitError> {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot register functions after JIT module is created; create a new Engine".into(),
            ));
        }
        let key = (name.to_string(), 0);
        if self.funcs.contains_key(&key) {
            return Err(JitError::FunctionExists {
                name: name.to_string(),
                arity: 0,
            });
        }
        self.funcs.insert(key, RegisteredFn::Nullary { f, uses_ctx });
        Ok(())
    }
    /// Registers a unary (1-argument) function with the engine.
    pub fn register_unary(&mut self, name: &str, f: Fn1, uses_ctx: bool) -> Result<(), JitError> {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot register functions after JIT module is created; create a new Engine".into(),
            ));
        }
        let key = (name.to_string(), 1);
        if self.funcs.contains_key(&key) {
            return Err(JitError::FunctionExists {
                name: name.to_string(),
                arity: 1,
            });
        }
        self.funcs.insert(key, RegisteredFn::Unary { f, uses_ctx });
        Ok(())
    }
    /// Registers a binary (2-argument) function with the engine.
    ///
    /// # Examples
    ///
    /// ```
    /// use tabulon::Tabula;
    ///
    /// extern "C" fn my_pow(_ctx: *mut std::ffi::c_void, base: f64, exp: f64) -> f64 {
    ///     base.powf(exp)
    /// }
    ///
    /// let mut engine = Tabula::new();
    /// // The function must be registered before compiling any expressions.
    /// engine.register_binary("my_pow", my_pow, false).unwrap();
    ///
    /// let expr = engine.compile("my_pow(a, 3)").unwrap();
    /// let result = expr.eval(&[2.0]).unwrap();
    /// assert_eq!(result, 8.0);
    /// ```
    pub fn register_binary(&mut self, name: &str, f: Fn2, uses_ctx: bool) -> Result<(), JitError> {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot register functions after JIT module is created; create a new Engine".into(),
            ));
        }
        let key = (name.to_string(), 2);
        if self.funcs.contains_key(&key) {
            return Err(JitError::FunctionExists {
                name: name.to_string(),
                arity: 2,
            });
        }
        self.funcs.insert(key, RegisteredFn::Binary { f, uses_ctx });
        Ok(())
    }
    /// Registers a ternary (3-argument) function with the engine.
    pub fn register_ternary(&mut self, name: &str, f: Fn3, uses_ctx: bool) -> Result<(), JitError> {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot register functions after JIT module is created; create a new Engine".into(),
            ));
        }
        let key = (name.to_string(), 3);
        if self.funcs.contains_key(&key) {
            return Err(JitError::FunctionExists {
                name: name.to_string(),
                arity: 3,
            });
        }
        self.funcs.insert(key, RegisteredFn::Ternary { f, uses_ctx });
        Ok(())
    }

    /// Registers a function using its #[function]-generated marker type with compile-time
    /// context checking. This method is generic over the engine's Ctx type and only compiles
    /// when the function's context (if any) matches the engine's Ctx.
    pub fn register_typed<F>(&mut self) -> Result<(), JitError>
    where
        F: crate::registry::FunctionForEngineCtx<Ctx>,
    {
        if self.module.is_some() {
            return Err(JitError::Internal(
                "cannot register functions after JIT module is created; create a new Engine".into(),
            ));
        }
        let key = (F::NAME.to_string(), F::ARITY);
        if self.funcs.contains_key(&key) {
            return Err(JitError::FunctionExists {
                name: F::NAME.to_string(),
                arity: F::ARITY,
            });
        }
        unsafe {
            match F::ARITY {
                0 => {
                    let f: Fn0 = std::mem::transmute::<*const u8, Fn0>(F::addr());
                    self.funcs.insert(key, RegisteredFn::Nullary { f, uses_ctx: F::USES_CTX });
                }
                1 => {
                    let f: Fn1 = std::mem::transmute::<*const u8, Fn1>(F::addr());
                    self.funcs.insert(key, RegisteredFn::Unary { f, uses_ctx: F::USES_CTX });
                }
                2 => {
                    let f: Fn2 = std::mem::transmute::<*const u8, Fn2>(F::addr());
                    self.funcs.insert(key, RegisteredFn::Binary { f, uses_ctx: F::USES_CTX });
                }
                3 => {
                    let f: Fn3 = std::mem::transmute::<*const u8, Fn3>(F::addr());
                    self.funcs.insert(key, RegisteredFn::Ternary { f, uses_ctx: F::USES_CTX });
                }
                n => {
                    return Err(JitError::Internal(format!("unsupported arity {} for {}", n, F::NAME)));
                }
            }
        }
        Ok(())
    }


    fn ensure_module_and_register(&mut self) -> Result<(), JitError> {
        if self.module.is_none() {
            // Build ISA with opt_level = speed_and_size. This enables full optimization for the
            // generated code, which can be significantly faster than the default "speed" setting.
            // The trade-off is a slightly longer compile time.
            let mut flag_builder = settings::builder();
            flag_builder
                .set("opt_level", "speed_and_size")
                .map_err(|e| JitError::Internal(format!("settings error: {}", e)))?;
            let isa_builder = native::builder().map_err(|e| JitError::Internal(e.to_string()))?;
            let isa = isa_builder
                .finish(settings::Flags::new(flag_builder))
                .map_err(|e| JitError::Internal(e.to_string()))?;

            let mut jb = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
            // Register built-in pow helper (ctx-ignoring trampoline)
            jb.symbol("tabulon_pow_f64_ctx", tabulon_pow_f64_ctx as *const u8);
            // Register user-provided variable getter (if any)
            if let Some((symbol, fptr)) = self.var_getter {
                jb.symbol(symbol, fptr as *const u8);
            }
            // Register all known functions as symbols once
            for ((name, arity), func) in &self.funcs {
                let sym = format!("{}#{}", name, arity);
                let addr: *const u8 = match func {
                    RegisteredFn::Nullary { f, .. } => *f as *const u8,
                    RegisteredFn::Unary { f, .. } => *f as *const u8,
                    RegisteredFn::Binary { f, .. } => *f as *const u8,
                    RegisteredFn::Ternary { f, .. } => *f as *const u8,
                };
                jb.symbol(sym.as_str(), addr);
            }
            self.module = Some(JITModule::new(jb));
        }
        Ok(())
    }

    fn build_and_finalize_with(
        &mut self,
        var_index: &HashMap<String, usize>,
        ast: &Ast,
        needs_bool_consts: bool,
        ordered_len: usize,
        strat: VarAccessStrategy,
        analysis_opt: Option<&crate::analysis::Analysis>,
    ) -> Result<*const u8, JitError> {
        self.ensure_module_and_register()?;
        let module = self.module.as_mut().unwrap();

        // Common signature: args pointer and ctx pointer params, one f64 return
        let mut sig = module.make_signature();
        let ptr_ty = module.target_config().pointer_type();
        sig.params.push(AbiParam::new(ptr_ty)); // args ptr
        sig.params.push(AbiParam::new(ptr_ty)); // ctx ptr
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
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let vars_param = builder.block_params(entry)[0];
            let ctx_param = builder.block_params(entry)[1];

            // Lazy-constructed boolean constants provider bound to entry block.
            let mut consts = F64Consts::new();
            if needs_bool_consts {
                // Pre-initialize in entry block to avoid switching blocks later.
                let _ = consts.one(&mut builder);
                let _ = consts.zero(&mut builder);
            }

            let result_val = match strat {
                VarAccessStrategy::DirectF64 | VarAccessStrategy::IndirectPtr => {
                    // Eagerly preload all variable values into SSA registers
                    let mut mf = MemFlags::new();
                    mf.set_readonly();
                    mf.set_aligned();

                    let mut var_vals: Vec<Value> = Vec::with_capacity(ordered_len);
                    match strat {
                        VarAccessStrategy::DirectF64 => {
                            // Direct f64 array: base + idx*8
                            for idx in 0..ordered_len {
                                let offset = (idx as i32) * 8;
                                let v = builder.ins().load(types::F64, mf, vars_param, offset);
                                var_vals.push(v);
                            }
                        }
                        VarAccessStrategy::IndirectPtr => {
                            // Pointer array -> f64
                            let ptr_bytes: i32 = if ptr_ty == types::I64 { 8 } else { 4 };
                            for idx in 0..ordered_len {
                                let offset = (idx as i32) * ptr_bytes;
                                let p = builder.ins().load(ptr_ty, mf, vars_param, offset);
                                let v = builder.ins().load(types::F64, mf, p, 0);
                                var_vals.push(v);
                            }
                        }
                        _ => unreachable!(),
                    }

                    // Use direct codegen path
                    codegen_expr(
                        module,
                        &self.funcs,
                        &mut builder,
                        var_index,
                        &var_vals,
                        ctx_param,
                        ast,
                        types::F64,
                        &mut consts,
                    )?
                }
                VarAccessStrategy::ResolverCall { symbol } => {
                    // Declare external variable resolver: extern "C" fn(ctx: ptr, idx: i32) -> f64
                    let mut ext_sig = module.make_signature();
                    ext_sig.params.push(AbiParam::new(ptr_ty)); // ctx
                    ext_sig.params.push(AbiParam::new(types::I32)); // idx
                    ext_sig.returns.push(AbiParam::new(types::F64));
                    let callee_id = module
                        .declare_function(symbol, Linkage::Import, &ext_sig)
                        .map_err(|e| JitError::Internal(e.to_string()))?;
                    let func_ref = module.declare_func_in_func(callee_id, builder.func);

                    let var_ir = VarAccessIR::Resolver { func_ref };
                    // Use provided analysis when available; otherwise compute locally
                    let computed_analysis;
                    let analysis_ref: &crate::analysis::Analysis = if let Some(a) = analysis_opt {
                        a
                    } else {
                        computed_analysis = crate::analysis::Analysis::compute(ast, var_index);
                        &computed_analysis
                    };

                    // If there are no short-circuiting or if-like constructs, take a fast path:
                    // preload all variables once via resolver and use the direct codegen.
                    let no_sc_or_if =
                        analysis_ref.and_carry.is_empty()
                            && analysis_ref.or_carry.is_empty()
                            && analysis_ref.if_carry.is_empty()
                            && analysis_ref.ifs_cond_carry.is_empty();

                    if no_sc_or_if {
                        // Preload in SSA: call resolver once per variable index
                        let mut var_vals: Vec<Value> = Vec::with_capacity(ordered_len);
                        for idx in 0..ordered_len {
                            let idx_val = builder.ins().iconst(types::I32, idx as i64);
                            let call = builder.ins().call(func_ref, &[ctx_param, idx_val]);
                            let v = builder.inst_results(call)[0];
                            var_vals.push(v);
                        }
                        codegen_expr(
                            module,
                            &self.funcs,
                            &mut builder,
                            var_index,
                            &var_vals,
                            ctx_param,
                            ast,
                            types::F64,
                            &mut consts,
                        )?
                    } else {
                        // Block-local SSA cache for resolver calls
                        let mut blk_cache: HashMap<Block, HashMap<usize, Value>> = HashMap::new();

                        codegen_expr_with_access(
                            module,
                            &self.funcs,
                            &mut builder,
                            var_index,
                            &var_ir,
                            ctx_param,
                            ast,
                            types::F64,
                            &mut consts,
                            analysis_ref,
                            &mut blk_cache,
                            entry,
                        )?
                    }
                }
            };

            builder.ins().return_(&[result_val]);
            builder.finalize();
        }
        debug!("JIT code\n{}", ctx.func.display());

        module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::Internal(e.to_string()))?;
        module.clear_context(&mut ctx);
        module
            .finalize_definitions()
            .map_err(|e| JitError::Internal(e.to_string()))?;

        Ok(module.get_finalized_function(func_id))
    }


    /// Compiles a pre-parsed and prepared expression into an executable `CompiledExpr`.
    ///
    /// This path performs codegen only; it assumes the caller already parsed (and optionally
    /// optimized) the AST and collected the variable ordering/indexing into a PreparedExpr.
    pub fn compile_prepared<K>(&mut self, prepared: &PreparedExpr<K>) -> Result<CompiledExpr<K, Ctx>, JitError>
        where K: Clone,
    {
        let code = self.build_and_finalize_with(&prepared.var_index, &*prepared.ast, prepared.needs_bool_consts, prepared.ordered_vars.len(), VarAccessStrategy::DirectF64, prepared.analysis.as_ref())?;
        let func_ptr: JitFn = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExpr::<K, Ctx> {
            func_ptr,
            ordered_vars: prepared.ordered_vars.clone(),
            gen_token: self.generation.clone(),
            gen_at_compile: gen_at,
            uses_ctx: ast_uses_ctx(&*prepared.ast, &self.funcs),
            resolver_mode: false,
            _phantom_ctx: std::marker::PhantomData,
        })
    }
    
    /// Compiles a pre-parsed and prepared expression into an executable `CompiledExprRef` that
    /// expects inputs as references or raw pointers.
    pub fn compile_prepared_ref<K>(&mut self, prepared: &PreparedExpr<K>) -> Result<CompiledExprRef<K, Ctx>, JitError>
        where K: Clone,
    {
        let code = self.build_and_finalize_with(&prepared.var_index, &*prepared.ast, prepared.needs_bool_consts, prepared.ordered_vars.len(), VarAccessStrategy::IndirectPtr, prepared.analysis.as_ref())?;
        let func_ptr: JitFnRef = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExprRef::<K, Ctx> {
            func_ptr,
            ordered_vars: prepared.ordered_vars.clone(),
            gen_token: self.generation.clone(),
            gen_at_compile: gen_at,
            uses_ctx: ast_uses_ctx(&*prepared.ast, &self.funcs),
            resolver_mode: false,
            _phantom_ctx: std::marker::PhantomData,
        })
    }
    
    /// Like compile_prepared, but allows selecting how variables are accessed by the compiled code.
    pub fn compile_prepared_with<K: Clone>(&mut self, prepared: &PreparedExpr<K>, strat: VarAccessStrategy) -> Result<CompiledExpr<K, Ctx>, JitError> {
        let (code, is_resolver) = match strat {
            VarAccessStrategy::DirectF64 | VarAccessStrategy::IndirectPtr => (
                self.build_and_finalize_with(
                    &prepared.var_index,
                    &prepared.ast,
                    prepared.needs_bool_consts,
                    prepared.ordered_vars.len(),
                    strat,
                    prepared.analysis.as_ref(),
                )?,
                false,
            ),
            VarAccessStrategy::ResolverCall { .. } => (
                self.build_and_finalize_with(
                    &prepared.var_index,
                    &prepared.ast,
                    prepared.needs_bool_consts,
                    prepared.ordered_vars.len(),
                    strat,
                    prepared.analysis.as_ref(),
                )?,
                true,
            ),
        };
        let func_ptr: JitFn = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExpr::<K, Ctx> {
            func_ptr,
            ordered_vars: prepared.ordered_vars.clone(),
            gen_token: self.generation.clone(),
            gen_at_compile: gen_at,
            uses_ctx: ast_uses_ctx(&*prepared.ast, &self.funcs),
            resolver_mode: is_resolver,
            _phantom_ctx: std::marker::PhantomData,
        })
    }

    /// Like compile_prepared_ref, but allows selecting how variables are accessed by the compiled code.
    pub fn compile_prepared_ref_with<K: Clone>(&mut self, prepared: &PreparedExpr<K>, strat: VarAccessStrategy) -> Result<CompiledExprRef<K, Ctx>, JitError> {
        let code = self.build_and_finalize_with(
            &prepared.var_index,
            &prepared.ast,
            prepared.needs_bool_consts,
            prepared.ordered_vars.len(),
            strat,
            prepared.analysis.as_ref(),
        )?;
        let func_ptr: JitFnRef = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExprRef::<K, Ctx> {
            func_ptr,
            ordered_vars: prepared.ordered_vars.clone(),
            gen_token: self.generation.clone(),
            gen_at_compile: gen_at,
            uses_ctx: ast_uses_ctx(&*prepared.ast, &self.funcs),
            resolver_mode: matches!(strat, VarAccessStrategy::ResolverCall { .. }),
            _phantom_ctx: std::marker::PhantomData,
        })
    }
    
    /// Compiles an expression string into an executable `CompiledExpr`.
    ///
    /// This method parses, optimizes, and JIT-compiles the expression to native machine code.
    /// The returned `CompiledExpr` owns the compiled code and the variable map.
    /// Evaluation is performed by passing a slice of `f64` values.
    ///
    /// # Errors
    /// Returns a `JitError` if parsing, resolution, or compilation fails.
    pub fn compile(&mut self, expr: &str) -> Result<CompiledExpr<String, Ctx>, JitError> {
        let parser = Parser::new(expr)?;
        let prepared = parser.parse_with_var_resolver(&IdentityResolver)?;
        self.compile_prepared(&prepared)
    }

    /// Compiles an expression string into an executable `CompiledExprRef`.
    ///
    /// This is similar to `compile`, but is designed for evaluation via pointers/references.
    /// The returned `CompiledExprRef` is tied to the lifetime of the `Tabula` engine.
    /// Evaluation is performed by passing a slice of `&f64` or `*const f64`.
    ///
    /// # Errors
    /// Returns a `JitError` if parsing, resolution, or compilation fails.
    pub fn compile_ref(&mut self, expr: &str) -> Result<CompiledExprRef<String, Ctx>, JitError> {
        let parser = Parser::new(expr)?;
        let prepared = parser.parse_with_var_resolver(&IdentityResolver)?;
        self.compile_prepared_ref(&prepared)
    }

    /// Frees all JIT-allocated memory for compiled expressions and resets the JIT module.
    ///
    /// After calling this, any previously created `CompiledExpr` or `CompiledExprRef` instances
    /// become invalid and attempting to use them will result in an `JitError::Invalidated` error.
    /// This is useful for reclaiming memory in long-running applications.
    ///
    /// # Examples
    ///
    /// ```
    /// use tabulon::{Tabula, JitError};
    ///
    /// let mut engine = Tabula::new();
    /// let expr = engine.compile("a + 1").unwrap();
    /// assert_eq!(expr.eval(&[5.0]).unwrap(), 6.0);
    ///
    /// // Free all compiled code
    /// engine.free_memory();
    ///
    /// // Evaluating the old expression now returns an error
    /// match expr.eval(&[5.0]) {
    ///     Err(JitError::Invalidated) => { /* This is expected */ },
    ///     _ => panic!("Expected an Invalidated error"),
    /// }
    /// ```
    pub fn free_memory(&mut self) {
        if let Some(module) = self.module.take() {
            unsafe {
                module.free_memory();
            }
        }
        // bump generation to invalidate previously compiled expressions
        self.generation.fetch_add(1, Ordering::Relaxed);
    }

    /// Clears the custom function registry.
    ///
    /// This allows re-registering a different set of functions before compiling new expressions.
    /// Note: This should typically be called after `free_memory` if expressions have already been compiled.
    pub fn clear_registered_functions(&mut self) {
        self.funcs.clear();
    }
}

/// A compiled, executable expression that owns its variable map.
///
/// Created by [`Tabula::compile`].
/// Evaluation requires passing a slice of `f64` values.
#[derive(Debug, Clone)]
pub struct CompiledExpr<K = String, Ctx = ()> {
    pub(crate) func_ptr: JitFn,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
    pub(crate) uses_ctx: bool,
    pub(crate) resolver_mode: bool,
    pub(crate) _phantom_ctx: std::marker::PhantomData<Ctx>,
}

impl<K, Ctx> CompiledExpr<K, Ctx> {
    /// Returns a slice of variable keys in the order they must be supplied for evaluation.
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

    /// Preferred accessor name for variable keys (alias of vars()).
    pub fn var_names(&self) -> &[K] {
        &self.ordered_vars
    }

    /// Returns true if any function in this expression uses the evaluation context.
    pub fn uses_ctx(&self) -> bool {
        self.uses_ctx
    }

    /// Alias for uses_ctx() for improved discoverability.
    pub fn requires_ctx(&self) -> bool {
        self.uses_ctx
    }
}

impl<K> CompiledExpr<K, ()> {
    /// Evaluates the compiled expression with the given values.
    ///
    /// The `values` slice must provide `f64` values in the exact order specified by `vars()`.
    ///
    /// # Errors
    /// - `JitError::ValuesLen` if `values.len()` is less than `self.vars().len()`.
    /// - `JitError::Invalidated` if the expression was invalidated by `Tabula::free_memory`.
    pub fn eval(&self, values: &[f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(values.as_ptr(), std::ptr::null_mut()) };
        Ok(out)
    }
}

impl<K, Ctx> CompiledExpr<K, Ctx> {
    /// Evaluates the compiled expression with the given values and a mutable context reference.
    pub fn eval_with_ctx(&self, values: &[f64], ctx: &mut Ctx) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let ctx_ptr = (ctx as *mut Ctx) as crate::rt_types::CtxPtr;
        let out = unsafe { f(values.as_ptr(), ctx_ptr) };
        Ok(out)
    }

    /// Evaluates a resolver-compiled expression without requiring a values slice.
    /// Only valid when compiled with VarAccessStrategy::ResolverCall.
    pub fn eval_resolver_ctx(&self, ctx: &mut Ctx) -> Result<f64, JitError> {
        // Check invalidation
        if self.gen_token.load(Ordering::Relaxed) != self.gen_at_compile {
            return Err(JitError::Invalidated);
        }
        if !self.resolver_mode {
            return Err(JitError::Internal("eval_resolver_ctx called on non-resolver compiled expr".into()));
        }
        let f = self.func_ptr;
        let ctx_ptr = (ctx as *mut Ctx) as crate::rt_types::CtxPtr;
        let out = unsafe { f(std::ptr::null(), ctx_ptr) };
        Ok(out)
    }
}

impl<K, Ctx> GenToken for CompiledExpr<K, Ctx> {
    fn gen_token(&self) -> usize {
        self.gen_token.load(Ordering::Relaxed)
    }

    fn gen_at_compile(&self) -> usize {
        self.gen_at_compile
    }
}

/// A compiled, executable expression that is evaluated via references or pointers.
///
/// Created by [`Tabula::compile_ref`].
/// This version is optimized for evaluation methods that use pointers (`eval` and `eval_ptrs`),
/// which can be slightly more efficient if the underlying data is not contiguous.
#[derive(Debug,Clone)]
pub struct CompiledExprRef<K = String, Ctx = ()> {
    pub(crate) func_ptr: JitFnRef,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
    pub(crate) uses_ctx: bool,
    pub(crate) resolver_mode: bool,
    pub(crate) _phantom_ctx: std::marker::PhantomData<Ctx>,
}

impl<K, Ctx> CompiledExprRef<K, Ctx> {
    /// Returns a slice of variable keys in the order they must be supplied for evaluation.
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

    /// Preferred accessor name for variable keys (alias of vars()).
    pub fn var_names(&self) -> &[K] {
        &self.ordered_vars
    }

    /// Returns true if any function in this expression uses the evaluation context.
    pub fn uses_ctx(&self) -> bool {
        self.uses_ctx
    }

    /// Alias for uses_ctx() for improved discoverability.
    pub fn requires_ctx(&self) -> bool {
        self.uses_ctx
    }

    /// Evaluates a resolver-compiled expression without requiring pointer arrays.
    /// Only valid when compiled with VarAccessStrategy::ResolverCall.
    pub fn eval_resolver_ctx(&self, ctx: &mut Ctx) -> Result<f64, JitError> {
        // Check invalidation
        if self.gen_token.load(Ordering::Relaxed) != self.gen_at_compile {
            return Err(JitError::Invalidated);
        }
        if !self.resolver_mode {
            return Err(JitError::Internal("eval_resolver_ctx called on non-resolver compiled expr".into()));
        }
        let f = self.func_ptr;
        let ctx_ptr = (ctx as *mut Ctx) as crate::rt_types::CtxPtr;
        // For resolver path, first param is unused; pass null
        let out = unsafe { f(std::ptr::null(), ctx_ptr) };
        Ok(out)
    }
}

impl<K> CompiledExprRef<K, ()> {
    /// Evaluates the compiled expression with the given values (as references).
    ///
    /// The `values` slice must provide `&f64` references in the exact order specified by `vars()`.
    pub fn eval(&self, values: &[&f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(values.as_ptr() as *const *const f64, std::ptr::null_mut()) };
        Ok(out)
    }

    /// Evaluates this compiled expression using raw pointers to `f64` inputs.
    ///
    /// # Safety
    /// The caller must ensure that each pointer in `ptrs` is valid, aligned, and points to
    /// memory that outlives the duration of this call.
    pub fn eval_ptrs(&self, ptrs: &[*const f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(ptrs, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(ptrs.as_ptr(), std::ptr::null_mut()) };
        Ok(out)
    }
}

impl<K, Ctx> CompiledExprRef<K, Ctx> {
    /// Evaluates with a mutable context reference, which is internally converted to a raw pointer.
    pub fn eval_with_ctx(&self, values: &[&f64], ctx: &mut Ctx) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let ctx_ptr = (ctx as *mut Ctx) as crate::rt_types::CtxPtr;
        let out = unsafe { f(values.as_ptr() as *const *const f64, ctx_ptr) };
        Ok(out)
    }

    /// Evaluates this compiled expression using raw pointers to `f64` inputs and a mutable context reference.
    ///
    /// The `ptrs` slice must provide pointers in the exact order specified by `vars()`.
    /// The pointers must be valid and aligned for reads of `f64` for the duration of the call.
    pub fn eval_ptrs_with_ctx(&self, ptrs: &[*const f64], ctx: &mut Ctx) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(ptrs, needed)?;
        let f = self.func_ptr;
        let ctx_ptr = (ctx as *mut Ctx) as crate::rt_types::CtxPtr;
        let out = unsafe { f(ptrs.as_ptr(), ctx_ptr) };
        Ok(out)
    }
}

impl<K, Ctx> GenToken for CompiledExprRef<K, Ctx> {
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

impl<G> CheckGen for G
where
    G: GenToken,
{
    fn check_gen<T>(&self, arr: &[T], needed: usize) -> Result<(), JitError> {
        if arr.len() < needed {
            return Err(JitError::ValuesLen {
                expected: needed,
                got: arr.len(),
            });
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



impl<Ctx> Tabula<Ctx> {
    /// Creates a new `Tabula` engine with the default configuration for a specific context type.
    pub fn new_ctx() -> Self {
        Self {
            _phantom_ctx: std::marker::PhantomData,
            funcs: HashMap::new(),
            module: None,
            generation: Arc::new(AtomicUsize::new(0)),
            var_getter: None,
        }
    }
}
