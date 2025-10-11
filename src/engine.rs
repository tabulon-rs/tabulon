use crate::ast::Ast;
use crate::codegen::{F64Consts, codegen_expr};
use crate::collect::collect_vars;
use crate::error::JitError;
#[cfg(feature = "optimize")]
use crate::optimizer::optimize;
use crate::parser::Parser;
use crate::resolver::{IdentityResolver, VarResolver};
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
pub struct Tabula<K = String, R = IdentityResolver> {
    pub(crate) resolver: R,
    pub(crate) _phantom: std::marker::PhantomData<K>,
    pub(crate) funcs: HashMap<(String, u8), RegisteredFn>,
    pub(crate) module: Option<JITModule>,
    pub(crate) generation: Arc<AtomicUsize>,
}

impl Default for Tabula<String, IdentityResolver> {
    fn default() -> Self {
        Self::new()
    }
}

impl Tabula<String, IdentityResolver> {
    /// Creates a new `Tabula` engine with the default configuration.
    ///
    /// The default engine uses `String` keys for variables and resolves them to themselves.
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

pub(crate) type ParsedMeta<K> = (Ast, Vec<K>, HashMap<String, usize>);

fn ast_needs_bool_consts(ast: &Ast) -> bool {
    use crate::ast::Ast::*;
    match ast {
        Num(_) | Var(_) => false,
        Neg(x) => ast_needs_bool_consts(x),
        Not(_) => true,
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) | Pow(a, b) | Max(a, b) | Min(a, b) => {
            ast_needs_bool_consts(a) || ast_needs_bool_consts(b)
        }
        Eq(_, _) | Ne(_, _) | Lt(_, _) | Le(_, _) | Gt(_, _) | Ge(_, _) | And(_, _) | Or(_, _) => {
            true
        }
        If(_, _, _) => true,
        Ifs(_) => true,
        Call { args, .. } => args.iter().any(ast_needs_bool_consts),
    }
}

impl<K, R> Tabula<K, R>
where
    K: Clone + Eq + std::hash::Hash + Send + Sync + 'static,
    R: VarResolver<K>,
{
    /// Creates a new `Tabula` engine with a custom variable resolver.
    ///
    /// This allows you to define custom logic for mapping variable names from expression strings
    /// to a key type `K` of your choice (e.g., a u64, an enum, etc.).
    ///
    /// # Examples
    ///
    /// ```
    /// use tabulon::{Tabula, VarResolver, VarResolveError};
    ///
    /// // A resolver that maps "strength" to key 1 and "dexterity" to key 2.
    /// struct MyResolver;
    /// impl VarResolver<u32> for MyResolver {
    ///     fn resolve(&self, ident: &str) -> Result<u32, VarResolveError> {
    ///         match ident {
    ///             "strength" => Ok(1),
    ///             "dexterity" => Ok(2),
    ///             _ => Err(VarResolveError::Unknown(ident.to_string())),
    ///         }
    ///     }
    /// }
    ///
    /// let mut engine = Tabula::with_resolver(MyResolver);
    /// let expr = engine.compile("strength * 2").unwrap();
    /// assert_eq!(expr.vars(), &[1]);
    /// ```
    pub fn with_resolver(resolver: R) -> Self {
        Self {
            resolver,
            _phantom: std::marker::PhantomData,
            funcs: HashMap::new(),
            module: None,
            generation: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// Registers a nullary (0-argument) function with the engine.
    ///
    /// Functions must be registered before any expressions are compiled.
    pub fn register_nullary(&mut self, name: &str, f: Fn0) -> Result<(), JitError> {
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
        self.funcs.insert(key, RegisteredFn::Nullary(f));
        Ok(())
    }
    /// Registers a unary (1-argument) function with the engine.
    pub fn register_unary(&mut self, name: &str, f: Fn1) -> Result<(), JitError> {
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
        self.funcs.insert(key, RegisteredFn::Unary(f));
        Ok(())
    }
    /// Registers a binary (2-argument) function with the engine.
    ///
    /// # Examples
    ///
    /// ```
    /// use tabulon::Tabula;
    ///
    /// extern "C" fn my_pow(base: f64, exp: f64) -> f64 {
    ///     base.powf(exp)
    /// }
    ///
    /// let mut engine = Tabula::new();
    /// // The function must be registered before compiling any expressions.
    /// engine.register_binary("my_pow", my_pow).unwrap();
    ///
    /// let expr = engine.compile("my_pow(a, 3)").unwrap();
    /// let result = expr.eval(&[2.0]).unwrap();
    /// assert_eq!(result, 8.0);
    /// ```
    pub fn register_binary(&mut self, name: &str, f: Fn2) -> Result<(), JitError> {
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
        self.funcs.insert(key, RegisteredFn::Binary(f));
        Ok(())
    }
    /// Registers a ternary (3-argument) function with the engine.
    pub fn register_ternary(&mut self, name: &str, f: Fn3) -> Result<(), JitError> {
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
        self.funcs.insert(key, RegisteredFn::Ternary(f));
        Ok(())
    }

    // --- Common helpers shared by compile and compile_ref ---
    fn parse_and_resolve(&self, expr: &str) -> Result<ParsedMeta<K>, JitError> {
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
                Err(_) => {
                    return Err(JitError::UnknownIdent(name.clone()));
                }
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
            // Register built-in pow helper
            jb.symbol("tabulon_pow_f64", tabulon_pow_f64 as *const u8);
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

            // Eagerly preload all variable values into SSA registers
            let mut mf = MemFlags::new();
            mf.set_readonly();
            mf.set_aligned();

            let mut var_vals: Vec<Value> = Vec::with_capacity(ordered_len);
            match load_mode {
                LoadMode::DirectF64 => {
                    // Direct f64 array: base + idx*8
                    for idx in 0..ordered_len {
                        let offset = (idx as i32) * 8;
                        let v = builder.ins().load(types::F64, mf, vars_ptr, offset);
                        var_vals.push(v);
                    }
                }
                LoadMode::IndirectPtr => {
                    // Pointer array -> f64
                    let ptr_bytes: i32 = if ptr_ty == types::I64 { 8 } else { 4 };
                    for idx in 0..ordered_len {
                        let offset = (idx as i32) * ptr_bytes;
                        let p = builder.ins().load(ptr_ty, mf, vars_ptr, offset);
                        let v = builder.ins().load(types::F64, mf, p, 0);
                        var_vals.push(v);
                    }
                }
            }

            // Lazy-constructed boolean constants provider bound to entry block.
            let mut consts = F64Consts::new();
            if ast_needs_bool_consts(ast) {
                // Pre-initialize in entry block to avoid switching blocks later.
                let _ = consts.one(&mut builder);
                let _ = consts.zero(&mut builder);
            }

            let val = codegen_expr(
                module,
                &self.funcs,
                &mut builder,
                var_index,
                &var_vals,
                ast,
                types::F64,
                &mut consts,
            )?;
            builder.ins().return_(&[val]);
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

        let code = module.get_finalized_function(func_id);
        Ok(code)
    }

    /// Compiles an expression string into an executable `CompiledExpr`.
    ///
    /// This method parses, optimizes, and JIT-compiles the expression to native machine code.
    /// The returned `CompiledExpr` owns the compiled code and the variable map.
    /// Evaluation is performed by passing a slice of `f64` values.
    ///
    /// # Errors
    /// Returns a `JitError` if parsing, resolution, or compilation fails.
    pub fn compile(&mut self, expr: &str) -> Result<CompiledExpr<K>, JitError> {
        let (ast, ordered_vars, var_index) = self.parse_and_resolve(expr)?;
        let code =
            self.build_and_finalize(&var_index, &ast, ordered_vars.len(), LoadMode::DirectF64)?;
        let func_ptr: JitFn = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExpr::<K> {
            func_ptr,
            ordered_vars,
            gen_token: self.generation.clone(),
            gen_at_compile: gen_at,
        })
    }

    /// Compiles an expression string into an executable `CompiledExprRef`.
    ///
    /// This is similar to `compile`, but is designed for evaluation via pointers/references.
    /// The returned `CompiledExprRef` is tied to the lifetime of the `Tabula` engine.
    /// Evaluation is performed by passing a slice of `&f64` or `*const f64`.
    ///
    /// # Errors
    /// Returns a `JitError` if parsing, resolution, or compilation fails.
    pub fn compile_ref(&mut self, expr: &str) -> Result<CompiledExprRef<K>, JitError> {
        let (ast, ordered_vars, var_index) = self.parse_and_resolve(expr)?;
        let code =
            self.build_and_finalize(&var_index, &ast, ordered_vars.len(), LoadMode::IndirectPtr)?;
        let func_ptr: JitFnRef = unsafe { std::mem::transmute(code) };
        let gen_at = self.generation.load(Ordering::Relaxed);
        Ok(CompiledExprRef::<K> {
            func_ptr,
            ordered_vars,
            gen_token: self.generation.clone(),
            gen_at_compile: gen_at,
        })
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
pub struct CompiledExpr<K = String> {
    pub(crate) func_ptr: JitFn,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
}

impl<K> CompiledExpr<K> {
    /// Returns a slice of variable keys in the order they must be supplied for evaluation.
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

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
        let out = unsafe { f(values.as_ptr()) };
        Ok(out)
    }
}

impl<K> GenToken for CompiledExpr<K> {
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
pub struct CompiledExprRef<K = String> {
    pub(crate) func_ptr: JitFnRef,
    pub(crate) ordered_vars: Vec<K>,
    pub(crate) gen_token: Arc<AtomicUsize>,
    pub(crate) gen_at_compile: usize,
}

impl<K> CompiledExprRef<K> {
    /// Returns a slice of variable keys in the order they must be supplied for evaluation.
    pub fn vars(&self) -> &[K] {
        &self.ordered_vars
    }

    /// Evaluates the compiled expression with the given values (as references).
    ///
    /// The `values` slice must provide `&f64` references in the exact order specified by `vars()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tabulon::Tabula;
    ///
    /// let mut engine = Tabula::new();
    /// let expr = engine.compile_ref("a * b").unwrap();
    ///
    /// let a = 10.0;
    /// let b = 5.5;
    ///
    /// // Pass values as a slice of references
    /// let result = expr.eval(&[&a, &b]).unwrap();
    /// assert_eq!(result, 55.0);
    /// ```
    ///
    /// # Errors
    /// - `JitError::ValuesLen` if `values.len()` is less than `self.vars().len()`.
    /// - `JitError::Invalidated` if the expression was invalidated by `Tabula::free_memory`.
    pub fn eval(&self, values: &[&f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(values, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(values.as_ptr() as *const *const f64) };
        Ok(out)
    }

    /// Evaluates this compiled expression using raw pointers to `f64` inputs.
    ///
    /// This is an advanced, unsafe API for integrations (e.g., FFI) where holding references
    /// is not feasible. Pointers must be valid and point to live `f64` data.
    ///
    /// # Safety
    /// The caller must ensure that each pointer in `ptrs` is valid, aligned, and points to
    /// memory that outlives the duration of this call. Misuse can lead to undefined behavior.
    pub fn eval_ptrs(&self, ptrs: &[*const f64]) -> Result<f64, JitError> {
        let needed = self.ordered_vars.len();
        self.check_gen(ptrs, needed)?;
        let f = self.func_ptr;
        let out = unsafe { f(ptrs.as_ptr()) };
        Ok(out)
    }
}

impl<K> GenToken for CompiledExprRef<K> {
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

#[derive(Copy, Clone)]
enum LoadMode {
    DirectF64,
    IndirectPtr,
}
