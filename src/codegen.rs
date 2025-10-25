use crate::ast::Ast;
use crate::error::JitError;
use crate::rt_types::RegisteredFn;
use cranelift::codegen::ir::FuncRef;
use cranelift::codegen::ir::instructions::BlockArg;
use cranelift::jit::JITModule;
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;
use std::collections::HashMap;

// Variable access abstraction used by codegen when emitting Var loads.
// - Preloaded: values loaded in entry block (legacy path)
// - Resolver: call external getter with (ctx, idx) to fetch variable lazily
pub(crate) enum VarAccessIR {
    Resolver { func_ref: FuncRef },
}

#[derive(Copy, Clone)]
pub(crate) struct F64Consts {
    one: Option<Value>,
    zero: Option<Value>,
}

impl F64Consts {
    pub fn new() -> Self {
        Self {
            one: None,
            zero: None,
        }
    }
    pub fn one<'a>(&mut self, builder: &mut FunctionBuilder<'a>) -> Value {
        if let Some(v) = self.one {
            return v;
        }
        // Create in the current block; engine pre-inits in entry when needed
        let v = builder.ins().f64const(1.0);
        self.one = Some(v);
        v
    }
    pub fn zero<'a>(&mut self, builder: &mut FunctionBuilder<'a>) -> Value {
        if let Some(v) = self.zero {
            return v;
        }
        // Create in the current block; engine pre-inits in entry when needed
        let v = builder.ins().f64const(0.0);
        self.zero = Some(v);
        v
    }
}

pub(crate) fn codegen_expr<'a>(
    module: &mut JITModule,
    registry: &HashMap<(String, u8), RegisteredFn>,
    builder: &mut FunctionBuilder<'a>,
    var_index: &HashMap<String, usize>,
    var_vals: &[Value],
    ctx_val: Value,
    ast: &Ast,
    f64_ty: Type,
    consts: &mut F64Consts,
) -> Result<Value, JitError> {
    match ast {
        Ast::Num(v) => Ok(builder.ins().f64const(*v)),
        Ast::Var(name) => {
            let idx = *var_index
                .get(name)
                .ok_or_else(|| JitError::UnknownIdent(name.clone()))?;
            Ok(var_vals[idx])
        }
        Ast::Neg(x) => {
            let v = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, x, f64_ty, consts,
            )?;
            Ok(builder.ins().fneg(v))
        }
        Ast::Not(x) => {
            let v = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, x, f64_ty, consts,
            )?;
            let zero = consts.zero(builder);
            let is_zero = builder.ins().fcmp(FloatCC::Equal, v, zero);
            let one = consts.one(builder);
            Ok(builder.ins().select(is_zero, one, zero))
        }
        Ast::Add(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            Ok(builder.ins().fadd(va, vb))
        }
        Ast::Sub(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            Ok(builder.ins().fsub(va, vb))
        }
        Ast::Mul(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            Ok(builder.ins().fmul(va, vb))
        }
        Ast::Div(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            Ok(builder.ins().fdiv(va, vb))
        }
        Ast::Pow(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            // Declare external pow helper symbol and call it with ctx: extern "C" fn tabulon_pow_f64_ctx(ctx, f64, f64) -> f64
            let mut ext_sig = module.make_signature();
            let ptr_ty = module.target_config().pointer_type();
            ext_sig.params.push(AbiParam::new(ptr_ty)); // ctx
            ext_sig.params.push(AbiParam::new(types::F64));
            ext_sig.params.push(AbiParam::new(types::F64));
            ext_sig.returns.push(AbiParam::new(types::F64));
            let callee_id = module
                .declare_function("tabulon_pow_f64_ctx", Linkage::Import, &ext_sig)
                .map_err(|e| JitError::Internal(e.to_string()))?;
            let callee_ref = module.declare_func_in_func(callee_id, builder.func);
            let call = builder.ins().call(callee_ref, &[ctx_val, va, vb]);
            let results = builder.inst_results(call);
            Ok(results[0])
        }
        Ast::Eq(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::Equal, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ne(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::NotEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Lt(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::LessThan, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Le(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::LessThanOrEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Gt(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThan, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ge(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::And(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let zero = consts.zero(builder);
            let a_true = builder.ins().fcmp(FloatCC::NotEqual, va, zero);

            let rhs_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            builder.ins().brif(a_true, rhs_block, &[], else_block, &[]);
            builder.seal_block(rhs_block);
            builder.seal_block(else_block);

            builder.switch_to_block(rhs_block);
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let rhs_val = builder.ins().select(b_true, vb, zero);
            builder.ins().jump(merge_block, &[BlockArg::Value(rhs_val)]);

            builder.switch_to_block(else_block);
            builder.ins().jump(merge_block, &[BlockArg::Value(zero)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Or(a, b) => {
            let true_block = builder.create_block();
            let rhs_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);
            let zero = consts.zero(builder);

            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let is_a_true = builder.ins().fcmp(FloatCC::NotEqual, va, zero);

            builder
                .ins()
                .brif(is_a_true, true_block, &[], rhs_block, &[]);
            builder.seal_block(true_block);
            builder.seal_block(rhs_block);

            builder.switch_to_block(true_block);
            builder.ins().jump(merge_block, &[BlockArg::Value(va)]);

            builder.switch_to_block(rhs_block);
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            let is_b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let b_result = builder.ins().select(is_b_true, vb, zero);
            builder
                .ins()
                .jump(merge_block, &[BlockArg::Value(b_result)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::If(c, t, e) => {
            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            let vc = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, c, f64_ty, consts,
            )?;
            let one = consts.one(builder);
            let cond = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, vc, one);

            builder.ins().brif(cond, then_block, &[], else_block, &[]);
            builder.seal_block(then_block);
            builder.seal_block(else_block);

            builder.switch_to_block(then_block);
            let vt = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, t, f64_ty, consts,
            )?;
            builder.ins().jump(merge_block, &[BlockArg::Value(vt)]);

            builder.switch_to_block(else_block);
            let ve = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, e, f64_ty, consts,
            )?;
            builder.ins().jump(merge_block, &[BlockArg::Value(ve)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Ifs(args) => {
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            let mut arg_chunks = args.chunks_exact(2);

            while let Some(chunk) = arg_chunks.next() {
                let cond_ast = &chunk[0];
                let then_ast = &chunk[1];

                let then_block = builder.create_block();
                let next_cond_block = builder.create_block();

                let vc = codegen_expr(
                    module, registry, builder, var_index, var_vals, ctx_val, cond_ast, f64_ty,
                    consts,
                )?;
                let one = consts.one(builder);
                let cond = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, vc, one);

                builder
                    .ins()
                    .brif(cond, then_block, &[], next_cond_block, &[]);
                builder.seal_block(then_block);

                builder.switch_to_block(then_block);
                let vt = codegen_expr(
                    module, registry, builder, var_index, var_vals, ctx_val, then_ast, f64_ty,
                    consts,
                )?;
                builder.ins().jump(merge_block, &[BlockArg::Value(vt)]);

                builder.seal_block(next_cond_block);
                builder.switch_to_block(next_cond_block);
            }

            let else_ast = arg_chunks.remainder().get(0).unwrap();
            let v_else = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, else_ast, f64_ty, consts,
            )?;
            builder.ins().jump(merge_block, &[BlockArg::Value(v_else)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Max(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            Ok(builder.ins().fmax(va, vb))
        }
        Ast::Min(a, b) => {
            let va = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
            )?;
            let vb = codegen_expr(
                module, registry, builder, var_index, var_vals, ctx_val, b, f64_ty, consts,
            )?;
            Ok(builder.ins().fmin(va, vb))
        }
        Ast::Call { name, args } => {
            let arity = args.len() as u8;
            if !registry.contains_key(&(name.clone(), arity)) {
                return Err(JitError::UnknownFunction {
                    name: name.clone(),
                    arity,
                });
            }
            let mut ext_sig = module.make_signature();
            let ptr_ty = module.target_config().pointer_type();
            ext_sig.params.push(AbiParam::new(ptr_ty)); // ctx first
            for _ in 0..arity {
                ext_sig.params.push(AbiParam::new(types::F64));
            }
            ext_sig.returns.push(AbiParam::new(types::F64));
            let sym = format!("{}#{}", name, arity);
            let callee_id = module
                .declare_function(&sym, Linkage::Import, &ext_sig)
                .map_err(|e| JitError::Internal(e.to_string()))?;
            let callee_ref = module.declare_func_in_func(callee_id, builder.func);
            let mut argv: Vec<Value> = Vec::with_capacity(args.len() + 1);
            argv.push(ctx_val);
            for a in args {
                let v = codegen_expr(
                    module, registry, builder, var_index, var_vals, ctx_val, a, f64_ty, consts,
                )?;
                argv.push(v);
            }
            let call = builder.ins().call(callee_ref, &argv);
            let results = builder.inst_results(call);
            Ok(results[0])
        }
    }
}

/// Alternate codegen entry that supports resolver-based variable access.
pub(crate) fn codegen_expr_with_access<'a>(
    module: &mut JITModule,
    registry: &HashMap<(String, u8), RegisteredFn>,
    builder: &mut FunctionBuilder<'a>,
    var_index: &HashMap<String, usize>,
    var_access: &VarAccessIR,
    ctx_val: Value,
    ast: &Ast,
    f64_ty: Type,
    consts: &mut F64Consts,
    analysis: &crate::analysis::Analysis,
    blk_cache: &mut HashMap<Block, HashMap<usize, Value>>,
    cur_block: Block,
) -> Result<Value, JitError> {
    match ast {
        Ast::Num(v) => Ok(builder.ins().f64const(*v)),
        Ast::Var(name) => {
            let idx = *var_index
                .get(name)
                .ok_or_else(|| JitError::UnknownIdent(name.clone()))?;
            match var_access {
                VarAccessIR::Resolver { func_ref } => {
                    // Block-local cache: reuse value within the same block to avoid duplicate resolver calls
                    let entry = blk_cache.entry(cur_block).or_default();
                    if let Some(&v) = entry.get(&idx) {
                        return Ok(v);
                    }
                    let idx_val = builder.ins().iconst(types::I32, idx as i64);
                    let call = builder.ins().call(*func_ref, &[ctx_val, idx_val]);
                    let results = builder.inst_results(call);
                    let v = results[0];
                    entry.insert(idx, v);
                    Ok(v)
                }
            }
        }
        Ast::Neg(x) => {
            let v = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, x, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fneg(v))
        }
        Ast::Not(x) => {
            let v = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, x, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let zero = consts.zero(builder);
            let is_zero = builder.ins().fcmp(FloatCC::Equal, v, zero);
            let one = consts.one(builder);
            Ok(builder.ins().select(is_zero, one, zero))
        }
        Ast::Add(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fadd(va, vb))
        }
        Ast::Sub(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fsub(va, vb))
        }
        Ast::Mul(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fmul(va, vb))
        }
        Ast::Div(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fdiv(va, vb))
        }
        Ast::Pow(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let mut ext_sig = module.make_signature();
            let ptr_ty = module.target_config().pointer_type();
            ext_sig.params.push(AbiParam::new(ptr_ty)); // ctx
            ext_sig.params.push(AbiParam::new(types::F64));
            ext_sig.params.push(AbiParam::new(types::F64));
            ext_sig.returns.push(AbiParam::new(types::F64));
            let callee_id = module
                .declare_function("tabulon_pow_f64_ctx", Linkage::Import, &ext_sig)
                .map_err(|e| JitError::Internal(e.to_string()))?;
            let callee_ref = module.declare_func_in_func(callee_id, builder.func);
            let call = builder.ins().call(callee_ref, &[ctx_val, va, vb]);
            let results = builder.inst_results(call);
            Ok(results[0])
        }
        Ast::Eq(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::Equal, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ne(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::NotEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Lt(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::LessThan, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Le(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::LessThanOrEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Gt(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThan, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ge(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::And(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let zero = consts.zero(builder);
            let a_true = builder.ins().fcmp(FloatCC::NotEqual, va, zero);

            // Pre-resolve carry vars for And(lhs, rhs): fv(lhs) ∩ fv(rhs) using analysis
            let and_key = ast as *const crate::ast::Ast as usize;
            if let Some(carry) = analysis.and_carry.get(&and_key) {
                let parent_entry = blk_cache.entry(cur_block).or_default();
                for &idx in carry.iter() {
                    if !parent_entry.contains_key(&idx) {
                        match var_access {
                            VarAccessIR::Resolver { func_ref } => {
                                let idx_val = builder.ins().iconst(types::I32, idx as i64);
                                let call = builder.ins().call(*func_ref, &[ctx_val, idx_val]);
                                let v = builder.inst_results(call)[0];
                                parent_entry.insert(idx, v);
                            }
                        }
                    }
                }
            }

            let rhs_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            // Seed only the carry subset into rhs_block; else_block needs no vars
            if let Some(parent) = blk_cache.get(&cur_block) {
                if let Some(carry) = analysis.and_carry.get(&and_key) {
                    let mut seed: HashMap<usize, Value> = HashMap::new();
                    for &idx in carry.iter() {
                        if let Some(&v) = parent.get(&idx) {
                            seed.insert(idx, v);
                        }
                    }
                    blk_cache.insert(rhs_block, seed);
                }
            }

            builder.ins().brif(a_true, rhs_block, &[], else_block, &[]);
            builder.seal_block(rhs_block);
            builder.seal_block(else_block);

            builder.switch_to_block(rhs_block);
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, rhs_block,
            )?;
            let b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let rhs_val = builder.ins().select(b_true, vb, zero);
            builder.ins().jump(merge_block, &[BlockArg::Value(rhs_val)]);

            builder.switch_to_block(else_block);
            builder.ins().jump(merge_block, &[BlockArg::Value(zero)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Or(a, b) => {
            let true_block = builder.create_block();
            let rhs_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);
            let zero = consts.zero(builder);

            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let is_a_true = builder.ins().fcmp(FloatCC::NotEqual, va, zero);

            // Pre-resolve carry vars for Or(lhs, rhs): fv(lhs) ∩ fv(rhs)
            let or_key = ast as *const crate::ast::Ast as usize;
            if let Some(carry) = analysis.or_carry.get(&or_key) {
                let parent_entry = blk_cache.entry(cur_block).or_default();
                for &idx in carry.iter() {
                    if !parent_entry.contains_key(&idx) {
                        match var_access {
                            VarAccessIR::Resolver { func_ref } => {
                                let idx_val = builder.ins().iconst(types::I32, idx as i64);
                                let call = builder.ins().call(*func_ref, &[ctx_val, idx_val]);
                                let v = builder.inst_results(call)[0];
                                parent_entry.insert(idx, v);
                            }
                        }
                    }
                }
            }

            // Seed only the carry subset into rhs_block; true_block needs no vars
            if let Some(parent) = blk_cache.get(&cur_block) {
                if let Some(carry) = analysis.or_carry.get(&or_key) {
                    let mut seed: HashMap<usize, Value> = HashMap::new();
                    for &idx in carry.iter() {
                        if let Some(&v) = parent.get(&idx) {
                            seed.insert(idx, v);
                        }
                    }
                    blk_cache.insert(rhs_block, seed);
                }
            }

            builder
                .ins()
                .brif(is_a_true, true_block, &[], rhs_block, &[]);
            builder.seal_block(true_block);
            builder.seal_block(rhs_block);

            builder.switch_to_block(true_block);
            builder.ins().jump(merge_block, &[BlockArg::Value(va)]);

            builder.switch_to_block(rhs_block);
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, rhs_block,
            )?;
            let is_b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let b_result = builder.ins().select(is_b_true, vb, zero);
            builder
                .ins()
                .jump(merge_block, &[BlockArg::Value(b_result)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::If(c, t, e) => {
            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            // Evaluate condition first in current block
            let vc = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, c, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let one = consts.one(builder);
            let cond = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, vc, one);

            // Use precomputed carry set from analysis to resolve shared vars once in current block
            let if_key = ast as *const crate::ast::Ast as usize;
            if let Some(carry) = analysis.if_carry.get(&if_key) {
                let parent_entry = blk_cache.entry(cur_block).or_default();
                for &idx in carry.iter() {
                    if !parent_entry.contains_key(&idx) {
                        match var_access {
                            VarAccessIR::Resolver { func_ref } => {
                                let idx_val = builder.ins().iconst(types::I32, idx as i64);
                                let call = builder.ins().call(*func_ref, &[ctx_val, idx_val]);
                                let v = builder.inst_results(call)[0];
                                parent_entry.insert(idx, v);
                            }
                        }
                    }
                }
            }

            // Seed caches for both branches from current block (includes condition-loaded values)
            if let Some(parent) = blk_cache.get(&cur_block).cloned() {
                blk_cache.insert(then_block, parent.clone());
                blk_cache.insert(else_block, parent);
            }

            builder.ins().brif(cond, then_block, &[], else_block, &[]);
            builder.seal_block(then_block);
            builder.seal_block(else_block);

            builder.switch_to_block(then_block);
            let vt = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, t, f64_ty, consts,
                analysis, blk_cache, then_block,
            )?;
            builder.ins().jump(merge_block, &[BlockArg::Value(vt)]);

            builder.switch_to_block(else_block);
            let ve = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, e, f64_ty, consts,
                analysis, blk_cache, else_block,
            )?;
            builder.ins().jump(merge_block, &[BlockArg::Value(ve)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Ifs(args) => {
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            let mut cond_block = cur_block;
            let n = args.len();
            debug_assert!(n >= 1, "Ifs requires at least an else expression");

            let mut i = 0usize;
            while i + 1 < n {
                let cond_ast = &args[i];
                let then_ast = &args[i + 1];

                // Use precomputed carry set for this condition from analysis
                let cond_key = &**cond_ast as *const crate::ast::Ast as usize;
                if let Some(carry) = analysis.ifs_cond_carry.get(&cond_key) {
                    let entry = blk_cache.entry(cond_block).or_default();
                    for &idx in carry.iter() {
                        if !entry.contains_key(&idx) {
                            match var_access {
                                VarAccessIR::Resolver { func_ref } => {
                                    let idx_val = builder.ins().iconst(types::I32, idx as i64);
                                    let call = builder.ins().call(*func_ref, &[ctx_val, idx_val]);
                                    let v = builder.inst_results(call)[0];
                                    entry.insert(idx, v);
                                }
                            }
                        }
                    }
                }

                // Evaluate condition in the current cond_block
                let vc = codegen_expr_with_access(
                    module, registry, builder, var_index, var_access, ctx_val, cond_ast, f64_ty,
                    consts, analysis, blk_cache, cond_block,
                )?;
                let one = consts.one(builder);
                let cond = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, vc, one);

                let then_block = builder.create_block();
                let next_cond_block = builder.create_block();

                // Seed caches from cond_block into successors (includes condition-loaded values)
                if let Some(parent) = blk_cache.get(&cond_block).cloned() {
                    blk_cache.insert(then_block, parent.clone());
                    blk_cache.insert(next_cond_block, parent);
                }

                builder
                    .ins()
                    .brif(cond, then_block, &[], next_cond_block, &[]);
                builder.seal_block(then_block);

                builder.switch_to_block(then_block);
                let vt = codegen_expr_with_access(
                    module, registry, builder, var_index, var_access, ctx_val, then_ast, f64_ty,
                    consts, analysis, blk_cache, then_block,
                )?;
                builder.ins().jump(merge_block, &[BlockArg::Value(vt)]);

                builder.seal_block(next_cond_block);
                builder.switch_to_block(next_cond_block);

                // Move to next condition block
                cond_block = next_cond_block;

                i += 2;
            }

            // else branch (last arg)
            let else_ast = &args[n - 1];
            let v_else = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, else_ast, f64_ty,
                consts, analysis, blk_cache, cond_block,
            )?;
            builder.ins().jump(merge_block, &[BlockArg::Value(v_else)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Max(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fmax(va, vb))
        }
        Ast::Min(a, b) => {
            let va = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            let vb = codegen_expr_with_access(
                module, registry, builder, var_index, var_access, ctx_val, b, f64_ty, consts,
                analysis, blk_cache, cur_block,
            )?;
            Ok(builder.ins().fmin(va, vb))
        }
        Ast::Call { name, args } => {
            let arity = args.len() as u8;
            if !registry.contains_key(&(name.clone(), arity)) {
                return Err(JitError::UnknownFunction {
                    name: name.clone(),
                    arity,
                });
            }
            let mut ext_sig = module.make_signature();
            let ptr_ty = module.target_config().pointer_type();
            ext_sig.params.push(AbiParam::new(ptr_ty)); // ctx first
            for _ in 0..arity {
                ext_sig.params.push(AbiParam::new(types::F64));
            }
            ext_sig.returns.push(AbiParam::new(types::F64));
            let sym = format!("{}#{}", name, arity);
            let callee_id = module
                .declare_function(&sym, Linkage::Import, &ext_sig)
                .map_err(|e| JitError::Internal(e.to_string()))?;
            let callee_ref = module.declare_func_in_func(callee_id, builder.func);
            let mut argv: Vec<Value> = Vec::with_capacity(args.len() + 1);
            argv.push(ctx_val);
            for a in args {
                let v = codegen_expr_with_access(
                    module, registry, builder, var_index, var_access, ctx_val, a, f64_ty, consts,
                    analysis, blk_cache, cur_block,
                )?;
                argv.push(v);
            }
            let call = builder.ins().call(callee_ref, &argv);
            let results = builder.inst_results(call);
            Ok(results[0])
        }
    }
}
