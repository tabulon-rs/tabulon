use crate::ast::Ast;
use crate::error::JitError;
use crate::rt_types::RegisteredFn;
use cranelift::codegen::ir::instructions::BlockArg;
use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};
use std::collections::HashMap;
use crate::engine::VarCache;

pub(crate) fn codegen_expr<'a>(
    module: &mut JITModule,
    registry: &HashMap<(String, u8), RegisteredFn>,
    builder: &mut FunctionBuilder<'a>,
    var_index: &HashMap<String, usize>,
    var_vals: &[Value],
    ast: &Ast,
    f64_ty: Type,
) -> Result<Value, JitError> {
    match ast {
        Ast::Num(v) => Ok(builder.ins().f64const(*v)),
        Ast::Var(name) => {
            let idx = *var_index.get(name).ok_or_else(|| JitError::UnknownIdent(name.clone()))?;
            Ok(var_vals[idx])
        }
        Ast::Neg(x) => {
            let v = codegen_expr(module, registry, builder, var_index, var_vals, x, f64_ty)?;
            Ok(builder.ins().fneg(v))
        }
        Ast::Add(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            Ok(builder.ins().fadd(va, vb))
        }
        Ast::Sub(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            Ok(builder.ins().fsub(va, vb))
        }
        Ast::Mul(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            Ok(builder.ins().fmul(va, vb))
        }
        Ast::Div(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            Ok(builder.ins().fdiv(va, vb))
        }
        Ast::Eq(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let cmp = builder.ins().fcmp(FloatCC::Equal, va, vb);
            let one = builder.ins().f64const(1.0);
            let zero = builder.ins().f64const(0.0);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ne(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let cmp = builder.ins().fcmp(FloatCC::NotEqual, va, vb);
            let one = builder.ins().f64const(1.0);
            let zero = builder.ins().f64const(0.0);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Lt(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let cmp = builder.ins().fcmp(FloatCC::LessThan, va, vb);
            let one = builder.ins().f64const(1.0);
            let zero = builder.ins().f64const(0.0);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Le(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let cmp = builder.ins().fcmp(FloatCC::LessThanOrEqual, va, vb);
            let one = builder.ins().f64const(1.0);
            let zero = builder.ins().f64const(0.0);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Gt(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThan, va, vb);
            let one = builder.ins().f64const(1.0);
            let zero = builder.ins().f64const(0.0);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ge(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, va, vb);
            let one = builder.ins().f64const(1.0);
            let zero = builder.ins().f64const(0.0);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::And(a, b) => {
            // Short-circuit AND: if left is false (== 0.0), skip evaluating right
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let zero_lhs = builder.ins().f64const(0.0);
            let a_true = builder.ins().fcmp(FloatCC::NotEqual, va, zero_lhs);

            let rhs_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            // Branch based on left truthiness
            builder.ins().brif(a_true, rhs_block, &[], else_block, &[]);

            // True path: evaluate right only if left is true
            builder.seal_block(rhs_block);
            builder.switch_to_block(rhs_block);
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let zero_rhs = builder.ins().f64const(0.0);
            let one_rhs = builder.ins().f64const(1.0);
            let b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero_rhs);
            let rhs_val = builder.ins().select(b_true, one_rhs, zero_rhs);
            builder.ins().jump(merge_block, &[BlockArg::Value(rhs_val)]);

            // False path: result is 0.0
            builder.seal_block(else_block);
            builder.switch_to_block(else_block);
            let zero_else = builder.ins().f64const(0.0);
            builder.ins().jump(merge_block, &[BlockArg::Value(zero_else)]);

            // Merge results
            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Or(a, b) => {
            let true_block = builder.create_block();
            let rhs_block = builder.create_block();
            let merge_block = builder.create_block();
            builder.append_block_param(merge_block, f64_ty);

            let one = builder.ins().f64const(1.0);

            // 1. Evaluate `a`.
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let is_a_true = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, va, one);

            // 2. If `a` is true, short-circuit. Otherwise, evaluate `b`.
            builder.ins().brif(is_a_true, true_block, &[], rhs_block, &[]);

            // 3. `true_block`: short-circuit path, result is 1.0.
            builder.switch_to_block(true_block);
            builder.seal_block(true_block);
            builder.ins().jump(merge_block, &[BlockArg::Value(one)]);

            // 4. `rhs_block`: `a` was false, result depends on `b`.
            builder.switch_to_block(rhs_block);
            builder.seal_block(rhs_block);
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            let zero = builder.ins().f64const(0.0);
            let is_b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let b_result = builder.ins().select(is_b_true, one, zero);
            builder.ins().jump(merge_block, &[BlockArg::Value(b_result)]);

            // 5. `merge_block`: join the paths.
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);
            let final_val = builder.block_params(merge_block)[0];
            Ok(final_val)
        }
        Ast::If(c, t, e) => {
            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();

            builder.append_block_param(merge_block, f64_ty);

            let vc = codegen_expr(module, registry, builder, var_index, var_vals, c, f64_ty)?;
            let one = builder.ins().f64const(1.0);
            let cond = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, vc, one);

            builder.ins().brif(cond, then_block, &[], else_block, &[]);

            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            let vt = codegen_expr(module, registry, builder, var_index, var_vals, t, f64_ty)?;
            builder.ins().jump(merge_block, &[BlockArg::Value(vt)]);

            builder.switch_to_block(else_block);
            builder.seal_block(else_block);
            let ve = codegen_expr(module, registry, builder, var_index, var_vals, e, f64_ty)?;
            builder.ins().jump(merge_block, &[BlockArg::Value(ve)]);

            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let final_val = builder.block_params(merge_block)[0];
            Ok(final_val)
        }
        Ast::Max(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            Ok(builder.ins().fmax(va, vb))
        }
        Ast::Min(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty)?;
            Ok(builder.ins().fmin(va, vb))
        }
        Ast::Call { name, args } => {
            let arity = args.len() as u8;
            if !registry.contains_key(&(name.clone(), arity)) {
                return Err(JitError::UnknownFunction { name: name.clone(), arity });
            }
            // External function signature (f64,..) -> f64
            let mut ext_sig = module.make_signature();
            for _ in 0..arity { ext_sig.params.push(AbiParam::new(types::F64)); }
            ext_sig.returns.push(AbiParam::new(types::F64));
            let sym = format!("{}#{}", name, arity);
            let callee_id = module
                .declare_function(&sym, Linkage::Import, &ext_sig)
                .map_err(|e| JitError::Internal(e.to_string()))?;
            let callee_ref = module.declare_func_in_func(callee_id, &mut builder.func);
            let mut argv: Vec<Value> = Vec::with_capacity(args.len());
            for a in args {
                let v = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty)?;
                argv.push(v);
            }
            let call = builder.ins().call(callee_ref, &argv);
            let results = builder.inst_results(call);
            Ok(results[0])
        }
    }
}

fn ensure_var(
    builder: &mut FunctionBuilder,
    vars_ptr: Value,
    ptr_ty: Type,
    mf: MemFlags,
    idx: usize,
    cache: &mut VarCache,
) -> Value {
    if let Some(v) = cache.get(idx) { return v; }
    let ptr_bytes: i32 = if ptr_ty == types::I64 { 8 } else { 4 };
    let offset = (idx as i32) * ptr_bytes;
    let p = builder.ins().load(ptr_ty, mf, vars_ptr, offset);
    let v = builder.ins().load(types::F64, mf, p, 0);
    cache.set(idx, v);
    v
}