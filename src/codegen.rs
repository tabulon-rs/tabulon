use crate::ast::Ast;
use crate::error::JitError;
use crate::rt_types::RegisteredFn;
use cranelift::codegen::ir::instructions::BlockArg;
use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};
use std::collections::HashMap;

#[derive(Copy, Clone)]
pub(crate) struct F64Consts {
    entry: Block,
    one: Option<Value>,
    zero: Option<Value>,
}

impl F64Consts {
    pub fn new(entry: Block) -> Self {
        Self { entry, one: None, zero: None }
    }
    pub fn one<'a>(&mut self, builder: &mut FunctionBuilder<'a>) -> Value {
        if let Some(v) = self.one { return v; }
        // Create in the current block; engine pre-inits in entry when needed
        let v = builder.ins().f64const(1.0);
        self.one = Some(v);
        v
    }
    pub fn zero<'a>(&mut self, builder: &mut FunctionBuilder<'a>) -> Value {
        if let Some(v) = self.zero { return v; }
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
            let v = codegen_expr(module, registry, builder, var_index, var_vals, x, f64_ty, consts)?;
            Ok(builder.ins().fneg(v))
        }
        Ast::Add(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            Ok(builder.ins().fadd(va, vb))
        }
        Ast::Sub(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            Ok(builder.ins().fsub(va, vb))
        }
        Ast::Mul(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            Ok(builder.ins().fmul(va, vb))
        }
        Ast::Div(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            Ok(builder.ins().fdiv(va, vb))
        }
        Ast::Eq(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let cmp = builder.ins().fcmp(FloatCC::Equal, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ne(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let cmp = builder.ins().fcmp(FloatCC::NotEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Lt(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let cmp = builder.ins().fcmp(FloatCC::LessThan, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Le(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let cmp = builder.ins().fcmp(FloatCC::LessThanOrEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Gt(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThan, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::Ge(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let cmp = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, va, vb);
            let one = consts.one(builder);
            let zero = consts.zero(builder);
            Ok(builder.ins().select(cmp, one, zero))
        }
        Ast::And(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
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
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let one = consts.one(builder);
            let rhs_val = builder.ins().select(b_true, one, zero);
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
            let one = consts.one(builder);
            let zero = consts.zero(builder);

            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let is_a_true = builder.ins().fcmp(FloatCC::NotEqual, va, zero);

            builder.ins().brif(is_a_true, true_block, &[], rhs_block, &[]);
            builder.seal_block(true_block);
            builder.seal_block(rhs_block);

            builder.switch_to_block(true_block);
            builder.ins().jump(merge_block, &[BlockArg::Value(one)]);

            builder.switch_to_block(rhs_block);
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            let is_b_true = builder.ins().fcmp(FloatCC::NotEqual, vb, zero);
            let b_result = builder.ins().select(is_b_true, one, zero);
            builder.ins().jump(merge_block, &[BlockArg::Value(b_result)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::If(c, t, e) => {
            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();
            let res = builder.append_block_param(merge_block, f64_ty);

            let vc = codegen_expr(module, registry, builder, var_index, var_vals, c, f64_ty, consts)?;
            let one = consts.one(builder);
            let cond = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, vc, one);

            builder.ins().brif(cond, then_block, &[], else_block, &[]);
            builder.seal_block(then_block);
            builder.seal_block(else_block);

            builder.switch_to_block(then_block);
            let vt = codegen_expr(module, registry, builder, var_index, var_vals, t, f64_ty, consts)?;
            builder.ins().jump(merge_block, &[BlockArg::Value(vt)]);

            builder.switch_to_block(else_block);
            let ve = codegen_expr(module, registry, builder, var_index, var_vals, e, f64_ty, consts)?;
            builder.ins().jump(merge_block, &[BlockArg::Value(ve)]);

            builder.seal_block(merge_block);
            builder.switch_to_block(merge_block);
            Ok(res)
        }
        Ast::Max(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            Ok(builder.ins().fmax(va, vb))
        }
        Ast::Min(a, b) => {
            let va = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
            let vb = codegen_expr(module, registry, builder, var_index, var_vals, b, f64_ty, consts)?;
            Ok(builder.ins().fmin(va, vb))
        }
        Ast::Call { name, args } => {
            let arity = args.len() as u8;
            if !registry.contains_key(&(name.clone(), arity)) {
                return Err(JitError::UnknownFunction { name: name.clone(), arity });
            }
            let mut ext_sig = module.make_signature();
            for _ in 0..arity {
                ext_sig.params.push(AbiParam::new(types::F64));
            }
            ext_sig.returns.push(AbiParam::new(types::F64));
            let sym = format!("{}#{}", name, arity);
            let callee_id = module
                .declare_function(&sym, Linkage::Import, &ext_sig)
                .map_err(|e| JitError::Internal(e.to_string()))?;
            let callee_ref = module.declare_func_in_func(callee_id, builder.func);
            let mut argv: Vec<Value> = Vec::with_capacity(args.len());
            for a in args {
                let v = codegen_expr(module, registry, builder, var_index, var_vals, a, f64_ty, consts)?;
                argv.push(v);
            }
            let call = builder.ins().call(callee_ref, &argv);
            let results = builder.inst_results(call);
            Ok(results[0])
        }
    }
}

