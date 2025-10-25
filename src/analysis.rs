use crate::ast::Ast;
use std::collections::HashMap;

/// Precomputed front-end analysis to reduce work during codegen.
///
/// We currently precompute carry sets for short-circuiting constructs so that
/// codegen can resolve only the variables needed by both sides of a branch.
///
/// Keys are based on stable addresses of Ast nodes within the lifetime of a
/// single AST instance. We use the node's pointer value (usize) as an ID.
#[derive(Debug, Default, Clone)]
pub struct Analysis {
    /// For each If node: carry = free_vars(then) ∩ free_vars(else)
    pub if_carry: HashMap<usize, Vec<usize>>, // if_node_ptr -> var indices
    /// For each condition node inside Ifs: carry_i = fv(then_i) ∩ fv(rest_after_i)
    pub ifs_cond_carry: HashMap<usize, Vec<usize>>, // cond_node_ptr -> var indices
    /// For each And node: carry = free_vars(lhs) ∩ free_vars(rhs)
    pub and_carry: HashMap<usize, Vec<usize>>, // and_node_ptr -> var indices
    /// For each Or node: carry = free_vars(lhs) ∩ free_vars(rhs)
    pub or_carry: HashMap<usize, Vec<usize>>, // or_node_ptr -> var indices
}

#[inline]
fn node_key(n: &Ast) -> usize {
    n as *const Ast as usize
}

impl Analysis {
    pub fn compute(ast: &Ast, var_index: &HashMap<String, usize>) -> Analysis {
        let mut ctx = Ctx {
            var_index,
            if_carry: HashMap::new(),
            ifs_cond_carry: HashMap::new(),
            and_carry: HashMap::new(),
            or_carry: HashMap::new(),
        };
        // run recursive traversal; we don't need the returned fv here.
        let _ = ctx.free_vars(ast);
        Analysis {
            if_carry: ctx.if_carry,
            ifs_cond_carry: ctx.ifs_cond_carry,
            and_carry: ctx.and_carry,
            or_carry: ctx.or_carry,
        }
    }
}

struct Ctx<'a> {
    var_index: &'a HashMap<String, usize>,
    if_carry: HashMap<usize, Vec<usize>>,
    ifs_cond_carry: HashMap<usize, Vec<usize>>,
    and_carry: HashMap<usize, Vec<usize>>,
    or_carry: HashMap<usize, Vec<usize>>,
}

impl<'a> Ctx<'a> {
    fn new_marks(&self) -> Vec<bool> {
        vec![false; self.var_index.len()]
    }

    fn or_inplace(dst: &mut [bool], src: &[bool]) {
        for (d, s) in dst.iter_mut().zip(src.iter()) {
            *d = *d || *s;
        }
    }
    fn and_to_indices(a: &[bool], b: &[bool]) -> Vec<usize> {
        let mut out = Vec::new();
        for (i, (&aa, &bb)) in a.iter().zip(b.iter()).enumerate() {
            if aa && bb {
                out.push(i);
            }
        }
        out
    }

    fn free_vars(&mut self, ast: &Ast) -> Vec<bool> {
        use Ast::*;
        match ast {
            Num(_) => self.new_marks(),
            Var(name) => {
                let mut m = self.new_marks();
                if let Some(&idx) = self.var_index.get(name) {
                    if let Some(slot) = m.get_mut(idx) {
                        *slot = true;
                    }
                }
                m
            }
            Neg(x) | Not(x) => self.free_vars(x),
            Add(a, b)
            | Sub(a, b)
            | Mul(a, b)
            | Div(a, b)
            | Pow(a, b)
            | Eq(a, b)
            | Ne(a, b)
            | Lt(a, b)
            | Le(a, b)
            | Gt(a, b)
            | Ge(a, b)
            | Max(a, b)
            | Min(a, b) => {
                let mut m = self.free_vars(a);
                let mb = self.free_vars(b);
                Self::or_inplace(&mut m, &mb);
                m
            }
            And(a, b) => {
                let mut fv_a = self.free_vars(a);
                let fv_b = self.free_vars(b);
                // carry = fv(lhs) ∩ fv(rhs)
                let carry = Self::and_to_indices(&fv_a, &fv_b);
                self.and_carry.insert(node_key(ast), carry);
                Self::or_inplace(&mut fv_a, &fv_b);
                fv_a
            }
            Or(a, b) => {
                let mut fv_a = self.free_vars(a);
                let fv_b = self.free_vars(b);
                // carry = fv(lhs) ∩ fv(rhs)
                let carry = Self::and_to_indices(&fv_a, &fv_b);
                self.or_carry.insert(node_key(ast), carry);
                Self::or_inplace(&mut fv_a, &fv_b);
                fv_a
            }
            If(c, t, e) => {
                let fv_c = self.free_vars(c);
                let fv_t = self.free_vars(t);
                let fv_e = self.free_vars(e);
                // carry set does not include cond vars; only intersection of then/else
                let carry = Self::and_to_indices(&fv_t, &fv_e);
                self.if_carry.insert(node_key(ast), carry);
                let mut m = fv_c;
                Self::or_inplace(&mut m, &fv_t);
                Self::or_inplace(&mut m, &fv_e);
                m
            }
            Ifs(list) => {
                // compute fv for each node first
                let mut fvs: Vec<Vec<bool>> = Vec::with_capacity(list.len());
                for n in list.iter() {
                    fvs.push(self.free_vars(n));
                }
                let n = list.len();
                // Build suffix OR array suf where suf[i] = OR of fvs[i..n)
                let mut suf: Vec<Vec<bool>> = vec![self.new_marks(); n + 1];
                // suf[n] is zeros by construction
                for i in (0..n).rev() {
                    let mut acc = suf[i + 1].clone();
                    Self::or_inplace(&mut acc, &fvs[i]);
                    suf[i] = acc;
                }
                // carries per (cond_i, then_i)
                let mut idx = 0usize;
                while idx + 1 < n {
                    let fv_then = &fvs[idx + 1];
                    // rest_after_i = OR of fvs[j] for j > idx+1 → suf[idx+2]
                    let fv_rest = &suf[(idx + 2).min(n)];
                    let carry = Self::and_to_indices(fv_then, fv_rest);
                    let cond_key = node_key(&list[idx]);
                    self.ifs_cond_carry.insert(cond_key, carry);
                    idx += 2;
                }
                // full fv of Ifs: OR of all children → suf[0]
                suf[0].clone()
            }
            Call { name: _name, args } => {
                let mut m = self.new_marks();
                for a in args.iter() {
                    let fv = self.free_vars(a);
                    Self::or_inplace(&mut m, &fv);
                }
                m
            }
        }
    }
}
