use std::{
    collections::{BTreeMap, BTreeSet},
    default,
};

use anyhow::Context;
use arena_traits::IndexAlloc;

use waffle::{
    cfg::CFGInfo, passes::basic_opt::value_is_pure, util::new_sig, Block, BlockTarget, Func,
    FunctionBody, Module, Operator, Terminator, Value, ValueDef,
};
pub mod bound;
pub fn tunnel(
    f: &mut FunctionBody,
    m: &mut Module,
    mut plugins: Vec<Box<dyn FnMut(&mut FunctionBody, &mut Module) -> anyhow::Result<bool>>>,
) -> anyhow::Result<()> {
    // let mut trials: usize = 0;
    // let mut plugins = plugins.into_iter().map(|a| (a, 0)).collect::<Vec<_>>();
    'a: loop {
        let mut t = Tunnel::default();
        for p in plugins.iter_mut() {
            // if *cd == 0 {
            if p(f, m)? {
                t.fused = true;
                // *cd = 8;
            }
            // } else {
            //     *cd -= 1;
            // }
        }
        let sig = new_sig(
            m,
            waffle::SignatureData::Func {
                params: f.blocks[f.entry].params.iter().map(|a| a.0).collect(),
                returns: f.rets.clone(),
            },
        );
        let mut new = FunctionBody::new(&m, sig);
        let e = t.translate(&mut new, &f, f.entry)?;
        new.entry = e;
        new.recompute_edges();
        *f = new;
        if !t.fused {
            // trials += 1;
            // if trials >= 4 {
            return Ok(());
            // }
        } else {
            // if trials < 4 {
            // trials = 0;
            // }
        };
        f.optimize(&Default::default());
        f.convert_to_max_ssa(None);
        // waffle::passes::tcore::tcore_tco_pass(m, fname, f)?;
    }
}
#[derive(Default)]
pub struct Tunnel {
    pub blocks: BTreeMap<Block, Block>,
    pub fused: bool,
}
impl Tunnel {
    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let new = dst.add_block();
            self.blocks.insert(k, new);
            let mut state = src.blocks[k]
                .params
                .iter()
                .map(|(k, v)| (*v, dst.add_blockparam(new, *k)))
                .collect::<BTreeMap<_, _>>();
            let mut k = k;
            let mut reloop = BTreeSet::new();
            reloop.insert(k);
            'b: loop {
                'a: for i in src.blocks[k].insts.iter().cloned() {
                    if value_is_pure(i, src) {
                        let mut unused = true;
                        for j in src.blocks[k].insts.iter().cloned() {
                            src.values[j].visit_uses(&src.arg_pool, |u| {
                                if u == i {
                                    unused = false;
                                }
                            });
                        }
                        src.blocks[k].terminator.visit_uses(|u| {
                            if u == i {
                                unused = false;
                            }
                        });
                        if unused {
                            continue 'a;
                        }
                    }
                    let v = match &src.values[i] {
                        waffle::ValueDef::BlockParam(block, _, _) => todo!(),
                        waffle::ValueDef::Operator(operator, list_ref, list_ref1) => {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .cloned()
                                .collect::<Vec<_>>();
                            let tys = &src.type_pool[*list_ref1];
                            dst.add_op(new, operator.clone(), &args, tys)
                        }
                        waffle::ValueDef::PickOutput(value, a, b) => {
                            let value = state
                                .get(value)
                                .cloned()
                                .context("in getting the referenced value")?;
                            let new_value = dst.values.alloc(ValueDef::PickOutput(value, *a, *b));
                            dst.append_to_block(new, new_value);
                            new_value
                        }
                        waffle::ValueDef::Alias(value) => state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?,
                        waffle::ValueDef::Placeholder(_) => todo!(),
                        waffle::ValueDef::None => dst.add_op(new, Operator::Nop, &[], &[]),
                    };
                    state.insert(i, v);
                }
                let mut target_ = |this: &mut Tunnel,
                                   dst: &mut FunctionBody,
                                   state: &mut BTreeMap<Value, Value>,
                                   k: &BlockTarget| {
                    anyhow::Ok(BlockTarget {
                        args: k
                            .args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .cloned()
                            .collect(),
                        block: this.translate(dst, src, k.block)?,
                    })
                };
                let mut ttr = |this: &mut Tunnel,
                               dst: &mut FunctionBody,
                               state: &mut BTreeMap<Value, Value>,
                               target: &BlockTarget| {
                    if reloop.contains(&target.block)
                    // || matches!(&src.blocks[target.block].terminator, Terminator::Br { .. })
                    {
                        anyhow::Ok(Ok(Terminator::Br {
                            target: target_(this, dst, state, target)?,
                        }))
                    } else {
                        reloop.insert(target.block);
                        // k = target.block;
                        *state = src.blocks[target.block]
                            .params
                            .iter()
                            .map(|a| a.1)
                            .zip(target.args.iter().cloned())
                            .collect();
                        this.fused = true;
                        Ok(Err(target.block))
                    }
                };
                let t = match &src.blocks[k].terminator {
                    waffle::Terminator::Br { target } => {
                        match ttr(self, dst, &mut state, target)? {
                            Ok(a) => a,
                            Err(e) => {
                                k = e;
                                continue 'b;
                            }
                        }
                    }
                    waffle::Terminator::CondBr {
                        cond,
                        if_true,
                        if_false,
                    } => {
                        // let if_true = target_(if_true)?;
                        // let if_false = target_(if_false)?;
                        let cond = state
                            .get(cond)
                            .cloned()
                            .context("in getting the referenced value")?;
                        match dst.values[cond].clone() {
                            ValueDef::Operator(Operator::I32Const { value }, _, _) => {
                                self.fused = true;
                                match ttr(
                                    self,
                                    dst,
                                    &mut state,
                                    if value != 0 { if_true } else { if_false },
                                )? {
                                    Ok(a) => a,
                                    Err(e) => {
                                        k = e;
                                        continue 'b;
                                    }
                                }
                            }
                            ValueDef::Operator(Operator::I64Const { value }, _, _) => {
                                self.fused = true;
                                match ttr(
                                    self,
                                    dst,
                                    &mut state,
                                    if value != 0 { if_true } else { if_false },
                                )? {
                                    Ok(a) => a,
                                    Err(e) => {
                                        k = e;
                                        continue 'b;
                                    }
                                }
                            }
                            _ => waffle::Terminator::CondBr {
                                cond,
                                if_true: target_(self, dst, &mut state, if_true)?,
                                if_false: target_(self, dst, &mut state, if_false)?,
                            },
                        }
                    }
                    waffle::Terminator::Select {
                        value,
                        targets,
                        default,
                    } => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        match dst.values[value].clone() {
                            ValueDef::Operator(Operator::I32Const { value }, _, _) => {
                                self.fused = true;
                                match ttr(
                                    self,
                                    dst,
                                    &mut state,
                                    targets.get(value as usize).unwrap_or(default),
                                )? {
                                    Ok(a) => a,
                                    Err(e) => {
                                        k = e;
                                        continue 'b;
                                    }
                                }
                            }
                            ValueDef::Operator(Operator::I64Const { value }, _, _) => {
                                self.fused = true;
                                match ttr(
                                    self,
                                    dst,
                                    &mut state,
                                    targets.get(value as usize).unwrap_or(default),
                                )? {
                                    Ok(a) => a,
                                    Err(e) => {
                                        k = e;
                                        continue 'b;
                                    }
                                }
                            }
                            _ => {
                                let default = target_(self, dst, &mut state, default)?;
                                let targets = targets
                                    .iter()
                                    .map(|x| target_(self, dst, &mut state, x))
                                    .collect::<anyhow::Result<Vec<_>>>()?;
                                waffle::Terminator::Select {
                                    value,
                                    targets,
                                    default,
                                }
                            }
                        }
                    }
                    waffle::Terminator::Return { values } => waffle::Terminator::Return {
                        values: values
                            .iter()
                            .filter_map(|b| state.get(b))
                            .cloned()
                            .collect(),
                    },
                    waffle::Terminator::ReturnCall { func, args } => {
                        waffle::Terminator::ReturnCall {
                            func: *func,
                            args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                        }
                    }
                    waffle::Terminator::ReturnCallIndirect { sig, table, args } => {
                        waffle::Terminator::ReturnCallIndirect {
                            sig: *sig,
                            table: *table,
                            args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                        }
                    }
                    waffle::Terminator::ReturnCallRef { sig, args } => {
                        waffle::Terminator::ReturnCallRef {
                            sig: *sig,
                            args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                        }
                    }
                    waffle::Terminator::Unreachable => waffle::Terminator::Unreachable,
                    waffle::Terminator::None => waffle::Terminator::None,
                    _ => waffle::Terminator::None,
                };
                dst.set_terminator(new, t);
                break 'b;
            }
        });
    }
}
