use std::{
    collections::BTreeMap,
    default, iter,
    mem::{replace, swap},
};

use anyhow::Context;
use arena_traits::IndexAlloc;

use either::Either;
use itertools::Itertools;
use rand::{
    distributions::{DistString, Standard},
    seq::SliceRandom,
    Rng, SeedableRng,
};
use waffle::{
    cfg::CFGInfo, passes::basic_opt::value_is_pure, util::new_sig, Block, BlockTarget, Export,
    FunctionBody, Module, Operator, SignatureData, Terminator, Type, ValueDef,
};
#[derive(Default)]
pub struct Shf<R> {
    pub blocks: BTreeMap<Block, Block>,
    pub rng: R,
    pub trick_tunnel: bool,
}
impl<R: Rng> Shf<R> {
    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        r#mod: &mut Module,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let mut new = dst.add_block();
            let mut state = src.blocks[k]
                .params
                .iter()
                .map(|(k, v)| (*v, dst.add_blockparam(new, *k)))
                .collect::<BTreeMap<_, _>>();
            self.blocks.insert(k, new);
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
                let v = if self.trick_tunnel && self.rng.gen() {
                    let t = dst.values[v].ty(&dst.type_pool);
                    match t {
                        None => v,
                        Some(t) => {
                            let s = new_sig(
                                r#mod,
                                SignatureData::Func {
                                    params: vec![t.clone()],
                                    returns: vec![t.clone()],
                                },
                            );
                            let mut b = FunctionBody::new(r#mod, s);
                            b.set_terminator(
                                b.entry,
                                Terminator::Return {
                                    values: b.blocks[b.entry].params.iter().map(|p| p.1).collect(),
                                },
                            );
                            let b = r#mod.funcs.push(waffle::FuncDecl::Body(
                                s,
                                Standard.sample_string(&mut self.rng, 32),
                                b,
                            ));
                            r#mod.exports.push(Export {
                                name: format!(
                                    "@tunnel_marker/{}",
                                    Standard.sample_string(&mut self.rng, 32)
                                ),
                                kind: waffle::ExportKind::Func(b),
                            });
                            dst.add_op(new, Operator::Call { function_index: b }, &[v], &[t])
                        }
                    }
                } else {
                    v
                };
                state.insert(i, v);
                let t = dst.values[v].ty(&dst.type_pool);
                if let Some((t, op, v)) = t.and_then(|ty| match ty {
                    Type::I32 => Some((ty, Operator::I32Eqz, v)),
                    Type::I64 => Some((ty, Operator::I64Eqz, v)),
                    _ => None,
                }) {
                    if self.rng.gen_range(0..32) < 3 {
                        let n2 = dst.add_block();
                        let cond = dst.add_op(new, op, &[v], &[Type::I32]);
                        dst.set_terminator(
                            new,
                            Terminator::CondBr {
                                cond,
                                if_true: BlockTarget {
                                    block: n2,
                                    args: vec![],
                                },
                                if_false: BlockTarget {
                                    block: n2,
                                    args: vec![],
                                },
                            },
                        );
                        new = n2;
                    }
                }
            }
            let mut target_ = |k: &BlockTarget| {
                anyhow::Ok(BlockTarget {
                    args: k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .collect(),
                    block: self.translate(dst, src, k.block, r#mod)?,
                })
            };
            let mut t = match &src.blocks[k].terminator {
                waffle::Terminator::Br { target } => waffle::Terminator::Br {
                    target: target_(target)?,
                },
                waffle::Terminator::CondBr {
                    cond,
                    if_true,
                    if_false,
                } => {
                    let if_true = target_(if_true)?;
                    let if_false = target_(if_false)?;
                    let cond = state
                        .get(cond)
                        .cloned()
                        .context("in getting the referenced value")?;
                    waffle::Terminator::CondBr {
                        cond,
                        if_true,
                        if_false,
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
                    let default = target_(default)?;
                    let targets = targets
                        .iter()
                        .map(target_)
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    waffle::Terminator::Select {
                        value,
                        targets,
                        default,
                    }
                }
                waffle::Terminator::Return { values } => waffle::Terminator::Return {
                    values: values
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .collect(),
                },
                waffle::Terminator::ReturnCall { func, args } => waffle::Terminator::ReturnCall {
                    func: *func,
                    args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                },
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
                _ => todo!(),
            };
            loop {
                if let Terminator::Br { target } = t {
                    let max: u8 = loop {
                        let a = self.rng.gen();
                        if a != 0 {
                            break a;
                        }
                    };
                    let sel = self.rng.gen_range(0..max);
                    let selv = dst.add_op(
                        new,
                        Operator::I32Const { value: sel as u32 },
                        &[],
                        &[Type::I32],
                    );
                    let sbs = src
                        .blocks
                        .iter()
                        .filter(|b| {
                            src.blocks[*b]
                                .params
                                .iter()
                                .map(|a| a.0)
                                .all(|t| matches!(t, Type::F32 | Type::F64 | Type::I32 | Type::I64))
                        })
                        .map(Either::Left)
                        .chain(
                            r#mod
                                .funcs
                                .iter()
                                .filter_map(|f| {
                                    let SignatureData::Func { params, returns } =
                                        r#mod.signatures[r#mod.funcs[f].sig()].clone()
                                    else {
                                        unreachable!()
                                    };
                                    if !params.iter().cloned().all(|t| {
                                        matches!(t, Type::F32 | Type::F64 | Type::I32 | Type::I64)
                                    }) {
                                        return None;
                                    }
                                    if returns != src.rets {
                                        return None;
                                    }
                                    return Some((f, params));
                                })
                                .map(Either::Right),
                        )
                        .collect::<Vec<_>>();
                    let mut alt = rand_chacha::ChaCha20Rng::from_rng(&mut self.rng)?;
                    let mut ts = iter::from_fn(move || sbs.choose(&mut alt).cloned())
                        .map(|k| {
                            let k = match k {
                                Either::Left(k) => self.translate(dst, src, k, r#mod)?,
                                Either::Right((f, params)) => {
                                    let k = dst.add_block();
                                    let vals = params
                                        .iter()
                                        .cloned()
                                        .map(|p| dst.add_blockparam(k, p))
                                        .collect();
                                    dst.set_terminator(
                                        k,
                                        Terminator::ReturnCall {
                                            func: f,
                                            args: vals,
                                        },
                                    );
                                    k
                                }
                            };
                            anyhow::Ok(BlockTarget {
                                block: k,
                                args: dst.blocks[k]
                                    .params
                                    .iter()
                                    .map(|a| a.0)
                                    .collect::<Vec<_>>()
                                    .into_iter()
                                    .filter_map(|t| {
                                        Some(match t {
                                            Type::I32 => dst.add_op(
                                                new,
                                                Operator::I32Const {
                                                    value: self.rng.gen(),
                                                },
                                                &[],
                                                &[t],
                                            ),
                                            Type::I64 => dst.add_op(
                                                new,
                                                Operator::I64Const {
                                                    value: self.rng.gen(),
                                                },
                                                &[],
                                                &[t],
                                            ),
                                            Type::F32 => dst.add_op(
                                                new,
                                                Operator::F32Const {
                                                    value: self.rng.gen(),
                                                },
                                                &[],
                                                &[t],
                                            ),
                                            Type::F64 => dst.add_op(
                                                new,
                                                Operator::F64Const {
                                                    value: self.rng.gen(),
                                                },
                                                &[],
                                                &[t],
                                            ),
                                            _ => return None,
                                        })
                                    })
                                    .collect(),
                            })
                        })
                        .take(max as usize)
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    let t2 = replace(&mut ts[sel as usize], target);

                    t = Terminator::Select {
                        value: selv,
                        targets: ts,
                        default: t2,
                    }
                } else {
                    if let Terminator::CondBr {
                        cond,
                        if_true,
                        if_false,
                    } = t
                    {
                        t = Terminator::Select {
                            value: cond,
                            targets: vec![if_false],
                            default: if_true,
                        }
                    }
                    if let Terminator::Select {
                        value,
                        targets,
                        default,
                    } = &mut t
                    {
                        let x: u8 = self.rng.gen();
                        for b in bit_iter::BitIter::from(x).map(|a| 2usize.pow((a + 1) as u32)) {
                            while targets.len() % b != 0 {
                                targets.push(default.clone());
                            }
                            for k in targets.chunks_mut(b) {
                                let (a, b) = k.split_at_mut(b / 2);
                                for (a, b) in a.iter_mut().zip(b.iter_mut()) {
                                    swap(a, b);
                                }
                            }
                        }
                        let x = dst.add_op(
                            new,
                            Operator::I32Const { value: x as u32 },
                            &[],
                            &[Type::I32],
                        );
                        *value = dst.add_op(new, Operator::I32Xor, &[*value, x], &[Type::I32]);
                    }
                }
                if self.rng.gen() {
                    break;
                }
                // if self.rng.gen() {
                let b = dst.add_block();
                dst.set_terminator(b, t);
                t = if self.rng.gen() {
                    Terminator::Br {
                        target: BlockTarget {
                            block: b,
                            args: vec![],
                        },
                        // }
                    }
                } else {
                    let mut i2 = src.blocks[k]
                        .insts
                        .iter()
                        .filter_map(|a| state.get(a))
                        .cloned()
                        .collect_vec();
                    let mut alt = rand_chacha::ChaCha20Rng::from_rng(&mut self.rng)?;
                    let cond = iter::from_fn(move || {
                        i2.shuffle(&mut alt);
                        return i2.pop();
                    })
                    .find_map(|x| {
                        let ty = dst.values[x].ty(&dst.type_pool)?;
                        match ty {
                            Type::I32 => Some((ty, Operator::I32Eqz, x)),
                            Type::I64 => Some((ty, Operator::I64Eqz, x)),
                            _ => None,
                        }
                    });
                    let cond = match cond {
                        None => dst.add_op(new, Operator::I32Const { value: 0 }, &[], &[Type::I32]),
                        Some((ty, s, x)) => dst.add_op(new, s, &[x], &[Type::I32]),
                    };
                    Terminator::CondBr {
                        if_true: BlockTarget {
                            block: b,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: b,
                            args: vec![],
                        },
                        cond, // }
                    }
                }
            }
            dst.set_terminator(new, t);
        });
    }
}
