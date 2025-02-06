use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    default,
};

use anyhow::Context;
use arena_traits::IndexAlloc;

use waffle::{
    cfg::CFGInfo, const_eval, passes::basic_opt::value_is_pure, util::new_sig, Block, BlockTarget,
    ConstVal, Func, FunctionBody, Module, Operator, Terminator, Type, Value, ValueDef,
};
pub mod bound;
pub fn tunnel(
    f: &mut FunctionBody,
    m: &mut Module,
    mut plugins: Vec<Box<dyn FnMut(&mut FunctionBody, &mut Module) -> anyhow::Result<bool>>>,
    pinners: BTreeSet<Func>,
) -> anyhow::Result<()> {
    // let mut trials: usize = 0;
    // let mut plugins = plugins.into_iter().map(|a| (a, 0)).collect::<Vec<_>>();
    'a: loop {
        let mut t = Tunnel::default();
        t.peggers = pinners.clone();
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
        let e = t.translate(
            &mut new,
            &f,
            f.entry,
            f.blocks[f.entry].params.iter().map(|_| None).collect(),
        )?;
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
    pub blocks: BTreeMap<Block, HashMap<Vec<Option<ConstVal>>, Block>>,
    pub fused: bool,
    pub peggers: BTreeSet<Func>,
}
fn co(x: &ConstVal, t: Type) -> Operator {
    match x {
        ConstVal::I32(a) => Operator::I32Const { value: *a },
        ConstVal::I64(a) => Operator::I64Const { value: *a },
        ConstVal::F32(a) => Operator::F32Const { value: *a },
        ConstVal::F64(a) => Operator::F64Const { value: *a },
        ConstVal::None => todo!(),
        ConstVal::Ref(func) => todo!(),
    }
}
impl Tunnel {
    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        splice: Vec<Option<ConstVal>>,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k).and_then(|a| a.get(&splice)) {
                return Ok(*l);
            }
            let new = dst.add_block();
            self.blocks
                .entry(k)
                .or_default()
                .insert(splice.clone(), new);
            let mut pegged = BTreeSet::new();
            let mut cvals = BTreeMap::new();
            let mut state = src.blocks[k]
                .params
                .iter()
                .zip(splice.iter())
                .map(|((k, v), s)| {
                    (
                        *v,
                        match s {
                            None => dst.add_blockparam(new, *k),
                            Some(x) => {
                                let v = dst.add_op(new, co(x, *k), &[], &[*k]);
                                pegged.insert(v);
                                cvals.insert(v, x.clone());
                                v
                            }
                        },
                    )
                })
                .collect::<BTreeMap<_, _>>();

            let mut k = k;
            let mut reloop = BTreeSet::new();
            reloop.insert(k);
            'b: loop {
                'a: for i in src.blocks[k].insts.iter().cloned() {
                    if state.contains_key(&i) {
                        continue 'a;
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
                            let mut pegged2 = false;
                            let v = if self
                                .peggers
                                .iter()
                                .any(|p| *operator == Operator::Call { function_index: *p })
                            {
                                pegged2 = true;
                                let v = dst.values.push(ValueDef::Alias(args[0]));
                                dst.append_to_block(new, v);
                                v
                            } else {
                                dst.add_op(new, operator.clone(), &args, tys)
                            };
                            if args.iter().all(|a| cvals.contains_key(a)) {
                                if let Some(cv) = const_eval(
                                    operator,
                                    &args
                                        .iter()
                                        .flat_map(|a| cvals.get(a))
                                        .cloned()
                                        .collect::<Vec<_>>(),
                                    None,
                                )
                                .or_else(|| pegged2.then(|| cvals.get(&args[0]).cloned()).flatten())
                                {
                                    cvals.insert(v, cv);
                                }
                            }
                            if (args.iter().any(|a| pegged.contains(a)) || pegged2)
                                && cvals.contains_key(&v)
                            {
                                pegged.insert(v);
                            }

                            v
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
                                   k: &BlockTarget,
                                   a: Option<(Value, ConstVal)>| {
                    let mut p = vec![];
                    let args = k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .filter_map(|v| {
                            if pegged.contains(&v) {
                                let c = cvals.get(&v).cloned().unwrap();
                                p.push(Some(c));
                                None
                            } else {
                                match a {
                                    // Some((w, c)) if v == w => {
                                    //     p.push(Some(c));
                                    //     None
                                    // }
                                    _ => {
                                        p.push(None);
                                        Some(v)
                                    }
                                }
                            }
                        })
                        .collect();
                    anyhow::Ok(BlockTarget {
                        args: args,
                        block: this.translate(dst, src, k.block, p)?,
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
                            target: target_(this, dst, state, target, None)?,
                        }))
                    } else {
                        reloop.insert(target.block);
                        // k = target.block;
                        *state = src.blocks[target.block]
                            .params
                            .iter()
                            .map(|a| a.1)
                            .zip(target.args.iter().filter_map(|v| state.get(v)).cloned())
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
                        match cvals.get(&cond).cloned() {
                            Some(ConstVal::I32(value)) => {
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
                            Some(ConstVal::I64(value)) => {
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
                            _ => {
                                let tv = match dst.values[cond].ty(&dst.type_pool) {
                                    Some(Type::I32) => ConstVal::I32(0),
                                    Some(Type::I64) => ConstVal::I64(0),
                                    _ => todo!(),
                                };
                                waffle::Terminator::CondBr {
                                    cond,
                                    if_true: target_(self, dst, &mut state, if_true, None)?,
                                    if_false: target_(
                                        self,
                                        dst,
                                        &mut state,
                                        if_false,
                                        Some((cond, tv)),
                                    )?,
                                }
                            }
                        }
                    }
                    waffle::Terminator::Select {
                        value,
                        targets,
                        default,
                    } => {
                        // let ov = *value;
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        match cvals.get(&value).cloned() {
                            Some(ConstVal::I32(value2)) => {
                                self.fused = true;
                                // pegged.insert(value);
                                match ttr(
                                    self,
                                    dst,
                                    &mut state,
                                    targets.get(value2 as usize).unwrap_or(default),
                                )? {
                                    Ok(a) => a,
                                    Err(e) => {
                                        k = e;
                                        continue 'b;
                                    }
                                }
                            }
                            Some(ConstVal::I64(value2)) => {
                                self.fused = true;
                                // pegged.insert(value);
                                match ttr(
                                    self,
                                    dst,
                                    &mut state,
                                    targets.get(value2 as usize).unwrap_or(default),
                                )? {
                                    Ok(a) => a,
                                    Err(e) => {
                                        k = e;
                                        continue 'b;
                                    }
                                }
                            }
                            _ => {
                                let default = target_(self, dst, &mut state, default, None)?;
                                let targets = targets
                                    .iter()
                                    .enumerate()
                                    .map(|(i, x)| {
                                        let tv = match dst.values[value].ty(&dst.type_pool) {
                                            Some(Type::I32) => {
                                                ConstVal::I32((i as u64 & 0xffffffff) as u32)
                                            }
                                            Some(Type::I64) => ConstVal::I64(i as u64),
                                            _ => todo!(),
                                        };
                                        target_(self, dst, &mut state, x, Some((value, tv)))
                                    })
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
