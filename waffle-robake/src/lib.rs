use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet},
};

use itertools::Itertools;
use once_map::{OnceMap, RandomState};
use waffle::{
    copying::fcopy::{obf_mod, DontObf, Obfuscate},
    entity::PerEntity,
    Block, BlockTarget, Func, Memory, MemoryArg, Module, Operator, Type,
};
use waffle_ast::bulk_memory_lowering::LowerBulkMemory;
pub struct Robake {
    pub rom: PerEntity<Memory, BTreeMap<u64, u8>>,
    pub rf: Option<Func>,
}
impl Robake {
    pub fn from_vals(m: &Module, i: PerEntity<Memory, BTreeSet<u64>>) -> Self {
        let mut x: PerEntity<Memory, BTreeMap<u64, u8>> = PerEntity::default();
        for (m, d) in m.memories.entries() {
            x[m] = i[m]
                .iter()
                .cloned()
                .filter_map(|a| {
                    Some((
                        a,
                        d.segments
                            .iter()
                            .find_map(|s| {
                                let a = a.checked_sub(s.offset as u64)?;
                                s.data.get(a as usize).cloned()
                            })
                            .unwrap_or(0),
                    ))
                })
                .collect();
        }
        return Self { rom: x, rf: None };
    }
    pub fn from_map(m: &Module, x: impl Iterator<Item = u8>, mem: Memory) -> Self {
        let mut i: PerEntity<Memory, BTreeSet<u64>> = PerEntity::default();
        i[mem].extend(
            x.batching(|mut i| i.next_array())
                .map(|a| u64::from_le_bytes(a))
                .tuples()
                .flat_map(|(a, b)| a..b),
        );
        return Self::from_vals(m, i);
    }
    pub fn bake(&mut self, m: &mut Module) -> anyhow::Result<()> {
        obf_mod(m, &mut LowerBulkMemory {})?;
        // obf_mod(
        //     m,
        //     &mut waffle_ast::bulk_memory_lowering::Reload {
        //         wrapped: DontObf {},
        //     },
        // )?;
        return obf_mod(m, self);
    }
    fn redo(
        &mut self,
        o: waffle::Operator,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut waffle::Module,
        memory: MemoryArg,
        mut unpack: impl FnMut(&mut (dyn Iterator<Item = Option<u8>> + '_)) -> Option<Option<u64>>,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        let n = f.add_block();
        let fb = f.add_block();
        {
            let (a, fb) = DontObf {}.obf(o, f, fb, args, types, module)?;
            f.set_terminator(
                fb,
                waffle::Terminator::Br {
                    target: BlockTarget {
                        block: n,
                        args: vec![a],
                    },
                },
            );
        };
        let bs: OnceMap<u64, Box<Block>, RandomState> = Default::default();
        // let mut mr = self.rom[memory.memory]
        //     .iter()
        //     .filter_map(|(a, b)| Some((a.checked_sub(memory.offset)?, *b)))
        //     .collect::<BTreeMap<_, _>>();
        let base = self.rom[memory.memory].keys().cloned().min().unwrap_or(0);
        let cases = (base..(match self.rom[memory.memory].keys().cloned().max() {
            None => 0,
            Some(a) => a + 1,
        }))
            .filter_map(|a| a.checked_sub(memory.offset))
            .map(|a| self.rom[memory.memory].get(&(a + memory.offset)).cloned())
            .collect_vec()
            .into_iter()
            .batching(move |a| unpack(a))
            .map(|a| match a {
                None => BlockTarget {
                    block: fb,
                    args: vec![],
                },
                Some(a) => BlockTarget {
                    block: *bs.insert(a as u64, |_| {
                        // let i = a as usize;
                        let b = f.add_block();
                        let i = f.add_op(b, Operator::I64Const { value: a }, &[], &[Type::I64]);
                        let i = if types[0] == Type::I32 {
                            f.add_op(b, Operator::I32WrapI64, &[i], &[Type::I32])
                        } else {
                            i
                        };
                        let i = match self.rf {
                            None => i,
                            Some(r) => f.add_op(
                                b,
                                Operator::Call { function_index: r },
                                &[i],
                                &[Type::I32],
                            ),
                        };
                        f.set_terminator(
                            b,
                            waffle::Terminator::Br {
                                target: BlockTarget {
                                    block: n,
                                    args: vec![i],
                                },
                            },
                        );
                        Box::new(b)
                    }),
                    args: vec![],
                },
            })
            .collect::<Vec<_>>();
        let mut r = args[0];
        let k = f.add_op(
            b,
            if module.memories[memory.memory].memory64 {
                Operator::I64Const { value: base }
            } else {
                Operator::I32Const {
                    value: (base & 0xffffffff) as u32,
                }
            },
            &[],
            if module.memories[memory.memory].memory64 {
                &[Type::I64]
            } else {
                &[Type::I32]
            },
        );
        r = f.add_op(
            b,
            if module.memories[memory.memory].memory64 {
                Operator::I64Sub
            } else {
                Operator::I32Sub
            },
            &[r, k],
            if module.memories[memory.memory].memory64 {
                &[Type::I64]
            } else {
                &[Type::I32]
            },
        );
        f.set_terminator(
            b,
            waffle::Terminator::Select {
                value: r,
                targets: cases,
                default: BlockTarget {
                    block: fb,
                    args: vec![],
                },
            },
        );
        return Ok((f.add_blockparam(n, Type::I32), n));
    }
}
macro_rules! ttr {
    ($a:expr) => {
        match $a {
            Some(Some(b)) => b,
            Some(None) => return Some(None),
            None => return None,
        }
    };
}
impl Obfuscate for Robake {
    fn obf(
        &mut self,
        o: waffle::Operator,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut waffle::Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        if let Operator::I32Load8U { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                a.next().map(|a| a.map(|b| b as u64))
            });
        }
        if let Operator::I32Load8S { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                a.next().map(|a| a.map(|b| b as i8 as i64 as u64))
            });
        }
        if let Operator::I32Load16U { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(
                    u16::from_le_bytes([ttr!(a.next()), ttr!(a.next())]) as u64
                ))
            });
        }
        if let Operator::I32Load16S { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(
                    u16::from_le_bytes([ttr!(a.next()), ttr!(a.next())]) as i16 as i64 as u64,
                ))
            });
        }
        if let Operator::I64Load8U { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                a.next().map(|a| a.map(|b| b as u64))
            });
        }
        if let Operator::I64Load8S { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                a.next().map(|a| a.map(|b| b as i8 as i64 as u64))
            });
        }
        if let Operator::I64Load16U { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(
                    u16::from_le_bytes([ttr!(a.next()), ttr!(a.next())]) as u64
                ))
            });
        }
        if let Operator::I64Load16S { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(
                    u16::from_le_bytes([ttr!(a.next()), ttr!(a.next())]) as i16 as i64 as u64,
                ))
            });
        }
        if let Operator::I64Load32U { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(u32::from_le_bytes([
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                ]) as u64))
            });
        }
        if let Operator::I64Load32S { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(u32::from_le_bytes([
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                ]) as i32 as i64 as u64))
            });
        }
        if let Operator::I32Load { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(u32::from_le_bytes([
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                ]) as u64))
            });
        }
        if let Operator::I64Load { memory } = o.clone() {
            return self.redo(o, f, b, args, types, module, memory, |a| {
                Some(Some(u64::from_le_bytes([
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                    ttr!(a.next()),
                ])))
            });
        }
        return DontObf {}.obf(o, f, b, args, types, module);
    }
}
