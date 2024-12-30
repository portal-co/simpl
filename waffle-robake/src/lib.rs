use std::collections::{BTreeMap, BTreeSet};

use waffle::{
    copying::fcopy::{DontObf, Obfuscate},
    entity::PerEntity,
    Block, BlockTarget, Memory, Module, Operator, Type,
};

pub struct Robake {
    pub rom: PerEntity<Memory, BTreeMap<u64, u8>>,
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
                        d.segments.iter().find_map(|s| {
                            let a = a.checked_sub(s.offset as u64)?;
                            s.data.get(a as usize).cloned()
                        })?,
                    ))
                })
                .collect();
        }
        return Self { rom: x };
    }
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
            let bs: [Block; 256] = std::array::from_fn(|i| {
                let b = f.add_block();
                let i = f.add_op(b, Operator::I32Const { value: i as u32 }, &[], &[Type::I32]);
                f.set_terminator(
                    b,
                    waffle::Terminator::Br {
                        target: BlockTarget {
                            block: n,
                            args: vec![i],
                        },
                    },
                );
                b
            });
            // let mut mr = self.rom[memory.memory]
            //     .iter()
            //     .filter_map(|(a, b)| Some((a.checked_sub(memory.offset)?, *b)))
            //     .collect::<BTreeMap<_, _>>();
            let cases = (0..(match self.rom[memory.memory].keys().cloned().max() {
                None => 0,
                Some(a) => a + 1,
            }))
                .filter_map(|a| a.checked_sub(memory.offset))
                .map(
                    |a| match self.rom[memory.memory].get(&(a + memory.offset)).cloned() {
                        None => BlockTarget {
                            block: fb,
                            args: vec![],
                        },
                        Some(a) => BlockTarget {
                            block: bs[a as usize],
                            args: vec![],
                        },
                    },
                )
                .collect::<Vec<_>>();
            f.set_terminator(
                b,
                waffle::Terminator::Select {
                    value: args[0],
                    targets: cases,
                    default: BlockTarget {
                        block: fb,
                        args: vec![],
                    },
                },
            );
            return Ok((f.add_blockparam(n, Type::I32), n));
        }
        return DontObf {}.obf(o, f, b, args, types, module);
    }
}
