use std::mem::swap;

use waffle::{
    copying::fcopy::{obf_fn_body, DontObf, Obfuscate},
    BlockTarget, Func, FunctionBody, Module, Operator, ValueDef,
};

pub struct Bound {
    pub next_era: bool,
    pub era: bool,
    pub binders: Binders,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub struct Binders {
    pub u32: Option<Func>,
    pub u64: Option<Func>,
}
pub fn bound(b: Binders) -> Box<dyn FnMut(&mut FunctionBody, &mut Module) -> anyhow::Result<bool>> {
    let mut b = Bound {
        next_era: false,
        era: false,
        binders: b,
    };
    return Box::new(move |f, m| {
        swap(&mut b.next_era, &mut b.era);
        obf_fn_body(m, f, &mut b)?;
        return Ok(b.next_era);
    });
}
impl Obfuscate for Bound {
    fn obf(
        &mut self,
        o: waffle::Operator,
        f: &mut waffle::FunctionBody,
        mut b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut waffle::Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        if self.era {
            self.next_era = false;
            return DontObf {}.obf(o, f, b, args, types, module);
        }
        if let Operator::I32RemU | Operator::I32RemS = o {
            if let ValueDef::Operator(Operator::I32Const { value }, _, _) =
                f.values[args[1]].clone()
            {
                if value < 256 {
                    self.next_era = true;
                    let a;
                    (a, b) = DontObf {}.obf(o, f, b, args, types, module)?;
                    let n = f.add_block();
                    let ks = (0..value)
                        .map(|x| {
                            let c = f.add_block();
                            let mut cv = f.add_op(c, Operator::I32Const { value: x }, &[], types);
                            if let Some(b) = self.binders.u32 {
                                cv =
                                    f.add_op(c, Operator::Call { function_index: b }, &[cv], types);
                            }
                            f.set_terminator(
                                c,
                                waffle::Terminator::Br {
                                    target: BlockTarget {
                                        block: n,
                                        args: vec![cv],
                                    },
                                },
                            );
                            BlockTarget {
                                block: c,
                                args: vec![],
                            }
                        })
                        .collect::<Vec<_>>();
                    let u = f.add_block();
                    f.set_terminator(u, waffle::Terminator::Unreachable);
                    f.set_terminator(
                        b,
                        waffle::Terminator::Select {
                            value: a,
                            targets: ks,
                            default: BlockTarget {
                                block: u,
                                args: vec![],
                            },
                        },
                    );
                    return Ok((f.add_blockparam(n, types[0].clone()), n));
                }
            }
        }
        if let Operator::I32And = o {
            for a in args.iter().cloned() {
                if let ValueDef::Operator(Operator::I32Const { value }, _, _) = f.values[a].clone()
                {
                    if value < 256 {
                        self.next_era = true;
                        let a;
                        (a, b) = DontObf {}.obf(o, f, b, args, types, module)?;
                        let n = f.add_block();
                        let ks = (0..=value)
                            .map(|x| {
                                let c = f.add_block();
                                let mut cv =
                                    f.add_op(c, Operator::I32Const { value: x }, &[], types);
                                if let Some(b) = self.binders.u32 {
                                    cv = f.add_op(
                                        c,
                                        Operator::Call { function_index: b },
                                        &[cv],
                                        types,
                                    );
                                }
                                f.set_terminator(
                                    c,
                                    waffle::Terminator::Br {
                                        target: BlockTarget {
                                            block: n,
                                            args: vec![cv],
                                        },
                                    },
                                );
                                BlockTarget {
                                    block: c,
                                    args: vec![],
                                }
                            })
                            .collect::<Vec<_>>();
                        let u = f.add_block();
                        f.set_terminator(u, waffle::Terminator::Unreachable);
                        f.set_terminator(
                            b,
                            waffle::Terminator::Select {
                                value: a,
                                targets: ks,
                                default: BlockTarget {
                                    block: u,
                                    args: vec![],
                                },
                            },
                        );
                        return Ok((f.add_blockparam(n, types[0].clone()), n));
                    }
                }
            }
        }
        if let Operator::I64RemU | Operator::I64RemS = o {
            if let ValueDef::Operator(Operator::I64Const { value }, _, _) =
                f.values[args[1]].clone()
            {
                if value < 256 {
                    self.next_era = true;
                    let a;
                    (a, b) = DontObf {}.obf(o, f, b, args, types, module)?;
                    let n = f.add_block();
                    let ks = (0..value)
                        .map(|x| {
                            let c = f.add_block();
                            let mut cv = f.add_op(c, Operator::I64Const { value: x }, &[], types);
                            if let Some(b) = self.binders.u64 {
                                cv =
                                    f.add_op(c, Operator::Call { function_index: b }, &[cv], types);
                            }
                            f.set_terminator(
                                c,
                                waffle::Terminator::Br {
                                    target: BlockTarget {
                                        block: n,
                                        args: vec![cv],
                                    },
                                },
                            );
                            BlockTarget {
                                block: c,
                                args: vec![],
                            }
                        })
                        .collect::<Vec<_>>();
                    let u = f.add_block();
                    f.set_terminator(u, waffle::Terminator::Unreachable);
                    f.set_terminator(
                        b,
                        waffle::Terminator::Select {
                            value: a,
                            targets: ks,
                            default: BlockTarget {
                                block: u,
                                args: vec![],
                            },
                        },
                    );
                    return Ok((f.add_blockparam(n, types[0].clone()), n));
                }
            }
        }
        if let Operator::I64And = o {
            for a in args.iter().cloned() {
                if let ValueDef::Operator(Operator::I64Const { value }, _, _) = f.values[a].clone()
                {
                    if value < 256 {
                        self.next_era = true;
                        let a;
                        (a, b) = DontObf {}.obf(o, f, b, args, types, module)?;
                        let n = f.add_block();
                        let ks = (0..=value)
                            .map(|x| {
                                let c = f.add_block();
                                let mut cv =
                                    f.add_op(c, Operator::I64Const { value: x }, &[], types);
                                if let Some(b) = self.binders.u64 {
                                    cv = f.add_op(
                                        c,
                                        Operator::Call { function_index: b },
                                        &[cv],
                                        types,
                                    );
                                }
                                f.set_terminator(
                                    c,
                                    waffle::Terminator::Br {
                                        target: BlockTarget {
                                            block: n,
                                            args: vec![cv],
                                        },
                                    },
                                );
                                BlockTarget {
                                    block: c,
                                    args: vec![],
                                }
                            })
                            .collect::<Vec<_>>();
                        let u = f.add_block();
                        f.set_terminator(u, waffle::Terminator::Unreachable);
                        f.set_terminator(
                            b,
                            waffle::Terminator::Select {
                                value: a,
                                targets: ks,
                                default: BlockTarget {
                                    block: u,
                                    args: vec![],
                                },
                            },
                        );
                        return Ok((f.add_blockparam(n, types[0].clone()), n));
                    }
                }
            }
        }
        return DontObf {}.obf(o, f, b, args, types, module);
    }
}
