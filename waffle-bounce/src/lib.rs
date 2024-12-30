use std::collections::BTreeSet;

use waffle::{
    copying::{
        fcopy::{obf_mod, DontObf, Obfuscate},
        module::tree_shake,
    },
    util::new_sig,
    BlockTarget, ExportKind, FuncDecl, FunctionBody, HeapType, Module, Operator, SignatureData,
    Table, Terminator, Type, ValueDef, WithNullable,
};
pub fn bounce(m: &mut Module) -> anyhow::Result<()> {
    tree_shake(m)?;
    let mut b = PreBounce::new(m);
    obf_mod(m, &mut b)?;
    let mut b = b.next();
    obf_mod(m, &mut b)?;
    m.try_take_per_func_body(|m, f| {
        f.convert_to_max_ssa(None);
        let sig = new_sig(
            m,
            waffle::SignatureData::Func {
                params: f.blocks[f.entry].params.iter().map(|a| a.0).collect(),
                returns: f.rets.clone(),
            },
        );
        let mut new = FunctionBody::new(&m, sig);
        let e = waffle::passes::frint::Frint::default().translate_base(&mut new, f, f.entry)?;
        new.entry = e;
        new.recompute_edges();
        new.optimize(&Default::default());
        *f = new;

        anyhow::Ok(())
    })?;
    Ok(())
}
pub struct PreBounce {
    viable_tables: BTreeSet<Table>,
}
impl PreBounce {
    pub fn new(m: &Module) -> Self {
        return Self {
            viable_tables: m
                .tables
                .iter()
                .filter(|t| m.tables[*t].func_elements.is_some())
                .filter(|t| match &m.tables[*t].ty {
                    Type::Heap(WithNullable {
                        value: HeapType::FuncRef,
                        nullable,
                    }) => true,
                    Type::Heap(WithNullable {
                        value: HeapType::Sig { sig_index },
                        nullable,
                    }) => matches!(&m.signatures[*sig_index], SignatureData::Func { .. }),
                    _ => false,
                })
                .filter(|t| {
                    !m.imports
                        .iter()
                        .filter_map(|k| match &k.kind {
                            waffle::ImportKind::Table(table) => Some(table),
                            _ => None,
                        })
                        .chain(m.exports.iter().filter_map(|k| match &k.kind {
                            ExportKind::Table(t) => Some(t),
                            _ => None,
                        }))
                        .any(|x| x == t)
                })
                .filter(|t| {
                    !m.funcs
                        .iter()
                        .filter_map(|f| match &m.funcs[f] {
                            FuncDecl::Body(b_, _, b) => Some(b),
                            _ => None,
                        })
                        .flat_map(|b| {
                            b.values.iter().filter_map(|v| match &b.values[v] {
                                ValueDef::Operator(
                                    Operator::TableSet { table_index }
                                    | Operator::TableGrow { table_index },
                                    _,
                                    _,
                                ) => Some(table_index),
                                _ => None,
                            })
                        })
                        .any(|x| x == t)
                })
                .collect(),
        };
    }
    pub fn next(self) -> Bounce {
        return Bounce {
            viable_tables: self.viable_tables,
        };
    }
}
pub struct Bounce {
    viable_tables: BTreeSet<Table>,
}
impl Obfuscate for Bounce {
    fn obf(
        &mut self,
        o: Operator,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[Type],
        module: &mut waffle::Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        if let Operator::TableSize { table_index } = o.clone() {
            if self.viable_tables.contains(&table_index) {
                return self.obf(
                    if module.tables[table_index].table64 {
                        Operator::I64Const {
                            value: module.tables[table_index]
                                .func_elements
                                .as_ref()
                                .unwrap()
                                .len() as u64,
                        }
                    } else {
                        Operator::I32Const {
                            value: module.tables[table_index]
                                .func_elements
                                .as_ref()
                                .unwrap()
                                .len() as u32,
                        }
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                );
            }
        }
        if let Operator::TableGet { table_index } = o.clone() {
            if self.viable_tables.contains(&table_index) {
                let n = f.add_block();
                let elems = module.tables[table_index]
                    .func_elements
                    .iter()
                    .flatten()
                    .cloned()
                    .map(|a| {
                        let l = f.add_block();
                        let r = f.add_op(l, Operator::RefFunc { func_index: a }, &[], types);
                        f.set_terminator(
                            l,
                            Terminator::Br {
                                target: BlockTarget {
                                    block: n,
                                    args: vec![r],
                                },
                            },
                        );
                        return BlockTarget {
                            block: l,
                            args: vec![],
                        };
                    })
                    .collect::<Vec<_>>();
                let u = f.add_block();
                f.set_terminator(u, Terminator::Unreachable);
                f.set_terminator(
                    b,
                    Terminator::Select {
                        value: args[0],
                        targets: elems,
                        default: BlockTarget {
                            block: u,
                            args: vec![],
                        },
                    },
                );
                return Ok((f.add_blockparam(n, types[0].clone()), n));
            }
        }
        return DontObf {}.obf(o, f, b, args, types, module);
    }
}
impl Obfuscate for PreBounce {
    fn obf(
        &mut self,
        o: waffle::Operator,
        f: &mut waffle::FunctionBody,
        mut b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut waffle::Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        if let Operator::CallIndirect {
            sig_index,
            table_index,
        } = o.clone()
        {
            if self.viable_tables.contains(&table_index) {
                let mut a;
                a = f.add_op(
                    b,
                    Operator::TableGet {
                        table_index: table_index,
                    },
                    &[args[0]],
                    &[Type::Heap(WithNullable {
                        nullable: true,
                        value: waffle::HeapType::FuncRef,
                    })],
                );
                a = f.add_op(
                    b,
                    Operator::RefCast {
                        ty: Type::Heap(WithNullable {
                            value: HeapType::Sig { sig_index },
                            nullable: true,
                        }),
                    },
                    &[a],
                    &[Type::Heap(WithNullable {
                        value: HeapType::Sig { sig_index },
                        nullable: true,
                    })],
                );
                return self.obf(
                    Operator::CallRef { sig_index },
                    f,
                    b,
                    &vec![a]
                        .into_iter()
                        .chain(args.iter().cloned())
                        .collect::<Vec<_>>(),
                    types,
                    module,
                );
            }
        }
        return DontObf {}.obf(o, f, b, args, types, module);
    }
    fn obf_term(
        &mut self,
        t: waffle::Terminator,
        b: waffle::Block,
        f: &mut waffle::FunctionBody,
    ) -> anyhow::Result<()> {
        if let Terminator::ReturnCallIndirect {
            sig,
            table,
            mut args,
        } = t.clone()
        {
            if self.viable_tables.contains(&table) {
                let mut a;
                a = f.add_op(
                    b,
                    Operator::TableGet { table_index: table },
                    &[args.last().cloned().unwrap()],
                    &[Type::Heap(WithNullable {
                        nullable: true,
                        value: waffle::HeapType::FuncRef,
                    })],
                );
                a = f.add_op(
                    b,
                    Operator::RefCast {
                        ty: Type::Heap(WithNullable {
                            value: HeapType::Sig { sig_index: sig },
                            nullable: true,
                        }),
                    },
                    &[a],
                    &[Type::Heap(WithNullable {
                        value: HeapType::Sig { sig_index: sig },
                        nullable: true,
                    })],
                );
                *args.last_mut().unwrap() = a;
                return self.obf_term(Terminator::ReturnCallRef { sig, args }, b, f);
            }
        }
        return DontObf {}.obf_term(t, b, f);
    }
}
