use rand::{distributions::Standard, prelude::Distribution, Rng};
use rand_derive2::RandGen;
use waffle::{Block, FunctionBody, Operator, Type, Value};

#[derive(Clone, RandGen)]
pub enum AbiMod {
    Xor { a: u64 },
    Add { a: u64 },
    Compose{
        first: Box<AbiMod>,
        second: Box<AbiMod>
    },
    None
}
impl Distribution<Box<AbiMod>> for Standard{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Box<AbiMod> {
        Box::new(rng.gen())
    }
}
impl AbiMod {
    pub fn other(&self) -> AbiMod {
        match self {
            AbiMod::Xor { a } => AbiMod::Xor { a: *a },
            AbiMod::Add { a } => AbiMod::Add {
                a: -(*a as i64) as u64,
            },
            AbiMod::Compose { first, second } => AbiMod::Compose { first: Box::new(second.other()), second: Box::new(first.other()) },
            AbiMod::None => AbiMod::None,
        }
    }
    pub fn resty(&self, a: Type) -> Type{
        match self{
            AbiMod::Compose { first, second } => second.resty(first.resty(a)),
            _ => a
        }
    }
    pub fn apply(&self, f: &mut FunctionBody, b: Block, val: Value) -> Value {
        match (self, f.values[val].ty(&f.type_pool).unwrap()) {
            (AbiMod::Xor { a }, Type::I32) => {
                let s = f.add_op(
                    b,
                    Operator::I32Const {
                        value: (*a & 0xffffffff) as u32,
                    },
                    &[],
                    &[Type::I32],
                );
                f.add_op(b, Operator::I32Xor, &[val, s], &[Type::I32])
            }
            (AbiMod::Add { a }, Type::I32) => {
                let s = f.add_op(
                    b,
                    Operator::I32Const {
                        value: (*a & 0xffffffff) as u32,
                    },
                    &[],
                    &[Type::I32],
                );
                f.add_op(b, Operator::I32Add, &[val, s], &[Type::I32])
            }
            (AbiMod::Xor { a }, Type::I64) => {
                let s = f.add_op(b, Operator::I64Const { value: *a }, &[], &[Type::I64]);
                f.add_op(b, Operator::I64Xor, &[val, s], &[Type::I64])
            }
            (AbiMod::Add { a }, Type::I64) => {
                let s = f.add_op(b, Operator::I64Const { value: *a }, &[], &[Type::I64]);
                f.add_op(b, Operator::I64Add, &[val, s], &[Type::I64])
            }
            (AbiMod::Compose { first, second },_) => {
                let val = first.apply(f, b, val);
                second.apply(f, b, val)
            }
            _ => val,
        }
    }
}
