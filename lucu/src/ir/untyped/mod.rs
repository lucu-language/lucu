use std::collections::HashMap;
use std::ops::Index;
use std::sync::Arc;

use compact_str::CompactString;
use indexmap::IndexSet;

use crate::module::Module;

pub mod display;
pub mod lower;

#[derive(Default, Debug)]
pub struct IR {
    kinds: IndexSet<KindStruct>,
    types: IndexSet<TypeEnum>,
    regions: IndexSet<RegionEnum>,
}

#[derive(Default, Debug)]
pub struct Untyped {
    items: HashMap<CompactString, Item>,
}

#[derive(Debug)]
pub enum Item {
    Alias(Kind, Term),
    Struct(Kind, Vec<StructMember>),
    Effect,
    EffectFunction,
    Function,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum IntSize {
    Exact(usize),
    Register,
    Address,
    Index,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct GenericParameter {
    /// a De Bruijn index
    pub index: usize,
    pub apply: Option<Arc<[GenericArgument]>>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Integer {
    signed: bool,
    size: IntSize,
}

impl Integer {
    pub const fn signed(size: IntSize) -> Self {
        Self { signed: true, size }
    }
    pub const fn unsigned(size: IntSize) -> Self {
        Self {
            signed: false,
            size,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum TypeEnum {
    Generic(GenericParameter),
    Struct(Module, CompactString, Option<Arc<[GenericArgument]>>),
    Integer(Integer),
    Pointer(Type, Region),
    Slice(Type, Region),
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum RegionEnum {
    Generic(GenericParameter),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum KindEnum {
    Type,
    Effect,
    Region,
    Constant(Type),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct KindStruct {
    params: Option<Arc<[Kind]>>,
    output: KindEnum,
}

impl KindStruct {
    pub const TYPE: KindStruct = KindStruct {
        params: None,
        output: KindEnum::Type,
    };
    pub const EFFECT: KindStruct = KindStruct {
        params: None,
        output: KindEnum::Effect,
    };
    pub const REGION: KindStruct = KindStruct {
        params: None,
        output: KindEnum::Region,
    };
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Type(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Region(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Kind(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Term {
    Type(Type),
    Region(Region),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct GenericArgument {
    pub term: Term,
    pub arity: Option<usize>,
}

impl Index<Type> for IR {
    type Output = TypeEnum;

    fn index(&self, index: Type) -> &Self::Output {
        &self.types[index.0]
    }
}

impl Index<Region> for IR {
    type Output = RegionEnum;

    fn index(&self, index: Region) -> &Self::Output {
        &self.regions[index.0]
    }
}

impl Index<Kind> for IR {
    type Output = KindStruct;

    fn index(&self, index: Kind) -> &Self::Output {
        &self.kinds[index.0]
    }
}

impl IR {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert_type(&mut self, value: TypeEnum) -> Type {
        Type(self.types.insert_full(value).0)
    }
    pub fn insert_region(&mut self, value: RegionEnum) -> Region {
        Region(self.regions.insert_full(value).0)
    }
    pub fn insert_kind(&mut self, value: KindStruct) -> Kind {
        Kind(self.kinds.insert_full(value).0)
    }
}

pub trait Substitute {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self;
}

impl GenericParameter {
    fn instantiate(self, ir: &mut IR, arg: GenericArgument) -> Term {
        match &self.apply {
            Some(apply) => {
                assert_eq!(arg.arity, Some(apply.len()));
                arg.term.subst(ir, 0, apply)
            }
            None => {
                assert_eq!(arg.arity, None);
                arg.term
            }
        }
    }
}

impl Substitute for GenericParameter {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self {
        GenericParameter {
            index: if self.index < start + args.len() {
                self.index
            } else {
                self.index - args.len()
            },
            apply: self
                .apply
                .map(|apply| apply.iter().map(|arg| arg.subst(ir, start, args)).collect()),
        }
    }
}

impl Substitute for GenericArgument {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self {
        GenericArgument {
            term: self.term.subst(ir, start + self.arity.unwrap_or(0), args),
            arity: self.arity,
        }
    }
}

impl Substitute for Term {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.subst(ir, start, args)),
            Term::Region(region) => Term::Region(region.subst(ir, start, args)),
        }
    }
}

impl Substitute for Type {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match ir[self] {
            TypeEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(ir, start, args);
                if let Some(arg) = index.and_then(|i| args.get(i).copied()) {
                    match generic.instantiate(ir, arg) {
                        Term::Type(ty) => return ty,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    TypeEnum::Generic(generic)
                }
            }
            TypeEnum::Struct(ref module, ref name, ref types) => {
                let module = module.clone();
                let name = name.clone();
                let types = types.clone();
                TypeEnum::Struct(
                    module,
                    name,
                    types.map(|types| types.iter().map(|ty| ty.subst(ir, start, args)).collect()),
                )
            }
            TypeEnum::Pointer(ty, region) => {
                TypeEnum::Pointer(ty.subst(ir, start, args), region.subst(ir, start, args))
            }
            TypeEnum::Slice(ty, region) => {
                TypeEnum::Slice(ty.subst(ir, start, args), region.subst(ir, start, args))
            }
            TypeEnum::Integer(_) => return self,
        };
        ir.insert_type(changed)
    }
}

impl Substitute for Region {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match ir[self] {
            RegionEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(ir, start, args);
                if let Some(arg) = index.and_then(|i| args.get(i).copied()) {
                    match generic.instantiate(ir, arg) {
                        Term::Region(region) => return region,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    RegionEnum::Generic(generic)
                }
            }
        };
        ir.insert_region(changed)
    }
}

impl Substitute for Kind {
    fn subst(self, ir: &mut IR, start: usize, args: &[GenericArgument]) -> Self {
        let params = ir[self].params.clone().map(|params| {
            params
                .iter()
                .map(|arg| arg.subst(ir, start, args))
                .collect()
        });
        let output = match ir[self].output {
            KindEnum::Constant(ty) => KindEnum::Constant(ty.subst(ir, start, args)),
            k => k,
        };
        ir.insert_kind(KindStruct { params, output })
    }
}
