use std::ops::Index;
use std::sync::Arc;

use compact_str::CompactString;
use indexmap::IndexSet;

use crate::module::Module;

pub mod display;
pub mod substitute;

#[derive(Default, Debug)]
pub struct TypeTable {
    kinds: IndexSet<KindEnum>,
    types: IndexSet<TypeEnum>,
    regions: IndexSet<RegionEnum>,
    effects: IndexSet<EffectEnum>,
    function_signatures: IndexSet<FunctionSignatureValue>,
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
    pub signed: bool,
    pub size: IntSize,
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

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Item {
    pub module: Module,
    pub name: CompactString,
    pub apply: Option<Arc<[GenericArgument]>>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum TypeEnum {
    Generic(GenericParameter),
    Item(Item),
    Integer(Integer),
    Boolean,
    Unit,
    Pointer(Type, Region),
    PointerSlice(Type, Region),
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum RegionEnum {
    Generic(GenericParameter),
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum EffectEnum {
    Generic(GenericParameter),
    Item(Item),
    Row(Arc<[Effect]>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum SimpleKind {
    Type,
    Effect,
    Region,
    Constant(Type),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct KindEnum {
    pub params: Option<Arc<[Kind]>>,
    pub output: SimpleKind,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FunctionSignatureValue {
    pub type_params: Option<Arc<[Kind]>>,
    pub params: Option<Arc<[FunctionParameter]>>,
    pub returns: FunctionReturns,
    pub effects: Arc<[Effect]>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum FunctionParameter {
    Data(Type),
    Lambda(FunctionSignature),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum FunctionReturns {
    Data(Type),
    Never,
}

impl KindEnum {
    pub const TYPE: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Type,
    };
    pub const EFFECT: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Effect,
    };
    pub const REGION: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Region,
    };
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Type(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Region(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Effect(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Kind(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct FunctionSignature(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Term {
    Type(Type),
    Region(Region),
    Effect(Effect),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct GenericArgument {
    pub term: Term,
    pub arity: Option<usize>,
}

impl Index<Type> for TypeTable {
    type Output = TypeEnum;

    fn index(&self, index: Type) -> &Self::Output {
        &self.types[index.0]
    }
}

impl Index<Region> for TypeTable {
    type Output = RegionEnum;

    fn index(&self, index: Region) -> &Self::Output {
        &self.regions[index.0]
    }
}

impl Index<Effect> for TypeTable {
    type Output = EffectEnum;

    fn index(&self, index: Effect) -> &Self::Output {
        &self.effects[index.0]
    }
}

impl Index<Kind> for TypeTable {
    type Output = KindEnum;

    fn index(&self, index: Kind) -> &Self::Output {
        &self.kinds[index.0]
    }
}

impl Index<FunctionSignature> for TypeTable {
    type Output = FunctionSignatureValue;

    fn index(&self, index: FunctionSignature) -> &Self::Output {
        &self.function_signatures[index.0]
    }
}

impl TypeTable {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert_type(&mut self, value: TypeEnum) -> Type {
        Type(self.types.insert_full(value).0)
    }
    pub fn insert_region(&mut self, value: RegionEnum) -> Region {
        Region(self.regions.insert_full(value).0)
    }
    pub fn insert_effect(&mut self, value: EffectEnum) -> Effect {
        Effect(self.effects.insert_full(value).0)
    }
    pub fn insert_kind(&mut self, value: KindEnum) -> Kind {
        Kind(self.kinds.insert_full(value).0)
    }
    pub fn insert_function_signature(
        &mut self,
        value: FunctionSignatureValue,
    ) -> FunctionSignature {
        FunctionSignature(self.function_signatures.insert_full(value).0)
    }
}
