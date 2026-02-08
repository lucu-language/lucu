use std::ops::Index;
use std::slice;
use std::sync::Arc;

use asta_handle_map::HandleMap;
use compact_str::CompactString;
use itertools::Itertools;

use crate::module::Module;

pub mod display;
pub mod substitute;
pub mod unapply;

#[derive(Default)]
pub struct TypeTable {
    kinds: HandleMap<KindEnum>,
    types: HandleMap<TypeEnum>,
    regions: HandleMap<RegionEnum>,
    effects: HandleMap<EffectEnum>,
    function_signatures: HandleMap<FunctionSignatureValue>,
    constants: HandleMap<ConstantEnum>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum IntSize {
    /// Exact number of bits
    Exact(usize),

    /// The size of a continuous block of memory
    /// At least 16 bits
    /// At most IntSize::Address
    Index,
    /// The size of a memory address
    /// At least 16 bits
    Address,
    /// The size of the largest general purpose integer register
    /// At least 16 bits
    Register,

    /// Equivalent of a C char
    /// Smallest addressable unit of the machine
    /// At least 8 bits
    /// At most IntSize::CShort
    CChar,
    /// Equivalent of a C short int
    /// At least 16 bits
    /// At most IntSize::CInt
    CShort,
    /// Equivalent of a C int
    /// At least 16 bits
    /// At most IntSize::CLong
    CInt,
    /// Equivalent of a C long int
    /// At least 32 bits
    /// At most IntSize::CLongLong
    CLong,
    /// Equivalent of a C long long int
    /// At least 64 bits
    CLongLong,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Integer {
    Integer(bool, IntSize),
    /// Integer of the same size as a C char
    /// Unknown sign
    CChar,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct GenericParameter {
    /// a De Bruijn index
    pub index: usize,
    pub apply: Option<Arc<[GenericArgument]>>,
}

impl IntSize {
    pub const fn smaller_than(self, other: IntSize) -> bool {
        match (self, other) {
            (IntSize::Exact(a), IntSize::Exact(b)) => a < b,
            (IntSize::Exact(n), IntSize::Index | IntSize::Address | IntSize::Register) => n < 16,

            (IntSize::Exact(n), IntSize::CChar) => n < 8,
            (IntSize::Exact(n), IntSize::CShort | IntSize::CInt) => n < 16,
            (IntSize::Exact(n), IntSize::CLong) => n < 32,
            (IntSize::Exact(n), IntSize::CLongLong) => n < 64,

            _ => false,
        }
    }
    #[rustfmt::skip]
    pub const fn fits_inside(self, other: IntSize) -> bool {
        match (self, other) {
            (IntSize::Exact(a), IntSize::Exact(b)) => a <= b,
            (IntSize::Exact(n), IntSize::Index | IntSize::Address | IntSize::Register) => n <= 16,

            (IntSize::Index, IntSize::Index | IntSize::Address) => true,
            (IntSize::Address, IntSize::Address) => true,
            (IntSize::Register, IntSize::Register) => true,

            (IntSize::Exact(n), IntSize::CChar) => n <= 8,
            (IntSize::Exact(n), IntSize::CShort | IntSize::CInt) => n <= 16,
            (IntSize::Exact(n), IntSize::CLong) => n <= 32,
            (IntSize::Exact(n), IntSize::CLongLong) => n <= 64,

            (IntSize::CChar, IntSize::CChar | IntSize::CShort | IntSize::CInt | IntSize::CLong | IntSize::CLongLong) => true,
            (IntSize::CShort, IntSize::CShort | IntSize::CInt | IntSize::CLong | IntSize::CLongLong) => true,
            (IntSize::CInt, IntSize::CInt | IntSize::CLong | IntSize::CLongLong) => true,
            (IntSize::CLong, IntSize::CLong | IntSize::CLongLong) => true,
            (IntSize::CLongLong, IntSize::CLongLong) => true,
            
            _ => false,
        }
    }
}

impl Integer {
    pub const fn signed(size: IntSize) -> Self {
        Self::Integer(true, size)
    }
    pub const fn unsigned(size: IntSize) -> Self {
        Self::Integer(false, size)
    }
    pub const fn fits_inside(self, other: Integer) -> bool {
        // an unsigned type fits inside an unside type, if its size is smaller (or equal)
        // an unsigned type fits inside a signed type, if its size is *strictly* smaller
        // a signed type fits inside a signed type, if its size is smaller (or equal)
        // a signed type *never* fits inside an unsigned type
        match (self, other) {
            (Integer::Integer(sign_a, int_size_a), Integer::Integer(sign_b, int_size_b)) => {
                if sign_a == sign_b {
                    int_size_a.fits_inside(int_size_b)
                } else {
                    sign_b && int_size_a.smaller_than(int_size_b)
                }
            }

            (Integer::Integer(sign, int_size), Integer::CChar) => {
                !sign && int_size.smaller_than(IntSize::CChar)
            }
            (Integer::CChar, Integer::Integer(sign, int_size)) => {
                sign && IntSize::CChar.smaller_than(int_size)
            }
            (Integer::CChar, Integer::CChar) => true,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Item {
    pub module: Module,
    pub name: CompactString,
    pub apply: Option<Arc<[GenericArgument]>>,
}

/// Currently only Null-Terminated
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub struct Sentinel;

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum TypeEnum {
    Generic(GenericParameter),
    Item(Item),
    Integer(Integer),
    Boolean,
    Unit,
    Never,
    Pointer(Type, Region),
    PointerSlice(Type, Region, Option<Sentinel>),
    Array(Type, Constant, Option<Sentinel>),
}

impl TypeEnum {
    pub const U8: Self = TypeEnum::Integer(Integer::unsigned(IntSize::Exact(8)));
    pub const INT: Self = TypeEnum::Integer(Integer::signed(IntSize::Register));
    pub const USIZE: Self = TypeEnum::Integer(Integer::unsigned(IntSize::Index));
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
    Read(Region),
    Write(Region),
    Divergent,
}

impl EffectEnum {
    pub fn empty() -> Self {
        Self::Row(Arc::new([]))
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum SimpleKind {
    Type,
    Effect,
    Region,
    Thunk,
    Constant(Type),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct KindEnum {
    pub params: Option<Arc<[Kind]>>,
    pub output: SimpleKind,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone, Copy)]
pub struct Thunk {
    pub returns: Type,
    pub effect: Effect, // a (row) effect
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FunctionSignatureValue {
    pub type_params: Option<Arc<[Kind]>>,
    pub implicit_regions: usize,

    pub params: Option<Arc<[FunctionParameter]>>,
    pub thunk: Thunk,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum FunctionParameter {
    Data(Type),
    Lambda(FunctionSignature),
}

impl KindEnum {
    pub const THUNK: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Thunk,
    };
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
    pub const fn constant(ty: Type) -> Self {
        KindEnum {
            params: None,
            output: SimpleKind::Constant(ty),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ConstantEnum {
    Generic(GenericParameter),
    True,
    False,
    Integer(u64),
    String(CompactString),
    Character(CompactString),
    Zero,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Type(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Region(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Effect(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Kind(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Constant(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct FunctionSignature(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum Term {
    Type(Type),
    Region(Region),
    Effect(Effect),
    Constant(Constant),
    Thunk(Thunk),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct GenericArgument {
    pub term: Term,
    pub arity: Option<usize>,
}

impl Effect {
    pub fn empty(tt: &TypeTable) -> Self {
        tt.insert_effect(EffectEnum::Row(Arc::new([])))
    }
    pub fn row<'a>(effects: impl IntoIterator<Item = &'a Effect>, tt: &TypeTable) -> Self {
        let row = effects
            .into_iter()
            .flat_map(|e| match &tt[*e] {
                EffectEnum::Row(effects) => effects.iter().copied(),
                _ => slice::from_ref(e).iter().copied(),
            })
            .unique()
            .sorted()
            .collect::<Arc<_>>();
        match *row {
            [single] => single,
            _ => tt.insert_effect(EffectEnum::Row(row)),
        }
    }
}

impl Index<Type> for TypeTable {
    type Output = TypeEnum;

    fn index(&self, index: Type) -> &Self::Output {
        unsafe { self.types.get_unchecked(index.0) }
    }
}

impl Index<Region> for TypeTable {
    type Output = RegionEnum;

    fn index(&self, index: Region) -> &Self::Output {
        unsafe { self.regions.get_unchecked(index.0) }
    }
}

impl Index<Effect> for TypeTable {
    type Output = EffectEnum;

    fn index(&self, index: Effect) -> &Self::Output {
        unsafe { self.effects.get_unchecked(index.0) }
    }
}

impl Index<Kind> for TypeTable {
    type Output = KindEnum;

    fn index(&self, index: Kind) -> &Self::Output {
        unsafe { self.kinds.get_unchecked(index.0) }
    }
}

impl Index<Constant> for TypeTable {
    type Output = ConstantEnum;

    fn index(&self, index: Constant) -> &Self::Output {
        unsafe { self.constants.get_unchecked(index.0) }
    }
}

impl Index<FunctionSignature> for TypeTable {
    type Output = FunctionSignatureValue;

    fn index(&self, index: FunctionSignature) -> &Self::Output {
        unsafe { self.function_signatures.get_unchecked(index.0) }
    }
}

impl TypeTable {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert_type(&self, value: TypeEnum) -> Type {
        Type(self.types.insert(value))
    }
    pub fn insert_region(&self, value: RegionEnum) -> Region {
        Region(self.regions.insert(value))
    }
    pub fn insert_effect(&self, value: EffectEnum) -> Effect {
        Effect(self.effects.insert(value))
    }
    pub fn insert_kind(&self, value: KindEnum) -> Kind {
        Kind(self.kinds.insert(value))
    }
    pub fn insert_constant(&self, value: ConstantEnum) -> Constant {
        Constant(self.constants.insert(value))
    }
    pub fn insert_function_signature(
        &self,
        value: FunctionSignatureValue,
    ) -> FunctionSignature {
        FunctionSignature(self.function_signatures.insert(value))
    }
    pub fn eprint_lengths(&self) {
        eprintln!("types: {}/{}", self.types.len(), self.types.capacity());
        eprintln!("regions: {}/{}", self.regions.len(), self.regions.capacity());
        eprintln!("effects: {}/{}", self.effects.len(), self.effects.capacity());
        eprintln!("kinds: {}/{}", self.kinds.len(), self.kinds.capacity());
        eprintln!("constants: {}/{}", self.constants.len(), self.constants.capacity());
        eprintln!("function_signatures: {}/{}", self.function_signatures.len(), self.function_signatures.capacity());
    }
}
