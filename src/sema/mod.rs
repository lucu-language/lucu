use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx},
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(TypeIdx);
vecmap_index!(GenericIdx);
vecmap_index!(HandlerIdx);

mod codegen;
pub use codegen::*;

#[derive(Debug, Default)]
pub struct FunSign {
    pub name: String,
    pub generics: Generics,

    pub params: Vec<TypeIdx>,
    pub return_type: TypeIdx,
}

impl Default for TypeIdx {
    fn default() -> Self {
        Self(0)
    }
}

#[derive(Debug, Default)]
pub struct Effect {
    pub name: String,
    pub generics: Generics,

    pub params: GenericParams,
    pub funs: VecMap<EffFunIdx, FunSign>,
    pub implied: Vec<ImpliedHandler>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EffectIdent {
    pub effect: EffIdx,
    pub params: GenericParams,
}

pub type Generics = VecMap<GenericIdx, TypeIdx>;
pub type GenericParams = Vec<TypeIdx>;

#[derive(Debug)]
pub struct ImpliedHandler {
    pub generics: Generics,

    pub params: GenericParams,
    pub fail: TypeIdx,
    pub handler: HandlerIdx,
}

#[derive(Debug)]
pub struct Handler {
    pub captures: TypeIdx,

    // TODO: should be a vecmap of FunImpl
    pub funs: VecMap<EffFunIdx, FunIdx>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum GenericVal<T> {
    Literal(T),
    Generic(GenericIdx),
}

impl<T> GenericVal<T> {
    pub fn literal(&self) -> Option<&T> {
        match self {
            GenericVal::Literal(t) => Some(t),
            GenericVal::Generic(_) => None,
        }
    }
    pub fn map<U>(&self, f: impl FnOnce(&T) -> U) -> GenericVal<U> {
        match *self {
            GenericVal::Literal(ref t) => GenericVal::Literal(f(t)),
            GenericVal::Generic(idx) => GenericVal::Generic(idx),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Type {
    Handler {
        effect: TypeIdx, // HandlerType
        fail: TypeIdx,
        handler: GenericVal<HandlerIdxRef>,
    },
    BoundHandler {
        effect: TypeIdx, // HandlerType
        handler: GenericVal<HandlerIdxRef>,
    },

    Type,
    Effect,
    HandlerType(GenericVal<EffectIdent>),

    Generic(GenericIdx),

    Pointer(TypeIdx),
    Const(TypeIdx),
    ConstArray(GenericVal<u64>, TypeIdx),
    Slice(TypeIdx),

    Int,
    UInt,
    USize,
    UPtr,
    U8,

    Str,
    Bool,
    None,
    Never,
    Unknown,
}

#[derive(Debug)]
pub struct SemIR {
    pub effects: VecMap<EffIdx, Effect>,
    pub fun_sign: VecMap<FunIdx, FunSign>,
    pub entry: FunIdx,

    pub types: VecSet<TypeIdx, Type>,
    pub handlers: VecMap<HandlerIdx, Handler>,
    pub handler_refs: Vec<Option<HandlerIdx>>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum HandlerIdxRef {
    Idx(HandlerIdx),
    Ref(usize),
}

impl From<HandlerIdx> for HandlerIdxRef {
    fn from(value: HandlerIdx) -> Self {
        Self::Idx(value)
    }
}

impl SemIR {
    pub fn handler(&self, idx: HandlerIdxRef) -> Option<&Handler> {
        match idx {
            HandlerIdxRef::Idx(idx) => Some(&self.handlers[idx]),
            HandlerIdxRef::Ref(idx) => match self.handler_refs[idx] {
                Some(idx) => Some(&self.handlers[idx]),
                None => None,
            },
        }
    }
}
