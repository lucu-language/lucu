use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx},
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(TypeIdx);
vecmap_index!(GenericIdx);
vecmap_index!(HandlerIdx);

mod codegen;
pub use codegen::*;

#[derive(Debug, Default, Clone)]
pub struct Generics {
    pub ty: VecMap<GenericIdx, ()>,
    pub effect: VecMap<GenericIdx, ()>,
    pub constant: VecMap<GenericIdx, TypeIdx>,
    pub handler: VecMap<GenericIdx, GenericVal<EffIdx>>,
}

#[derive(Debug, Default, Clone)]
pub struct FunSign {
    pub generics: Generics,
    pub params: Vec<TypeIdx>,
    pub return_type: TypeIdx,
}

impl Default for TypeIdx {
    fn default() -> Self {
        Self(0)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Effect {
    pub funs: VecMap<EffFunIdx, FunSign>,
}

#[derive(Debug)]
pub struct Handler {
    pub captures: TypeIdx,
    pub funs: VecMap<EffFunIdx, FunIdx>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum GenericVal<T> {
    Literal(T),
    Generic(GenericIdx),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Type {
    HandlerHint {
        effect: GenericVal<EffIdx>,
        fail: TypeIdx,
    },
    Handler {
        effect: GenericVal<EffIdx>,
        fail: TypeIdx,
        handler: GenericVal<HandlerIdx>,
    },
    BoundHandler {
        effect: GenericVal<EffIdx>,
        handler: GenericVal<HandlerIdx>,
    },

    Pointer(TypeIdx),
    Const(TypeIdx),
    ConstArray(GenericVal<u64>, TypeIdx),
    Slice(TypeIdx),
    Generic(GenericIdx),

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
}
