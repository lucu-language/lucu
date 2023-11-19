use std::fmt::{self};

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
    pub generics: Generics, // indices correspond 1-1 with ast generics

    pub funs: VecMap<EffFunIdx, FunSign>,
    pub implied: Vec<ImpliedHandler>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EffectIdent {
    pub effect: EffIdx,
    pub generic_params: GenericParams,
}

pub type Generics = VecMap<GenericIdx, TypeIdx>;
pub type GenericParams = VecMap<GenericIdx, TypeIdx>;

#[derive(Debug)]
pub struct ImpliedHandler {
    pub generics: Generics,

    pub generic_params: GenericParams,
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
    EffectInstance(GenericVal<EffectIdent>),

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

impl TypeIdx {
    fn display(self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        match ir.types[self] {
            Type::Handler {
                effect: _,
                fail,
                handler,
            } => {
                match handler {
                    GenericVal::Literal(handler) => match handler {
                        HandlerIdxRef::Idx(idx) => write!(f, "handle H{}", usize::from(idx))?,
                        HandlerIdxRef::Ref(idx) => match ir.handler_refs[idx] {
                            Some(idx) => write!(f, "handle H{}", usize::from(idx))?,
                            None => write!(f, "handle UNKNOWN")?,
                        },
                        HandlerIdxRef::Me => write!(f, "self")?,
                    },
                    GenericVal::Generic(idx) => write!(f, "handle `{}", usize::from(idx))?,
                }
                match ir.types[fail] {
                    Type::Never => {}
                    Type::None => {
                        write!(f, " fails")?;
                    }
                    _ => {
                        write!(f, " fails ")?;
                        fail.display(ir, f)?;
                    }
                }
                Ok(())
            }
            Type::BoundHandler { effect: _, handler } => {
                match handler {
                    GenericVal::Literal(handler) => match handler {
                        HandlerIdxRef::Idx(idx) => write!(f, "handle H{}", usize::from(idx))?,
                        HandlerIdxRef::Ref(idx) => match ir.handler_refs[idx] {
                            Some(idx) => write!(f, "handle H{}", usize::from(idx))?,
                            None => write!(f, "handle UNKNOWN")?,
                        },
                        HandlerIdxRef::Me => write!(f, "self")?,
                    },
                    GenericVal::Generic(idx) => write!(f, "handle `{}", usize::from(idx))?,
                }
                Ok(())
            }
            Type::Type => write!(f, "type"),
            Type::Effect => write!(f, "effect"),
            Type::EffectInstance(ref effect) => match *effect {
                GenericVal::Literal(ref effect) => {
                    write!(f, "{}", ir.effects[effect.effect].name)?;

                    if !effect.generic_params.is_empty() {
                        write!(f, "<")?;
                        let mut iter = effect.generic_params.values().copied();

                        let first = iter.next().unwrap();
                        first.display(ir, f)?;
                        for next in iter {
                            write!(f, ", ")?;
                            next.display(ir, f)?;
                        }
                        write!(f, ">")?;
                    }

                    Ok(())
                }
                GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx)),
            },
            Type::Generic(idx) => {
                write!(f, "`{}", usize::from(idx))
            }
            Type::Pointer(inner) => {
                write!(f, "^")?;
                inner.display(ir, f)
            }
            Type::Const(inner) => {
                write!(f, "const ")?;
                inner.display(ir, f)
            }
            Type::ConstArray(size, inner) => {
                write!(f, "[")?;
                match size {
                    GenericVal::Literal(size) => write!(f, "{}", size)?,
                    GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx))?,
                }
                write!(f, "]")?;
                inner.display(ir, f)
            }
            Type::Slice(inner) => {
                write!(f, "[]")?;
                inner.display(ir, f)
            }
            Type::Int => write!(f, "int"),
            Type::UInt => write!(f, "uint"),
            Type::USize => write!(f, "usize"),
            Type::UPtr => write!(f, "uptr"),
            Type::U8 => write!(f, "u8"),
            Type::Str => write!(f, "str"),
            Type::Bool => write!(f, "bool"),
            Type::None => write!(f, "void"),
            Type::Never => write!(f, "never"),
            Type::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

impl FunSign {
    fn display(
        &self,
        padding: &str,
        skip_generics: usize,
        ir: &SemIR,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        write!(f, "{}fun {}", padding, self.name)?;
        let mut iter = self
            .generics
            .values()
            .copied()
            .enumerate()
            .skip(skip_generics);
        if let Some((idx, next)) = iter.next() {
            write!(f, "<")?;

            write!(f, "`{} ", idx)?;
            next.display(ir, f)?;
            for (idx, next) in iter {
                write!(f, ", `{} ", idx)?;
                next.display(ir, f)?;
            }
            write!(f, ">")?;
        }
        write!(f, "(")?;
        if !self.params.is_empty() {
            let mut iter = self.params.iter().copied();

            let first = iter.next().unwrap();
            first.display(ir, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.display(ir, f)?;
            }
        }
        write!(f, ")")?;
        if !matches!(ir.types[self.return_type], Type::None) {
            write!(f, " ")?;
            self.return_type.display(ir, f)?;
        }
        Ok(())
    }
}

impl Effect {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        // effect signature
        write!(f, "effect {}", self.name)?;
        if !self.generics.is_empty() {
            write!(f, "<")?;
            let mut iter = self.generics.values().copied().enumerate();

            let first = iter.next().unwrap().1;
            write!(f, "`0 ")?;
            first.display(ir, f)?;
            for (idx, next) in iter {
                write!(f, ", `{} ", idx)?;
                next.display(ir, f)?;
            }
            write!(f, ">")?;
        }
        writeln!(f)?;

        // effect functions
        for fun in self.funs.values() {
            fun.display("  ", self.generics.len(), ir, f)?;
            writeln!(f)?;
        }

        // effect implied
        for implied in self.implied.iter() {
            write!(f, "handle")?;
            if !implied.generics.is_empty() {
                write!(f, "<")?;
                let mut iter = implied.generics.values().copied().enumerate();

                let first = iter.next().unwrap().1;
                write!(f, "`0 ")?;
                first.display(ir, f)?;
                for (idx, next) in iter {
                    write!(f, ", `{} ", idx)?;
                    next.display(ir, f)?;
                }
                write!(f, ">")?;
            }

            write!(f, " {}", self.name)?;
            if !implied.generic_params.is_empty() {
                write!(f, "<")?;
                let mut iter = implied.generic_params.values().copied();

                let first = iter.next().unwrap();
                first.display(ir, f)?;
                for next in iter {
                    write!(f, ", ")?;
                    next.display(ir, f)?;
                }
                write!(f, ">")?;
            }
            writeln!(f)?;
        }

        Ok(())
    }
}

impl fmt::Display for SemIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // effects
        for effect in self.effects.values() {
            effect.display(self, f)?;
            writeln!(f)?;
        }

        // functions
        for fun in self.fun_sign.values() {
            // fun signature
            fun.display("", 0, self, f)?;

            // fun impl
            // TODO

            writeln!(f)?;
        }

        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum HandlerIdxRef {
    Idx(HandlerIdx),
    Ref(usize),
    Me,
}

impl From<HandlerIdx> for HandlerIdxRef {
    fn from(value: HandlerIdx) -> Self {
        Self::Idx(value)
    }
}
