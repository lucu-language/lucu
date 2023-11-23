use std::fmt::{self};

use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx},
    vecmap::{vecmap_index, VecMap, VecMapOffset, VecSet},
};

vecmap_index!(TypeIdx);
vecmap_index!(GenericIdx);
vecmap_index!(HandlerIdx);
vecmap_index!(HandlerTypeIdx);

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
    pub implied: Vec<HandlerIdx>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EffectIdent {
    pub effect: EffIdx,
    pub generic_params: GenericParams,
}

pub type Generics = VecMapOffset<GenericIdx, TypeIdx>;
pub type GenericParams = VecMapOffset<GenericIdx, TypeIdx>;

#[derive(Debug)]
pub struct Capture {
    pub debug_name: String,
    pub ty: TypeIdx,
}

#[derive(Debug)]
pub struct Handler {
    pub debug_name: String,
    pub generics: Generics,

    pub effect: EffIdx,
    pub generic_params: GenericParams,
    pub fail: TypeIdx,

    pub captures: Vec<Capture>,
    pub funs: VecMap<EffFunIdx, FunSign>, // TODO: FunDecl
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
pub enum TypeConstraints {
    None,
    Handler(GenericVal<EffectIdent>, TypeIdx), // effect, fail
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum FunIdent {
    Top(FunIdx),
    Effect(TypeIdx, EffIdx, EffFunIdx), // handler, effect, function
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Type {
    Handler(HandlerIdx),
    HandlerSelf,

    Type(TypeConstraints),
    Effect,

    Generic(TypeIdx, GenericIdx),
    FunOutput {
        ty: TypeIdx, // type-type
        fun: FunIdent,
        generic_params: GenericParams,
    },

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
    pub entry: Option<FunIdx>,

    pub types: VecSet<TypeIdx, Type>,
    pub handlers: VecMap<HandlerIdx, Handler>,
}

impl TypeConstraints {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        match *self {
            TypeConstraints::None => Ok(()),
            TypeConstraints::Handler(ref effect, fail) => {
                write!(f, " / handle ")?;
                match *effect {
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
                    }
                    GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx))?,
                }
                match ir.types[fail] {
                    Type::Never => {}
                    Type::None => write!(f, " fails")?,
                    _ => {
                        write!(f, " fails ")?;
                        fail.display(ir, f)?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl TypeIdx {
    fn matches(self, other: Self, _ir: &SemIR) -> bool {
        // TypeIdx(0) should ALWAYS be Type::Unknown
        self == other || self == TypeIdx(0) || other == TypeIdx(0)
    }
    fn can_move_to(self, other: Self, ir: &SemIR) -> bool {
        self.matches(other, ir)
            || match (&ir.types[self], &ir.types[other]) {
                // any constrained type -> unconstrained type
                (Type::Type(_), Type::Type(TypeConstraints::None)) => true,

                // handler type -> handler type IF same handler && fail -> fail
                (
                    &Type::Type(TypeConstraints::Handler(ref eff_a, fail_a)),
                    &Type::Type(TypeConstraints::Handler(ref eff_b, fail_b)),
                ) => eff_a == eff_b && fail_a.can_move_to(fail_b, ir),

                // fun output -> fun output IF same function && typeof output -> typeof output
                (
                    &Type::FunOutput {
                        ty: ty_a,
                        fun: fun_a,
                        generic_params: ref generic_a,
                    },
                    &Type::FunOutput {
                        ty: ty_b,
                        fun: fun_b,
                        generic_params: ref generic_b,
                    },
                ) => fun_a == fun_b && generic_a == generic_b && ty_a.can_move_to(ty_b, ir),

                // generic -> generic IF typeof generic -> typeof generic
                (&Type::Generic(ty_a, idx_a), &Type::Generic(ty_b, idx_b)) => {
                    idx_a == idx_b && ty_a.can_move_to(ty_b, ir)
                }

                // never -> any
                (Type::Never, _) => true,

                _ => false,
            }
    }
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        match ir.types[*self] {
            Type::HandlerSelf => write!(f, "self"),
            Type::Handler(idx) => write!(f, "{}", ir.handlers[idx].debug_name),
            Type::Type(ref constraints) => {
                write!(f, "type")?;
                constraints.display(ir, f)
            }
            Type::FunOutput {
                ty,
                ref fun,
                ref generic_params,
            } => {
                match *fun {
                    FunIdent::Top(idx) => {
                        write!(f, "#{}", ir.fun_sign[idx].name)?;
                    }
                    FunIdent::Effect(handler, eff, idx) => {
                        handler.display(ir, f)?;
                        write!(f, "#{}", ir.effects[eff].funs[idx].name)?;
                    }
                }
                if !generic_params.is_empty() {
                    write!(f, "<")?;
                    let mut iter = generic_params.values().copied();

                    let first = iter.next().unwrap();
                    first.display(ir, f)?;
                    for next in iter {
                        write!(f, ", ")?;
                        next.display(ir, f)?;
                    }
                    write!(f, ">")?;
                }
                match ir.types[ty] {
                    Type::Type(ref constraints) => constraints.display(ir, f)?,
                    _ => {
                        write!(f, " ")?;
                        ty.display(ir, f)?;
                    }
                }
                Ok(())
            }
            Type::Effect => write!(f, "effect"),
            Type::Generic(_, idx) => {
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
            Type::Never => write!(f, "!"),
            Type::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

impl Generics {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let mut iter = self.iter(GenericIdx);
        if let Some((idx, &next)) = iter.next() {
            write!(f, "<")?;

            write!(f, "`{}", usize::from(idx))?;
            match ir.types[next] {
                Type::Type(ref constraints) => constraints.display(ir, f)?,
                _ => {
                    write!(f, " ")?;
                    next.display(ir, f)?;
                }
            }

            for (idx, &next) in iter {
                write!(f, ", `{}", usize::from(idx))?;
                match ir.types[next] {
                    Type::Type(ref constraints) => constraints.display(ir, f)?,
                    _ => {
                        write!(f, " ")?;
                        next.display(ir, f)?;
                    }
                }
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

impl FunSign {
    fn display(&self, padding: &str, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        write!(f, "{}fun {}", padding, self.name)?;
        self.generics.display(ir, f)?;
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
        self.generics.display(ir, f)?;
        writeln!(f)?;

        // effect functions
        for fun in self.funs.values() {
            fun.display("  ", ir, f)?;
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
        }
        writeln!(f)?;

        // handlers
        for handler in self.handlers.values() {
            // effect signature
            write!(f, "type {} = handle", handler.debug_name)?;
            handler.generics.display(self, f)?;
            write!(f, " {}", self.effects[handler.effect].name)?;
            if !handler.generic_params.is_empty() {
                write!(f, "<")?;
                let mut iter = handler.generic_params.values().copied();

                let first = iter.next().unwrap();
                first.display(self, f)?;
                for next in iter {
                    write!(f, ", ")?;
                    next.display(self, f)?;
                }
                write!(f, ">")?;
            }
            writeln!(f)?;

            // captures
            for capture in handler.captures.iter() {
                write!(f, "  {} ", capture.debug_name)?;
                capture.ty.display(self, f)?;
                writeln!(f, ";")?;
            }

            // funs
            for fun in handler.funs.values() {
                // fun signature
                fun.display("  ", self, f)?;

                // fun impl
                // TODO

                writeln!(f)?;
            }
        }
        writeln!(f)?;

        // functions
        for fun in self.fun_sign.values() {
            // fun signature
            fun.display("", self, f)?;

            // fun impl
            // TODO

            writeln!(f)?;
        }

        Ok(())
    }
}
