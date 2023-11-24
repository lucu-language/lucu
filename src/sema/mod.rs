use std::fmt::{self};

use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx},
    error::Range,
    vecmap::{vecmap_index, VecMap, VecMapOffset, VecSet},
};

vecmap_index!(TypeIdx);
vecmap_index!(GenericIdx);
vecmap_index!(AssocIdx);
vecmap_index!(HandlerIdx);
vecmap_index!(LazyIdx);

mod codegen;
pub use codegen::*;

#[derive(Debug, Default)]
pub struct FunSign {
    pub def: Option<Range>,
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

#[derive(Debug)]
pub struct Assoc {
    pub name: String,
    pub infer: bool,
    pub typeof_ty: TypeIdx,
    pub generics: Generics,
}

#[derive(Debug, Default)]
pub struct Effect {
    pub name: String,
    pub generics: Generics, // indices correspond 1-1 with ast generics

    pub assoc_types: VecMap<AssocIdx, Assoc>,

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

    pub assoc_types: VecMap<AssocIdx, TypeIdx>,

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
    LazyHandler(TypeIdx, LazyIdx),
    HandlerSelf,

    DataType(TypeConstraints),
    Effect,

    Generic(TypeIdx, GenericIdx),
    AssocType {
        ty: TypeIdx, // type-type
        handler: TypeIdx,
        effect: EffIdx,
        idx: AssocIdx,
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
    Unknown(TypeIdx),
}

#[derive(Debug)]
pub struct SemIR {
    pub effects: VecMap<EffIdx, Effect>,
    pub fun_sign: VecMap<FunIdx, FunSign>,
    pub entry: Option<FunIdx>,

    pub types: VecSet<TypeIdx, Type>,
    pub handlers: VecMap<HandlerIdx, Handler>,
    pub lazy_handlers: VecMap<LazyIdx, Option<HandlerIdx>>,
}

impl TypeConstraints {
    fn display(
        &self,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
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
                            first.display(ir, generic_params, f)?;
                            for next in iter {
                                write!(f, ", ")?;
                                next.display(ir, generic_params, f)?;
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
                        fail.display(ir, generic_params, f)?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl TypeIdx {
    fn can_move_to(self, other: Self, ir: &SemIR) -> bool {
        self == other
            || match (&ir.types[self], &ir.types[other]) {
                // any constrained type -> unconstrained type
                (Type::DataType(_), Type::DataType(TypeConstraints::None)) => true,

                // handler -> handler IF same handler && fail -> fail
                (
                    &Type::DataType(TypeConstraints::Handler(ref eff_a, fail_a)),
                    &Type::DataType(TypeConstraints::Handler(ref eff_b, fail_b)),
                ) => eff_a == eff_b && fail_a.can_move_to(fail_b, ir),

                // assoc -> assoc IF handler -> handler && typeof assoc -> typeof assoc
                (
                    &Type::AssocType {
                        ty: ty_a,
                        handler: handler_a,
                        effect: eff_a,
                        idx: idx_a,
                        generic_params: ref generic_a,
                    },
                    &Type::AssocType {
                        ty: ty_b,
                        handler: handler_b,
                        effect: eff_b,
                        idx: idx_b,
                        generic_params: ref generic_b,
                    },
                ) => {
                    eff_a == eff_b
                        && idx_a == idx_b
                        && generic_a == generic_b
                        && handler_a.can_move_to(handler_b, ir)
                        && ty_a.can_move_to(ty_b, ir)
                }

                // generic -> generic IF typeof generic -> typeof generic
                (&Type::Generic(ty_a, idx_a), &Type::Generic(ty_b, idx_b)) => {
                    idx_a == idx_b && ty_a.can_move_to(ty_b, ir)
                }

                // never -> any
                (Type::Never, _) => true,

                // unknown
                (&Type::Unknown(typeof_ty), _) => other.is_instance_rev(typeof_ty, ir),
                (_, &Type::Unknown(typeof_ty)) => self.is_instance(typeof_ty, ir),

                _ => false,
            }
    }
    fn is_instance(self, ty: TypeIdx, ir: &SemIR) -> bool {
        match ir.types[self] {
            Type::HandlerSelf => false,
            Type::Effect => false,
            Type::DataType(_) => false,

            Type::Generic(typeof_ty, _)
            | Type::LazyHandler(typeof_ty, _)
            | Type::AssocType { ty: typeof_ty, .. }
            | Type::Unknown(typeof_ty) => typeof_ty.can_move_to(ty, ir),

            Type::Pointer(_)
            | Type::Const(_)
            | Type::ConstArray(_, _)
            | Type::Slice(_)
            | Type::Int
            | Type::UInt
            | Type::USize
            | Type::UPtr
            | Type::U8
            | Type::Str
            | Type::Bool
            | Type::None
            | Type::Never => match ir.types[ty] {
                Type::DataType(TypeConstraints::None) => true,
                _ => false,
            },
            Type::Handler(idx) => match ir.types[ty] {
                Type::DataType(TypeConstraints::None) => true,
                Type::DataType(TypeConstraints::Handler(GenericVal::Literal(ref ident), fail)) => {
                    let handler = &ir.handlers[idx];
                    handler.effect == ident.effect
                        && handler.generic_params == ident.generic_params
                        && handler.fail.can_move_to(fail, ir)
                }
                _ => false,
            },
        }
    }
    fn is_instance_rev(self, ty: TypeIdx, ir: &SemIR) -> bool {
        match ir.types[self] {
            Type::HandlerSelf => false,
            Type::Effect => false,
            Type::DataType(_) => false,

            Type::Generic(typeof_ty, _)
            | Type::LazyHandler(typeof_ty, _)
            | Type::AssocType { ty: typeof_ty, .. }
            | Type::Unknown(typeof_ty) => ty.can_move_to(typeof_ty, ir),

            Type::Pointer(_)
            | Type::Const(_)
            | Type::ConstArray(_, _)
            | Type::Slice(_)
            | Type::Int
            | Type::UInt
            | Type::USize
            | Type::UPtr
            | Type::U8
            | Type::Str
            | Type::Bool
            | Type::None
            | Type::Never => match ir.types[ty] {
                Type::DataType(TypeConstraints::None) => true,
                _ => false,
            },
            Type::Handler(idx) => match ir.types[ty] {
                Type::DataType(TypeConstraints::None) => true,
                Type::DataType(TypeConstraints::Handler(GenericVal::Literal(ref ident), fail)) => {
                    let handler = &ir.handlers[idx];
                    handler.effect == ident.effect
                        && handler.generic_params == ident.generic_params
                        && fail.can_move_to(handler.fail, ir)
                }
                _ => false,
            },
        }
    }
    fn display(
        &self,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        match ir.types[*self] {
            Type::HandlerSelf => write!(f, "self"),
            Type::Handler(idx) => write!(f, "{}", ir.handlers[idx].debug_name),
            Type::DataType(ref constraints) => {
                write!(f, "type")?;
                constraints.display(ir, generic_params, f)
            }
            Type::AssocType {
                ty: _,
                handler,
                effect,
                idx,
                generic_params: ref params,
            } => {
                handler.display(ir, generic_params, f)?;
                write!(f, "::{}", ir.effects[effect].assoc_types[idx].name)?;
                if !params.is_empty() {
                    write!(f, "<")?;
                    let mut iter = params.values().copied();

                    let first = iter.next().unwrap();
                    first.display(ir, generic_params, f)?;
                    for next in iter {
                        write!(f, ", ")?;
                        next.display(ir, generic_params, f)?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Type::Effect => write!(f, "effect"),
            Type::Generic(_, idx) => {
                if idx.0 >= generic_params.start()
                    && idx.0 < generic_params.start() + generic_params.len()
                {
                    generic_params[idx].display(ir, generic_params, f)
                } else {
                    write!(f, "`{}", usize::from(idx))
                }
            }
            Type::Pointer(inner) => {
                write!(f, "^")?;
                inner.display(ir, generic_params, f)
            }
            Type::Const(inner) => {
                write!(f, "const ")?;
                inner.display(ir, generic_params, f)
            }
            Type::ConstArray(size, inner) => {
                write!(f, "[")?;
                match size {
                    GenericVal::Literal(size) => write!(f, "{}", size)?,
                    GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx))?,
                }
                write!(f, "]")?;
                inner.display(ir, generic_params, f)
            }
            Type::Slice(inner) => {
                write!(f, "[]")?;
                inner.display(ir, generic_params, f)
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
            Type::Unknown(typeof_ty) => {
                write!(f, "UNKNOWN")?;
                match ir.types[typeof_ty] {
                    Type::DataType(ref costraints) => {
                        costraints.display(ir, generic_params, f)?;
                    }
                    _ => {
                        write!(f, " ")?;
                        typeof_ty.display(ir, generic_params, f)?;
                    }
                }
                Ok(())
            }
            Type::LazyHandler(typeof_ty, idx) => match ir.lazy_handlers[idx] {
                Some(idx) => {
                    write!(f, "{}", ir.handlers[idx].debug_name)?;
                    Ok(())
                }
                None => {
                    write!(f, "LAZY#{}", idx.0)?;
                    match ir.types[typeof_ty] {
                        Type::DataType(ref costraints) => {
                            costraints.display(ir, generic_params, f)?;
                        }
                        _ => {
                            write!(f, " ")?;
                            typeof_ty.display(ir, generic_params, f)?;
                        }
                    }
                    Ok(())
                }
            },
        }
    }
}

impl Generics {
    fn display(
        &self,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        let mut iter = self.iter(GenericIdx);
        if let Some((idx, &next)) = iter.next() {
            write!(f, "<")?;

            write!(f, "`{}", usize::from(idx))?;
            match ir.types[next] {
                Type::DataType(ref constraints) => constraints.display(ir, generic_params, f)?,
                _ => {
                    write!(f, " ")?;
                    next.display(ir, generic_params, f)?;
                }
            }

            for (idx, &next) in iter {
                write!(f, ", `{}", usize::from(idx))?;
                match ir.types[next] {
                    Type::DataType(ref constraints) => {
                        constraints.display(ir, generic_params, f)?
                    }
                    _ => {
                        write!(f, " ")?;
                        next.display(ir, generic_params, f)?;
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
        let no_params = &GenericParams::default();

        write!(f, "{}fun {}", padding, self.name)?;
        self.generics.display(ir, no_params, f)?;
        write!(f, "(")?;
        if !self.params.is_empty() {
            let mut iter = self.params.iter().copied();

            let first = iter.next().unwrap();
            first.display(ir, no_params, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.display(ir, no_params, f)?;
            }
        }
        write!(f, ")")?;
        if !matches!(ir.types[self.return_type], Type::None) {
            write!(f, " ")?;
            self.return_type.display(ir, no_params, f)?;
        }
        Ok(())
    }
}

impl Effect {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        // signature
        write!(f, "effect {}", self.name)?;
        self.generics.display(ir, no_params, f)?;
        writeln!(f)?;

        // assoc
        for assoc in self.assoc_types.values() {
            match ir.types[assoc.typeof_ty] {
                Type::DataType(ref constraints) => {
                    write!(f, "  type {}", assoc.name)?;
                    assoc.generics.display(ir, no_params, f)?;
                    constraints.display(ir, no_params, f)?;
                }
                _ => {
                    write!(f, "  let {}", assoc.name)?;
                    assoc.generics.display(ir, no_params, f)?;
                    write!(f, " ")?;
                    assoc.typeof_ty.display(ir, no_params, f)?;
                }
            }
            writeln!(f)?;
        }

        // functions
        for fun in self.funs.values() {
            fun.display("  ", ir, f)?;
            writeln!(f)?;
        }

        Ok(())
    }
}

impl Handler {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        // effect signature
        write!(f, "type {} = handle", self.debug_name)?;
        self.generics.display(ir, no_params, f)?;
        write!(f, " {}", ir.effects[self.effect].name)?;
        if !self.generic_params.is_empty() {
            write!(f, "<")?;
            let mut iter = self.generic_params.values().copied();

            let first = iter.next().unwrap();
            first.display(ir, no_params, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.display(ir, no_params, f)?;
            }
            write!(f, ">")?;
        }
        writeln!(f)?;

        // captures
        for capture in self.captures.iter() {
            write!(f, "  {} ", capture.debug_name)?;
            capture.ty.display(ir, no_params, f)?;
        }

        // assoc
        for (idx, &ty) in self.assoc_types.iter(AssocIdx) {
            let assoc = &ir.effects[self.effect].assoc_types[idx];
            match ir.types[assoc.typeof_ty] {
                Type::DataType(ref constraints) => {
                    write!(f, "  type {}", assoc.name)?;
                    assoc.generics.display(ir, &self.generic_params, f)?;
                    constraints.display(ir, &self.generic_params, f)?;
                }
                _ => {
                    write!(f, "  let {}", assoc.name)?;
                    assoc.generics.display(ir, &self.generic_params, f)?;
                    write!(f, " ")?;
                    assoc.typeof_ty.display(ir, &self.generic_params, f)?;
                }
            }
            write!(f, " = ")?;
            ty.display(ir, no_params, f)?;
            writeln!(f)?;
        }

        // funs
        for fun in self.funs.values() {
            // fun signature
            fun.display("  ", ir, f)?;

            // fun impl
            // TODO

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
            handler.display(self, f)?;
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
