use std::fmt::{self};

use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx},
    error::Range,
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(TypeIdx);
vecmap_index!(GenericIdx);
vecmap_index!(AssocIdx);
vecmap_index!(HandlerIdx);
vecmap_index!(LazyIdx);

mod codegen;
pub use codegen::*;

#[derive(Debug, Clone)]
pub struct Param {
    pub name_def: Option<Range>,
    pub type_def: Range,
    pub ty: TypeIdx,
}

#[derive(Debug, Default)]
pub struct ReturnType {
    pub type_def: Option<Range>,
    pub ty: TypeIdx,
}

#[derive(Debug, Default)]
pub struct FunSign {
    pub def: Option<Range>,
    pub name: String,
    pub generics: Generics,

    pub params: Vec<Param>,
    pub return_type: ReturnType,
}

impl Default for TypeIdx {
    fn default() -> Self {
        Self(0)
    }
}

#[derive(Debug)]
pub struct AssocDef {
    pub assoc: Assoc,
    pub infer: bool,
    pub generics: Generics,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Generic {
    pub idx: GenericIdx,
    pub typeof_ty: TypeIdx,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Assoc {
    pub idx: AssocIdx,
    pub typeof_ty: TypeIdx,
}

#[derive(Debug, Default)]
pub struct Effect {
    pub name: String,
    pub generics: Generics, // indices correspond 1-1 with ast generics

    pub assocs: Vec<AssocDef>,

    pub funs: VecMap<EffFunIdx, FunSign>,
    pub implied: Vec<HandlerIdx>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EffectIdent {
    pub effect: EffIdx,
    pub generic_params: GenericParams,
}

pub type Generics = Vec<Generic>;
pub type GenericParams = Vec<(GenericIdx, TypeIdx)>;

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

    pub assoc_types: Vec<(AssocIdx, TypeIdx)>,

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

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Type {
    Handler(HandlerIdx),
    LazyHandler(TypeIdx, LazyIdx),
    HandlerSelf,

    DataType(TypeConstraints),
    Effect,

    Generic(Generic),
    AssocType {
        assoc: Assoc,
        handler: TypeIdx,
        effect: EffIdx,
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
    pub lazy_handlers: VecMap<LazyIdx, Option<HandlerIdx>>,

    pub generic_names: VecMap<GenericIdx, String>,
    pub assoc_names: VecMap<AssocIdx, String>,
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
                            let mut iter = effect.generic_params.iter().copied();

                            let first = iter.next().unwrap();
                            first.1.display(ir, generic_params, f)?;
                            for next in iter {
                                write!(f, ", ")?;
                                next.1.display(ir, generic_params, f)?;
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

pub fn get_param(generic_params: &GenericParams, idx: GenericIdx) -> Option<TypeIdx> {
    get_value(generic_params, &idx).copied()
}

pub fn get_value<'a, K: PartialEq, V>(vec: &'a Vec<(K, V)>, key: &K) -> Option<&'a V> {
    vec.iter().find(|(k, _)| k.eq(key)).map(|(_, v)| v)
}

pub fn get_value_mut<'a, K: PartialEq, V>(vec: &'a mut Vec<(K, V)>, key: &K) -> Option<&'a mut V> {
    vec.iter_mut().find(|(k, _)| k.eq(key)).map(|(_, v)| v)
}

impl TypeIdx {
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
                assoc,
                generic_params: ref params,
                ..
            } => {
                write!(f, "{}", ir.assoc_names[assoc.idx])?;
                if !params.is_empty() {
                    write!(f, "<")?;
                    let mut iter = params.iter().copied();

                    let first = iter.next().unwrap();
                    first.1.display(ir, generic_params, f)?;
                    for next in iter {
                        write!(f, ", ")?;
                        next.1.display(ir, generic_params, f)?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Type::Effect => write!(f, "effect"),
            Type::Generic(generic) => match get_param(generic_params, generic.idx) {
                Some(ty) => ty.display(ir, generic_params, f),
                None => {
                    write!(f, "{}", ir.generic_names[generic.idx])
                }
            },
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
            Type::Unknown => write!(f, "UNKNOWN"),
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

fn display_generics(
    generics: &Generics,
    ir: &SemIR,
    generic_params: &GenericParams,
    f: &mut impl fmt::Write,
) -> fmt::Result {
    let mut iter = generics.iter();
    if let Some(generic) = iter.next() {
        let idx = generic.idx;
        let next = generic.typeof_ty;

        write!(f, "<")?;
        write!(f, "{}", ir.generic_names[idx])?;
        match ir.types[next] {
            Type::DataType(ref constraints) => constraints.display(ir, generic_params, f)?,
            _ => {
                write!(f, " ")?;
                next.display(ir, generic_params, f)?;
            }
        }

        for generic in iter {
            let idx = generic.idx;
            let next = generic.typeof_ty;

            write!(f, ", {}", ir.generic_names[idx])?;
            match ir.types[next] {
                Type::DataType(ref constraints) => constraints.display(ir, generic_params, f)?,
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

impl FunSign {
    fn display(&self, padding: &str, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        write!(f, "{}fun {}", padding, self.name)?;
        display_generics(&self.generics, ir, no_params, f)?;
        write!(f, "(")?;
        if !self.params.is_empty() {
            let mut iter = self.params.iter().map(|param| param.ty);

            let first = iter.next().unwrap();
            first.display(ir, no_params, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.display(ir, no_params, f)?;
            }
        }
        write!(f, ")")?;
        if !matches!(ir.types[self.return_type.ty], Type::None) {
            write!(f, " ")?;
            self.return_type.ty.display(ir, no_params, f)?;
        }
        Ok(())
    }
}

impl Effect {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        // signature
        write!(f, "effect {}", self.name)?;
        display_generics(&self.generics, ir, no_params, f)?;
        writeln!(f)?;

        // assoc
        for assoc in self.assocs.iter() {
            match ir.types[assoc.assoc.typeof_ty] {
                Type::DataType(ref constraints) => {
                    write!(f, "  type {}", ir.assoc_names[assoc.assoc.idx])?;
                    display_generics(&assoc.generics, ir, no_params, f)?;
                    constraints.display(ir, no_params, f)?;
                }
                _ => {
                    write!(f, "  let {}", ir.assoc_names[assoc.assoc.idx])?;
                    display_generics(&assoc.generics, ir, no_params, f)?;
                    write!(f, " ")?;
                    assoc.assoc.typeof_ty.display(ir, no_params, f)?;
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
        display_generics(&self.generics, ir, no_params, f)?;
        write!(f, " {}", ir.effects[self.effect].name)?;
        if !self.generic_params.is_empty() {
            write!(f, "<")?;
            let mut iter = self.generic_params.iter().copied();

            let first = iter.next().unwrap();
            first.1.display(ir, no_params, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.1.display(ir, no_params, f)?;
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
        for (idx, ty) in self.assoc_types.iter().copied() {
            let def = ir.effects[self.effect]
                .assocs
                .iter()
                .find(|def| def.assoc.idx == idx)
                .unwrap();
            match ir.types[def.assoc.typeof_ty] {
                Type::DataType(ref constraints) => {
                    write!(f, "  type {}", ir.assoc_names[idx])?;
                    display_generics(&def.generics, ir, &self.generic_params, f)?;
                    constraints.display(ir, &self.generic_params, f)?;
                }
                _ => {
                    write!(f, "  let {}", ir.assoc_names[idx])?;
                    display_generics(&def.generics, ir, &self.generic_params, f)?;
                    write!(f, " ")?;
                    def.assoc.typeof_ty.display(ir, &self.generic_params, f)?;
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
