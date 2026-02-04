use std::fmt;

use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionReturns,
    FunctionSignature, GenericArgument, GenericParameter, IntSize, Integer, Item, Kind, KindEnum,
    Region, RegionEnum, Sentinel, SimpleKind, Term, Type, TypeEnum, TypeTable,
};

#[derive(Clone, Copy)]
struct Interned<'a, T>(T, &'a TypeTable);

impl fmt::Display for Interned<'_, Kind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = &self.1[self.0];
        if let Some(params) = &kind.params {
            for param in params.iter().copied() {
                if param.enclosed(self.1) {
                    write!(f, "({}) -> ", param.display(self.1))?;
                } else {
                    write!(f, "{} -> ", param.display(self.1))?;
                }
            }
        }
        match kind.output {
            SimpleKind::Type => write!(f, "*")?,
            SimpleKind::Effect => write!(f, "EFFECT")?,
            SimpleKind::Region => write!(f, "REGION")?,
            SimpleKind::Constant(ty) => write!(f, "{}", ty.display(self.1))?,
        }
        Ok(())
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Integer::Integer(signed, size) => {
                let prefix = if signed { "I" } else { "U" };
                let c_prefix = if signed { "" } else { "U" };
                match (signed, size) {
                    (_, IntSize::Exact(size)) => write!(f, "{prefix}{size}"),

                    (_, IntSize::Index) => write!(f, "{prefix}Size"),
                    (_, IntSize::Address) => write!(f, "{prefix}Ptr"),
                    (_, IntSize::Register) => write!(f, "{c_prefix}Int"),

                    (true, IntSize::CChar) => write!(f, "c.SChar"),
                    (false, IntSize::CChar) => write!(f, "c.UChar"),
                    (_, IntSize::CShort) => write!(f, "c.{c_prefix}Short"),
                    (_, IntSize::CInt) => write!(f, "c.{c_prefix}Int"),
                    (_, IntSize::CLong) => write!(f, "c.{c_prefix}Long"),
                    (_, IntSize::CLongLong) => write!(f, "c.{c_prefix}LongLong"),
                }
            }
            Integer::CChar => write!(f, "c.Char"),
        }
    }
}

impl fmt::Display for Interned<'_, &'_ GenericParameter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.index)?;
        if let Some(args) = &self.0.apply {
            for arg in args.iter() {
                if arg.enclosed(self.1) {
                    write!(f, " ({})", arg.display(self.1))?;
                } else {
                    write!(f, " {}", arg.display(self.1))?;
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for Interned<'_, &'_ Item> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.module.name() != "preamble" {
            write!(f, "{}.", self.0.module.name())?;
        }
        write!(f, "{}", self.0.name)?;
        if let Some(args) = &self.0.apply {
            for arg in args.iter() {
                if arg.enclosed(self.1) {
                    write!(f, " ({})", arg.display(self.1))?;
                } else {
                    write!(f, " {}", arg.display(self.1))?;
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for Interned<'_, Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1[self.0] {
            TypeEnum::Generic(ref param) => {
                write!(f, "{}", param.display(self.1))
            }
            TypeEnum::Item(ref item) => {
                write!(f, "{}", item.display(self.1))
            }
            TypeEnum::Boolean => write!(f, "Bool"),
            TypeEnum::Unit => write!(f, "()"),
            TypeEnum::Integer(size) => write!(f, "{size}"),
            TypeEnum::Pointer(ty, region) => {
                write!(f, "^(@{}){}", region.display(self.1), ty.display(self.1))
            }
            TypeEnum::PointerSlice(ty, region, sentinel) => {
                write!(f, "^(@{})[", region.display(self.1))?;
                if let Some(Sentinel) = sentinel {
                    write!(f, ":0")?;
                }
                write!(f, "]{}", ty.display(self.1))?;
                Ok(())
            }
            TypeEnum::Array(ty, size, sentinel) => {
                write!(f, "[{}", size.display(self.1))?;
                if let Some(Sentinel) = sentinel {
                    write!(f, ":0")?;
                }
                write!(f, "]{}", ty.display(self.1))?;
                Ok(())
            }
        }
    }
}

impl fmt::Display for Interned<'_, Region> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1[self.0] {
            RegionEnum::Generic(ref param) => write!(f, "{}", param.display(self.1)),
        }
    }
}

impl fmt::Display for Interned<'_, Effect> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1[self.0] {
            EffectEnum::Generic(ref param) => write!(f, "{}", param.display(self.1)),
            EffectEnum::Item(ref item) => write!(f, "{}", item.display(self.1)),
            EffectEnum::Row(ref effects) => {
                for (i, effect) in effects.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", effect.display(self.1))?;
                }
                Ok(())
            }
            EffectEnum::Read(region) => write!(f, "read {}", region.display(self.1)),
            EffectEnum::Write(region) => write!(f, "write {}", region.display(self.1)),
            EffectEnum::Divergent => write!(f, "div"),
        }
    }
}

impl fmt::Display for Interned<'_, Constant> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1[self.0] {
            ConstantEnum::Generic(ref param) => write!(f, "{}", param.display(self.1)),
            ConstantEnum::True => write!(f, "True"),
            ConstantEnum::False => write!(f, "False"),
            ConstantEnum::Integer(integer) => write!(f, "{}", integer),
            // TODO: unescaping
            ConstantEnum::String(ref string) => write!(f, "\"{}\"", string),
            // TODO: unescaping
            ConstantEnum::Character(ref character) => write!(f, "'{}'", character),
            ConstantEnum::Zero => write!(f, "0"),
        }
    }
}

impl fmt::Display for Interned<'_, Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Type(ty) => write!(f, "{}", ty.display(self.1)),
            Term::Region(region) => write!(f, "{}", region.display(self.1)),
            Term::Effect(effect) => write!(f, "{}", effect.display(self.1)),
            Term::Constant(constant) => write!(f, "{}", constant.display(self.1)),
        }
    }
}

impl fmt::Display for Interned<'_, GenericArgument> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(arity) = self.0.arity {
            for _ in 0..arity {
                write!(f, "λ ")?;
            }
        }
        write!(f, "{}", self.0.term.display(self.1))?;
        Ok(())
    }
}

impl fmt::Display for Interned<'_, FunctionSignature> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sig = &self.1[self.0];
        if let Some(params) = &sig.type_params {
            for &param in params.iter() {
                write!(f, "∀")?;
                if self.1[param] != KindEnum::TYPE {
                    write!(f, ":")?;
                    if param.enclosed(self.1) {
                        write!(f, "({})", param.display(self.1))?;
                    } else {
                        write!(f, "{}", param.display(self.1))?;
                    }
                }
                write!(f, " ")?;
            }
        }
        for _ in 0..sig.implicit_regions {
            write!(f, "∀:REGION ")?;
        }

        if let Some(params) = &sig.params {
            for ty in params.iter().copied() {
                match ty {
                    FunctionParameter::Data(ty) => {
                        write!(f, "{} -> ", ty.display(self.1))?;
                    }
                    FunctionParameter::Lambda(sig) => {
                        if sig.enclosed(self.1) {
                            write!(f, "({}) -> ", sig.display(self.1))?;
                        } else {
                            write!(f, "{} -> ", sig.display(self.1))?;
                        }
                    }
                }
            }
        }

        write!(f, "⟨{}⟩ ", sig.effect.display(self.1))?;

        match sig.returns {
            FunctionReturns::Data(ty) => write!(f, "{}", ty.display(self.1))?,
            FunctionReturns::Never => write!(f, "Void")?,
        }
        Ok(())
    }
}

impl Kind {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        tt[self].params.is_some()
    }
}
impl Type {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            TypeEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
            TypeEnum::Item(item) => item.apply.is_some(),
            _ => false,
        }
    }
}
impl Region {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            RegionEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
        }
    }
}
impl Effect {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            EffectEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
            EffectEnum::Item(item) => item.apply.is_some(),
            EffectEnum::Row(_) => true,
            EffectEnum::Read(_) => true,
            EffectEnum::Write(_) => true,
            EffectEnum::Divergent => false,
        }
    }
}
impl Constant {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            ConstantEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
            _ => false,
        }
    }
}
impl Term {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        match self {
            Term::Type(ty) => ty.enclosed(tt),
            Term::Region(region) => region.enclosed(tt),
            Term::Effect(effect) => effect.enclosed(tt),
            Term::Constant(constant) => constant.enclosed(tt),
        }
    }
}
impl GenericArgument {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        self.arity.unwrap_or(0) > 0 || self.term.enclosed(tt)
    }
}
impl FunctionSignature {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    fn enclosed(self, tt: &TypeTable) -> bool {
        tt[self].type_params.is_some() || tt[self].implicit_regions > 0 || tt[self].params.is_some()
    }
}
impl GenericParameter {
    pub fn display(&self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
}
impl Item {
    pub fn display(&self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
}
