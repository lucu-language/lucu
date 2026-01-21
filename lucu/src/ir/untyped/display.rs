use std::fmt;

use crate::ir::untyped::{
    Effect, EffectDefinition, EffectEnum, FunctionDefinition, FunctionParameter, FunctionReturns,
    FunctionSignature, GenericArgument, GenericParameter, IntSize, Integer, Item, Kind, KindEnum,
    Parent, Region, RegionEnum, SimpleKind, Term, Type, TypeEnum, TypeTable, Untyped,
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
        let prefix = if self.signed { 'I' } else { 'U' };
        match (self.signed, self.size) {
            (true, IntSize::Register) => write!(f, "Int"),
            (false, IntSize::Register) => write!(f, "UInt"),
            (_, IntSize::Exact(size)) => write!(f, "{prefix}{size}"),
            (_, IntSize::Address) => write!(f, "{prefix}Ptr"),
            (_, IntSize::Index) => write!(f, "{prefix}Size"),
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

impl fmt::Display for Interned<'_, Type> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1[self.0] {
            TypeEnum::Generic(ref param) => {
                write!(f, "{}", param.display(self.1))
            }
            TypeEnum::Item(ref module, ref name, ref generic_arguments) => {
                if module.name() != "preamble" {
                    write!(f, "{}.", module.name())?;
                }
                write!(f, "{name}")?;
                if let Some(args) = generic_arguments {
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
            TypeEnum::Boolean => write!(f, "Bool"),
            TypeEnum::Unit => write!(f, "()"),
            TypeEnum::Integer(size) => write!(f, "{size}"),
            TypeEnum::Pointer(ty, region) => {
                write!(f, "^{}@{}", ty.display(self.1), region.display(self.1))
            }
            TypeEnum::Slice(ty, region) => {
                write!(f, "[{}]@{}", ty.display(self.1), region.display(self.1))
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
            EffectEnum::Item(ref module, ref name, ref generic_arguments) => {
                if module.name() != "preamble" {
                    write!(f, "{}.", module.name())?;
                }
                write!(f, "{name}")?;
                if let Some(args) = generic_arguments {
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
    }
}

impl fmt::Display for Interned<'_, Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Type(ty) => write!(f, "{}", ty.display(self.1)),
            Term::Region(region) => write!(f, "{}", region.display(self.1)),
            Term::Effect(effect) => write!(f, "{}", effect.display(self.1)),
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

        write!(f, "⟨")?;
        for (i, effect) in sig.effects.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(f, "{}", effect.display(self.1))?;
        }
        write!(f, "⟩ ")?;

        match sig.returns {
            FunctionReturns::Data(ty) => write!(f, "{}", ty.display(self.1))?,
            FunctionReturns::Never => write!(f, "Void")?,
        }
        Ok(())
    }
}

impl fmt::Display for Interned<'_, &'_ Untyped> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (name, &item)) in self.0.items.iter().enumerate() {
            if let Item::Function(_, Parent::Effect(_)) = item {
                continue;
            }
            if i > 0 {
                writeln!(f)?;
            }
            match item {
                Item::Alias(kind, term) => {
                    writeln!(f, "{name} :: {}", kind.display(self.1))?;
                    write!(f, "{name} = ")?;
                    for _ in 0..self.1[kind]
                        .params
                        .as_ref()
                        .map(|params| params.len())
                        .unwrap_or(0)
                    {
                        write!(f, "λ ")?;
                    }
                    writeln!(f, "{}", term.display(self.1))?;
                }
                Item::Struct(kind, def) => {
                    writeln!(f, "{name} :: {}", kind.display(self.1))?;
                    write!(f, "{name} = ")?;
                    for _ in 0..self.1[kind]
                        .params
                        .as_ref()
                        .map(|params| params.len())
                        .unwrap_or(0)
                    {
                        write!(f, "λ ")?;
                    }
                    writeln!(f, "{name} {{")?;
                    for member in &self.0[def].members {
                        writeln!(f, "  {} :: {},", member.name, member.ty.display(self.1))?;
                    }
                    writeln!(f, "}}")?;
                }
                Item::Effect(kind, def) => {
                    writeln!(f, "{name} :: {}", kind.display(self.1))?;

                    if let EffectDefinition::Body { members } = &self.0[def] {
                        write!(f, "{name} = ")?;
                        for _ in 0..self.1[kind]
                            .params
                            .as_ref()
                            .map(|params| params.len())
                            .unwrap_or(0)
                        {
                            write!(f, "λ ")?;
                        }

                        writeln!(f, "{name} {{")?;
                        for member in members {
                            writeln!(
                                f,
                                "  {} :: {},",
                                member.name,
                                member.signature.display(self.1)
                            )?;
                        }
                        writeln!(f, "}}")?;
                    }
                }
                Item::Function(sign, def) => {
                    let Parent::TopLevel(def) = def else {
                        unreachable!()
                    };
                    writeln!(f, "{name} :: {}", sign.display(self.1))?;

                    if let FunctionDefinition::Expression { captures, body } = &self.0[def] {
                        // TODO
                    }
                }
            }
        }
        Ok(())
    }
}

impl Kind {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        tt[self].params.is_some()
    }
}
impl Type {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            TypeEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
            TypeEnum::Item(_, _, generic_arguments) => generic_arguments.is_some(),
            _ => false,
        }
    }
}
impl Region {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            RegionEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
        }
    }
}
impl Effect {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            EffectEnum::Generic(generic_parameter) => generic_parameter.apply.is_some(),
            EffectEnum::Item(_, _, generic_arguments) => generic_arguments.is_some(),
        }
    }
}
impl Term {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        match self {
            Term::Type(ty) => ty.enclosed(tt),
            Term::Region(region) => region.enclosed(tt),
            Term::Effect(effect) => effect.enclosed(tt),
        }
    }
}
impl GenericArgument {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        self.arity.unwrap_or(0) > 0 || self.term.enclosed(tt)
    }
}
impl FunctionSignature {
    pub fn display(self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
    pub fn enclosed(self, tt: &TypeTable) -> bool {
        tt[self].type_params.is_some() || tt[self].params.is_some()
    }
}
impl GenericParameter {
    pub fn display(&self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
}
impl Untyped {
    pub fn display(&self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
}
