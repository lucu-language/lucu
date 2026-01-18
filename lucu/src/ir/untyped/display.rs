use std::fmt::{self};

use crate::ir::untyped::{
    GenericArgument, GenericParameter, IR, IntSize, Integer, Item, Kind, KindEnum, Region, RegionEnum, Term, Type, TypeEnum, Untyped
};

#[derive(Clone, Copy)]
struct Interned<'a, T>(T, &'a IR);

impl fmt::Display for Interned<'_, Kind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = &self.1[self.0];
        if let Some(params) = &kind.params {
            write!(f, "(")?;
            for param in params.iter().copied() {
                write!(f, "{} -> ", param.display(self.1))?;
            }
        }
        match kind.output {
            KindEnum::Type => write!(f, "*")?,
            KindEnum::Effect => write!(f, "EFFECT")?,
            KindEnum::Region => write!(f, "REGION")?,
            KindEnum::Constant(ty) => write!(f, "{}", ty.display(self.1))?,
        }
        if kind.params.is_some() {
            write!(f, ")")?;
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
        if self.0.apply.is_some() {
            write!(f, "(")?;
        }
        write!(f, "{}", self.0.index)?;
        if let Some(args) = &self.0.apply {
            for arg in args.iter() {
                write!(f, " {}", arg.display(self.1))?;
            }
            write!(f, ")")?;
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
            TypeEnum::Struct(ref module, ref name, ref generic_arguments) => {
                if generic_arguments.is_some() {
                    write!(f, "(")?;
                }
                write!(f, "{}.{}", module.name(), name)?;
                if let Some(args) = generic_arguments {
                    for arg in args.iter() {
                        write!(f, " {}", arg.display(self.1))?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            TypeEnum::Boolean => write!(f, "Bool"),
            TypeEnum::Integer(size) => write!(f, "{size}"),
            TypeEnum::Pointer(ty, region) => {
                write!(f, "^{}@{}", ty.display(self.1), region.display(self.1))
            }
            TypeEnum::Slice(ty, region) => {
                write!(f, "[]{}@{}", ty.display(self.1), region.display(self.1))
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

impl fmt::Display for Interned<'_, Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Type(ty) => write!(f, "{}", ty.display(self.1)),
            Term::Region(region) => write!(f, "{}", region.display(self.1)),
        }
    }
}

impl fmt::Display for Interned<'_, GenericArgument> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(arity) = self.0.arity {
            write!(f, "(")?;
            for _ in 0..arity {
                write!(f, "λ ")?;
            }
        }
        write!(f, "{}", self.0.term.display(self.1))?;
        if self.0.arity.is_some() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Display for Interned<'_, &'_ Untyped> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, item) in self.0.items.iter() {
            match item {
                Item::Alias(kind, term) => {
                    writeln!(f, "{name} :: {}", kind.display(self.1))?;
                    write!(f, "{name} = ")?;
                    for _ in 0..self.1[*kind]
                        .params
                        .as_ref()
                        .map(|params| params.len())
                        .unwrap_or(0)
                    {
                        write!(f, "λ ")?;
                    }
                    writeln!(f, "{}", term.display(self.1))?;
                }
                Item::Struct(kind, struct_members) => {
                    writeln!(f, "{name} :: {}", kind.display(self.1))?;
                    write!(f, "{name} = ")?;
                    for _ in 0..self.1[*kind]
                        .params
                        .as_ref()
                        .map(|params| params.len())
                        .unwrap_or(0)
                    {
                        write!(f, "λ ")?;
                    }
                    writeln!(f, "{name} {{")?;
                    if let Some(struct_members) = struct_members {
                        for member in struct_members {
                            writeln!(f, "  {} :: {},", member.name, member.ty.display(self.1))?;
                        }
                    } else {
                        writeln!(f, "  ?")?;
                    }
                    writeln!(f, "}}")?;
                }
                Item::Effect => {
                    writeln!(f, "{name} :: EFFECT")?;
                }
                Item::EffectFunction => {
                    writeln!(f, "{name} :: ?")?;
                }
                Item::Function => {
                    writeln!(f, "{name} :: ?")?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl Kind {
    pub fn display(self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
impl Type {
    pub fn display(self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
impl Region {
    pub fn display(self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
impl Term {
    pub fn display(self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
impl GenericArgument {
    pub fn display(self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
impl GenericParameter {
    pub fn display(&self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
impl Untyped {
    pub fn display(&self, ir: &IR) -> impl fmt::Display {
        Interned(self, ir)
    }
}
