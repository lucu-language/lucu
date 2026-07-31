use std::fmt;

use crate::header::{Header, ItemDecl};
use crate::type_table::{EffectEnum, TypeTable};

#[derive(Clone, Copy)]
struct Interned<'a, T>(T, &'a TypeTable);

impl fmt::Display for Interned<'_, &'_ Header> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (name, item)) in self.0.items.iter().enumerate() {
            if let ItemDecl::Function(_, Some(_), _, _) = item {
                continue;
            }
            if i > 0 {
                writeln!(f)?;
            }
            match *item {
                ItemDecl::Alias(kind, term) => {
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
                ItemDecl::Struct(kind, ref def) => {
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
                    for member in &def.get().unwrap().members {
                        writeln!(f, "  {} :: {},", member.name, member.ty.display(self.1))?;
                    }
                    writeln!(f, "}}")?;
                }
                ItemDecl::Effect(kind, ref def) => {
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
                    for member in &def.get().unwrap().members {
                        writeln!(
                            f,
                            "  {} :: {},",
                            member.name,
                            member.signature.display(self.1)
                        )?;
                    }
                    writeln!(f, "}}")?;
                }
                ItemDecl::Function(sign, _, _, _) => {
                    writeln!(f, "{name} :: {}", sign.display(self.1))?;
                }
            }
        }
        for handler in self.0.global_handlers.iter() {
            writeln!(f)?;
            write!(f, "instance ")?;
            for _ in 0..handler
                .type_params
                .as_ref()
                .map(|params| params.len())
                .unwrap_or(0)
                + handler.implicit_regions
            {
                write!(f, "λ ")?;
            }
            if self.1[handler.with_effect] != EffectEnum::empty() {
                write!(f, "⟨{}⟩ => ", handler.with_effect.display(self.1))?;
            }
            writeln!(f, "{}", handler.effect.display(self.1))?;
        }
        Ok(())
    }
}

impl Header {
    pub fn display(&self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
}
