use std::fmt;

use crate::ir::{EffectDefinition, FunctionDefinition, IR, Item, Parent, TypeTable};

#[derive(Clone, Copy)]
struct Interned<'a, T>(T, &'a TypeTable);

impl fmt::Display for Interned<'_, &'_ IR> {
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

impl IR {
    pub fn display(&self, tt: &TypeTable) -> impl fmt::Display {
        Interned(self, tt)
    }
}
