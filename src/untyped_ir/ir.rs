use std::{
    collections::HashMap,
    fmt::{self, Display},
    num::NonZeroU32,
    ops::Index,
};

use string_interner::{backend::BufferBackend, symbol::SymbolU32, StringInterner};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Reg(pub NonZeroU32);

#[derive(Debug)]
pub struct File {
    strings: StringInterner<BufferBackend>,
    instructions: Vec<Instruction>,
    exports: HashMap<SymbolU32, Reg>,
}

impl File {
    pub(super) fn new() -> Self {
        Self {
            strings: StringInterner::new(),
            instructions: vec![Instruction::Dummy],
            exports: HashMap::new(),
        }
    }
    pub(super) fn push(&mut self, i: Instruction) -> Reg {
        let idx = self.instructions.len();
        self.instructions.push(i);
        Reg(unsafe { NonZeroU32::new_unchecked(idx as u32) })
    }
    pub(super) fn intern(&mut self, s: &str) -> SymbolU32 {
        self.strings.get_or_intern(s)
    }
    pub(super) fn get_interned(&self, s: &str) -> Option<SymbolU32> {
        self.strings.get(s)
    }
    pub(super) fn export(&mut self, r: Reg, s: &str) {
        let sym = self.intern(s);
        self.exports.insert(sym, r);
    }
}

impl Display for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for top in self.iter_top() {
            top.fmt(self, 0, f)?;
        }
        Ok(())
    }
}

impl Reg {
    fn fmt(self, file: &File, spaces: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if matches!(file[self], Instruction::BreakBlock { value: None, .. }) {
            return Ok(());
        }

        write!(f, "{: <1$}", "", spaces)?;
        write!(f, "%{} = ", self.0)?;
        write!(f, "{}", file[self])?;
        match file[self] {
            Instruction::Import { path: sym }
            | Instruction::String(sym)
            | Instruction::EffectDefinition(sym) => write!(f, "(\"{}\")", unsafe {
                file.strings.resolve_unchecked(sym)
            })?,
            Instruction::Block => {
                writeln!(f, " {{")?;
                for inner in file.iter_list(self) {
                    inner.fmt(file, spaces + 2, f)?;
                }
                let end = file.end(self);
                end.fmt(file, spaces + 2, f)?;
                write!(f, "{: <1$}", "", spaces)?;
                write!(f, "}}")?;
            }
            Instruction::List => {
                writeln!(f, " [")?;
                for inner in file.iter_list(self) {
                    inner.fmt(file, spaces + 2, f)?;
                }
                write!(f, "{: <1$}", "", spaces)?;
                write!(f, "]")?;
            }
            Instruction::Unify(left, right)
            | Instruction::TypeArray(left, right)
            | Instruction::HigherKind {
                args: left,
                output: right,
            }
            | Instruction::Call {
                fun: left,
                args: right,
            }
            | Instruction::If {
                cond: left,
                body: right,
            }
            | Instruction::Else {
                if_: left,
                body: right,
            }
            | Instruction::Resolve {
                higher: left,
                args: right,
            }
            | Instruction::HandlerDefinition {
                def: left,
                handler: right,
            } => write!(f, "(%{}, %{})", left.0, right.0)?,

            Instruction::BreakList { list: left }
            | Instruction::Generic { kind: left }
            | Instruction::Constraint { constant: left }
            | Instruction::Typeof(left)
            | Instruction::TypeSlice(left)
            | Instruction::BlockParam { def: left }
            | Instruction::Array { list: left }
            | Instruction::Loop { body: left } => write!(f, "(%{})", left.0)?,

            Instruction::Dummy
            | Instruction::Type
            | Instruction::Effect
            | Instruction::Never
            | Instruction::ValueUnit => write!(f, "()")?,

            Instruction::Param { mutable, typed } => {
                if mutable {
                    write!(f, "_mut")?;
                }
                write!(f, "(%{})", typed.0)?;
            }

            Instruction::DefinitionEffect { defs } => {
                write!(f, "(")?;
                if let Some(defs) = defs {
                    write!(f, "defs = %{}", defs.0)?;
                }
                write!(f, ")")?;
            }
            Instruction::Break { block, value } | Instruction::BreakBlock { block, value } => {
                write!(f, "(%{}", block.0)?;
                if let Some(value) = value {
                    write!(f, ", value = %{}", value.0)?;
                }
                write!(f, ")")?;
            }
            Instruction::Handler { effect, defs } => {
                write!(f, "(%{}", effect.0)?;
                if let Some(defs) = defs {
                    write!(f, ", defs = %{}", defs.0)?;
                }
                write!(f, ")")?;
            }
            Instruction::DefinitionConstant { kind, value } => {
                write!(f, "(")?;
                if let Some(kind) = kind {
                    write!(f, "kind = %{}", kind.0)?;
                }
                if kind.is_some() && value.is_some() {
                    write!(f, ", ")?;
                }
                if let Some(value) = value {
                    write!(f, "value = %{}", value.0)?;
                }
                write!(f, ")")?;
            }
            Instruction::DefinitionFunction { ret, body } => {
                write!(f, "(")?;
                if let Some(ret) = ret {
                    write!(f, "ret = %{}", ret.0)?;
                }
                if ret.is_some() && body.is_some() {
                    write!(f, ", ")?;
                }
                if let Some(body) = body {
                    write!(f, "body = %{}", body.0)?;
                }
                write!(f, ")")?;
            }

            Instruction::Integer(i) => write!(f, "({})", i)?,
            Instruction::Identifier { package, name } => {
                write!(f, "(\"{}\"", unsafe {
                    file.strings.resolve_unchecked(name)
                })?;
                if let Some(package) = package {
                    write!(f, ", pkg = \"{}\"", unsafe {
                        file.strings.resolve_unchecked(package)
                    })?;
                }
                write!(f, ")")?;
            }
        }
        writeln!(f)?;
        Ok(())
    }
}

impl File {
    pub fn get(&self, s: &str) -> Option<Reg> {
        self.strings
            .get(s)
            .and_then(|sym| self.exports.get(&sym))
            .copied()
    }
    pub fn iter_top(&self) -> impl Iterator<Item = Reg> + '_ {
        struct Top<'a> {
            file: &'a File,
            curr: Option<Reg>,
        }
        impl Iterator for Top<'_> {
            type Item = Reg;
            fn next(&mut self) -> Option<Self::Item> {
                let next = match self.curr {
                    Some(cur) => Reg(cur.0.saturating_add(1)),
                    None => Reg(unsafe { NonZeroU32::new_unchecked(1) }),
                };
                if next.0.get() as usize >= self.file.instructions.len() {
                    return None;
                }
                match self.file[next] {
                    Instruction::Block | Instruction::List => {
                        self.curr = Some(self.file.end(next));
                        Some(next)
                    }
                    _ => {
                        self.curr = Some(next);
                        Some(next)
                    }
                }
            }
        }
        Top {
            file: self,
            curr: None,
        }
    }
    pub fn iter_list(&self, start: Reg) -> impl Iterator<Item = Reg> + '_ {
        struct List<'a> {
            file: &'a File,
            start: Reg,
            curr: Reg,
        }
        impl Iterator for List<'_> {
            type Item = Reg;
            fn next(&mut self) -> Option<Self::Item> {
                let next = Reg(self.curr.0.saturating_add(1));
                match self.file[next] {
                    Instruction::BreakBlock { block, .. } if block == self.start => None,
                    Instruction::BreakList { list, .. } if list == self.start => None,
                    Instruction::Block | Instruction::List => {
                        self.curr = self.file.end(next);
                        Some(next)
                    }
                    _ => {
                        self.curr = next;
                        Some(next)
                    }
                }
            }
        }

        assert!(matches!(
            self[start],
            Instruction::List | Instruction::Block
        ));
        List {
            file: self,
            start,
            curr: start,
        }
    }
    pub fn end(&self, start: Reg) -> Reg {
        assert!(matches!(
            self[start],
            Instruction::Block | Instruction::List
        ));
        let idx = self
            .instructions
            .iter()
            .enumerate()
            .skip(start.0.get() as usize + 1)
            .find(|(_, i)| match i {
                Instruction::BreakBlock { block, .. } if *block == start => true,
                Instruction::BreakList { list, .. } if *list == start => true,
                _ => false,
            })
            .unwrap()
            .0;
        Reg(unsafe { NonZeroU32::new_unchecked(idx as u32) })
    }
}

impl Default for File {
    fn default() -> Self {
        Self::new()
    }
}

impl Index<Reg> for File {
    type Output = Instruction;

    fn index(&self, index: Reg) -> &Self::Output {
        &self.instructions[index.0.get() as usize]
    }
}

#[derive(Clone, Copy, Debug, strum::Display)]
#[strum(serialize_all = "snake_case")]
pub enum Instruction {
    Import {
        path: SymbolU32,
    },
    Block,
    BreakBlock {
        block: Reg,
        value: Option<Reg>,
    },

    List,
    BreakList {
        list: Reg,
    },

    // defines a generic of a definition
    // must be declared in the same block as the definition instruction
    Generic {
        kind: Reg,
    },
    // defines a constraint of a definition
    // must be declared in the same block as the definition instruction
    Constraint {
        constant: Reg,
    },
    // defines a function parameter
    // must be declared in the same block as the function instruction
    Param {
        mutable: bool,
        typed: Reg,
    },
    BlockParam {
        def: Reg, // block
    },

    HandlerDefinition {
        def: Reg,     // definition_...
        handler: Reg, // constraint
    },
    EffectDefinition(SymbolU32),

    DefinitionConstant {
        kind: Option<Reg>,
        value: Option<Reg>,
    },
    DefinitionFunction {
        ret: Option<Reg>,
        body: Option<Reg>,
    },
    DefinitionEffect {
        defs: Option<Reg>, // block
    },
    Handler {
        effect: Reg,
        defs: Option<Reg>, // list of definitions
    },

    // constant operations
    Unify(Reg, Reg),
    Typeof(Reg),
    TypeSlice(Reg),
    TypeArray(Reg, Reg),
    Integer(u64),
    String(SymbolU32),
    Resolve {
        higher: Reg,
        args: Reg, // list
    },

    // expressions
    Identifier {
        package: Option<SymbolU32>,
        name: SymbolU32,
    },
    HigherKind {
        args: Reg, // list
        output: Reg,
    },
    Array {
        list: Reg, // list
    },
    Call {
        fun: Reg,
        args: Reg, // list
    },
    Else {
        if_: Reg,
        body: Reg, // block
    },
    If {
        cond: Reg,
        body: Reg, // block
    },
    Loop {
        body: Reg, // block
    },
    Break {
        block: Reg,
        value: Option<Reg>,
    },

    // builtins
    Dummy,
    Type,
    Effect,
    Never,
    ValueUnit,
}
