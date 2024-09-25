use std::{
    collections::HashSet,
    fmt,
    num::NonZeroU32,
    ops::{Index, IndexMut},
};

#[derive(Clone, Debug)]
pub struct NodeData {
    pub variant: NodeVariant,
    pub len: u32,
    pub start: u32,
    pub left: Option<NonZeroU32>,
    pub right: Option<NonZeroU32>,
}

impl NodeData {
    pub fn first_child(&self) -> Option<NonZeroU32> {
        self.left.or(self.right)
    }
    pub fn last_child(&self) -> Option<NonZeroU32> {
        self.right.or(self.left)
    }
}

pub struct Nodes {
    nodes: Vec<NodeData>,
}

impl Nodes {
    pub fn new() -> Self {
        Self {
            nodes: vec![NodeData {
                variant: NodeVariant::Dummy,
                len: 0,
                start: 0,
                left: None,
                right: None,
            }],
        }
    }
    pub fn push(&mut self, data: NodeData) -> NonZeroU32 {
        self.nodes.push(data);
        NonZeroU32::new((self.nodes.len() - 1) as u32).unwrap()
    }
    pub fn get(&self, node: u32) -> Option<&NodeData> {
        self.nodes.get(node as usize)
    }
    pub fn get_mut(&mut self, node: u32) -> Option<&mut NodeData> {
        self.nodes.get_mut(node as usize)
    }
    pub fn children_rev(&self, node: u32) -> impl Iterator<Item = u32> + '_ {
        NodeChildren::new(&self.nodes, node)
    }

    fn draw(&self, node: u32, spaces: u32, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{: <2$}{:?}",
            "", self.nodes[node as usize], spaces as usize
        )?;

        let children_rev = self.children_rev(node).collect::<Box<[_]>>();
        children_rev
            .iter()
            .rev()
            .copied()
            .map(|c| self.draw(c, spaces + 2, f))
            .collect::<fmt::Result>()?;

        Ok(())
    }

    pub fn graphviz(&self, src: &str, mut w: impl std::io::Write) -> std::io::Result<()> {
        write!(w, "graph G{{")?;
        write!(w, "compound=true;")?;
        write!(w, "node[shape=box,style=\"filled\"];")?;
        let mut listed = HashSet::new();
        for (i, node) in self.nodes.iter().enumerate().skip(1).rev() {
            let mut children = self.children_rev(i as u32).collect::<Box<[_]>>();
            children.reverse();

            if matches!(node.variant, NodeVariant::List(_)) {
                write!(w, "subgraph cluster{}{{", i)?;
                for child in children.iter().copied() {
                    listed.insert(child);

                    write!(w, "a{}[label=\"", child)?;
                    let data = &self.get(child).unwrap();
                    data.display(src, &mut w)?;
                    if let Some(fillcolor) = data.fillcolor() {
                        write!(w, "\",fillcolor=\"{}", fillcolor)?;
                    }
                    write!(w, "\"];")?;
                }
                write!(w, "}}")?;
            } else {
                if !listed.contains(&(i as u32)) {
                    write!(w, "a{}[label=\"", i)?;
                    node.display(src, &mut w)?;
                    if let Some(fillcolor) = node.fillcolor() {
                        write!(w, "\",fillcolor=\"{}", fillcolor)?;
                    }
                    write!(w, "\"];")?;
                }
                for child in children.iter().copied() {
                    let data = self.get(child).unwrap();
                    let list = matches!(data.variant, NodeVariant::List(_));
                    if list {
                        if let Some(first) = data.first_child() {
                            write!(w, "a{}--a{}[lhead=cluster{}];", i, first, child)?;
                        }
                    } else {
                        write!(w, "a{}--a{};", i, child)?;
                    }
                }
            }
        }
        write!(w, "}}")?;
        Ok(())
    }
}

impl fmt::Debug for Nodes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.draw(self.nodes.len() as u32 - 1, 0, f)
    }
}

impl NodeData {
    pub fn fillcolor(&self) -> Option<&'static str> {
        match self.variant {
            NodeVariant::ConstrainedDefinition => Some("cornflowerblue"),
            NodeVariant::Definition(Definition::Constant) => Some("indianred2"),
            NodeVariant::Definition(Definition::Effect) => Some("lawngreen"),
            NodeVariant::Definition(Definition::Type) => Some("paleturquoise"),
            NodeVariant::Definition(Definition::Function) => Some("violet"),
            NodeVariant::Definition(Definition::Default) => Some("orange"),
            NodeVariant::Expression(_) => Some("green"),
            NodeVariant::Type(_) => Some("turquoise"),
            NodeVariant::Constant(_) => Some("cornsilk"),
            NodeVariant::Identifier(Identifier::Identifier) => Some("white"),
            _ => None,
        }
    }
    pub fn display(&self, src: &str, mut w: impl std::io::Write) -> std::io::Result<()> {
        match self.variant {
            NodeVariant::List(_) => write!(w, "list"),
            NodeVariant::Lucu => write!(w, "HEAD"),
            NodeVariant::Import => write!(w, "import"),
            NodeVariant::ConstrainedDefinition => write!(w, "def"),
            NodeVariant::NamedSignature => write!(w, "named fun sign"),
            NodeVariant::FunctionSignature => write!(w, "fun sign"),
            NodeVariant::FunctionParameters => write!(w, "params"),
            NodeVariant::Arguments => write!(w, "args"),
            NodeVariant::Handler => write!(w, "handler"),
            NodeVariant::Lambda => write!(w, "lambda"),
            NodeVariant::Member => write!(w, "member"),
            NodeVariant::Parameter { mutable: true } => write!(w, "mut member"),
            NodeVariant::Parameter { mutable: false } => write!(w, "member"),
            NodeVariant::BlockParameter => write!(w, "block param"),
            NodeVariant::Name => write!(w, "name"),
            NodeVariant::TypedName => write!(w, "typed name"),
            NodeVariant::TypedIdentifier => write!(w, "typed ident"),
            NodeVariant::GenericIdentifier => write!(w, "generic ident"),
            NodeVariant::Definition(Definition::Constant) => write!(w, "def const"),
            NodeVariant::Definition(Definition::Effect) => write!(w, "def effect"),
            NodeVariant::Definition(Definition::Type) => write!(w, "def type"),
            NodeVariant::Definition(Definition::Function) => write!(w, "def fun"),
            NodeVariant::Definition(Definition::Default) => write!(w, "default"),
            NodeVariant::Type(Type::Path) => write!(w, "type path"),
            NodeVariant::Type(Type::Slice) => write!(w, "[]"),
            NodeVariant::Type(Type::Array) => write!(w, "type array"),
            NodeVariant::Type(Type::Pointer { maybe: true }) => write!(w, "?^"),
            NodeVariant::Type(Type::Pointer { maybe: false }) => write!(w, "^"),
            NodeVariant::Type(Type::Struct) => write!(w, "type struct"),
            NodeVariant::Type(Type::Typeof) => write!(w, "@typeof"),
            NodeVariant::Type(Type::Type) => write!(w, "type"),
            NodeVariant::Type(Type::Effect) => write!(w, "effect"),
            NodeVariant::Type(Type::Never) => write!(w, "!"),
            NodeVariant::Constraint(_) => write!(w, "constraint"),
            NodeVariant::Constant(Constant::Path) => write!(w, "const path"),
            NodeVariant::Constant(Constant::Type) => write!(w, "const type"),
            NodeVariant::Constant(Constant::Sizeof) => write!(w, "@sizeof"),
            NodeVariant::Constant(Constant::Alignof) => write!(w, "@alignof"),
            NodeVariant::Constant(Constant::Array) => write!(w, "const array"),
            NodeVariant::Constant(Constant::Struct) => write!(w, "const struct"),
            NodeVariant::Constant(Constant::Zero) => write!(w, "0"),
            NodeVariant::Constant(Constant::Uninit) => write!(w, "---"),
            NodeVariant::Identifier(Identifier::Identifier)
            | NodeVariant::Constant(Constant::Integer) => write!(
                w,
                "{}",
                &src[self.start as usize..(self.start + self.len) as usize],
            ),
            NodeVariant::Constant(Constant::String) => write!(
                w,
                "\\\"{}\\\"",
                &src[self.start as usize + 1..(self.start + self.len) as usize - 1],
            ),
            NodeVariant::Constant(Constant::Character) => write!(
                w,
                "'{}'",
                &src[self.start as usize + 1..(self.start + self.len) as usize - 1],
            ),
            NodeVariant::Identifier(Identifier::PackagedIdentifier) => write!(w, "pkg ident"),
            NodeVariant::Identifier(Identifier::FullIdentifier) => write!(w, "full ident"),
            NodeVariant::Dummy => Ok(()),
            NodeVariant::Expression(Expression::Body) => write!(w, "body"),
            NodeVariant::Expression(Expression::Cast) => write!(w, "cast"),
            NodeVariant::Expression(Expression::Typed) => write!(w, ":"),
            NodeVariant::Expression(Expression::Reference) => write!(w, "&"),
            NodeVariant::Expression(Expression::Dereference) => write!(w, "^"),
            NodeVariant::Expression(Expression::Constant) => write!(w, "expr constant"),
            NodeVariant::Expression(Expression::Path) => write!(w, "expr path"),
            NodeVariant::Expression(Expression::TryWith) => write!(w, "try"),
            NodeVariant::Expression(Expression::Call) => write!(w, "call"),
            NodeVariant::Expression(Expression::Struct) => write!(w, "expr struct"),
            NodeVariant::Expression(Expression::If) => write!(w, "if"),
            NodeVariant::Expression(Expression::Else) => write!(w, "else"),
            NodeVariant::Expression(Expression::Let { mutable: true }) => write!(w, "let mut"),
            NodeVariant::Expression(Expression::Let { mutable: false }) => write!(w, "let"),
            NodeVariant::Expression(Expression::Loop) => write!(w, "loop"),
            NodeVariant::Expression(Expression::Break) => write!(w, "break"),
            NodeVariant::Expression(Expression::Equals) => write!(w, "=="),
            NodeVariant::Expression(Expression::Index) => write!(w, "[]"),
            NodeVariant::Expression(Expression::PostIncrement) => write!(w, "post ++"),
            NodeVariant::Expression(Expression::Range) => write!(w, ".."),
            NodeVariant::Expression(Expression::Add) => write!(w, "+"),
            NodeVariant::Expression(Expression::Do) => write!(w, "do"),
            NodeVariant::Expression(Expression::Array) => write!(w, "expr array"),
            NodeVariant::Expression(Expression::Assign) => write!(w, "="),
            NodeVariant::Expression(_) => todo!("{:?}", self.variant),
        }
    }
}

impl Index<u32> for Nodes {
    type Output = NodeData;

    fn index(&self, index: u32) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl IndexMut<u32> for Nodes {
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

struct NodeChildren<'a>(&'a [NodeData], u32, bool);

impl<'a> NodeChildren<'a> {
    fn new(nodes: &'a [NodeData], parent: u32) -> Self {
        let node = &nodes[parent as usize];
        if matches!(node.variant, NodeVariant::List(_)) {
            if node.first_child().is_none() {
                NodeChildren(&[], 0, false)
            } else {
                let until_last = &nodes[..=node.last_child().unwrap().get() as usize];
                let first = node.first_child().unwrap().get();
                NodeChildren(until_last, first, false)
            }
        } else {
            if node.first_child().is_none() {
                NodeChildren(&[], 0, true)
            } else {
                let min = node
                    .last_child()
                    .unwrap()
                    .min(node.first_child().unwrap())
                    .get();
                let max = node
                    .last_child()
                    .unwrap()
                    .max(node.first_child().unwrap())
                    .get();
                let until_last = &nodes[..=max as usize];
                NodeChildren(until_last, min, true)
            }
        }
    }
}

impl Iterator for NodeChildren<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.0.last() {
            // skip children of nodes
            let mut last = self.0.len() - 1;
            if !self.2 {
                let mut node = next;
                while let Some(child) = node.first_child() {
                    last = child.get() as usize;
                    node = &self.0[last];
                }
            }

            let next = self.0.len() - 1;

            // stop when target is reached
            if self.2 {
                if next != self.1 as usize {
                    self.0 = &self.0[..=self.1 as usize];
                } else {
                    self.0 = &[];
                }
            } else {
                if last > self.1 as usize {
                    self.0 = &self.0[..last];
                } else {
                    self.0 = &[];
                }
            }

            Some(next as u32)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NodeVariant {
    // lists
    List(List),

    // branches
    Lucu,   // (imports) (definitions)
    Import, // (string) (name?)

    ConstrainedDefinition, // (def) where (constraints?)

    NamedSignature,     // (name) (fun sig)
    FunctionSignature,  // (fun params) (type?)
    FunctionParameters, // (params?) { (block params?) }
    Arguments,          // (exprs?) { (lambdas)? }

    Handler, // (generic ident) { (full defs) } / (generic ident) { (lambda) }
    Lambda,  // (identifiers?) -> (exprs)

    Member,                      // (ident) : (type)
    Parameter { mutable: bool }, // (ident) : (type)
    BlockParameter,              // (named sig) (constraints?)

    Name,      // (ident) [ (typed names?) ]
    TypedName, // (name) : (type?)

    TypedIdentifier,   // (ident) : (type?)
    GenericIdentifier, // [ (typed names?) ] (full ident)

    // subvariants
    Expression(Expression),
    Definition(Definition),
    Type(Type),
    Constraint(Constraint),
    Constant(Constant),
    Identifier(Identifier),

    // dummy
    Dummy,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Identifier {
    Identifier,         // leaf
    PackagedIdentifier, // (ident?).(ident)
    FullIdentifier,     // (packaged ident) [ (constants?) ]
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum List {
    Expressions,
    ConstrainedDefinitions,
    Types,
    Constraints,
    TypedNames,
    Parameters,
    BlockParameters,
    Imports,
    Constants,
    Members,
    Identifiers,
    Lambdas,
    Handlers,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expression {
    TryWith, // try { (expr) } with (handlers?)
    If,      // if (expr) { (expr) } / if (expr) { (lambda) }
    Else,    // (if) else { (expr) }
    Loop,    // loop (expr)

    Break,                 // (expr?)
    Do,                    // (expr)
    Let { mutable: bool }, // let (typed ident) = (expr)

    Assign,        // (expr) = (expr)
    AssignAdd,     // (expr) += (expr)
    AssignSub,     // (expr) -= (expr)
    AssignDiv,     // (expr) /= (expr)
    AssignMul,     // (expr) *= (expr)
    AssignMod,     // (expr) %= (expr)
    Range,         // (expr) .. (expr)
    Equals,        // (expr) == (expr)
    NotEquals,     // (expr) != (expr)
    Greater,       // (expr) > (expr)
    GreaterEquals, // (expr) >= (expr)
    Less,          // (expr) < (expr)
    LessEquals,    // (expr) <= (expr)
    Add,           // (expr) + (expr)
    Sub,           // (expr) - (expr)
    Mul,           // (expr) * (expr)
    Div,           // (expr) / (expr)
    Mod,           // (expr) % (expr)
    Typed,         // (expr) : (type)
    Cast,          // cast (expr)
    Negate,        // -(expr)
    Plus,          // +(expr)
    Reference,     // &(expr)
    Dereference,   // (expr)^
    PreIncrement,  // ++(expr)
    PreDecrement,  // --(expr)
    PostDecrement, // (expr)--
    PostIncrement, // (expr)++
    Member,        // (expr).(id)
    Index,         // (expr) [ (exprs) ]
    Call,          // (packaged ident) (function arguments)
    Body,          // { (exprs) }

    // NOTE: full identifiers will be represented with E::Index(E::Path, ...)
    Path,     // (ident)
    Array,    // [ (exprs) ]
    Struct,   // ( (exprs) )
    Constant, // (constant)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Definition {
    Constant, // const (typed name) = (constant?)
    Effect,   // effect (name) = { (full defs?) } / effect (name) = [ (constraints?) ]
    Type,     // type (name) = (type?)
    Function, // fun (named sig) = (expr?)
    Default,  // default (generic ident) { (full defs?) } / default (generic ident) { (lambda?) }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Constraint {
    Handled,    // (full ident)
    UnifyTypes, // (type) ~ (type)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Type {
    Path,                    // (full ident)
    Slice,                   // [] (type)
    Array,                   // [(integer)] (type)
    Pointer { maybe: bool }, // ^(type)
    Struct,                  // struct ( (members) )
    Typeof,                  // @typeof (const)
    Type,                    // leaf
    Effect,                  // leaf
    Never,                   // leaf
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Constant {
    Path,      // (full ident)
    Type,      // (type)
    Sizeof,    // @sizeof (type)
    Alignof,   // @alignof (type)
    Array,     // [ (constants) ]
    Struct,    // ( (constants) )
    Integer,   // leaf
    String,    // leaf
    Character, // leaf
    Zero,      // leaf
    Uninit,    // leaf
}
