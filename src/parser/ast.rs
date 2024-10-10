use std::collections::HashSet;

use crate::tree::{NodeData, NodeTree};

pub type ParseTree = NodeTree<NodeVariant>;

impl ParseTree {
    pub fn graphviz(&self, src: &str, mut w: impl std::io::Write) -> std::io::Result<()> {
        write!(w, "graph G{{")?;
        write!(w, "compound=true;")?;
        write!(w, "node[shape=box,style=\"filled\"];")?;
        let mut listed = HashSet::new();
        for node in self.iter().rev() {
            if matches!(self[node].variant, Some(NodeVariant::List(_))) {
                write!(w, "subgraph cluster{}{{", node)?;
                for child in self.children(node) {
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
                if !listed.contains(&node) {
                    write!(w, "a{}[label=\"", node)?;
                    self[node].display(src, &mut w)?;
                    if let Some(fillcolor) = self[node].fillcolor() {
                        write!(w, "\",fillcolor=\"{}", fillcolor)?;
                    }
                    write!(w, "\"];")?;
                }
                for child in self.children(node) {
                    let list = matches!(self[child].variant, Some(NodeVariant::List(_)));
                    if list {
                        if let Some(first) = self[child].left {
                            write!(w, "a{}--a{}[lhead=cluster{}];", node, first, child)?;
                        }
                    } else {
                        write!(w, "a{}--a{};", node, child)?;
                    }
                }
            }
        }
        write!(w, "}}")?;
        Ok(())
    }
}

fn inner(s: &str) -> &str {
    &s[1..s.len() - 1]
}

impl NodeData<NodeVariant> {
    pub fn fillcolor(&self) -> Option<&'static str> {
        match self.variant.unwrap() {
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
    pub fn text<'a>(&self, src: &'a str) -> &'a str {
        match self.variant.unwrap() {
            NodeVariant::Identifier(Identifier::Identifier)
            | NodeVariant::Constant(Constant::Integer) => src[self.location].trim(),
            NodeVariant::Constant(Constant::String | Constant::Character) => {
                inner(src[self.location].trim())
            }
            _ => "",
        }
    }
    pub fn display(&self, src: &str, mut w: impl std::io::Write) -> std::io::Result<()> {
        match self.variant.unwrap() {
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
            NodeVariant::Constant(Constant::Case) => write!(w, "const case"),
            NodeVariant::ConstantCase | NodeVariant::ExpressionCase => write!(w, "case"),
            NodeVariant::Identifier(Identifier::Identifier)
            | NodeVariant::Constant(Constant::Integer) => {
                write!(w, "{}", src[self.location].trim(),)
            }
            NodeVariant::Constant(Constant::String) => {
                write!(w, "\\\"{}\\\"", inner(src[self.location].trim()),)
            }
            NodeVariant::Constant(Constant::Character) => {
                write!(w, "'{}'", inner(src[self.location].trim()),)
            }
            NodeVariant::Identifier(Identifier::PackagedIdentifier) => write!(w, "pkg ident"),
            NodeVariant::Identifier(Identifier::FullIdentifier) => write!(w, "full ident"),
            NodeVariant::Expression(Expression::Block) => write!(w, "body"),
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
            NodeVariant::Expression(Expression::Member) => write!(w, "."),
            NodeVariant::Expression(Expression::Case) => write!(w, "expr case"),
            NodeVariant::Expression(_) => todo!("{:?}", self.variant),
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

    ConstrainedDefinition, // with (constraints?) (def) / with (constraints?) (full defs)

    NamedSignature,     // (name) (fun sig)
    FunctionSignature,  // (fun params) (type?)
    FunctionParameters, // (params?) { (block params?) }
    Arguments,          // (exprs?) { (lambdas?) }

    Handler, // (generic ident) { (full defs) } / (generic ident) { (lambda) }
    Lambda,  // (identifiers?) -> (exprs)

    Member,                      // (ident) : (type)
    Parameter { mutable: bool }, // (ident) : (type)
    BlockParameter,              // (named sig) (constraints?)

    Name,      // (ident) [ (typed names?) ]
    TypedName, // (name) : (type?)

    TypedIdentifier,   // (ident) : (type?)
    GenericIdentifier, // [ (typed names?) ] (full ident)

    ConstantCase,   // (constants?) => (constant)
    ExpressionCase, // (constants?) => (expression)

    // subvariants
    Expression(Expression),
    Definition(Definition),
    Type(Type),
    Constraint(Constraint),
    Constant(Constant),
    Identifier(Identifier),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Identifier {
    Identifier,         // leaf
    PackagedIdentifier, // (ident).(ident)
    FullIdentifier,     // (packaged ident) [ (constants) ]
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
    ConstantCases,
    ExpressionCases,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expression {
    TryWith, // try { (expr) } with (handlers?)
    If,      // if (expr) { (expr) } / if (expr) { (lambda) }
    Else,    // (if) else { (expr) }
    Loop,    // loop (expr)
    Case,    // case (expr) { (expr cases) }

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
    Block,         // { (exprs) }

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
    Constant, // (constant)
    Unify,    // (constant) ~ (constant)
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
    Case,      // case (constant) { (const cases) }
    Integer,   // leaf
    String,    // leaf
    Character, // leaf
    Zero,      // leaf
    Uninit,    // leaf
}
