pub mod parser;
pub mod visit;

use std::fmt::{self, Debug};

use compact_str::CompactString;

use crate::span::{HasSpan, Span, Spanned};

#[derive(Debug, PartialEq, Eq)]
pub struct String(pub Spanned<CompactString>);

#[derive(Debug, PartialEq, Eq)]
pub struct Ident(pub Spanned<CompactString>);

impl String {
    pub fn as_str(&self) -> &str {
        self.0.0.as_str()
    }
}

impl Ident {
    pub fn as_str(&self) -> &str {
        self.0.0.as_str()
    }
}

impl HasSpan for String {
    fn span(&self) -> Span {
        self.0.span()
    }
}

impl HasSpan for Ident {
    fn span(&self) -> Span {
        self.0.span()
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Module {
    pub imports: Vec<Import>,
    pub definitions: Vec<Definition>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Import {
    pub path: String,
    pub ident: Option<Ident>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Definition {
    Function(Function),
    Type(TypeAlias),
}

impl Definition {
    pub fn name(&self) -> Option<&Name> {
        match self {
            Definition::Function(fun) => Some(&fun.declaration.name),
            Definition::Type(ty) => Some(&ty.name),
        }
    }
    pub fn generics(&self) -> &[Generic] {
        // TODO: those without a name may also have generics
        self.name()
            .and_then(|name| name.generics.as_deref())
            .unwrap_or_default()
    }
    pub fn children(&self) -> &[Definition] {
        // TODO: children
        &[]
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Function {
    pub declaration: FunctionDeclaration,
    pub definition: Expression,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeAlias {
    pub name: Name,
    pub definition: Type,
}

pub type Kind = Spanned<KindEnum>;

#[derive(Debug, PartialEq, Eq)]
pub enum KindEnum {
    Type,
    Constant(Type),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Generic {
    pub name: Name,
    pub kind: Option<Kind>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Name {
    pub ident: Ident,
    pub generics: Option<Vec<Generic>>,
}

impl Name {
    pub fn as_str(&self) -> &str {
        self.ident.as_str()
    }
}

#[derive(PartialEq, Eq)]
pub struct Path {
    pub package: Option<Ident>,
    pub name: Ident,
}

impl Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.package {
            Some(pkg) => write!(f, "\"{}.{}\"", pkg.0, self.name.0),
            None => write!(f, "\"{}\"", self.name.0),
        }
    }
}

pub type Type = Box<Spanned<TypeEnum>>;

#[derive(Debug, PartialEq, Eq)]
pub enum TypeEnum {
    Int,
    Path(Path),
    Struct(Struct),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Struct {
    pub members: Vec<StructMember>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StructMember {
    Data(Ident, Type),
}

pub type Expression = Box<Spanned<ExpressionEnum>>;

#[derive(Debug, PartialEq, Eq)]
pub enum ExpressionEnum {
    Block,
}

#[derive(Debug, PartialEq, Eq)]
pub enum FunctionParameter {
    Data(Ident, Type),
    Lambda(FunctionDeclaration),
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionDeclaration {
    pub name: Name,
    pub parameters: Option<Vec<FunctionParameter>>,
    pub returns: Option<Returns>,
}

pub type Returns = Spanned<ReturnsEnum>;

#[derive(Debug, PartialEq, Eq)]
pub enum ReturnsEnum {
    Never,
    Data(Type),
}
