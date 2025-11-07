use std::fmt::{self, Debug, Display};

use compact_str::CompactString;

use crate::stage::lexer::token::Span;

#[derive(Debug)]
pub struct String(pub Spanned<CompactString>);

#[derive(Debug)]
pub struct Ident(pub Spanned<CompactString>);

#[derive(Debug, Default)]
pub struct Module {
    pub imports: Vec<Import>,
    pub definitions: Vec<Definition>,
}

#[derive(Debug)]
pub struct Import {
    pub path: String,
    pub ident: Option<Ident>,
}

#[derive(Debug)]
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
}

#[derive(Debug)]
pub struct Function {
    pub declaration: FunctionDeclaration,
    pub definition: Expression,
}

#[derive(Debug)]
pub struct TypeAlias {
    pub name: Name,
    pub definition: Type,
}

pub type Kind = Spanned<KindEnum>;

#[derive(Debug)]
pub enum KindEnum {
    Type,
    Constant(Type),
}

#[derive(Debug)]
pub struct Generic {
    pub name: Name,
    pub kind: Option<Kind>,
}

#[derive(Debug)]
pub struct Name {
    pub ident: Ident,
    pub generics: Option<Vec<Generic>>,
}

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

#[derive(Debug)]
pub enum TypeEnum {
    Int,
    Path(Path),
    Struct(Struct),
}

#[derive(Debug)]
pub struct Struct {
    pub members: Vec<StructMember>,
}

#[derive(Debug)]
pub enum StructMember {
    Data(Ident, Type),
}

pub type Expression = Box<Spanned<ExpressionEnum>>;

#[derive(Debug)]
pub enum ExpressionEnum {
    Block,
}

#[derive(Debug)]
pub enum FunctionParameter {
    Data(Ident, Type),
    Lambda(FunctionDeclaration),
}

#[derive(Debug)]
pub struct FunctionDeclaration {
    pub name: Name,
    pub parameters: Option<Vec<FunctionParameter>>,
    pub returns: Option<Returns>,
}

pub type Returns = Spanned<ReturnsEnum>;

#[derive(Debug)]
pub enum ReturnsEnum {
    Never,
    Data(Type),
}

#[derive(Clone, Copy)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Debug for Spanned<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> Display for Spanned<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
