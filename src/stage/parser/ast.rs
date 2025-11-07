use std::fmt::{Debug, Display};

use compact_str::CompactString;

use crate::stage::lexer::token::Span;

pub type String = Spanned<CompactString>;
pub type Ident = Spanned<CompactString>;

#[derive(Debug)]
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
}

impl Definition {
    pub fn name(&self) -> Option<&Name> {
        match self {
            Definition::Function(function) => Some(&function.declaration.name),
        }
    }
}

#[derive(Debug)]
pub struct Function {
    pub declaration: FunctionDeclaration,
    pub definition: Expression,
}

pub type Kind = Box<Spanned<KindEnum>>;

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

pub type Type = Box<Spanned<TypeEnum>>;

#[derive(Debug)]
pub enum TypeEnum {
    Int,
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
    pub return_ty: Option<Type>,
}

#[derive(Clone, Copy)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Debug for Spanned<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> Display for Spanned<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
