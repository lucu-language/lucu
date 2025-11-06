use compact_str::CompactString;

use crate::stage::lexer::token::Span;

#[derive(Clone, Copy, Debug)]
pub struct Spanned<T>(pub T, pub Span);

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

#[derive(Debug)]
pub struct Function {
    pub name: Ident,
    pub signature: FunctionSignature,
    pub definition: Expression,
}

#[derive(Debug)]
pub enum Type {
    Int,
}

#[derive(Debug)]
pub enum Expression {
    Block,
}

#[derive(Debug)]
pub enum FunctionParameter {
    Data(Ident, Type),
    Lambda(Ident, FunctionSignature),
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub parameters: Option<Vec<FunctionParameter>>,
    pub return_ty: Option<Type>,
}
