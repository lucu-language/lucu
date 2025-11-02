use compact_str::CompactString;

use crate::stage::lexer::Span;

#[derive(Clone, Copy, Debug)]
pub struct Spanned<T>(pub T, pub Span);

pub type String = Spanned<CompactString>;
pub type Ident = Spanned<CompactString>;

#[derive(Debug)]
pub struct Module {
    pub imports: Vec<Import>,
}

#[derive(Debug)]
pub struct Import {
    pub path: String,
    pub ident: Option<Ident>,
}
