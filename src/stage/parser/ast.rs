use compact_str::CompactString;

use crate::stage::lexer::Span;

#[derive(Clone, Copy, Debug)]
pub struct Spanned<T>(pub T, pub Span);

pub type String = Spanned<CompactString>;
pub type Ident = Spanned<CompactString>;

impl Ident {
    pub fn valid(&self) -> bool {
        let alphanumeric = self
            .0
            .as_bytes()
            .iter()
            .all(|c| c.is_ascii_alphanumeric() || *c == b'_');
        let not_number =
            self.0.starts_with('_') || self.0.as_bytes().iter().any(|c| c.is_ascii_alphabetic());
        alphanumeric && not_number
    }
}

#[derive(Debug)]
pub struct Module {
    pub imports: Vec<Import>,
}

#[derive(Debug)]
pub struct Import {
    pub path: String,
    pub ident: Option<Ident>,
}
