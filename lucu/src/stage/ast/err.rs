use std::borrow::Cow;

use crate::err::Diagnostic;
use crate::stage::token::TokenEnum;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expected {
    Token(TokenEnum),
    Definition,
    Type,
    Kind,
    Returns,
    FunctionParameter,
    GenericArgument,
}

impl Diagnostic for Expected {
    fn label(&self) -> Option<Cow<'_, str>> {
        match self {
            Expected::Token(token) => Some(format!("expected {}", token).into()),
            Expected::Definition => Some("expected a definition".into()),
            Expected::Type => Some("expected a type".into()),
            Expected::Kind => Some("expected a kind or type".into()),
            Expected::Returns => Some("expected a type, '!', or 'with'".into()),
            Expected::FunctionParameter => Some("expected a function parameter".into()),
            Expected::GenericArgument => Some("expected a type or constant".into()),
        }
    }
}
