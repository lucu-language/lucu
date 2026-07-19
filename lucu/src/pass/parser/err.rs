use std::borrow::Cow;

use crate::error::Diagnostic;
use crate::tokens::TokenEnum;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expected {
    Token(TokenEnum),
    Item,
    Type,
    Kind,
    Returns,
    Parameter,
    GenericArgument,
    GenericParameter,
    Constant,
    UsizeConstant,
    RegionKind,
    PointerRegion,
    Effect,
    Expression,
    Index,
    IfBlock,
}

impl Diagnostic for Expected {
    fn label(&self) -> Option<Cow<'_, str>> {
        match self {
            Expected::Token(token) => Some(format!("expected {}", token).into()),
            Expected::Item => Some("expected a definition".into()),
            Expected::Type => Some("expected a type".into()),
            Expected::Kind => Some("expected a kind or type".into()),
            Expected::Returns => Some("expected a type or '!'".into()),
            Expected::Parameter => Some("expected a function parameter".into()),
            Expected::GenericArgument => Some("expected a type or constant".into()),
            Expected::Constant => Some("expected a constant".into()),
            Expected::UsizeConstant => Some("expected a constant of type usize".into()),
            Expected::GenericParameter => Some("expected an identifier or 'mut'".into()),
            Expected::RegionKind => Some("expected an identifier or 'mut'".into()),
            Expected::PointerRegion => Some("expected '@', 'mut', or a type".into()),
            Expected::Effect => Some("expected an effect".into()),
            Expected::Expression => Some("expected an expression".into()),
            Expected::Index => Some("expected '..' or an expression".into()),
            Expected::IfBlock => Some("expected 'then' or '{'".into()),
        }
    }
}
