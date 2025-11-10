use anstyle::{AnsiColor, Color};

use crate::stage::token::TokenKind;

impl TokenKind {
    pub fn color(self) -> Option<Color> {
        use AnsiColor::*;
        match self {
            TokenKind::Keyword(_) => Some(BrightCyan.into()),
            TokenKind::Literal(_) => Some(BrightGreen.into()),
            TokenKind::Open(_) | TokenKind::Close(_) => Some(BrightWhite.into()),
            TokenKind::Symbol(_) => Some(BrightWhite.into()),
            TokenKind::Unknown => Some(Red.into()),
            TokenKind::Identifier => None,
            TokenKind::Eof => None,
        }
    }
}
