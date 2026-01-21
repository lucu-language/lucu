use anstyle::{AnsiColor, Color};

use crate::tokens::{Keyword, TokenEnum};

pub const KEYWORD: Color = Color::Ansi(AnsiColor::Cyan);
pub const LITERAL: Color = Color::Ansi(AnsiColor::BrightGreen);
pub const SYMBOL: Color = Color::Ansi(AnsiColor::BrightWhite);
pub const UNKNOWN: Color = Color::Ansi(AnsiColor::Red);

impl TokenEnum {
    pub fn color(self) -> Option<Color> {
        match self {
            TokenEnum::Keyword(Keyword::Unknown) | TokenEnum::Unknown => Some(UNKNOWN),
            TokenEnum::Keyword(_) => Some(KEYWORD),
            TokenEnum::Literal(_) => Some(LITERAL),
            TokenEnum::Open(_) | TokenEnum::Close(_) | TokenEnum::Symbol(_) => Some(SYMBOL),
            TokenEnum::Identifier => None,
            TokenEnum::Eof => None,
        }
    }
}
