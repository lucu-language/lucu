use std::str::FromStr;

use strum::EnumString;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
    Keyword(Keyword),
    Symbol(Symbol),
    Literal(Literal),
    Open(Group),
    Close(Group),
    Unknown,
}

impl Token {
    pub fn from_word(word: &str) -> Token {
        if word == "_" {
            return Token::Symbol(Symbol::Underscore);
        }

        let default = if word.starts_with('@') {
            Token::Keyword(Keyword::Unknown)
        } else {
            Token::Literal(Literal::Identifier)
        };

        Keyword::from_str(word)
            .map(Token::Keyword)
            .unwrap_or(default)
    }
    pub fn is_semicolon(self) -> bool {
        matches!(self, Token::Symbol(Symbol::Semicolon))
    }

    pub fn prevent_semi_after(self) -> bool {
        matches!(
            self,
            Token::Open(_)
                | Token::Symbol(Symbol::Arrow)
                | Token::Symbol(Symbol::Semicolon)
                | Token::Symbol(Symbol::Comma)
        )
    }
    pub fn prevent_semi_before(self) -> bool {
        matches!(
            self,
            Token::Close(_)
                | Token::Keyword(Keyword::With)
                | Token::Symbol(Symbol::Semicolon)
                | Token::Symbol(Symbol::Comma)
        )
    }
    pub fn starts_type(self) -> bool {
        matches!(
            self,
            Token::Symbol(Symbol::Question)
                | Token::Symbol(Symbol::Caret)
                | Token::Keyword(Keyword::Struct)
                | Token::Keyword(Keyword::Typeof)
                | Token::Keyword(Keyword::Type)
                | Token::Keyword(Keyword::Effect)
                | Token::Symbol(Symbol::Bang)
                | Token::Literal(Literal::Identifier)
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FullToken {
    pub token: Token,
    pub len: u16,
    pub start: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString)]
#[strum(serialize_all = "snake_case")]
pub enum Keyword {
    Import,
    With,
    Try,
    Let,
    Const,
    Mut,
    Default,
    Effect,
    Type,
    Fun,
    If,
    Else,
    Struct,
    Cast,
    Do,
    Break,
    Loop,
    Then,
    Case,

    #[strum(serialize = "@sizeof")]
    Sizeof,
    #[strum(serialize = "@alignof")]
    Alignof,
    #[strum(serialize = "@typeof")]
    Typeof,

    #[strum(disabled)]
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Symbol {
    Semicolon,     // ;
    Colon,         // :
    Tilde,         // ~
    Comma,         // ,
    Dot,           // .
    DotDot,        // ..
    Underscore,    // _
    Caret,         // ^
    Question,      // ?
    Equals,        // =
    EqualsEquals,  // ==
    Arrow,         // =>
    Dash,          // -
    DashDash,      // --
    DashDashDash,  // ---
    DashEquals,    // -=
    Plus,          // +
    PlusPlus,      // ++
    PlusEquals,    // +=
    Ampersand,     // &
    Slash,         // /
    SlashEquals,   // /=
    Star,          // *
    StarEquals,    // *=
    Percent,       // %
    PercentEquals, // %=
    Greater,       // >
    GreaterEquals, // >=
    Less,          // <
    LessEquals,    // <=
    Bang,          // !
    BangEquals,    // !=
    Zero,          // 0
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    String,
    Character,
    Integer,
    Identifier,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Group {
    Parenthesis, // ()
    Brace,       // {}
    Bracket,     // []
}
