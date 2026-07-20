pub mod ansi;

use std::fmt::{self, Debug, Display};
use std::str::FromStr;

use strum::{EnumString, IntoStaticStr};

use crate::span::{HasSpan, Span};

impl HasSpan for Token {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub enum TokenEnum {
    Keyword(Keyword),
    Symbol(Symbol),
    Literal(Literal),
    Open(Group),
    Close(Group),
    Identifier,
    Underscore,
    Eof,
    #[default]
    Unknown,
}

impl Display for TokenEnum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenEnum::Keyword(k) => write!(f, "'{}'", Into::<&'static str>::into(k)),
            TokenEnum::Symbol(s) => write!(
                f,
                "'{}'",
                match s {
                    Symbol::At => "@",
                    Symbol::Semicolon => return write!(f, "a newline or ';'"),
                    Symbol::Colon => ":",
                    Symbol::Tilde => "~",
                    Symbol::Comma => ",",
                    Symbol::Dot => ".",
                    Symbol::DotDot => "..",
                    Symbol::Caret => "^",
                    Symbol::Question => "?",
                    Symbol::TripleQuestion => "???",
                    Symbol::Arrow => "->",
                    Symbol::FatArrow => "=>",
                    Symbol::Dash => "-",
                    Symbol::TripleDash => "---",
                    Symbol::Plus => "+",
                    Symbol::Ampersand => "&",
                    Symbol::AmpersandTilde => "&~",
                    Symbol::Slash => "/",
                    Symbol::Star => "*",
                    Symbol::Percent => "%",
                    Symbol::Bang => "!",
                    Symbol::Pipe => "|>",
                    Symbol::Bar => "|",
                    Symbol::ShiftLeft => "<<",
                    Symbol::ShiftRight => ">>",
                    Symbol::Equality(equality) => match equality {
                        SymbolEquality::EqualsEquals => "==",
                        SymbolEquality::BangEquals => "!=",
                    },
                    Symbol::Inequality(inequality) => match inequality {
                        SymbolInequality::Greater => ">",
                        SymbolInequality::GreaterEquals => ">=",
                        SymbolInequality::Less => "<",
                        SymbolInequality::LessEquals => "<=",
                    },
                    Symbol::Assign(assign) => match assign {
                        SymbolAssign::Equals => "=",
                        SymbolAssign::DashEquals => "-=",
                        SymbolAssign::PlusEquals => "+=",
                        SymbolAssign::SlashEquals => "/=",
                        SymbolAssign::StarEquals => "*=",
                        SymbolAssign::PercentEquals => "%=",
                        SymbolAssign::AmpersandEquals => "&=",
                        SymbolAssign::AmpersandTildeEquals => "&~=",
                        SymbolAssign::BarEquals => "|=",
                        SymbolAssign::TildeEquals => "~=",
                        SymbolAssign::ShiftLeftEquals => "<<=",
                        SymbolAssign::ShiftRightEquals => ">>=",
                    },
                }
            ),
            TokenEnum::Literal(l) => match l {
                Literal::String => write!(f, "a string"),
                Literal::Character => write!(f, "a character"),
                Literal::Integer => write!(f, "an integer"),
                Literal::Zero => write!(f, "'0'"),
            },
            TokenEnum::Open(g) => match g {
                Group::Parenthesis => write!(f, "'('"),
                Group::Brace => write!(f, "'{{'"),
                Group::Bracket => write!(f, "'['"),
            },
            TokenEnum::Close(g) => match g {
                Group::Parenthesis => write!(f, "')'"),
                Group::Brace => write!(f, "'}}'"),
                Group::Bracket => write!(f, "']'"),
            },
            TokenEnum::Identifier => write!(f, "an identifier"),
            TokenEnum::Underscore => write!(f, "'_'"),
            TokenEnum::Eof => write!(f, "end of file"),
            TokenEnum::Unknown => write!(f, "unknown symbol"),
        }
    }
}

pub fn is_valid_identifier(s: &str) -> bool {
    s.as_bytes()
        .iter()
        .all(|&c| c.is_ascii_alphanumeric() || c == b'_')
        && (s.starts_with('_') || s.as_bytes().iter().any(u8::is_ascii_alphabetic))
}

impl Token {
    pub fn is_eof(self) -> bool {
        self.token == TokenEnum::Eof
    }
    pub fn is_newline(self) -> bool {
        self.span.start == self.span.end && self.token == TokenEnum::Symbol(Symbol::Semicolon)
    }
}

impl TokenEnum {
    pub fn from_word(word: &str) -> TokenEnum {
        let default = if word.starts_with('#') {
            TokenEnum::Keyword(Keyword::Unknown)
        } else {
            TokenEnum::Identifier
        };

        Keyword::from_str(word)
            .map(TokenEnum::Keyword)
            .unwrap_or(default)
    }

    pub fn prevent_semi_after(self) -> bool {
        matches!(
            self,
            TokenEnum::Open(_)
                | TokenEnum::Symbol(Symbol::Arrow)
                | TokenEnum::Symbol(Symbol::Semicolon)
                | TokenEnum::Symbol(Symbol::Comma)
                | TokenEnum::Symbol(Symbol::Pipe)
                | TokenEnum::Symbol(Symbol::Assign(_))
                | TokenEnum::Symbol(Symbol::Equality(_))
                | TokenEnum::Symbol(Symbol::Inequality(_))
        )
    }
    pub fn prevent_semi_before(self) -> bool {
        matches!(
            self,
            TokenEnum::Close(_)
                | TokenEnum::Symbol(Symbol::Arrow)
                | TokenEnum::Symbol(Symbol::Semicolon)
                | TokenEnum::Symbol(Symbol::Comma)
                | TokenEnum::Symbol(Symbol::Pipe)
                | TokenEnum::Symbol(Symbol::Assign(_))
                | TokenEnum::Symbol(Symbol::Equality(_))
                | TokenEnum::Symbol(Symbol::Inequality(_))
                | TokenEnum::Keyword(Keyword::Intrinsic)
                | TokenEnum::Keyword(Keyword::With)
        )
    }
}

#[derive(Debug, Clone, Copy, Default, Hash, PartialEq, Eq)]
pub struct Token {
    pub token: TokenEnum,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString, IntoStaticStr, Hash)]
#[strum(serialize_all = "snake_case")]
pub enum Keyword {
    Import,
    With,
    Let,
    Const,
    Mut,
    Effect,
    Type,
    Fun,
    If,
    Then,
    Else,
    Struct,
    Discard,
    Region,
    Thunk,
    Handle,
    #[strum(serialize = "raise", serialize = "yeet")]
    Raise,
    Use,
    #[strum(serialize = "#ext")]
    Extend,
    #[strum(serialize = "#trunc")]
    Truncate,
    #[strum(serialize = "#transmute", serialize = "#transrights")]
    Transmute,
    #[strum(serialize = "#intrinsic")]
    Intrinsic,
    #[strum(disabled)]
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Symbol {
    At,             // @
    Semicolon,      // ;
    Colon,          // :
    Tilde,          // ~
    Comma,          // ,
    Dot,            // .
    DotDot,         // ..
    Caret,          // ^
    Question,       // ?
    TripleQuestion, // ???
    Arrow,          // ->
    FatArrow,       // =>
    Dash,           // -
    TripleDash,     // ---
    Plus,           // +
    Ampersand,      // &
    AmpersandTilde, // &~
    Slash,          // /
    Star,           // *
    Percent,        // %
    Bang,           // !
    Pipe,           // |>
    Bar,            // |
    ShiftLeft,      // <<
    ShiftRight,     // >>
    Equality(SymbolEquality),
    Inequality(SymbolInequality),
    Assign(SymbolAssign),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolEquality {
    EqualsEquals, // ==
    BangEquals,   // !=
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolInequality {
    Greater,       // >
    GreaterEquals, // >=
    Less,          // <
    LessEquals,    // <=
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolAssign {
    Equals,               // =
    DashEquals,           // -=
    PlusEquals,           // +=
    SlashEquals,          // /=
    StarEquals,           // *=
    PercentEquals,        // %=
    AmpersandEquals,      // &=
    AmpersandTildeEquals, // &~=
    BarEquals,            // |=
    TildeEquals,          // ~=
    ShiftLeftEquals,      // <<=
    ShiftRightEquals,     // >>=
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
    String,
    Character,
    Integer,
    Zero,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Group {
    /// ()
    Parenthesis,
    /// {}
    Brace,
    /// []
    Bracket,
}

impl From<Keyword> for TokenEnum {
    fn from(value: Keyword) -> Self {
        Self::Keyword(value)
    }
}

impl From<Symbol> for TokenEnum {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}

impl From<Literal> for TokenEnum {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}
