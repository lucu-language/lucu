pub mod lexer;

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
pub enum TokenKind {
    Keyword(Keyword),
    Symbol(Symbol),
    Literal(Literal),
    Open(Group),
    Close(Group),
    Identifier,
    Eof,
    #[default]
    Unknown,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Keyword(k) => write!(f, "'{}'", Into::<&'static str>::into(k)),
            TokenKind::Symbol(s) => write!(
                f,
                "'{}'",
                match s {
                    Symbol::Semicolon => return write!(f, "newline, ';'"),
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
                    Symbol::DashDashDash => "---",
                    Symbol::Plus => "+",
                    Symbol::Ampersand => "&",
                    Symbol::Slash => "/",
                    Symbol::Star => "*",
                    Symbol::Percent => "%",
                    Symbol::Bang => "!",
                    Symbol::Pipe => "|>",
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
                    },
                }
            ),
            TokenKind::Literal(l) => match l {
                Literal::String => write!(f, "string"),
                Literal::Character => write!(f, "character"),
                Literal::Integer => write!(f, "integer"),
            },
            TokenKind::Open(g) => match g {
                Group::Parenthesis => write!(f, "'('"),
                Group::Brace => write!(f, "'{{'"),
                Group::Bracket => write!(f, "'['"),
            },
            TokenKind::Close(g) => match g {
                Group::Parenthesis => write!(f, "')'"),
                Group::Brace => write!(f, "'}}'"),
                Group::Bracket => write!(f, "']'"),
            },
            TokenKind::Identifier => write!(f, "identifier"),
            TokenKind::Eof => write!(f, "end of file"),
            TokenKind::Unknown => write!(f, "unknown symbol"),
        }
    }
}

impl TokenKind {
    pub fn is_valid_identifier(s: &str) -> bool {
        s.as_bytes()
            .iter()
            .all(|&c| c.is_ascii_alphanumeric() || c == b'_')
            && (s.starts_with('_') || s.as_bytes().iter().any(u8::is_ascii_alphabetic))
    }
    pub fn from_word(word: &str) -> TokenKind {
        let default = if word.starts_with('@') {
            TokenKind::Keyword(Keyword::Unknown)
        } else {
            TokenKind::Identifier
        };

        Keyword::from_str(word)
            .map(TokenKind::Keyword)
            .unwrap_or(default)
    }

    pub fn prevent_semi_after(self) -> bool {
        matches!(
            self,
            TokenKind::Open(_)
                | TokenKind::Symbol(Symbol::Arrow)
                | TokenKind::Symbol(Symbol::Semicolon)
                | TokenKind::Symbol(Symbol::Comma)
                | TokenKind::Symbol(Symbol::Pipe)
        )
    }
    pub fn prevent_semi_before(self) -> bool {
        matches!(
            self,
            TokenKind::Close(_)
                | TokenKind::Symbol(Symbol::Semicolon)
                | TokenKind::Symbol(Symbol::Comma)
                | TokenKind::Symbol(Symbol::Pipe)
        )
    }
}

#[derive(Debug, Clone, Copy, Default, Hash, PartialEq, Eq)]
pub struct Token {
    pub token: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString, IntoStaticStr, Hash)]
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
    Then,
    Else,
    Struct,
    Do,
    Break,
    Use,
    #[strum(serialize = "@cast")]
    Cast,
    #[strum(serialize = "@addr")]
    Addr,
    #[strum(disabled)]
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Symbol {
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
    DashDashDash,   // ---
    Plus,           // +
    Ampersand,      // &
    Slash,          // /
    Star,           // *
    Percent,        // %
    Bang,           // !
    Pipe,           // |>
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
    Equals,        // =
    DashEquals,    // -=
    PlusEquals,    // +=
    SlashEquals,   // /=
    StarEquals,    // *=
    PercentEquals, // %=
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
    String,
    Character,
    Integer,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Group {
    Parenthesis, // ()
    Brace,       // {}
    Bracket,     // []
}

impl From<Keyword> for TokenKind {
    fn from(value: Keyword) -> Self {
        Self::Keyword(value)
    }
}

impl From<Symbol> for TokenKind {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}

impl From<Literal> for TokenKind {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}
