use std::ops::Range;

use crate::span::Span;
use crate::stage::token::{Group, Symbol, Token, TokenKind};

fn skip_whitespace(src: &mut &str) -> usize {
    let mut skipped = 0;
    while !src.is_empty() && (src.as_bytes()[0].is_ascii_whitespace() || src.as_bytes()[0] == b'#')
    {
        if src.as_bytes()[0] == b'#' {
            while !src.is_empty() && src.as_bytes()[0] != b'\n' {
                *src = &src[1..];
                skipped += 1;
            }
        }
        *src = &src[1..];
        skipped += 1;
    }
    skipped
}

pub struct Lexer<'a> {
    src: &'a str,
    pos: u32,
    groups: Vec<Group>,
    saved: Option<Token>,
    no_insertion: bool,
}

impl Lexer<'_> {
    pub fn for_range(mut self, range: Range<usize>) -> impl Iterator<Item = Token> {
        self.pos = range.start as u32;
        self.take_while(move |t| t.span.end <= range.end as u32)
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.saved.take() {
            return Some(next);
        }

        let next = next_token(self.src, self.pos as usize);
        if let Some(next) = next {
            let has_newline = self.src[Span::new(self.pos, next.span.start)]
                .find('\n')
                .map(|i| i as u32 + self.pos)
                .filter(|_| !self.no_insertion);
            self.pos = next.span.end;

            if let TokenKind::Open(g) = next.token {
                self.groups.push(g);
            } else if let TokenKind::Close(g) = next.token {
                while self.groups.pop().is_some_and(|popped| popped != g) {}
            }

            self.no_insertion = next.token.prevent_semi_after();
            if let Some(pos) = has_newline.filter(|_| {
                matches!(self.groups.last(), None | Some(Group::Brace))
                    && !next.token.prevent_semi_before()
            }) {
                self.saved = Some(next);
                return Some(Token {
                    token: TokenKind::Symbol(Symbol::Semicolon),
                    span: Span::new(pos, pos),
                });
            }
        }

        match next {
            Some(next) => Some(next),
            None if self.pos != u32::MAX => {
                self.pos = u32::MAX;
                let end = self.src.len() as u32;
                Some(Token {
                    token: TokenKind::Eof,
                    span: Span::new(end, end),
                })
            }
            None => None,
        }
    }
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            pos: 0,
            groups: Vec::new(),
            saved: None,
            no_insertion: true,
        }
    }
}

fn next_token(mut src: &str, pos: usize) -> Option<Token> {
    src = src.get(pos..)?;
    let start = pos + skip_whitespace(&mut src);
    if src.is_empty() {
        return None;
    }

    let mut len = 1;
    macro_rules! next {
        ($char: expr) => {
            if src.len() > len as usize && src.as_bytes()[len] == $char {
                len += 1;
                true
            } else {
                false
            }
        };
    }
    macro_rules! equals {
        ($single: expr, $double: expr) => {
            TokenKind::Symbol(if next!(b'=') { $double } else { $single })
        };
    }

    use super::Group::*;
    use super::Literal::*;
    use super::Symbol::*;
    use super::SymbolAssign::*;
    use super::SymbolEquality::*;
    use super::SymbolInequality::*;
    use super::TokenKind::*;

    let first = src.as_bytes()[0];
    let token = match first {
        b'(' => Open(Parenthesis),
        b'{' => Open(Brace),
        b'[' => Open(Bracket),

        b')' => Close(Parenthesis),
        b'}' => Close(Brace),
        b']' => Close(Bracket),

        b';' => Symbol(Semicolon),
        b':' => Symbol(Colon),
        b'~' => Symbol(Tilde),
        b',' => Symbol(Comma),
        b'^' => Symbol(Caret),
        b'&' => Symbol(Ampersand),

        b'/' => equals!(Slash, Assign(SlashEquals)),
        b'*' => equals!(Star, Assign(StarEquals)),
        b'%' => equals!(Percent, Assign(PercentEquals)),
        b'<' => equals!(Inequality(Less), Inequality(LessEquals)),
        b'>' => equals!(Inequality(Greater), Inequality(GreaterEquals)),
        b'!' => equals!(Bang, Equality(BangEquals)),

        b'?' => {
            if next!(b'?') {
                if next!(b'?') {
                    Symbol(TripleQuestion)
                } else {
                    Unknown
                }
            } else {
                Symbol(Question)
            }
        }
        b'=' => {
            if next!(b'>') {
                Symbol(FatArrow)
            } else {
                equals!(Assign(Equals), Equality(EqualsEquals))
            }
        }
        b'.' => {
            if next!(b'.') {
                Symbol(DotDot)
            } else {
                Symbol(Dot)
            }
        }
        b'+' => {
            equals!(Plus, Assign(PlusEquals))
        }
        b'-' => {
            if next!(b'-') {
                if next!(b'-') {
                    Symbol(DashDashDash)
                } else {
                    Unknown
                }
            } else if next!(b'>') {
                Symbol(Arrow)
            } else {
                equals!(Dash, Assign(DashEquals))
            }
        }
        b'|' => {
            if next!(b'>') {
                Symbol(Pipe)
            } else {
                Unknown
            }
        }

        b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'@' => {
            while src.len() > len
                && matches!(src.as_bytes()[len], b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
            {
                len += 1;
            }

            let word = &src[..len];
            if !word.starts_with('_')
                && word
                    .as_bytes()
                    .iter()
                    .copied()
                    .all(|c| c.is_ascii_digit() || c == b'_')
            {
                Literal(Integer)
            } else {
                TokenKind::from_word(word)
            }
        }

        b'\'' | b'"' => {
            while src.len() > len && src.as_bytes()[len] != first {
                if src.len() > len + 1 && src.as_bytes()[len] == b'\\' {
                    len += 2;
                } else {
                    len += 1;
                }
            }
            len += 1;

            if first == b'"' {
                Literal(String)
            } else {
                Literal(Character)
            }
        }

        _ => Unknown,
    };

    Some(Token {
        token,
        span: Span::new(start as u32, (start + len) as u32),
    })
}
