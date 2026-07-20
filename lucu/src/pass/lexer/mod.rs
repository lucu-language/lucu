use std::collections::VecDeque;
use std::ops::Range;

use crate::span::Span;
use crate::tokens::{Group, Symbol, Token, TokenEnum};

fn skip_whitespace(src: &mut &str, pos: usize, mut comments: Option<&mut VecDeque<Span>>) -> usize {
    let mut skipped = 0;
    while !src.is_empty()
        && (src.as_bytes()[0].is_ascii_whitespace()
            || (src.starts_with("--") && !src.starts_with("---")))
    {
        if src.starts_with("--") && !src.starts_with("---") {
            let start = pos + skipped;
            while !src.is_empty() && src.as_bytes()[0] != b'\n' {
                *src = &src[1..];
                skipped += 1;
            }
            if let Some(comments) = comments.as_mut() {
                let end = pos + skipped;
                comments.push_back(Span::new(start as u32, end as u32));
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
    comments: Option<&'a mut VecDeque<Span>>,
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

        let next = next_token(self.src, self.pos as usize, self.comments.as_deref_mut());
        if let Some(next) = next {
            let has_newline = self.src[Span::new(self.pos, next.span.start)]
                .find('\n')
                .map(|i| i as u32 + self.pos)
                .filter(|_| !self.no_insertion);
            self.pos = next.span.end;

            if let TokenEnum::Open(g) = next.token {
                self.groups.push(g);
            } else if let TokenEnum::Close(g) = next.token {
                while self.groups.pop().is_some_and(|popped| popped != g) {}
            }

            self.no_insertion = next.token.prevent_semi_after();
            if let Some(pos) = has_newline.filter(|_| {
                matches!(self.groups.last(), None | Some(Group::Brace))
                    && !next.token.prevent_semi_before()
            }) {
                self.saved = Some(next);
                return Some(Token {
                    token: TokenEnum::Symbol(Symbol::Semicolon),
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
                    token: TokenEnum::Eof,
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
            comments: None,
        }
    }
    pub fn with_comments(mut self, comments: &'a mut VecDeque<Span>) -> Self {
        self.comments = Some(comments);
        self
    }
}

fn next_token(mut src: &str, pos: usize, comments: Option<&mut VecDeque<Span>>) -> Option<Token> {
    src = src.get(pos..)?;
    let start = pos + skip_whitespace(&mut src, pos, comments);
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
            TokenEnum::Symbol(if next!(b'=') { $double } else { $single })
        };
    }

    use crate::tokens::Group::*;
    use crate::tokens::Literal::*;
    use crate::tokens::Symbol::*;
    use crate::tokens::SymbolAssign::*;
    use crate::tokens::SymbolEquality::*;
    use crate::tokens::SymbolInequality::*;
    use crate::tokens::TokenEnum::*;

    let first = src.as_bytes()[0];
    let token = match first {
        b'(' => Open(Parenthesis),
        b'{' => Open(Brace),
        b'[' => Open(Bracket),

        b')' => Close(Parenthesis),
        b'}' => Close(Brace),
        b']' => Close(Bracket),

        b'@' => Symbol(At),
        b';' => Symbol(Semicolon),
        b':' => Symbol(Colon),
        b',' => Symbol(Comma),
        b'^' => Symbol(Caret),

        b'/' => equals!(Slash, Assign(SlashEquals)),
        b'*' => equals!(Star, Assign(StarEquals)),
        b'%' => equals!(Percent, Assign(PercentEquals)),
        b'!' => equals!(Bang, Equality(BangEquals)),
        b'~' => equals!(Tilde, Assign(TildeEquals)),

        b'&' => {
            if next!(b'~') {
                equals!(AmpersandTilde, Assign(AmpersandTildeEquals))
            } else {
                equals!(Ampersand, Assign(AmpersandEquals))
            }
        }
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
                    Symbol(TripleDash)
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
                equals!(Bar, Assign(BarEquals))
            }
        }
        b'<' => {
            if next!(b'<') {
                equals!(ShiftLeft, Assign(ShiftLeftEquals))
            } else {
                equals!(Inequality(Less), Inequality(LessEquals))
            }
        }
        b'>' => {
            if next!(b'>') {
                equals!(ShiftRight, Assign(ShiftRightEquals))
            } else {
                equals!(Inequality(Greater), Inequality(GreaterEquals))
            }
        }

        b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'#' => {
            while src.len() > len
                && matches!(src.as_bytes()[len], b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
            {
                len += 1;
            }

            let word = &src[..len];
            if word == "_" {
                Underscore
            } else if word == "0" {
                Literal(Zero)
            } else if !word.starts_with('_')
                && !word.ends_with('_')
                && word
                    .as_bytes()
                    .iter()
                    .copied()
                    .all(|c| c.is_ascii_digit() || c == b'_')
            {
                Literal(Integer)
            } else {
                TokenEnum::from_word(word)
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
