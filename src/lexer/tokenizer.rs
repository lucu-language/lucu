use super::{FullToken, Group};

fn skip_whitespace(src: &mut &str) -> u32 {
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

struct Tokenizer<'a> {
    src: &'a str,
    pos: u32,
    groups: Vec<Group>,
    saved: Option<FullToken>,
    no_insertion: bool,
}

impl Iterator for Tokenizer<'_> {
    type Item = FullToken;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.saved.take() {
            return Some(next);
        }

        let next = next_token(self.src, self.pos);
        if let Some(next) = next {
            let has_newline = self.src[self.pos as usize..next.start as usize]
                .find('\n')
                .map(|i| i as u32 + self.pos)
                .filter(|_| !self.no_insertion);
            self.pos = next.start + next.len as u32;

            if let super::Token::Open(g) = next.token {
                self.groups.push(g);
            } else if let super::Token::Close(g) = next.token {
                while self.groups.pop().is_some_and(|popped| popped != g) {}
            }

            self.no_insertion = next.token.prevent_semi_after();
            if let Some(pos) = has_newline.filter(|_| {
                matches!(self.groups.last(), None | Some(Group::Brace))
                    && !next.token.prevent_semi_before()
            }) {
                self.saved = Some(next);
                return Some(FullToken {
                    token: super::Token::Symbol(super::Symbol::Semicolon),
                    len: 1,
                    start: pos,
                });
            }
        }

        next
    }
}

pub fn tokenize(src: &str) -> impl Iterator<Item = FullToken> + '_ {
    Tokenizer {
        src,
        pos: 0,
        groups: Vec::new(),
        saved: None,
        no_insertion: true,
    }
}

fn next_token(mut src: &str, pos: u32) -> Option<FullToken> {
    src = &src[pos as usize..];
    let start = pos + skip_whitespace(&mut src);

    if src.is_empty() {
        return None;
    }

    let mut len = 1u16;

    macro_rules! next {
        ($char: expr) => {
            if src.len() > len as usize && src.as_bytes()[len as usize] == $char {
                len += 1;
                true
            } else {
                false
            }
        };
    }
    macro_rules! equals {
        ($single: expr, $double: expr) => {
            super::Token::Symbol(if next!(b'=') { $double } else { $single })
        };
    }

    use super::Group::*;
    use super::Literal::*;
    use super::Symbol::*;
    use super::Token::*;

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
        b'?' => Symbol(Question),
        b'&' => Symbol(Ampersand),

        b'/' => equals!(Slash, SlashEquals),
        b'*' => equals!(Star, StarEquals),
        b'%' => equals!(Percent, PercentEquals),
        b'<' => equals!(Less, LessEquals),
        b'>' => equals!(Greater, GreaterEquals),
        b'!' => equals!(Bang, BangEquals),

        b'=' => {
            if next!(b'>') {
                Symbol(Arrow)
            } else {
                equals!(Equals, EqualsEquals)
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
            if next!(b'+') {
                Symbol(PlusPlus)
            } else {
                equals!(Plus, PlusEquals)
            }
        }
        b'-' => {
            if next!(b'-') {
                if next!(b'-') {
                    Symbol(DashDashDash)
                } else {
                    Symbol(DashDash)
                }
            } else {
                equals!(Dash, DashEquals)
            }
        }

        b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'@' => {
            while src.len() > len as usize
                && matches!(src.as_bytes()[len as usize], b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
            {
                len += 1;
            }

            let word = &src[..len as usize];
            if word == "0" {
                Symbol(Zero)
            } else if word.as_bytes().iter().all(|c| c.is_ascii_digit()) {
                Literal(Integer)
            } else {
                super::Token::from_word(word)
            }
        }

        b'\'' | b'"' => {
            while src.len() > len as usize && src.as_bytes()[len as usize] != first {
                if src.len() > len as usize + 1 && src.as_bytes()[len as usize] == b'\\' {
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

    Some(FullToken { token, len, start })
}
