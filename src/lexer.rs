use std::{iter::Peekable, str::Chars};

#[derive(Debug)]
pub enum Token {
    // Keywords
    Effect,
    Fun,
    Try,
    With,

    // Symbols
    Semicolon,
    Period,
    Slash,
    Open(Group),
    Close(Group),

    // Literals
    String(String),
    Ident(String),
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Group {
    Brace,
    Paren,
    Bracket,
}

pub struct Tokenizer<'a> {
    next: Peekable<Chars<'a>>,
    pub pos: usize,
}

#[derive(Debug)]
pub enum TokenErr {
    UnknownSymbol,
    UnclosedString,
}

#[derive(Debug)]
pub struct Ranged<T>(pub T, pub usize, pub usize);

impl<T> Ranged<T> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Ranged<U> {
        Ranged(f(self.0), self.1, self.2)
    }
}

impl<'a> Tokenizer<'a> {
    pub fn new(s: &'a str) -> Self {
        Self {
            next: s.chars().peekable(),
            pos: 0,
        }
    }
    fn next_char(&mut self) -> Option<char> {
        match self.next.next() {
            Some(c) => {
                self.pos += 1;
                Some(c)
            }
            None => None,
        }
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Ranged<Token>, Ranged<TokenErr>>;

    fn next(&mut self) -> Option<Self::Item> {
        // get next char
        let char = loop {
            match self.next_char() {
                // skip whitespace
                Some(' ') | Some('\t') | Some('\r') | Some('\n') => {}
                // skip comment
                Some('#') => loop {
                    match self.next_char() {
                        Some('\n') | None => break,
                        Some(_) => {}
                    }
                },
                Some(c) => break c,
                None => return None,
            }
        };

        let pos = self.pos - 1;
        let token = |token| Ranged(token, pos, self.pos);

        // get next token
        Some(match char {
            ';' => Ok(token(Token::Semicolon)),
            '.' => Ok(token(Token::Period)),
            '/' => Ok(token(Token::Slash)),
            '(' => Ok(token(Token::Open(Group::Paren))),
            '[' => Ok(token(Token::Open(Group::Bracket))),
            '{' => Ok(token(Token::Open(Group::Brace))),
            ')' => Ok(token(Token::Close(Group::Paren))),
            ']' => Ok(token(Token::Close(Group::Bracket))),
            '}' => Ok(token(Token::Close(Group::Brace))),
            '"' => {
                // string
                let mut escaped = false;
                loop {
                    match self.next_char() {
                        Some('"') if !escaped => {
                            break Ok(Ranged(
                                Token::String("todo parse str".to_owned()),
                                pos,
                                self.pos,
                            ))
                        }
                        Some('\n') | None => {
                            break Err(Ranged(TokenErr::UnclosedString, pos, self.pos + 1))
                        }

                        Some('\\') => escaped = !escaped,
                        Some(_) => escaped = false,
                    }
                }
            }
            'a'..='z' | 'A'..='Z' => {
                // get word
                let mut word = String::new();
                word.push(char);

                loop {
                    match self.next.peek() {
                        Some(&c) => match c {
                            'a'..='z' | 'A'..='Z' | '0'..='9' => {
                                self.next_char();
                                word.push(c);
                            }
                            _ => break,
                        },
                        None => break,
                    }
                }

                // find keyword
                Ok(Ranged(
                    match word.as_str() {
                        "effect" => Token::Effect,
                        "fun" => Token::Fun,
                        "try" => Token::Try,
                        "with" => Token::With,
                        _ => Token::Ident(word),
                    },
                    pos,
                    self.pos,
                ))
            }
            _ => Err(Ranged(TokenErr::UnknownSymbol, pos, self.pos)),
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.next.size_hint().1)
    }
}
