use std::{iter::Peekable, str::Chars};

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    // Keywords
    Effect,
    Fun,
    Try,
    With,
    If,
    Else,
    Break,

    // Symbols
    Semicolon,
    Period,
    Slash,
    Comma,
    Equals,
    Bang,
    DoubleEquals,
    Open(Group),
    Close(Group),

    // Literals
    String(String),
    Ident(String),
    Int(i128),
}

impl Token {
    pub fn is_anchor(&self) -> bool {
        matches!(
            self,
            Token::Effect
                | Token::Fun
                | Token::Try
                | Token::With
                | Token::Semicolon
                | Token::Comma
                | Token::Close(_)
        )
    }
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

#[derive(Debug, Clone, Copy)]
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
            ',' => Ok(token(Token::Comma)),
            '(' => Ok(token(Token::Open(Group::Paren))),
            '[' => Ok(token(Token::Open(Group::Bracket))),
            '{' => Ok(token(Token::Open(Group::Brace))),
            ')' => Ok(token(Token::Close(Group::Paren))),
            ']' => Ok(token(Token::Close(Group::Bracket))),
            '}' => Ok(token(Token::Close(Group::Brace))),
            '!' => Ok(token(Token::Bang)),
            '=' => match self.next.peek() {
                Some(&'=') => {
                    self.next_char();
                    Ok(Ranged(Token::DoubleEquals, pos, self.pos))
                }
                _ => {
                    // single
                    Ok(Ranged(Token::Equals, pos, self.pos))
                }
            },
            '"' => {
                // string
                let mut full = String::new();
                loop {
                    match self.next_char() {
                        Some('"') => break Ok(Ranged(Token::String(full), pos, self.pos)),
                        Some('\n') => break Err(Ranged(TokenErr::UnclosedString, pos, self.pos)),
                        None => break Err(Ranged(TokenErr::UnclosedString, pos, self.pos + 1)),

                        Some('\\') => full.push(match self.next_char() {
                            Some('n') => '\n',
                            Some('t') => '\t',
                            Some('r') => '\r',
                            Some('"') => '"',
                            Some('\\') => '\\',
                            Some('\n') => '\n',

                            Some(c) => c, // TODO: give error
                            None => break Err(Ranged(TokenErr::UnclosedString, pos, self.pos + 1)),
                        }),
                        Some(c) => full.push(c),
                    }
                }
            }
            'a'..='z' | 'A'..='Z' | '_' => {
                // get word
                let mut word = String::new();
                word.push(char);

                loop {
                    match self.next.peek() {
                        Some(&c) => match c {
                            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => {
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
                        "if" => Token::If,
                        "else" => Token::Else,
                        "break" => Token::Break,
                        _ => Token::Ident(word),
                    },
                    pos,
                    self.pos,
                ))
            }
            '0'..='9' => {
                let mut num = i128::from(char.to_digit(10).unwrap());
                loop {
                    match self.next.peek() {
                        Some(&'_') => {}
                        Some(&('0'..='9')) => {
                            num *= 10;
                            num += i128::from(self.next_char().unwrap().to_digit(10).unwrap());
                        }
                        _ => break,
                    }
                }
                Ok(Ranged(Token::Int(num), pos, self.pos))
            }
            _ => Err(Ranged(TokenErr::UnknownSymbol, pos, self.pos)),
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.next.size_hint().1)
    }
}
