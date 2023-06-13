use std::{iter::Peekable, str::Chars};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
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
    GroupOpen(Group),
    GroupClose(Group),

    // Literals
    String,
    Identifier,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Group {
    Brace,
    Parenthesis,
    Bracket,
}

pub struct Tokenizer<'a> {
    next: Peekable<Chars<'a>>,
    pos: usize,
}

#[derive(Debug)]
pub struct TokenElem {
    pub token: Token,
    pub pos: usize,
}

impl<'a> Tokenizer<'a> {
    pub fn new(s: &'a str) -> Self {
        Self {
            next: s.chars().peekable(),
            pos: 0,
        }
    }
    fn token(&self, token: Token, len: usize) -> TokenElem {
        TokenElem {
            token,
            pos: self.pos - len,
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
    type Item = Result<TokenElem, ()>;

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

        // get next token
        Some(match char {
            ';' => Ok(self.token(Token::Semicolon, 1)),
            '.' => Ok(self.token(Token::Period, 1)),
            '/' => Ok(self.token(Token::Slash, 1)),
            '(' => Ok(self.token(Token::GroupOpen(Group::Parenthesis), 1)),
            '[' => Ok(self.token(Token::GroupOpen(Group::Bracket), 1)),
            '{' => Ok(self.token(Token::GroupOpen(Group::Brace), 1)),
            ')' => Ok(self.token(Token::GroupClose(Group::Parenthesis), 1)),
            ']' => Ok(self.token(Token::GroupClose(Group::Bracket), 1)),
            '}' => Ok(self.token(Token::GroupClose(Group::Brace), 1)),
            '"' => {
                // string
                let mut escaped = false;
                let mut len = 2;
                loop {
                    match self.next_char() {
                        Some('"') if !escaped => break Ok(self.token(Token::String, len)),
                        Some('\\') => {
                            escaped = !escaped;
                            len += 1;
                        }
                        Some(_) => {
                            escaped = false;
                            len += 1;
                        }
                        None => break Err(()),
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
                Ok(self.token(
                    match word.as_str() {
                        "effect" => Token::Effect,
                        "fun" => Token::Fun,
                        "try" => Token::Try,
                        "with" => Token::With,
                        _ => Token::Identifier,
                    },
                    word.len(),
                ))
            }
            _ => Err(()),
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.next.size_hint().1)
    }
}
