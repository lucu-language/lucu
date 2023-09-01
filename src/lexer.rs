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

    // Error
    UnknownSymbol,
}

impl Token {
    pub fn is_anchor(&self) -> bool {
        matches!(
            self,
            Token::Effect
                | Token::Fun
                | Token::Try
                | Token::With
                | Token::Else
                | Token::Semicolon
                | Token::Comma
                | Token::Close(_)
        )
    }

    /// if a statement line ends with this token, it must continue on the next line
    /// these include all prefix and infix operators
    pub fn unfinished_statement(&self) -> bool {
        matches!(
            self,
            Token::With
                | Token::Else
                | Token::Period
                | Token::Bang
                | Token::Break
                | Token::Try
                | Token::If
                | Token::Effect
                | Token::Fun
                | Token::Slash
                | Token::Equals
                | Token::DoubleEquals
                | Token::Comma
                | Token::Open(_)

                // prevents double semicolons
                | Token::Semicolon
        )
    }

    /// if a statement line starts with this token, it must be attached to the previous line
    /// these include all infix and suffix operators
    pub fn continues_statement(&self) -> bool {
        matches!(
            self,
            Token::With
                | Token::Else
                | Token::Comma
                | Token::Close(_)
                | Token::Open(Group::Brace)
                | Token::Period
                | Token::Slash
                | Token::Equals
                | Token::DoubleEquals

                // prevents double semicolons
                | Token::Semicolon
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
    pos: usize,

    pub errors: Vec<Ranged<TokenErr>>,
    depth: usize,
    prev_unfinished: bool,
    peek: Option<Ranged<Token>>,
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
            depth: 0,
            prev_unfinished: true,
            peek: None,
            errors: Vec::new(),
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
    type Item = Ranged<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        // peeked token?
        if let Some(token) = self.peek.take() {
            self.prev_unfinished = token.0.unfinished_statement();
            return Some(token);
        }

        // remember newline between tokens
        let mut prev_newline = None;

        // get next char
        let char = loop {
            match self.next_char() {
                // skip newline
                Some('\n') => {
                    if prev_newline.is_none() {
                        prev_newline = Some(self.pos - 1);
                    }
                }
                // skip whitespace
                Some(' ') | Some('\t') | Some('\r') => {}
                // skip comment
                Some('#') => loop {
                    if prev_newline.is_none() {
                        prev_newline = Some(self.pos - 1);
                    }
                    match self.next_char() {
                        Some('\n') | None => break,
                        Some(_) => {}
                    }
                },
                Some(c) => break c,
                None => {
                    if let Some(newline) =
                        prev_newline.filter(|_| self.depth == 0 && !self.prev_unfinished)
                    {
                        return Some(Ranged(Token::Semicolon, newline, newline + 1));
                    } else {
                        return None;
                    }
                }
            }
        };

        let pos = self.pos - 1;

        // get next token
        let token = match char {
            ';' => Token::Semicolon,
            '.' => Token::Period,
            '/' => Token::Slash,
            ',' => Token::Comma,
            '(' => Token::Open(Group::Paren),
            '[' => Token::Open(Group::Bracket),
            '{' => Token::Open(Group::Brace),
            ')' => Token::Close(Group::Paren),
            ']' => Token::Close(Group::Bracket),
            '}' => Token::Close(Group::Brace),
            '!' => Token::Bang,
            '=' => {
                match self.next.peek() {
                    Some(&'=') => {
                        self.next_char();
                        Token::DoubleEquals
                    }
                    _ => {
                        // single
                        Token::Equals
                    }
                }
            }
            '"' => {
                // string
                let mut full = String::new();
                loop {
                    match self.next_char() {
                        Some('"') => break Token::String(full),
                        Some('\n') => {
                            self.errors
                                .push(Ranged(TokenErr::UnclosedString, pos, self.pos));
                            break Token::String(full);
                        }
                        None => {
                            self.errors
                                .push(Ranged(TokenErr::UnclosedString, pos, self.pos + 1));
                            break Token::String(full);
                        }

                        Some('\\') => full.push(match self.next_char() {
                            Some('n') => '\n',
                            Some('t') => '\t',
                            Some('r') => '\r',
                            Some('"') => '"',
                            Some('\\') => '\\',
                            Some('\n') => '\n',

                            Some(c) => c, // TODO: give error
                            None => {
                                self.errors.push(Ranged(
                                    TokenErr::UnclosedString,
                                    pos,
                                    self.pos + 1,
                                ));
                                break Token::String(full);
                            }
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
                match word.as_str() {
                    "effect" => Token::Effect,
                    "fun" => Token::Fun,
                    "try" => Token::Try,
                    "with" => Token::With,
                    "if" => Token::If,
                    "else" => Token::Else,
                    "break" => Token::Break,
                    _ => Token::Ident(word),
                }
            }
            '0'..='9' => {
                self.prev_unfinished = false;

                // number
                let mut num = i128::from(char.to_digit(10).unwrap());
                loop {
                    match self.next.peek() {
                        Some(&'_') => {}
                        Some(&('0'..='9')) => {
                            // TODO: error if too big
                            num *= 10;
                            num += i128::from(self.next_char().unwrap().to_digit(10).unwrap());
                        }
                        _ => break,
                    }
                }
                Token::Int(num)
            }
            _ => {
                self.prev_unfinished = false;

                self.errors
                    .push(Ranged(TokenErr::UnknownSymbol, pos, self.pos));
                Token::UnknownSymbol
            }
        };

        match token {
            Token::Open(g) if g != Group::Brace => {
                self.depth += 1;
            }
            Token::Close(g) if g != Group::Brace => {
                self.depth = self.depth.saturating_sub(1);
            }
            _ => {}
        }

        if let Some(newline) = prev_newline
            .filter(|_| self.depth == 0 && !self.prev_unfinished && !token.continues_statement())
        {
            self.peek = Some(Ranged(token, pos, self.pos));
            Some(Ranged(Token::Semicolon, newline, newline + 1))
        } else {
            self.prev_unfinished = token.unfinished_statement();
            Some(Ranged(token, pos, self.pos))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.next.size_hint().1)
    }
}
