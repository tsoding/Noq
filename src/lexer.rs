use std::fmt;
use std::iter::Peekable;

#[derive(Debug, Clone)]
pub struct Loc {
    pub file_path: Option<String>,
    pub row: usize,
    pub col: usize,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenKind {
    Sym,
    OpenParen,
    CloseParen,
    Comma,
    Equals,
    Invalid,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenKind::*;
        match self {
            Sym => write!(f, "symbol"),
            OpenParen => write!(f, "open paren"),
            CloseParen => write!(f, "close paren"),
            Comma => write!(f, "comma"),
            Equals => write!(f, "equals"),
            Invalid => write!(f, "invalid token"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub loc: Loc,
}

pub struct Lexer<Chars: Iterator<Item=char>> {
    chars: Peekable<Chars>,
    invalid: bool,
    file_path: Option<String>,
    lnum: usize,
    bol: usize,
    cnum: usize,
}

impl<Chars: Iterator<Item=char>> Lexer<Chars> {
    pub fn from_iter(chars: Chars) -> Self {
        Self {
            chars: chars.peekable(),
            invalid: false,
            file_path: None,
            lnum: 0,
            bol: 0,
            cnum: 0,
        }
    }

    fn loc(&self) -> Loc {
        Loc {
            file_path: self.file_path.clone(),
            row: self.lnum,
            col: self.cnum - self.bol,
        }
    }
}

impl<Chars: Iterator<Item=char>> Iterator for Lexer<Chars> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        if self.invalid { return None }

        while let Some(x) = self.chars.next_if(|x| x.is_whitespace()) {
            self.cnum += 1;
            if x == '\n' {
                self.lnum += 1;
                self.bol = self.cnum;
            }
        }

        let loc = self.loc();
        let x = self.chars.next()?;
        self.cnum += 1;
        let mut text = x.to_string();
        match x {
            '(' => Some(Token {kind: TokenKind::OpenParen, text, loc}),
            ')' => Some(Token {kind: TokenKind::CloseParen, text, loc}),
            ',' => Some(Token {kind: TokenKind::Comma, text, loc}),
            '=' => Some(Token {kind: TokenKind::Equals, text, loc}),
            _ => {
                if !x.is_alphanumeric() {
                    self.invalid = true;
                    Some(Token{kind: TokenKind::Invalid, text, loc})
                } else {
                    while let Some(x) = self.chars.next_if(|x| x.is_alphanumeric()) {
                        self.cnum += 1;
                        text.push(x)
                    }

                    Some(Token{kind: TokenKind::Sym, text, loc})
                }
            }
        }
    }
}
