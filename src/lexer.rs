use std::fmt;
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Loc {
    pub file_path: Option<String>,
    pub row: usize,
    pub col: usize,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.file_path {
            Some(file_path) => write!(f, "{}:{}:{}", file_path, self.row, self.col),
            None => write!(f, "{}:{}", self.row, self.col),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash)]
pub enum TokenKind {
    Ident,

    // Keywords
    Rule,
    Shape,
    Apply,
    Done,
    Undo,
    Quit,
    Reverse,
    Delete,

    // Special Characters
    OpenParen,
    CloseParen,
    Comma,
    Equals,
    Colon,

    // Binary Operators
    Plus,
    Dash,
    Asterisk,
    Slash,
    Caret,

    // Terminators
    Invalid,
    End,
}

fn keyword_by_name(text: &str) -> Option<TokenKind> {
    match text {
        "rule"    => Some(TokenKind::Rule),
        "shape"   => Some(TokenKind::Shape),
        "apply"   => Some(TokenKind::Apply),
        "done"    => Some(TokenKind::Done),
        "quit"    => Some(TokenKind::Quit),
        "undo"    => Some(TokenKind::Undo),
        "reverse" => Some(TokenKind::Reverse),
        "delete"  => Some(TokenKind::Delete),
        _ => None,
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenKind::*;
        match self {
            Ident => write!(f, "identifier"),
            Rule => write!(f, "`rule`"),
            Shape => write!(f, "`shape`"),
            Apply => write!(f, "`apply`"),
            Done => write!(f, "`done`"),
            Undo => write!(f, "`undo`"),
            Quit => write!(f, "`quit`"),
            Reverse => write!(f, "`reverse`"),
            Delete => write!(f, "`delete`"),
            OpenParen => write!(f, "open paren"),
            CloseParen => write!(f, "close paren"),
            Comma => write!(f, "comma"),
            Equals => write!(f, "equals"),
            Colon => write!(f, "colon"),
            Invalid => write!(f, "invalid token"),
            Plus => write!(f, "plus"),
            Dash => write!(f, "dash"),
            Asterisk => write!(f, "asterisk"),
            Slash => write!(f, "slash"),
            Caret => write!(f, "caret"),
            End => write!(f, "end of input"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub loc: Loc,
}

pub struct Lexer<Chars: Iterator<Item=char>> {
    chars: Peekable<Chars>,
    peeked: Option<Token>,
    exhausted: bool,
    file_path: Option<String>,
    lnum: usize,
    bol: usize,
    cnum: usize,
}

impl<Chars: Iterator<Item=char>> Lexer<Chars> {
    pub fn new(chars: Chars, file_path: Option<String>) -> Self {
        Self {
            chars: chars.peekable(),
            peeked: None,
            exhausted: false,
            file_path: file_path,
            lnum: 0,
            bol: 0,
            cnum: 0,
        }
    }

    pub fn loc(&self) -> Loc {
        Loc {
            file_path: self.file_path.clone(),
            row: self.lnum + 1,
            col: self.cnum - self.bol + 1,
        }
    }

    pub fn peek_token(&mut self) -> &Token {
        let token = self.next_token();
        self.peeked.insert(token)
    }

    pub fn next_token(&mut self) -> Token {
        self.peeked.take().unwrap_or_else(|| self.chop_tokens_from_chars())
    }

    fn drop_line(&mut self) {
        while let Some(_) = self.chars.next_if(|x| *x != '\n') {
            self.cnum += 1
        }
        if let Some(_) = self.chars.next_if(|x| *x == '\n') {
            self.cnum += 1;
            self.lnum += 1;
            self.bol = self.cnum
        }
    }

    fn trim_whitespaces(&mut self) {
        while let Some(_) = self.chars.next_if(|x| x.is_whitespace() && *x != '\n') {
            self.cnum += 1
        }
    }

    fn chop_tokens_from_chars(&mut self) -> Token {
        assert!(!self.exhausted, "Completely exhausted lexer. The lexer MUST ALWAYS end with the terminators. If the lexer caller tries to pull tokens after the terminators, this is a bug.");

        self.trim_whitespaces();
        while let Some(x) = self.chars.peek() {
            if *x != '\n' && *x != '#' {
                break
            }

            self.drop_line();
            self.trim_whitespaces();
        }

        let loc = self.loc();
        match self.chars.next() {
            Some(x) => {
                self.cnum += 1;
                let mut text = x.to_string();
                match x {
                    '(' => Token {kind: TokenKind::OpenParen,  text, loc},
                    ')' => Token {kind: TokenKind::CloseParen, text, loc},
                    ',' => Token {kind: TokenKind::Comma,      text, loc},
                    '=' => Token {kind: TokenKind::Equals,     text, loc},
                    ':' => Token {kind: TokenKind::Colon,      text, loc},
                    '+' => Token {kind: TokenKind::Plus,       text, loc},
                    '-' => Token {kind: TokenKind::Dash,       text, loc},
                    '*' => Token {kind: TokenKind::Asterisk,   text, loc},
                    '/' => Token {kind: TokenKind::Slash,      text, loc},
                    '^' => Token {kind: TokenKind::Caret,      text, loc},
                    _ => {
                        if !is_ident_char(&x) {
                            self.exhausted = true;
                            Token{kind: TokenKind::Invalid, text, loc}
                        } else {
                            while let Some(x) = self.chars.next_if(is_ident_char) {
                                self.cnum += 1;
                                text.push(x)
                            }

                            if let Some(kind) = keyword_by_name(&text) {
                                Token{kind, text, loc}
                            } else {
                                Token{kind: TokenKind::Ident, text, loc}
                            }
                        }
                    }
                }
            }

            None => {
                self.cnum += 1;
                self.exhausted = true;
                Token{kind: TokenKind::End, text: "".to_string(), loc}
            }
        }
    }
}

impl<Chars: Iterator<Item=char>> Iterator for Lexer<Chars> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            None
        } else {
            Some(self.next_token())
        }
    }
}

fn is_ident_char(x: &char) -> bool {
    x.is_alphanumeric() || *x == '_'
}
