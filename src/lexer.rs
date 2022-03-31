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

macro_rules! token_kind_enum {
    ($($kinds:ident),* $(,)?) => {
        #[derive(Debug, PartialEq, Clone, Copy, Eq, Hash)]
        pub enum TokenKind {
            $($kinds),*
        }

        pub const TOKEN_KIND_ITEMS: [TokenKind; [$(TokenKind::$kinds),*].len()] = [$(TokenKind::$kinds),*];
    }
}

token_kind_enum! {
    Ident,

    // Keywords
    Rule,
    Shape,
    Apply,
    Done,
    Undo,
    Quit,
    Reverse,

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

type TokenKindSetInnerType = u64;
#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash)]
pub struct TokenKindSet(TokenKindSetInnerType);

impl TokenKindSet {
    pub const fn empty() -> Self {
        Self(0)
    }

    pub const fn single(kind: TokenKind) -> Self {
        Self::empty().set(kind)
    }

    pub const fn set(self, kind: TokenKind) -> Self {
        let TokenKindSet(set) = self;
        TokenKindSet(set | (1 << kind as TokenKindSetInnerType))
    }

    pub fn contains(&self, kind: TokenKind) -> bool {
        let TokenKindSet(set) = self;
        (set & (1 << kind as TokenKindSetInnerType)) > 0
    }
}

impl fmt::Display for TokenKindSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let xs: Vec<TokenKind> = TOKEN_KIND_ITEMS.iter().cloned().filter(|kind| self.contains(*kind)).collect();
        match xs.len() {
            0 => write!(f, "nothing"),
            1 => write!(f, "{}", xs[0]),
            n => {
                write!(f, "{}", xs[0])?;
                for i in 1..n-1 {
                    write!(f, ", {}", xs[i])?
                }
                write!(f, ", or {}", xs[n-1])
            }
        }
    }
}

#[allow(dead_code)]
const TOKEN_KIND_SIZE_ASSERT: [(); (TOKEN_KIND_ITEMS.len() < TokenKindSetInnerType::BITS as usize) as usize] = [()];

fn keyword_by_name(text: &str) -> Option<TokenKind> {
    match text {
        "rule"    => Some(TokenKind::Rule),
        "shape"   => Some(TokenKind::Shape),
        "apply"   => Some(TokenKind::Apply),
        "done"    => Some(TokenKind::Done),
        "quit"    => Some(TokenKind::Quit),
        "undo"    => Some(TokenKind::Undo),
        "reverse" => Some(TokenKind::Reverse),
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
