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
    Sym,

    // Keywords
    Rule,
    Shape,
    Apply,
    Done,

    // Special Characters
    OpenParen,
    CloseParen,
    Comma,
    Equals,
    Colon,

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
        TokenKindSet(set | (1 << kind as u64))
    }

    pub const fn unset(self, kind: TokenKind) -> Self {
        let TokenKindSet(set) = self;
        TokenKindSet(set & !(1 << kind as u64))
    }

    pub fn contains(&self, kind: TokenKind) -> bool {
        let TokenKindSet(set) = self;
        (set & (1 << kind as u64)) > 0
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
const TOKEN_KIND_SIZE_ASSERT: [(); (TOKEN_KIND_ITEMS.len() < std::mem::size_of::<TokenKindSetInnerType>() * 8) as usize] = [()];

fn keyword_by_name(text: &str) -> Option<TokenKind> {
    match text {
        "rule"  => Some(TokenKind::Rule),
        "shape" => Some(TokenKind::Shape),
        "apply" => Some(TokenKind::Apply),
        "done"  => Some(TokenKind::Done),
        _ => None,
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenKind::*;
        match self {
            Sym => write!(f, "symbol"),
            Rule => write!(f, "rule keyword"),
            Shape => write!(f, "shape keyword"),
            Apply => write!(f, "apply keyword"),
            Done => write!(f, "done keyword"),
            OpenParen => write!(f, "open paren"),
            CloseParen => write!(f, "close paren"),
            Comma => write!(f, "comma"),
            Equals => write!(f, "equals"),
            Colon => write!(f, "colon"),
            Invalid => write!(f, "invalid token"),
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
    exhausted: bool,
    file_path: Option<String>,
    lnum: usize,
    bol: usize,
    cnum: usize,
}

impl<Chars: Iterator<Item=char>> Lexer<Chars> {
    pub fn from_iter(chars: Chars) -> Self {
        Self {
            chars: chars.peekable(),
            exhausted: false,
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

    pub fn set_file_path(&mut self, file_path: &str) {
        self.file_path = Some(file_path.to_string())
    }
}

impl<Chars: Iterator<Item=char>> Iterator for Lexer<Chars> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        if self.exhausted { return None }

        while let Some(x) = self.chars.next_if(|x| x.is_whitespace()) {
            self.cnum += 1;
            if x == '\n' {
                self.lnum += 1;
                self.bol = self.cnum;
            }
        }

        let loc = self.loc();
        match self.chars.next() {
            Some(x) => {
                self.cnum += 1;
                let mut text = x.to_string();
                match x {
                    '(' => Some(Token {kind: TokenKind::OpenParen,  text, loc}),
                    ')' => Some(Token {kind: TokenKind::CloseParen, text, loc}),
                    ',' => Some(Token {kind: TokenKind::Comma,      text, loc}),
                    '=' => Some(Token {kind: TokenKind::Equals,     text, loc}),
                    ':' => Some(Token {kind: TokenKind::Colon,      text, loc}),
                    _ => {
                        if !x.is_alphanumeric() {
                            self.exhausted = true;
                            Some(Token{kind: TokenKind::Invalid, text, loc})
                        } else {
                            while let Some(x) = self.chars.next_if(|x| x.is_alphanumeric()) {
                                self.cnum += 1;
                                text.push(x)
                            }

                            if let Some(kind) = keyword_by_name(&text) {
                                Some(Token{kind, text, loc})
                            } else {
                                Some(Token{kind: TokenKind::Sym, text, loc})
                            }
                        }
                    }
                }
            }

            None => {
                self.exhausted = true;
                Some(Token{kind: TokenKind::End, text: "".to_string(), loc})
            }
        }
    }
}
