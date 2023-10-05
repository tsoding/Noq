use std::fmt;

#[derive(Debug, Clone)]
pub enum Loc {
    File {
        path: String,
        row: usize,
        col: usize,
    },
    Repl {
        col: usize,
        line: Vec<char>,
    },
}

macro_rules! loc_here {
    () => {
        Loc::File {
            path: file!().to_string(),
            row: line!() as usize,
            col: column!() as usize,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash)]
pub enum TokenKind {
    Ident,
    Str,

    // Keywords
    Undo,
    Quit,
    Delete,
    Load,
    Save,
    List,

    // Special Characters
    OpenParen,
    CloseParen,
    Comma,
    Equals,
    Colon,
    DoubleColon,
    OpenCurly,
    CloseCurly,
    Bar,
    Bang,

    // Binary Operators
    Plus,
    Dash,
    Asterisk,
    Slash,
    Caret,
    Percent,
    EqualsEquals,

    // Terminators
    Invalid,
    UnclosedStr,
    End,
}

fn keyword_by_name(text: &str) -> Option<TokenKind> {
    match text {
        "quit"   => Some(TokenKind::Quit),
        "undo"   => Some(TokenKind::Undo),
        "delete" => Some(TokenKind::Delete),
        "load"   => Some(TokenKind::Load),
        "save"   => Some(TokenKind::Save),
        "list"   => Some(TokenKind::List),
        _ => None,
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenKind::*;
        match self {
            Ident => write!(f, "identifier"),
            Str => write!(f, "string"),
            Undo => write!(f, "`undo`"),
            Quit => write!(f, "`quit`"),
            List => write!(f, "`list`"),
            Delete => write!(f, "`delete`"),
            Load => write!(f, "`load`"),
            Save => write!(f, "`save`"),
            OpenParen => write!(f, "open paren"),
            CloseParen => write!(f, "close paren"),
            OpenCurly => write!(f, "open curly"),
            CloseCurly => write!(f, "close curly"),
            Comma => write!(f, "comma"),
            Equals => write!(f, "equals"),
            EqualsEquals => write!(f, "double equals"),
            Colon => write!(f, "colon"),
            DoubleColon => write!(f, "double colon"),
            Percent => write!(f, "percent"),
            Invalid => write!(f, "invalid token"),
            UnclosedStr => write!(f, "unclosed string literal"),
            Plus => write!(f, "plus"),
            Dash => write!(f, "dash"),
            Asterisk => write!(f, "asterisk"),
            Slash => write!(f, "slash"),
            Caret => write!(f, "caret"),
            Bar => write!(f, "bar"),
            Bang => write!(f, "bang"),
            End => write!(f, "end of input"),
        }
    }
}


#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub loc: Loc,
}

impl Token {
    pub fn report(&self) -> ReportToken<'_> {
        ReportToken { inner: self }
    }
}

pub struct ReportToken<'a> {
    pub inner: &'a Token
}

impl fmt::Display for ReportToken<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.inner.text.is_empty() {
            write!(f, "{}", self.inner.kind)
        } else {
            write!(f, "{} `{}`", self.inner.kind, self.inner.text)
        }
    }
}

impl PartialEq for Token {
    fn eq(&self, other: &Token) -> bool {
        self.kind == other.kind && self.text == other.text
    }
}

pub struct Lexer {
    chars: Vec<char>,
    peeked: Option<Token>,
    exhausted: bool,
    file_path: Option<String>,
    lnum: usize,
    bol: usize,
    cnum: usize,
}

impl Lexer {
    pub fn new(chars: Vec<char>, file_path: Option<String>) -> Self {
        Self {
            chars,
            peeked: None,
            exhausted: false,
            file_path,
            lnum: 0,
            bol: 0,
            cnum: 0,
        }
    }

    pub fn current_line(&self) -> Vec<char> {
        let mut eol = self.bol;
        while eol < self.chars.len() && self.chars[eol] != '\n' {
            eol += 1;
        }
        return self.chars[self.bol..eol].to_vec();
    }

    pub fn loc(&self) -> Loc {
        match &self.file_path {
            Some(file_path) => Loc::File {
                path: file_path.clone(),
                row: self.lnum + 1,
                col: self.cnum - self.bol,
            },
            None => Loc::Repl {
                col: self.cnum - self.bol,
                line: self.current_line(),
            },
        }
    }

    pub fn expect_token(&mut self, kind: TokenKind) -> Result<Token, (TokenKind, Token)> {
        let token = self.next_token();
        if kind == token.kind {
            Ok(token)
        } else {
            Err((kind, token))
        }
    }

    pub fn peek_token(&mut self) -> &Token {
        let token = self.next_token();
        self.peeked.insert(token)
    }

    pub fn next_token(&mut self) -> Token {
        self.peeked.take().unwrap_or_else(|| self.chop_tokens_from_chars())
    }

    fn drop_char_if(&mut self, predicate: impl FnOnce(char) -> bool) -> Option<char> {
        self.chars.get(self.cnum).cloned().and_then(|ch| {
            if predicate(ch) {
                self.drop_char()
            } else {
                None
            }
        })
    }

    fn drop_char(&mut self) -> Option<char> {
        self.chars.get(self.cnum).cloned().map(|ch| {
            self.cnum += 1;
            if ch == '\n' {
                self.bol = self.cnum;
                self.lnum += 1;
            }
            ch
        })
    }

    fn drop_line(&mut self) {
        while let Some(x) = self.drop_char() {
            if x == '\n' {
                return
            }
        }
    }

    fn trim_whitespaces(&mut self) {
        while let Some(x) = self.chars.get(self.cnum) {
            if x.is_whitespace() {
                self.drop_char();
            } else {
                break;
            }
        }
    }

    fn chop_tokens_from_chars(&mut self) -> Token {
        assert!(!self.exhausted, "Completely exhausted lexer. The lexer MUST ALWAYS end with the terminators. If the lexer caller tries to pull tokens after the terminators, this is a bug.");

        'again: loop {
            self.trim_whitespaces();

            let loc = self.loc();
            let token = match self.drop_char() {
                Some(x) => {
                    let mut text = x.to_string();
                    match x {
                        '(' => Token {kind: TokenKind::OpenParen,  text, loc},
                        ')' => Token {kind: TokenKind::CloseParen, text, loc},
                        ',' => Token {kind: TokenKind::Comma,      text, loc},
                        '=' => if let Some(x) = self.drop_char_if(|x| x == '=') {
                            text.push(x);
                            Token {kind: TokenKind::EqualsEquals, text, loc}
                        } else {
                            Token {kind: TokenKind::Equals, text, loc}
                        },
                        ':' => if let Some(x) = self.drop_char_if(|x| x == ':') {
                            text.push(x);
                            Token {kind: TokenKind::DoubleColon, text, loc}
                        } else {
                            Token {kind: TokenKind::Colon, text, loc}
                        },
                        '+' => Token {kind: TokenKind::Plus,       text, loc},
                        '-' => Token {kind: TokenKind::Dash,       text, loc},
                        '*' => Token {kind: TokenKind::Asterisk,   text, loc},
                        '/' => if let Some(_) = self.drop_char_if(|x| x == '/') {
                            self.drop_line();
                            continue 'again;
                        } else {
                            Token {kind: TokenKind::Slash, text, loc}
                        }
                        '^' => Token {kind: TokenKind::Caret,      text, loc},
                        '%' => Token {kind: TokenKind::Percent,    text, loc},
                        '{' => Token {kind: TokenKind::OpenCurly,  text, loc},
                        '}' => Token {kind: TokenKind::CloseCurly, text, loc},
                        '|' => Token {kind: TokenKind::Bar,        text, loc},
                        '!' => Token {kind: TokenKind::Bang,       text, loc},
                        '"' => {
                            // TODO: no support for escaped sequences inside of string literals
                            text.clear();
                            while let Some(x) = self.drop_char_if(|x| x != '"') {
                                text.push(x)
                            }
                            Token {
                                kind: if self.drop_char_if(|x| x == '"').is_some() {
                                    TokenKind::Str
                                } else {
                                    TokenKind::UnclosedStr
                                },
                                text,
                                loc
                            }
                        }
                        _ => {
                            if !is_ident_char(x) {
                                self.exhausted = true;
                                Token{kind: TokenKind::Invalid, text, loc}
                            } else {
                                while let Some(x) = self.drop_char_if(is_ident_char) {
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
                    self.exhausted = true;
                    Token{kind: TokenKind::End, text: "".to_string(), loc}
                }
            };

            return token;
        }
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            None
        } else {
            Some(self.next_token())
        }
    }
}

fn is_ident_char(x: char) -> bool {
    let extra_chars = "_.";
    x.is_alphanumeric() || extra_chars.contains(x)
}
