use std::fmt;
use std::collections::HashMap;
use std::iter::Peekable;
use std::io::{stdin, stdout};
use std::io::Write;

#[derive(Debug, Clone)]
struct Loc {
    file_path: Option<String>,
    row: usize,
    col: usize,
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Sym(String),
    Fun(String, Vec<Expr>)
}

enum Error {
    UnexpectedToken(TokenKind, Token),
    UnexpectedEOF(TokenKind),
}

impl Expr {
    fn parse_peekable(lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<Self, Error> {
        if let Some(name) = lexer.next() {
            match name.kind {
                TokenKind::Sym => {
                    if let Some(_) = lexer.next_if(|t| t.kind == TokenKind::OpenParen) {
                        let mut args = Vec::new();
                        if let Some(_) = lexer.next_if(|t| t.kind == TokenKind::CloseParen) {
                            return Ok(Expr::Fun(name.text, args))
                        }
                        args.push(Self::parse_peekable(lexer)?);
                        while let Some(_) = lexer.next_if(|t| t.kind == TokenKind::Comma) {
                            args.push(Self::parse_peekable(lexer)?);
                        }
                        if let Some(t) = lexer.peek() {
                            if t.kind == TokenKind::CloseParen {
                                Ok(Expr::Fun(name.text, args))
                            } else {
                                Err(Error::UnexpectedToken(TokenKind::CloseParen, t.clone()))
                            }
                        } else {
                            Err(Error::UnexpectedEOF(TokenKind::CloseParen))
                        }
                    } else {
                        Ok(Expr::Sym(name.text))
                    }
                },
                _ => Err(Error::UnexpectedToken(TokenKind::Sym, name))
            }
        } else {
            Err(Error::UnexpectedEOF(TokenKind::Sym))
        }
    }

    fn parse(lexer: &mut impl Iterator<Item=Token>) -> Result<Self, Error> {
        Self::parse_peekable(&mut lexer.peekable())
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Sym(name) => write!(f, "{}", name),
            Expr::Fun(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")? }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            },
        }
    }
}

#[derive(Debug)]
struct Rule {
    head: Expr,
    body: Expr,
}

fn substitute_bindings(bindings: &Bindings, expr: &Expr) -> Expr {
    use Expr::*;
    match expr {
        Sym(name) => {
            if let Some(value) = bindings.get(name) {
                value.clone()
            } else {
                expr.clone()
            }
        },

        Fun(name, args) => {
            let new_name = match bindings.get(name) {
                Some(Sym(new_name)) => new_name.clone(),
                None => name.clone(),
                Some(_) => panic!("Expected symbol in the place of the functor name"),
            };
            let mut new_args = Vec::new();
            for arg in args {
                new_args.push(substitute_bindings(bindings, &arg))
            }
            Fun(new_name, new_args)
        }
    }
}

impl Rule {
    fn apply_all(&self, expr: &Expr) -> Expr {
        if let Some(bindings) = pattern_match(&self.head, expr) {
            substitute_bindings(&bindings, &self.body)
        } else {
            use Expr::*;
            match expr {
                Sym(_) => expr.clone(),
                Fun(name, args) => {
                    let mut new_args = Vec::new();
                    for arg in args {
                        new_args.push(self.apply_all(arg))
                    }
                    Fun(name.clone(), new_args)
                }
            }
        }
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.head, self.body)
    }
}

type Bindings = HashMap<String, Expr>;

fn pattern_match(pattern: &Expr, value: &Expr) -> Option<Bindings> {
    fn pattern_match_impl(pattern: &Expr, value: &Expr, bindings: &mut Bindings) -> bool {
        use Expr::*;
        match (pattern, value) {
            (Sym(name), _) => {
                if let Some(bound_value) = bindings.get(name) {
                    bound_value == value
                } else {
                    bindings.insert(name.clone(), value.clone());
                    true
                }
            },
            (Fun(name1, args1), Fun(name2, args2)) => {
                if name1 == name2 && args1.len() == args2.len() {
                    for i in 0..args1.len() {
                        if !pattern_match_impl(&args1[i], &args2[i], bindings) {
                            return false;
                        }
                    }
                    true
                } else {
                    false
                }
            },
            _ => false,
        }
    }

    let mut bindings = HashMap::new();

    if pattern_match_impl(pattern, value, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

#[allow(unused_macros)]
macro_rules! fun_args {
    () => { vec![] };
    ($name:ident) => { vec![expr!($name)] };
    ($name:ident,$($rest:tt)*) => {
        {
            let mut t = vec![expr!($name)];
            t.append(&mut fun_args!($($rest)*));
            t
        }
    };
    ($name:ident($($args:tt)*)) => {
        vec![expr!($name($($args)*))]
    };
    ($name:ident($($args:tt)*),$($rest:tt)*) => {
        {
            let mut t = vec![expr!($name($($args)*))];
            t.append(&mut fun_args!($($rest)*));
            t
        }
    }
}

#[allow(unused_macros)]
macro_rules! expr {
    ($name:ident) => {
        Expr::Sym(stringify!($name).to_string())
    };
    ($name:ident($($args:tt)*)) => {
        Expr::Fun(stringify!($name).to_string(), fun_args!($($args)*))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn rule_apply_all() {
        // swap(pair(a, b)) = pair(b, a)
        let swap = Rule {
            head: expr!(swap(pair(a, b))),
            body: expr!(pair(b, a)),
        };

        let input = expr! {
            foo(swap(pair(f(a), g(b))),
                swap(pair(q(c), z(d))))
        };

        let expected = expr! {
            foo(pair(g(b), f(a)),
                pair(z(d), q(c)))
        };

        assert_eq!(swap.apply_all(&input), expected);
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum TokenKind {
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
struct Token {
    kind: TokenKind,
    text: String,
    loc: Loc,
}

struct Lexer<Chars: Iterator<Item=char>> {
    chars: Peekable<Chars>,
    invalid: bool,
    file_path: Option<String>,
    lnum: usize,
    bol: usize,
    cnum: usize,
}

impl<Chars: Iterator<Item=char>> Lexer<Chars> {
    fn from_iter(chars: Chars) -> Self {
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

fn main() {
    let swap = Rule {
        head: expr!(swap(pair(a, b))),
        body: expr!(pair(b, a)),
    };
    let mut command = String::new();

    let prompt = "> ";

    loop {
        command.clear();
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();
        match Expr::parse(&mut Lexer::from_iter(command.chars())) {
            Ok(expr) => println!("{}", swap.apply_all(&expr)),
            Err(Error::UnexpectedToken(expected, actual)) => {
                println!("{:>width$}^", "", width=prompt.len() + actual.loc.col);
                println!("ERROR: expected {} but got {} '{}'", expected, actual.kind, actual.text)
            }
            Err(Error::UnexpectedEOF(expected)) => {
                println!("{:>width$}^", "", width=prompt.len() + command.len());
                println!("ERROR: expected {} but got nothing", expected)
            }
        }
    }
}
