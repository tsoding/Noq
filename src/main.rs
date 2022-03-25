use std::collections::HashMap;
use std::iter::Peekable;
use std::io;
use std::io::{stdin, stdout};
use std::io::Write;
use std::fmt;
use std::fs;

mod lexer;

use lexer::*;

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Sym(String),
    Fun(String, Vec<Expr>)
}

#[derive(Debug)]
enum Error {
    UnexpectedToken(TokenKind, Token),
    IoError(io::Error),
}

impl Expr {
    fn parse_peekable(lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<Self, Error> {
        let name = lexer.next().expect("Completely exhausted lexer");

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
                    let close_paren = lexer.next().expect("Completely exhausted lexer");
                    if close_paren.kind == TokenKind::CloseParen {
                        Ok(Expr::Fun(name.text, args))
                    } else {
                        Err(Error::UnexpectedToken(TokenKind::CloseParen, close_paren))
                    }
                } else {
                    Ok(Expr::Sym(name.text))
                }
            },
            _ => Err(Error::UnexpectedToken(TokenKind::Sym, name))
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

fn expect_token_kind(lexer: &mut Peekable<impl Iterator<Item=Token>>, kind: TokenKind) -> Result<Token, Error> {
    let token = lexer.next().expect("Completely exhausted lexer");
    if token.kind == kind {
        Ok(token)
    } else {
        Err(Error::UnexpectedToken(kind, token))
    }
}

impl Rule {
    fn parse(lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<Rule, Error> {
        let head = Expr::parse_peekable(lexer)?;
        expect_token_kind(lexer, TokenKind::Equals)?;
        let body = Expr::parse_peekable(lexer)?;
        Ok(Rule{head, body})
    }

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

fn parse_rules_from_file(file_path: &str) -> Result<HashMap<String, Rule>, Error> {
    let mut rules = HashMap::new();
    let source = fs::read_to_string(file_path).map_err(|e| Error::IoError(e))?;
    let mut lexer = {
        let mut lexer = Lexer::from_iter(source.chars());
        lexer.set_file_path(file_path);
        lexer.peekable()
    };

    while let Some(token) = lexer.peek() {
        if token.kind == TokenKind::End {
            break;
        }

        expect_token_kind(&mut lexer, TokenKind::Rule)?;
        let name = expect_token_kind(&mut lexer, TokenKind::Sym)?;
        let rule = Rule::parse(&mut lexer)?;
        rules.insert(name.text, rule);
    }

    Ok(rules)
}

fn main() {
    let default_rules_path = "rules.noq";
    let rules = match parse_rules_from_file(default_rules_path) {
        Ok(rules) => {
            println!("INFO: successfully loaded rules from {}", default_rules_path);
            rules
        }
        Err(Error::IoError(err)) => {
            eprintln!("ERROR: could not read file {}: {:?}", default_rules_path, err);
            Default::default()
        }
        Err(Error::UnexpectedToken(expected, actual)) => {
            eprintln!("{}: ERROR: expected {} but got {} '{}'",
                      actual.loc, expected, actual.kind, actual.text);
            Default::default()
        }
    };

    println!("Available rules:");
    for (name, rule) in rules {
        println!("rule {} {}", name, rule);
    }

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
            Err(err) => {
                unreachable!("ERROR: {:?}", err)
            }
        }
    }
}
