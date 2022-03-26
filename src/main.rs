use std::collections::HashMap;
use std::iter::Peekable;
use std::io::{stdin, stdout};
use std::io::Write;
use std::fmt;
use std::env;
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
    UnexpectedToken(TokenKindSet, Token),
    RuleAlreadyExists(String, Loc, Loc),
    RuleDoesNotExist(String, Loc),
    AlreadyShaping(Loc),
    NoShapingInPlace(Loc),
}

impl Expr {
    fn parse(lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<Self, Error> {
        use TokenKind::*;
        let name = lexer.next().expect("Completely exhausted lexer");
        match name.kind {
            Sym => {
                if let Some(_) = lexer.next_if(|t| t.kind == OpenParen) {
                    let mut args = Vec::new();
                    if let Some(_) = lexer.next_if(|t| t.kind == CloseParen) {
                        return Ok(Expr::Fun(name.text, args))
                    }
                    args.push(Self::parse(lexer)?);
                    while let Some(_) = lexer.next_if(|t| t.kind == Comma) {
                        args.push(Self::parse(lexer)?);
                    }
                    let close_paren = lexer.next().expect("Completely exhausted lexer");
                    if close_paren.kind == CloseParen {
                        Ok(Expr::Fun(name.text, args))
                    } else {
                        Err(Error::UnexpectedToken(TokenKindSet::single(CloseParen), close_paren))
                    }
                } else {
                    Ok(Expr::Sym(name.text))
                }
            },
            _ => Err(Error::UnexpectedToken(TokenKindSet::single(Sym), name))
        }
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
    loc: Loc,
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
                Some(_) => todo!("Report expected symbol in the place of the functor name"),
            };
            let mut new_args = Vec::new();
            for arg in args {
                new_args.push(substitute_bindings(bindings, &arg))
            }
            Fun(new_name, new_args)
        }
    }
}

fn expect_token_kind(lexer: &mut Peekable<impl Iterator<Item=Token>>, kinds: TokenKindSet) -> Result<Token, Error> {
    let token = lexer.next().expect("Completely exhausted lexer");
    if kinds.contains(token.kind) {
        Ok(token)
    } else {
        Err(Error::UnexpectedToken(kinds, token))
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

#[derive(Default)]
struct Context {
    rules: HashMap<String, Rule>,
    current_expr: Option<Expr>,
    quit: bool,
}

impl Context {
    fn process_command(&mut self, lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<(), Error> {
        let expected_tokens = TokenKindSet::empty()
            .set(TokenKind::Rule)
            .set(TokenKind::Shape)
            .set(TokenKind::Apply)
            .set(TokenKind::Done)
            .set(TokenKind::Quit);
        let keyword = expect_token_kind(lexer, expected_tokens)?;
        // todo!("Ability to undo the rule application");
        match keyword.kind {
            TokenKind::Rule => {
                let name = expect_token_kind(lexer, TokenKindSet::single(TokenKind::Sym))?;
                if let Some(existing_rule) = self.rules.get(&name.text) {
                    return Err(Error::RuleAlreadyExists(name.text, name.loc, existing_rule.loc.clone()))
                }
                let head = Expr::parse(lexer)?;
                expect_token_kind(lexer, TokenKindSet::single(TokenKind::Equals))?;
                let body = Expr::parse(lexer)?;
                let rule = Rule {
                    loc: keyword.loc,
                    head,
                    body,
                };
                println!("rule {}", &rule);
                self.rules.insert(name.text, rule);
            }
            TokenKind::Shape => {
                if let Some(_) = self.current_expr {
                    return Err(Error::AlreadyShaping(keyword.loc))
                }

                let expr = Expr::parse(lexer)?;
                println!("shaping {}", &expr);
                self.current_expr = Some(expr);
            },
            TokenKind::Apply => {
                if let Some(expr) = &self.current_expr {
                    let expected_kinds = TokenKindSet::empty()
                        .set(TokenKind::Sym)
                        .set(TokenKind::Rule);
                    let token = expect_token_kind(lexer, expected_kinds)?;
                    match token.kind {
                        TokenKind::Sym => {
                            if let Some(rule) = self.rules.get(&token.text) {
                                // todo!("Throw an error if not a single match for the rule was found")
                                let new_expr = rule.apply_all(&expr);
                                println!(" => {}", &new_expr);
                                self.current_expr = Some(new_expr);
                            } else {
                                return Err(Error::RuleDoesNotExist(token.text, token.loc));
                            }
                        }

                        TokenKind::Rule => {
                            let head = Expr::parse(lexer)?;
                            expect_token_kind(lexer, TokenKindSet::single(TokenKind::Equals))?;
                            let body = Expr::parse(lexer)?;
                            let new_expr = Rule {loc: token.loc, head, body}.apply_all(&expr);
                            println!(" => {}", &new_expr);
                            self.current_expr = Some(new_expr);
                        }

                        _ => unreachable!("Expected {} but got {}", expected_kinds, token.kind)
                    }
                } else {
                    return Err(Error::NoShapingInPlace(keyword.loc));
                }
            }
            TokenKind::Done => {
                if let Some(_) = &self.current_expr {
                    self.current_expr = None
                } else {
                    return Err(Error::NoShapingInPlace(keyword.loc))
                }
            }
            TokenKind::Quit => {
                self.quit = true;
            }
            _ => unreachable!("Expected {} but got {}", expected_tokens, keyword.kind),
        }
        Ok(())
    }
}

fn eprint_repl_loc_cursor(prompt: &str, loc: &Loc) {
    assert!(loc.row == 1);
    eprintln!("{:>width$}^", "", width=prompt.len() + loc.col - 1);
}

fn main() {
    let mut args = env::args();
    args.next(); // skip program

    let mut context = Context::default();

    if let Some(file_path) = args.next() {
        let source = fs::read_to_string(&file_path).unwrap();
        let mut lexer = {
            let mut lexer = Lexer::from_iter(source.chars());
            lexer.set_file_path(&file_path);
            lexer.peekable()
        };
        while !context.quit && lexer.peek().expect("Completely exhausted lexer").kind != TokenKind::End {
            if let Err(err) = context.process_command(&mut lexer) {
                match err {
                    Error::UnexpectedToken(expected_kinds, actual_token) => {
                        eprintln!("{}: ERROR: expected {} but got {}", actual_token.loc, expected_kinds, actual_token.kind);
                    }
                    Error::RuleAlreadyExists(name, new_loc, old_loc) => {
                        eprintln!("{}: ERROR: redefinition of existing rule {}", new_loc, name);
                        eprintln!("{}: Previous definition is located here", old_loc);
                    }
                    Error::RuleDoesNotExist(name, loc) => {
                        eprintln!("{}: ERROR: rule {} does not exist", loc, name);
                    }
                    Error::AlreadyShaping(loc) => {
                        eprintln!("{}: ERROR: already shaping an expression. Finish the current shaping with {} first.",
                                  loc, TokenKind::Done);
                    }
                    Error::NoShapingInPlace(loc) => {
                        eprintln!("{}: ERROR: no shaping in place.", loc);
                    }
                }
                std::process::exit(1);
            }
        }
    } else {
        let mut command = String::new();

        let default_prompt = "noq> ";
        let shaping_prompt = "> ";
        let mut prompt: &str;

        while !context.quit {
            command.clear();
            if let Some(_) = &context.current_expr {
                prompt = shaping_prompt;
            } else {
                prompt = default_prompt;
            }
            print!("{}", prompt);
            stdout().flush().unwrap();
            stdin().read_line(&mut command).unwrap();
            let mut lexer = Lexer::from_iter(command.trim().chars()).peekable();
            let result = context.process_command(&mut lexer)
                .and_then(|()| expect_token_kind(&mut lexer, TokenKindSet::single(TokenKind::End)));
            match result {
                Err(Error::UnexpectedToken(expected, actual)) => {
                    eprint_repl_loc_cursor(prompt, &actual.loc);
                    eprintln!("ERROR: expected {} but got {} '{}'", expected, actual.kind, actual.text);
                }
                Err(Error::RuleAlreadyExists(name, new_loc, _old_loc)) => {
                    eprint_repl_loc_cursor(prompt, &new_loc);
                    eprintln!("ERROR: redefinition of existing rule {}", name);
                }
                Err(Error::AlreadyShaping(loc)) => {
                    eprint_repl_loc_cursor(prompt, &loc);
                    eprintln!("ERROR: already shaping an expression. Finish the current shaping with {} first.",
                              TokenKind::Done);
                }
                Err(Error::NoShapingInPlace(loc)) => {
                    eprint_repl_loc_cursor(prompt, &loc);
                    eprintln!("ERROR: no shaping in place.");
                }
                Err(Error::RuleDoesNotExist(name, loc)) => {
                    eprint_repl_loc_cursor(prompt, &loc);
                    eprintln!("ERROR: rule {} does not exist", name);
                }
                Ok(_) => {}
            }
        }
    }
}
