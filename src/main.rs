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
    Var(String),
    Fun(Box<Expr>, Vec<Expr>),
}

#[derive(Debug)]
enum Error {
    UnexpectedToken(TokenKindSet, Token),
    RuleAlreadyExists(String, Loc, Loc),
    RuleDoesNotExist(String, Loc),
    AlreadyShaping(Loc),
    NoShapingInPlace(Loc),
    NoHistory(Loc),
    UnknownStrategy(String, Loc),
}

impl Expr {
    fn var_or_sym_from_name(name: &str) -> Expr {
        if name.chars().next().expect("Empty names are not allowed").is_uppercase() {
            Expr::Var(name.to_string())
        } else {
            Expr::Sym(name.to_string())
        }
    }

    fn parse(lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<Self, Error> {
        use TokenKind::*;
        let name = expect_token_kind(lexer, TokenKindSet::single(Ident))?;
        if let Some(_) = lexer.next_if(|t| t.kind == OpenParen) {
            let mut args = Vec::new();
            if let Some(_) = lexer.next_if(|t| t.kind == CloseParen) {
                return Ok(Expr::Fun(Box::new(Self::var_or_sym_from_name(&name.text)), args))
            }
            args.push(Self::parse(lexer)?);
            while let Some(_) = lexer.next_if(|t| t.kind == Comma) {
                args.push(Self::parse(lexer)?);
            }
            let close_paren = lexer.next().expect("Completely exhausted lexer");
            if close_paren.kind == CloseParen {
                Ok(Expr::Fun(Box::new(Self::var_or_sym_from_name(&name.text)), args))
            } else {
                Err(Error::UnexpectedToken(TokenKindSet::single(CloseParen), close_paren))
            }
        } else {
            Ok(Self::var_or_sym_from_name(&name.text))
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Sym(name) | Expr::Var(name) => write!(f, "{}", name),
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

enum Action {
    Skip,
    Apply
}

enum State {
    /// Stop the current recursion branch and try other braunches
    Bail,
    /// Continue applying the rule to the result of the application
    Cont,
    /// Completely stop the application process
    Halt,
}

struct Resolution {
    action: Action,
    state: State,
}

trait Strategy {
    fn matched(&mut self) -> Resolution;
}

#[derive(Debug)]
struct Rule {
    loc: Loc,
    head: Expr,
    body: Expr,
}

struct ApplyAll;

impl Strategy for ApplyAll {
    fn matched(&mut self) -> Resolution {
        Resolution {
            action: Action::Apply,
            state: State::Bail,
        }
    }
}

#[derive(Default)]
struct ApplyFirst;

impl Strategy for ApplyFirst {
    fn matched(&mut self) -> Resolution {
        Resolution {
            action: Action::Apply,
            state: State::Halt,
        }
    }
}

struct ApplyDeep;

impl Strategy for ApplyDeep {
    fn matched(&mut self) -> Resolution {
        Resolution {
            action: Action::Apply,
            state: State::Cont,
        }
    }
}

impl Rule {
    fn apply(&self, expr: &Expr, strategy: &mut impl Strategy) -> Expr {
        fn apply_to_subexprs(rule: &Rule, expr: &Expr, strategy: &mut impl Strategy) -> (Expr, bool) {
            use Expr::*;
            match expr {
                Sym(_) | Var(_) => (expr.clone(), false),
                Fun(head, args) => {
                    let (new_head, halt) = apply_impl(rule, head, strategy);
                    if halt {
                        (Fun(Box::new(new_head), args.clone()), true)
                    } else {
                        let mut new_args = Vec::<Expr>::new();
                        let mut halt_args = false;
                        for arg in args {
                            if halt_args {
                                new_args.push(arg.clone())
                            } else {
                                let (new_arg, halt) = apply_impl(rule, arg, strategy);
                                new_args.push(new_arg);
                                halt_args = halt;
                            }
                        }
                        (Fun(Box::new(new_head), new_args), false)
                    }
                }
            }
        }

        fn apply_impl(rule: &Rule, expr: &Expr, strategy: &mut impl Strategy) -> (Expr, bool) {
            if let Some(bindings) = pattern_match(&rule.head, expr) {
                let resolution = strategy.matched();
                let new_expr = match resolution.action {
                    Action::Apply => substitute_bindings(&bindings, &rule.body),
                    Action::Skip => expr.clone(),
                };
                match resolution.state {
                    State::Bail => (new_expr, false),
                    State::Cont => apply_to_subexprs(rule, &new_expr, strategy),
                    State::Halt => (new_expr, true),
                }
            } else {
                apply_to_subexprs(rule, expr, strategy)
            }
        }
        apply_impl(self, expr, strategy).0
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.head, self.body)
    }
}

fn substitute_bindings(bindings: &Bindings, expr: &Expr) -> Expr {
    use Expr::*;
    match expr {
        Sym(_) => expr.clone(),

        Var(name) => {
            if let Some(value) = bindings.get(name) {
                value.clone()
            } else {
                expr.clone()
            }
        },

        Fun(head, args) => {
            let new_head = substitute_bindings(bindings, head);
            let mut new_args = Vec::new();
            for arg in args {
                new_args.push(substitute_bindings(bindings, &arg))
            }
            Fun(Box::new(new_head), new_args)
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

type Bindings = HashMap<String, Expr>;

fn pattern_match(pattern: &Expr, value: &Expr) -> Option<Bindings> {
    fn pattern_match_impl(pattern: &Expr, value: &Expr, bindings: &mut Bindings) -> bool {
        use Expr::*;
        match (pattern, value) {
            (Sym(name1), Sym(name2)) => {
                name1 == name2
            }
            (Var(name), _) => {
                if let Some(bound_value) = bindings.get(name) {
                    bound_value == value
                } else {
                    bindings.insert(name.clone(), value.clone());
                    true
                }
            },
            (Fun(name1, args1), Fun(name2, args2)) => {
                if pattern_match_impl(name1, name2, bindings) && args1.len() == args2.len() {
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

#[derive(Default)]
struct Context {
    rules: HashMap<String, Rule>,
    current_expr: Option<Expr>,
    shaping_history: Vec<Expr>,
    quit: bool,
}

impl Context {
    fn process_command(&mut self, lexer: &mut Peekable<impl Iterator<Item=Token>>) -> Result<(), Error> {
        let expected_tokens = TokenKindSet::empty()
            .set(TokenKind::Rule)
            .set(TokenKind::Shape)
            .set(TokenKind::Apply)
            .set(TokenKind::Done)
            .set(TokenKind::Undo)
            .set(TokenKind::Quit);
        let keyword = expect_token_kind(lexer, expected_tokens)?;
        match keyword.kind {
            TokenKind::Rule => {
                let name = expect_token_kind(lexer, TokenKindSet::single(TokenKind::Ident))?;
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
                self.rules.insert(name.text, rule);
            }
            TokenKind::Shape => {
                if let Some(_) = self.current_expr {
                    return Err(Error::AlreadyShaping(keyword.loc))
                }

                let expr = Expr::parse(lexer)?;
                println!(" => {}", &expr);
                self.current_expr = Some(expr);
            },
            TokenKind::Apply => {
                if let Some(expr) = &self.current_expr {
                    let strategy_name = expect_token_kind(lexer, TokenKindSet::single(TokenKind::Ident))?;

                    let expected_kinds = TokenKindSet::empty()
                        .set(TokenKind::Ident)
                        .set(TokenKind::Rule);
                    let token = expect_token_kind(lexer, expected_kinds)?;
                    let mut anonymous_rule: Option<Rule> = None;
                    let rule = match token.kind {
                        TokenKind::Ident => {
                            if let Some(rule) = self.rules.get(&token.text) {
                                rule
                            } else {
                                return Err(Error::RuleDoesNotExist(token.text, token.loc));
                            }
                        }

                        TokenKind::Rule => {
                            let head = Expr::parse(lexer)?;
                            expect_token_kind(lexer, TokenKindSet::single(TokenKind::Equals))?;
                            let body = Expr::parse(lexer)?;
                            anonymous_rule.insert(Rule {loc: token.loc, head, body})
                        }

                        _ => unreachable!("Expected {} but got {}", expected_kinds, token.kind)
                    };

                    // todo!("Throw an error if not a single match for the rule was found")

                    let new_expr = match &strategy_name.text as &str {
                        "all" => rule.apply(&expr, &mut ApplyAll),
                        "first" => rule.apply(&expr, &mut ApplyFirst),
                        "deep" => rule.apply(&expr, &mut ApplyDeep),
                        _ => return Err(Error::UnknownStrategy(strategy_name.text, strategy_name.loc))
                    };
                    println!(" => {}", &new_expr);
                    self.shaping_history.push(
                        self.current_expr.replace(new_expr).expect("current_expr must have something")
                    );
                } else {
                    return Err(Error::NoShapingInPlace(keyword.loc));
                }
            }
            TokenKind::Done => {
                if let Some(_) = &self.current_expr {
                    self.current_expr = None;
                    self.shaping_history.clear();
                } else {
                    return Err(Error::NoShapingInPlace(keyword.loc))
                }
            }
            TokenKind::Undo => {
                if let Some(_) = &self.current_expr {
                    if let Some(previous_expr) = self.shaping_history.pop() {
                        println!(" => {}", &previous_expr);
                        self.current_expr.replace(previous_expr);
                    } else {
                        return Err(Error::NoHistory(keyword.loc))
                    }
                } else {
                    return Err(Error::NoShapingInPlace(keyword.loc))
                }
            }
            TokenKind::Quit => {
                self.quit = true;
            }
            _ => unreachable!("Expected {} but got {} '{}'", expected_tokens, keyword.kind, keyword.text),
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
                        eprintln!("{}: ERROR: expected {} but got {} '{}'",
                                  actual_token.loc, expected_kinds, actual_token.kind, actual_token.text);
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
                    Error::NoHistory(loc) => {
                        eprintln!("{}: ERROR: no history", loc);
                    }
                    Error::UnknownStrategy(name, loc) => {
                        eprintln!("{}: ERROR: unknown rule application strategy '{}'", loc, name);
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
            if lexer.peek().expect("Completely exhausted lexer").kind != TokenKind::End {
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
                    Err(Error::NoHistory(loc)) => {
                        eprint_repl_loc_cursor(prompt, &loc);
                        eprintln!("ERROR: no history");
                    }
                    Err(Error::UnknownStrategy(name, loc)) => {
                        eprint_repl_loc_cursor(prompt, &loc);
                        eprintln!("ERROR: unknown rule application strategy '{}'", name);
                    }
                    Ok(_) => {}
                }
            }
        }
    }
}
