use std::collections::HashMap;
use std::io::{stdin, stdout};
use std::io::Write;
use std::fmt;
use std::env;
use std::fs;
use std::io;

#[macro_use]
mod lexer;

use lexer::*;

#[derive(Debug, Copy, Clone, PartialEq)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Mod,
}

impl Op {
    const MAX_PRECEDENCE: usize = 2;

    fn from_token_kind(kind: TokenKind) -> Option<Self> {
        match kind {
            TokenKind::Plus => Some(Op::Add),
            TokenKind::Dash => Some(Op::Sub),
            TokenKind::Asterisk => Some(Op::Mul),
            TokenKind::Slash => Some(Op::Div),
            TokenKind::Caret => Some(Op::Pow),
            TokenKind::Percent => Some(Op::Mod),
            _ => None
        }
    }

    fn precedence(&self) -> usize {
        use Op::*;
        match self {
            Add | Sub       => 0,
            Mul | Div | Mod => 1,
            Pow             => 2,
        }
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Add => write!(f, "+"),
            Op::Sub => write!(f, "-"),
            Op::Mul => write!(f, "*"),
            Op::Div => write!(f, "/"),
            Op::Mod => write!(f, "%"),
            Op::Pow => write!(f, "^"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Sym(String),
    Var(String),
    Fun(Box<Expr>, Vec<Expr>),
    Op(Op, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
#[allow(clippy::enum_variant_names)]
/// An error that happens during parsing the Noq source code
enum SyntaxError {
    ExpectedToken(TokenKind, Token),
    ExpectedPrimary(Token),
    ExpectedAppliedRule(Token),
    ExpectedCommand(Token),
}

#[derive(Debug)]
/// An error that happens during execution of the Noq source code
enum RuntimeError {
    RuleAlreadyExists(String, Loc, Option<Loc>),
    RuleDoesNotExist(String, Loc),
    AlreadyShaping(Loc),
    NoShapingInPlace(Loc),
    NoHistory(Loc),
    UnknownStrategy(String, Loc),
    IrreversibleRule(Loc),
    StrategyIsNotSym(Expr, Loc),
    NoMatch(Loc),
    CouldNotLoadFile(Loc, io::Error),
}

#[derive(Debug)]
enum Error {
    Runtime(RuntimeError),
    Syntax(SyntaxError),
}

impl From<SyntaxError> for Error {
    fn from(err: SyntaxError) -> Self {
        Self::Syntax(err)
    }
}

impl From<RuntimeError> for Error {
    fn from(err: RuntimeError) -> Self {
        Self::Runtime(err)
    }
}

enum AppliedRule {
    ByName {
        loc: Loc,
        name: String,
        reversed: bool,
    },
    Anonymous {
        loc: Loc,
        head: Expr,
        body: Expr,
    },
}

impl AppliedRule {
    fn reversed(self) -> Self {
        match self {
            Self::ByName{loc, reversed, name} => Self::ByName {
                loc,
                reversed: !reversed,
                name
            },
            Self::Anonymous{loc, head, body} => Self::Anonymous {
                loc,
                head: body,
                body: head,
            },
        }
    }

    fn parse(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<Self, SyntaxError> {
        let token = lexer.next_token();
        match token.kind {
            TokenKind::Reverse => Ok(Self::parse(lexer)?.reversed()),
            TokenKind::DoubleColon => {
                let head = Expr::parse(lexer)?;
                expect_token_kind(lexer, TokenKind::Equals)?;
                let body = Expr::parse(lexer)?;
                Ok(AppliedRule::Anonymous{ loc: token.loc, head, body })
            },
            TokenKind::Ident => Ok(AppliedRule::ByName {
                loc: token.loc,
                name: token.text,
                reversed: false,
            }),
            _ => Err(SyntaxError::ExpectedAppliedRule(token))
        }
    }
}

type Bindings = HashMap<String, Expr>;

impl Expr {
    fn substitute(&self, bindings: &Bindings) -> Self {
        match self {
            Self::Sym(_) => self.clone(),

            Self::Var(name) => {
                if let Some(value) = bindings.get(name) {
                    value.clone()
                } else {
                    self.clone()
                }
            }

            Self::Op(op, lhs, rhs) => {
                Self::Op(
                    *op,
                    Box::new(lhs.substitute(bindings)),
                    Box::new(rhs.substitute(bindings))
                )
            },

            Self::Fun(head, args) => {
                let new_head = head.substitute(bindings);
                let mut new_args = Vec::new();
                for arg in args {
                    new_args.push(arg.substitute(bindings))
                }
                Self::Fun(Box::new(new_head), new_args)
            }
        }
    }

    pub fn var_or_sym_based_on_name(name: &str) -> Self {
        let x = name.chars().next().expect("Empty names are not allowed. This might be a bug in the lexer.");
        if x.is_uppercase() || x == '_' {
            Self::Var(name.to_string())
        } else {
            Self::Sym(name.to_string())
        }
    }


    pub fn human_name(&self) -> &'static str {
        match self {
            Self::Sym(_) => "a symbol",
            Self::Var(_) => "a variable",
            Self::Fun(_, _) => "a functor",
            Self::Op(_, _, _) => "a binary operator",
        }
    }

    fn parse_fun_args(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<Vec<Self>, SyntaxError> {
        use TokenKind::*;
        let mut args = Vec::new();
        expect_token_kind(lexer, OpenParen)?;
        if lexer.peek_token().kind == CloseParen {
            lexer.next_token();
            return Ok(args)
        }
        args.push(Self::parse(lexer)?);
        while lexer.peek_token().kind == Comma {
            lexer.next_token();
            args.push(Self::parse(lexer)?);
        }
        let close_paren = lexer.next_token();
        if close_paren.kind == CloseParen {
            Ok(args)
        } else {
            Err(SyntaxError::ExpectedToken(CloseParen, close_paren))
        }
    }

    fn parse_fun_or_var_or_sym(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<Self, SyntaxError> {
        let mut head = {
            let token = lexer.peek_token().clone();
            match token.kind {
                TokenKind::OpenParen => {
                    lexer.next_token();
                    let result = Self::parse(lexer)?;
                    expect_token_kind(lexer, TokenKind::CloseParen)?;
                    result
                }

                TokenKind::Ident => {
                    lexer.next_token();
                    Self::var_or_sym_based_on_name(&token.text)
                },

                _ => return Err(SyntaxError::ExpectedPrimary(token))
            }
        };

        while lexer.peek_token().kind == TokenKind::OpenParen {
            head = Expr::Fun(Box::new(head), Self::parse_fun_args(lexer)?)
        }
        Ok(head)
    }

    fn parse_binary_operator(lexer: &mut Lexer<impl Iterator<Item=char>>, current_precedence: usize) -> Result<Self, SyntaxError> {
        if current_precedence > Op::MAX_PRECEDENCE {
            return Self::parse_fun_or_var_or_sym(lexer)
        }

        let mut result = Self::parse_binary_operator(lexer, current_precedence + 1)?;

        while let Some(op) = Op::from_token_kind(lexer.peek_token().kind) {
            if current_precedence != op.precedence() {
                break
            }

            lexer.next_token();

            result = Expr::Op(
                op,
                Box::new(result),
                Box::new(Self::parse_binary_operator(lexer, current_precedence)?)
            );
        }

        Ok(result)
    }

    pub fn parse(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<Self, SyntaxError> {
        Self::parse_binary_operator(lexer, 0)
    }

    fn pattern_match(&self, value: &Expr) -> Option<Bindings> {
        fn pattern_match_impl(pattern: &Expr, value: &Expr, bindings: &mut Bindings) -> bool {
            use Expr::*;
            match (pattern, value) {
                (Sym(name1), Sym(name2)) => {
                    name1 == name2
                }
                (Var(name), _) => {
                    if name == "_" {
                        true
                    } else if let Some(bound_value) = bindings.get(name) {
                        bound_value == value
                    } else {
                        bindings.insert(name.clone(), value.clone());
                        true
                    }
                }
                (Op(op1, lhs1, rhs1), Op(op2, lhs2, rhs2)) => {
                    *op1 == *op2 && pattern_match_impl(lhs1, lhs2, bindings) && pattern_match_impl(rhs1, rhs2, bindings)
                }
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

        if pattern_match_impl(self, value, &mut bindings) {
            Some(bindings)
        } else {
            None
        }
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
        Expr::var_or_sym_based_on_name(stringify!($name))
    };
    ($name:ident($($args:tt)*)) => {
        Expr::Fun(Box::new(Expr::var_or_sym_based_on_name(stringify!($name))), fun_args!($($args)*))
    };
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Sym(name) | Expr::Var(name) => write!(f, "{}", name),
            Expr::Fun(head, args) => {
                match &**head {
                    Expr::Sym(name) | Expr::Var(name) => write!(f, "{}", name)?,
                    other => write!(f, "({})", other)?,
                }
                write!(f, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")? }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            },
            Expr::Op(op, lhs, rhs) => {
                match **lhs {
                    Expr::Op(sub_op, _, _) => if sub_op.precedence() <= op.precedence() {
                        write!(f, "({})", lhs)?
                    } else {
                        write!(f, "{}", lhs)?
                    }
                    _ => write!(f, "{}", lhs)?
                }
                if op.precedence() == 0 {
                    write!(f, " {} ", op)?;
                } else {
                    write!(f, "{}", op)?;
                }
                match **rhs {
                    Expr::Op(sub_op, _, _) => if sub_op.precedence() <= op.precedence() {
                        write!(f, "({})", rhs)
                    } else {
                        write!(f, "{}", rhs)
                    }
                    _ => write!(f, "{}", rhs)
                }
            }
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

#[derive(Debug, Clone)]
enum Rule {
    User {
        loc: Loc,
        head: Expr,
        body: Expr,
    },
    Replace,
}

enum Strategy {
    All,
    Deep,
    Nth(usize),
}

impl Strategy {
    fn by_name(name: &str) -> Option<Self> {
        match name {
            "all"   => Some(Self::All),
            "first" => Some(Self::Nth(0)),
            "deep"  => Some(Self::Deep),
            x       => x.parse().map(Self::Nth).ok()
        }
    }

    fn matched(&self, index: usize) -> Resolution {
        match self {
            Self::All => Resolution {
                action: Action::Apply,
                state: State::Bail,
            },

            Self::Deep => Resolution {
                action: Action::Apply,
                state: State::Cont,
            },

            #[allow(clippy::comparison_chain)]
            Self::Nth(target) => if index == *target {
                Resolution {
                    action: Action::Apply,
                    state: State::Halt,
                }
            } else if index > *target {
                Resolution {
                    action: Action::Skip,
                    state: State::Halt,
                }
            } else {
                Resolution {
                    action: Action::Skip,
                    state: State::Cont,
                }
            },
        }
    }
}

impl Rule {
    fn apply(&self, expr: &Expr, strategy: &Strategy, apply_command_loc: &Loc) -> Result<Expr, RuntimeError> {
        fn apply_to_subexprs(rule: &Rule, expr: &Expr, strategy: &Strategy, apply_command_loc: &Loc, match_count: &mut usize) -> Result<(Expr, bool), RuntimeError> {
            use Expr::*;
            match expr {
                Sym(_) | Var(_) => Ok((expr.clone(), false)),
                Op(op, lhs, rhs) => {
                    let (new_lhs, halt) = apply_impl(rule, lhs, strategy, apply_command_loc, match_count)?;
                    if halt { return Ok((Op(*op, Box::new(new_lhs), rhs.clone()), true)) }
                    let (new_rhs, halt) = apply_impl(rule, rhs, strategy, apply_command_loc, match_count)?;
                    Ok((Op(*op, Box::new(new_lhs), Box::new(new_rhs)), halt))
                },
                Fun(head, args) => {
                    let (new_head, halt) = apply_impl(rule, head, strategy, apply_command_loc, match_count)?;
                    if halt {
                        Ok((Fun(Box::new(new_head), args.clone()), true))
                    } else {
                        let mut new_args = Vec::<Expr>::new();
                        let mut halt_args = false;
                        for arg in args {
                            if halt_args {
                                new_args.push(arg.clone())
                            } else {
                                let (new_arg, halt) = apply_impl(rule, arg, strategy, apply_command_loc, match_count)?;
                                new_args.push(new_arg);
                                halt_args = halt;
                            }
                        }
                        Ok((Fun(Box::new(new_head), new_args), false))
                    }
                }
            }
        }

        fn apply_impl(rule: &Rule, expr: &Expr, strategy: &Strategy, apply_command_loc: &Loc, match_count: &mut usize) -> Result<(Expr, bool), RuntimeError> {
            match rule {
                Rule::User{loc: _, head, body} => {
                    if let Some(bindings) = head.pattern_match(expr) {
                        let resolution = strategy.matched(*match_count);
                        *match_count += 1;
                        let new_expr = match resolution.action {
                            Action::Apply => body.substitute(&bindings),
                            Action::Skip => expr.clone(),
                        };
                        match resolution.state {
                            State::Bail => Ok((new_expr, false)),
                            State::Cont => apply_to_subexprs(rule, &new_expr, strategy, apply_command_loc, match_count),
                            State::Halt => Ok((new_expr, true)),
                        }
                    } else {
                        apply_to_subexprs(rule, expr, strategy, apply_command_loc, match_count)
                    }
                },

                Rule::Replace => {
                    if let Some(bindings) = expr!(apply_rule(Strategy, Head, Body, Expr)).pattern_match(expr) {
                        *match_count += 1;
                        let meta_rule = Rule::User {
                            loc: loc_here!(),
                            head: bindings.get("Head").expect("Variable `Head` is present in the meta pattern").clone(),
                            body: bindings.get("Body").expect("Variable `Body` is present in the meta pattern").clone(),
                        };
                        let meta_strategy = bindings.get("Strategy").expect("Variable `Strategy` is present in the meta pattern");
                        if let Expr::Sym(meta_strategy_name) = meta_strategy {
                            let meta_expr = bindings.get("Expr").expect("Variable `Expr` is present in the meta pattern");
                            let result = match Strategy::by_name(meta_strategy_name) {
                                Some(strategy) => meta_rule.apply(meta_expr, &strategy, apply_command_loc),
                                None => Err(RuntimeError::UnknownStrategy(meta_strategy_name.to_string(), apply_command_loc.clone()))
                            };
                            Ok((result?, false))
                        } else {
                            Err(RuntimeError::StrategyIsNotSym(meta_strategy.clone(), apply_command_loc.clone()))
                        }
                    } else {
                        apply_to_subexprs(rule, expr, strategy, apply_command_loc, match_count)
                    }
                },
            }
        }
        let mut match_count = 0;
        let result = (apply_impl(self, expr, strategy, apply_command_loc, &mut match_count)?).0;
        if match_count > 0 {
            Ok(result)
        } else {
            Err(RuntimeError::NoMatch(apply_command_loc.clone()))
        }
    }
}

fn expect_token_kind(lexer: &mut Lexer<impl Iterator<Item=char>>, kind: TokenKind) -> Result<Token, SyntaxError> {
    let token = lexer.next_token();
    if kind == token.kind {
        Ok(token)
    } else {
        Err(SyntaxError::ExpectedToken(kind, token))
    }
}

enum Command {
    DefineRule(Loc, String, Rule),
    DefineRuleViaShaping {
        loc: Loc,
        name: String,
        expr: Expr,
    },
    StartShaping(Loc, Expr),
    ApplyRule {
        loc: Loc,
        strategy_name: String,
        applied_rule: AppliedRule,
    },
    FinishShaping(Loc),
    UndoRule(Loc),
    Quit,
    DeleteRule(Loc, String),
    Load(Loc, String),
}

impl Command {
    fn parse(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<Command, SyntaxError> {
        let keyword_kind = lexer.peek_token().kind;
        match keyword_kind {
            TokenKind::Load => {
                lexer.next_token();
                let token = expect_token_kind(lexer, TokenKind::Str)?;
                Ok(Self::Load(token.loc, token.text))
            },
            TokenKind::CloseCurly => {
                let keyword = lexer.next_token();
                Ok(Command::FinishShaping(keyword.loc))
            }
            TokenKind::Undo => {
                let keyword = lexer.next_token();
                Ok(Command::UndoRule(keyword.loc))
            }
            TokenKind::Quit => {
                lexer.next_token();
                Ok(Command::Quit)
            }
            TokenKind::Delete => {
                let keyword = lexer.next_token();
                Ok(Command::DeleteRule(keyword.loc, expect_token_kind(lexer, TokenKind::Ident)?.text))
            }
            _ => {
                let expr = Expr::parse(lexer)?;

                match lexer.peek_token().kind {
                    TokenKind::Bar => {
                        let keyword = lexer.next_token();
                        if let Expr::Sym(strategy_name) = expr {
                            let applied_rule = AppliedRule::parse(lexer)?;
                            Ok(Command::ApplyRule {
                                loc: keyword.loc,
                                strategy_name,
                                applied_rule,
                            })
                        } else {
                            todo!("Report that we expected a symbol")
                        }
                    }
                    TokenKind::OpenCurly  => {
                        let keyword = lexer.next_token();
                        Ok(Command::StartShaping(keyword.loc, expr))
                    }
                    TokenKind::DoubleColon => {
                        let keyword = lexer.next_token();
                        match expr {
                            Expr::Sym(name) => {
                                let head = Expr::parse(lexer)?;
                                match lexer.peek_token().kind {
                                    TokenKind::OpenCurly =>  {
                                        lexer.next_token();
                                        Ok(Command::DefineRuleViaShaping {
                                            loc: keyword.loc,
                                            name: name,
                                            expr: head
                                        })
                                    }
                                    TokenKind::Equals => {
                                        lexer.next_token();
                                        let body = Expr::parse(lexer)?;
                                        Ok(Command::DefineRule(
                                            keyword.loc.clone(),
                                            name,
                                            Rule::User {
                                                loc: keyword.loc.clone(),
                                                head,
                                                body,
                                            }
                                        ))
                                    }
                                    _ => Err(SyntaxError::ExpectedCommand(lexer.next_token()).into())
                                }
                            }
                            _ => todo!("Report that we expected a symbol")
                        }
                    }
                    _ => Err(SyntaxError::ExpectedCommand(lexer.next_token()).into())
                }
            }
        }
    }
}

struct Context {
    rules: HashMap<String, Rule>,
    current_expr: Option<Expr>,
    rule_via_shaping: Option<(String, Expr)>,
    shaping_history: Vec<Expr>,
    quit: bool,
}

impl Context {
    fn new() -> Self {
        let mut rules = HashMap::new();
        rules.insert("replace".to_string(), Rule::Replace);
        Self {
            rules,
            current_expr: None,
            rule_via_shaping: None,
            shaping_history: Vec::new(),
            quit: false,
        }
    }

    fn materialize_applied_rule(&self, applied_rule: AppliedRule) -> Result<Rule, RuntimeError> {
        match applied_rule {
            AppliedRule::ByName {loc, name, reversed} => match self.rules.get(&name) {
                Some(rule) => if reversed {
                    match rule.clone() {
                        Rule::User {loc, head, body} => Ok(Rule::User{loc, head: body, body: head}),
                        Rule::Replace => Err(RuntimeError::IrreversibleRule(loc))
                    }
                } else {
                    Ok(rule.clone())
                }

                None => Err(RuntimeError::RuleDoesNotExist(name, loc))
            }
            AppliedRule::Anonymous {loc, head, body} => Ok(Rule::User {loc, head, body}),
        }
    }

    fn process_command(&mut self, command: Command) -> Result<(), Error> {
        match command {
            Command::Load(loc, file_path) => {
                let source = match fs::read_to_string(&file_path) {
                    Ok(source) => source,
                    Err(err) => return Err(RuntimeError::CouldNotLoadFile(loc, err).into())
                };
                let mut lexer = Lexer::new(source.chars(), Some(file_path));
                while lexer.peek_token().kind != TokenKind::End {
                    self.process_command(Command::parse(&mut lexer)?)?
                }
            }
            Command::DefineRule(rule_loc, rule_name, rule) => {
                if let Some(existing_rule) = self.rules.get(&rule_name) {
                    let loc = match existing_rule {
                        Rule::User{loc, ..} => Some(loc),
                        Rule::Replace => None,
                    };
                    return Err(RuntimeError::RuleAlreadyExists(rule_name, rule_loc, loc.cloned()).into())
                }
                println!("defined rule `{}`", &rule_name);
                self.rules.insert(rule_name, rule);
            }
            Command::DefineRuleViaShaping{loc, name, expr, ..} => {
                if self.current_expr.is_some() {
                    return Err(RuntimeError::AlreadyShaping(loc).into())
                }
                println!(" => {}", &expr);
                self.current_expr = Some(expr.clone());
                self.rule_via_shaping = Some((name, expr));
            },
            Command::StartShaping(loc, expr) => {
                if self.current_expr.is_some() {
                    return Err(RuntimeError::AlreadyShaping(loc).into())
                }
                println!(" => {}", &expr);
                self.current_expr = Some(expr);
            },
            Command::ApplyRule {loc, strategy_name, applied_rule} => {
                if let Some(expr) = &self.current_expr {
                    let rule = self.materialize_applied_rule(applied_rule)?;

                    let new_expr = match Strategy::by_name(&strategy_name) {
                        Some(strategy) => rule.apply(expr, &strategy, &loc)?,
                        None => return Err(RuntimeError::UnknownStrategy(strategy_name, loc).into())
                    };
                    println!(" => {}", &new_expr);
                    self.shaping_history.push(
                        self.current_expr.replace(new_expr).expect("current_expr must have something")
                    );
                } else {
                    return Err(RuntimeError::NoShapingInPlace(loc).into());
                }
            }
            Command::FinishShaping(loc) => {
                if let Some(body) = self.current_expr.take() {
                    if let Some((name, head)) = self.rule_via_shaping.take() {
                        if let Some(existing_rule) = self.rules.get(&name) {
                            let old_loc = match existing_rule {
                                Rule::User{loc, ..} => Some(loc.clone()),
                                Rule::Replace => None,
                            };
                            return Err(RuntimeError::RuleAlreadyExists(name, loc, old_loc).into())
                        }
                        println!("defined rule `{}`", &name);
                        self.rules.insert(name, Rule::User {loc, head, body});
                    }
                    self.shaping_history.clear();
                } else {
                    return Err(RuntimeError::NoShapingInPlace(loc).into())
                }
            }
            Command::UndoRule(loc) => {
                if self.current_expr.is_some() {
                    if let Some(previous_expr) = self.shaping_history.pop() {
                        println!(" => {}", &previous_expr);
                        self.current_expr.replace(previous_expr);
                    } else {
                        return Err(RuntimeError::NoHistory(loc).into())
                    }
                } else {
                    return Err(RuntimeError::NoShapingInPlace(loc).into())
                }
            }
            Command::Quit => {
                self.quit = true;
            }
            Command::DeleteRule(loc, name) => {
                if self.rules.contains_key(&name) {
                    self.rules.remove(&name);
                } else {
                    return Err(RuntimeError::RuleDoesNotExist(name, loc).into());
                }
            }
        }
        Ok(())
    }
}

fn eprint_repl_loc_cursor(prompt: &str, loc: &Loc) {
    assert!(loc.row == 1);
    eprintln!("{:>width$}^", "", width=prompt.len() + loc.col - 1);
}

fn start_lexer_debugger() {
    let prompt = "lexer> ";
    let mut command = String::new();
    loop {
        command.clear();
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();
        println!("Tokens: {:?}", Lexer::new(command.trim().chars(), None).map(|t| (t.kind, t.text)).collect::<Vec<_>>());
    }
}

fn start_parser_debugger() {
    let prompt = "parser> ";
    let mut command = String::new();
    loop {
        command.clear();
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();

        let mut lexer = Lexer::new(command.trim().chars(), None);
        if lexer.peek_token().kind != TokenKind::End {
            match Expr::parse(&mut lexer) {
                Err(err) => report_error_in_repl(&err.into(), prompt),
                Ok(expr) => {
                    println!("  Display:  {}", expr);
                    println!("  Debug:    {:?}", expr);
                    println!("  Unparsed: {:?}", lexer.map(|t| (t.kind, t.text)).collect::<Vec<_>>());
                }
            }
        }
    }
}

fn report_error_in_repl(err: &Error, prompt: &str) {
    match err {
        Error::Syntax(err) => match err {
            SyntaxError::ExpectedToken(expected, actual) => {
                eprint_repl_loc_cursor(prompt, &actual.loc);
                eprintln!("ERROR: expected {} but got {} '{}'", expected, actual.kind, actual.text);
            }
            SyntaxError::ExpectedPrimary(token) => {
                eprint_repl_loc_cursor(prompt, &token.loc);
                eprintln!("ERROR: expected Primary Expression (which is either functor, symbol or variable), but got {}", token.kind)
            }
            SyntaxError::ExpectedAppliedRule(token) => {
                eprint_repl_loc_cursor(prompt, &token.loc);
                eprintln!("ERROR: expected applied rule argument, but got {}", token.kind)
            }
            SyntaxError::ExpectedCommand(token) => {
                eprint_repl_loc_cursor(prompt, &token.loc);
                eprintln!("ERROR: expected command, but got {}", token.kind);
            }
        }

        Error::Runtime(err) => match err {
            RuntimeError::RuleAlreadyExists(name, _new_loc, old_loc) => {
                eprintln!("ERROR: redefinition of existing rule {}", name);
                if let Some(loc) = old_loc {
                    if loc.file_path.is_some() {
                        eprintln!("{}: Previous definition is located here", loc);
                    }
                }
            }
            RuntimeError::AlreadyShaping(_loc) => {
                eprintln!("ERROR: already shaping an expression. Finish the current shaping with {} first.", TokenKind::CloseCurly);
            }
            RuntimeError::NoShapingInPlace(_loc) => {
                eprintln!("ERROR: no shaping in place.");
            }
            RuntimeError::RuleDoesNotExist(name, _loc) => {
                eprintln!("ERROR: rule {} does not exist", name);
            }
            RuntimeError::NoHistory(_loc) => {
                eprintln!("ERROR: no history");
            }
            RuntimeError::UnknownStrategy(name, _loc) => {
                eprintln!("ERROR: unknown rule application strategy '{}'", name);
            }
            RuntimeError::IrreversibleRule(_loc) => {
                eprintln!("ERROR: irreversible rule");
            }
            RuntimeError::StrategyIsNotSym(expr, _loc) => {
                eprintln!("ERROR: strategy must be a symbol but got {} {}", expr.human_name(), &expr);
            }
            RuntimeError::NoMatch(_loc) => {
                eprintln!("ERROR: no match found");
            }
            RuntimeError::CouldNotLoadFile(_loc, err) => {
                eprintln!("ERROR: could not load file {:?}", err)
            }
        }
    }
}

fn parse_and_process_command(context: &mut Context, lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<(), Error> {
    let command = Command::parse(lexer)?;
    context.process_command(command)?;
    Ok(())
}

fn interpret_file(file_path: &str) {
    let mut context = Context::new();
    let source = fs::read_to_string(&file_path).unwrap();
    let mut lexer = Lexer::new(source.chars(), Some(file_path.to_string()));
    while !context.quit && lexer.peek_token().kind != TokenKind::End {
        if let Err(err) = parse_and_process_command(&mut context, &mut lexer) {
            match err {
                Error::Syntax(SyntaxError::ExpectedToken(expected_kinds, actual_token)) => {
                    eprintln!("{}: ERROR: expected {} but got {} '{}'",
                              actual_token.loc, expected_kinds, actual_token.kind, actual_token.text);
                }
                Error::Syntax(SyntaxError::ExpectedPrimary(token)) => {
                    eprintln!("{}: ERROR: expected Primary Expression (which is either functor, symbol or variable), but got {}", token.loc, token.kind)
                }
                Error::Syntax(SyntaxError::ExpectedAppliedRule(token)) => {
                    eprintln!("{}: ERROR: expected applied rule argument, but got {}", token.loc, token.kind)
                }
                Error::Syntax(SyntaxError::ExpectedCommand(token)) => {
                    eprintln!("{}: ERROR: expected command, but got {}", token.loc, token.kind)
                }
                Error::Runtime(RuntimeError::RuleAlreadyExists(name, new_loc, old_loc)) => {
                    eprintln!("{}: ERROR: redefinition of existing rule {}", new_loc, name);
                    if let Some(loc) = old_loc {
                        eprintln!("{}: Previous definition is located here", loc);
                    }
                }
                Error::Runtime(RuntimeError::RuleDoesNotExist(name, loc)) => {
                    eprintln!("{}: ERROR: rule {} does not exist", loc, name);
                }
                Error::Runtime(RuntimeError::AlreadyShaping(loc)) => {
                    eprintln!("{}: ERROR: already shaping an expression. Finish the current shaping with {} first.",
                              loc, TokenKind::CloseCurly);
                }
                Error::Runtime(RuntimeError::NoShapingInPlace(loc)) => {
                    eprintln!("{}: ERROR: no shaping in place.", loc);
                }
                Error::Runtime(RuntimeError::NoHistory(loc)) => {
                    eprintln!("{}: ERROR: no history", loc);
                }
                Error::Runtime(RuntimeError::UnknownStrategy(name, loc)) => {
                    eprintln!("{}: ERROR: unknown rule application strategy '{}'", loc, name);
                }
                Error::Runtime(RuntimeError::IrreversibleRule(loc)) => {
                    eprintln!("{}: ERROR: irreversible rule", loc);
                }
                Error::Runtime(RuntimeError::StrategyIsNotSym(expr, loc)) => {
                    eprintln!("{}: ERROR: strategy must be a symbol but got {} `{}`", loc, expr.human_name(), &expr);
                }
                Error::Runtime(RuntimeError::NoMatch(loc)) => {
                    eprintln!("{}: ERROR: no match", loc);
                }
                Error::Runtime(RuntimeError::CouldNotLoadFile(loc, err)) => {
                    eprintln!("{}: ERROR: could not load file {:?}", loc, err);
                }
            }
            std::process::exit(1);
        }
    }
}

fn start_repl() {
    let mut context = Context::new();
    let mut command = String::new();

    let default_prompt = "noq> ";
    let shaping_prompt = "> ";
    let mut prompt: &str;

    while !context.quit {
        command.clear();
        if context.current_expr.is_some() {
            prompt = shaping_prompt;
        } else {
            prompt = default_prompt;
        }
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();
        let mut lexer = Lexer::new(command.trim().chars(), None);
        if lexer.peek_token().kind != TokenKind::End {
            let result = parse_and_process_command(&mut context, &mut lexer)
                .and_then(|()| expect_token_kind(&mut lexer, TokenKind::End).map_err(|e| e.into()));
            if let Err(err) = result {
                report_error_in_repl(&err, prompt);
            }
        }
    }
}

enum ReplMode {
    Normal,
    DebugParser,
    DebugLexer,
}

struct Config {
    file_path: Option<String>,
    mode: ReplMode,
}

impl Config {
    fn from_iter(args: &mut impl Iterator<Item=String>) -> Self {
        args.next().expect("Program name should be always present");
        let mut config: Self = Self {
            file_path: None,
            mode: ReplMode::Normal,
        };

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--debug" => {
                    if let Some(mode_name) = args.next() {
                        match mode_name.as_str() {
                            "parser" => config.mode = ReplMode::DebugParser,
                            "lexer" => config.mode = ReplMode::DebugLexer,
                            _ => {
                                eprintln!("ERROR: unknown debug mode {}", mode_name);
                                std::process::exit(1)
                            }
                        }
                    } else {
                        eprintln!("ERROR: no argument is provided for flag {}", arg);
                        std::process::exit(1)
                    }
                },

                other => if config.file_path.is_none() {
                    config.file_path = Some(other.to_string())
                } else {
                    eprintln!("ERROR: file path was already provided. Interpreting several files is not supported yet");
                    std::process::exit(1)
                }
            }
        }

        config
    }
}

fn main() {
    let config = Config::from_iter(&mut env::args());

    if let Some(file_path) = &config.file_path {
        interpret_file(file_path)
    } else {
        match config.mode {
            ReplMode::Normal => start_repl(),
            ReplMode::DebugParser => start_parser_debugger(),
            ReplMode::DebugLexer => start_lexer_debugger(),
        }
    }
}

// TODO: Nested shaping
// TODO: Custom arbitrary operators like in Haskell
// TODO: Save session to file
// TODO: Conditional matching of rules. Some sort of ability to combine several rules into one which tries all the provided rules sequentially and pickes the one that matches
