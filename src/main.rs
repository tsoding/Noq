use std::collections::HashMap;
use std::io::{stdin, stdout};
use std::io::Write;
use std::env;
use std::fs;
use std::io;
use std::fmt;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

#[macro_use]
mod lexer;
mod repl;
#[macro_use]
mod expr;

use lexer::*;
use repl::*;
use expr::*;

#[derive(Debug)]
enum CommandSyntaxError {
    LoadArg(Token),
    SaveArg(Token),
    DeleteArg(Token),
    /// Failed to parse the start of the command.
    ///
    /// The start of the command is always an expression. The specific
    /// command is determined by a token after the expression.
    CommandStart(expr::SyntaxError),
    /// Failed to parse the command separator.
    ///
    /// The command separator comes after the starting expression of
    /// the command and determines the command itself.
    CommandSep(Token),
    StrategyName(Token),
    AnonymousRuleBody(expr::SyntaxError),
    AnonymousRuleWithoutStrategy(Token),
    DefineRuleHead(expr::SyntaxError),
    DefineRuleBody(expr::SyntaxError),
    DefineRuleSep(Token),
    UnparsedInput(Token),
}

impl CommandSyntaxError {
    fn loc(&self) -> &Loc {
        match self {
            Self::LoadArg(token) |
            Self::SaveArg(token) |
            Self::DeleteArg(token) |
            Self::CommandSep(token) |
            Self::StrategyName(token) |
            Self::AnonymousRuleWithoutStrategy(token) |
            Self::UnparsedInput(token) |
            Self::DefineRuleSep(token) => &token.loc,

            Self::CommandStart(expr_err) |
            Self::AnonymousRuleBody(expr_err) |
            Self::DefineRuleHead(expr_err) |
            Self::DefineRuleBody(expr_err) => expr_err.loc(),
        }
    }
}

impl fmt::Display for CommandSyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::LoadArg(token) => write!(f, "`load` Command Argument must be {}, but got {} instead", TokenKind::Str, token),
            Self::SaveArg(token) => write!(f, "`save` Command Argument must be {}, but got {} instead", TokenKind::Str, token),
            Self::DeleteArg(token) => write!(f, "`delete` Command Argument must be {}, but got {} instead", TokenKind::Ident, token),
            // TODO: report what are the valid command separators
            Self::CommandSep(token) => write!(f, "expected Command Separator, but got {} instead", token),
            Self::StrategyName(token) => write!(f, "Strategy Name must be {}, but got {} instead", TokenKind::Ident, token),
            Self::AnonymousRuleWithoutStrategy(token) => write!(f, "expected {} after the Anonymous Rule, but got {}", TokenKind::Bar, token.kind),
            // TODO: report what are the valid rule definition separators
            Self::DefineRuleSep(token) => write!(f, "unexpected Rule Definition Separator {}", token),

            Self::UnparsedInput(token) => write!(f, "unexpected token {} after the End of the Command", token),
            Self::CommandStart(expr_err) => write!(f, "invalid Starting Expression of the Command: {}", expr_err),
            Self::AnonymousRuleBody(expr_err) => write!(f, "invalid Body of the Anonymous Rule: {}", expr_err),
            Self::DefineRuleHead(expr_err) => write!(f, "invalid Head of the Rule Definition: {}", expr_err),
            Self::DefineRuleBody(expr_err) => write!(f, "invalid Body of the Rule Definition: {}", expr_err),
        }
    }
}

#[derive(Debug)]
/// An error that happens during execution of the Noq source code
enum RuntimeError {
    RuleAlreadyExists(String, Loc, Option<Loc>),
    RuleDoesNotExist(String, Loc),
    NoShapingInPlace(Loc),
    EndOfHistory(Loc),
    UnknownStrategy(String, Loc),
    IrreversibleRule(Loc),
    StrategyIsNotSym(Expr, Loc),
    NoMatch(Loc),
    CouldNotLoadFile(Loc, io::Error),
    CouldNotSaveFile(Loc, io::Error),
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::RuleAlreadyExists(name, _new_loc, _old_loc) => write!(f, "redefinition of existing rule {}", name),
            Self::NoShapingInPlace(_loc) => write!(f, "no shaping in place."),
            Self::RuleDoesNotExist(name, _loc) => write!(f, "rule {} does not exist", name),
            Self::EndOfHistory(_loc) => write!(f, "end of history"),
            Self::UnknownStrategy(name, _loc) => write!(f, "unknown rule application strategy '{}'", name),
            Self::IrreversibleRule(_loc) => write!(f, "irreversible rule"),
            Self::StrategyIsNotSym(expr, _loc) => write!(f, "strategy must be a symbol but got {} {}", expr.human_name(), &expr),
            Self::NoMatch(_loc) => write!(f, "no match found"),
            Self::CouldNotLoadFile(_loc, err) => write!(f, "could not load file {:?}", err),
            Self::CouldNotSaveFile(_loc, err) => write!(f, "could not save file {:?}", err),
        }
    }
}

impl RuntimeError {
    fn loc(&self) -> &Loc {
        match self {
            Self::RuleAlreadyExists(_, loc, _) |
            Self::RuleDoesNotExist(_, loc) |
            Self::NoShapingInPlace(loc) |
            Self::EndOfHistory(loc) |
            Self::UnknownStrategy(_, loc) |
            Self::IrreversibleRule(loc) |
            Self::StrategyIsNotSym(_, loc) |
            Self::NoMatch(loc) |
            Self::CouldNotLoadFile(loc, _) |
            Self::CouldNotSaveFile(loc, _) => loc,
        }
    }
}

#[derive(Debug)]
enum Error {
    Runtime(RuntimeError),
    CommandSyntax(CommandSyntaxError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Runtime(err) => write!(f, "{}", err),
            Self::CommandSyntax(err) => write!(f, "{}", err),
        }
    }
}

impl Error {
    fn loc(&self) -> &Loc {
        match self {
            Self::Runtime(err) => err.loc(),
            Self::CommandSyntax(err) => err.loc(),
        }
    }
}

impl From<CommandSyntaxError> for Error {
    fn from(err: CommandSyntaxError) -> Self {
        Self::CommandSyntax(err)
    }
}

impl From<RuntimeError> for Error {
    fn from(err: RuntimeError) -> Self {
        Self::Runtime(err)
    }
}

#[derive(Clone)]
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

#[derive(Clone)]
enum Command {
    /// Define rule
    ///
    /// Example:
    /// ```noq
    /// sum_comm :: A + B = B + A
    /// ```
    DefineRule(Loc, String, Rule),
    /// Define rule via shaping
    ///
    /// Starts the process of shaping and defines a rule after it's done
    ///
    /// Example:
    /// ```noq
    /// sum_comm :: A + B { # <- the define rule via shaping command
    ///   ...
    /// }
    /// ```
    DefineRuleViaShaping {
        name: String,
        expr: Expr,
    },
    /// Starting shaping
    ///
    /// Example:
    /// ```noq
    /// A + B { # <- the start shaping command
    ///   ...
    /// }
    /// ```
    StartShaping(Loc, Expr),
    /// Apply rule during shaping
    ///
    /// Example:
    /// ```noq
    /// name :: ... {
    ///   ...
    ///   sum_comm      | all # <- the apply rule command
    ///   A + B = B + A | all # <- another apply rule command
    ///   ...
    /// }
    /// ```
    ApplyRule {
        loc: Loc,
        strategy_name: String,
        applied_rule: AppliedRule,
    },
    /// Finish the process of shaping
    ///
    /// Example:
    /// ```noq
    /// A + B :: {
    ///   ...
    /// } # <- the finish shaping command
    /// ```
    FinishShaping(Loc),
    /// Undo previusly applied rule
    ///
    /// Example:
    /// ```noq
    /// A + B :: {
    ///   ...
    ///   undo # <- the undo command
    ///   ...
    /// }
    /// ```
    UndoRule(Loc),
    /// Quit command
    ///
    /// Example:
    /// ```noq
    /// quit
    /// ```
    Quit,
    /// Delete rule by name
    ///
    /// ```noq
    /// sum_comm :: A + B = B + A
    /// delete sum_comm # <- the delete command
    /// ```
    DeleteRule(Loc, String),
    /// Load file
    ///
    /// ```noq
    /// load "std/std.noq" # <- the load command
    ///
    /// (a - a) + b {
    ///   ...
    /// ```
    Load(Loc, String),
    /// Save file
    ///
    /// ```noq
    /// ...
    ///
    /// save "session.noq" # <- the save command
    /// ```
    Save(Loc, String)
}

impl Command {
    fn parse(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<Command, CommandSyntaxError> {
        let keyword_kind = lexer.peek_token().kind;
        match keyword_kind {
            TokenKind::Load => {
                lexer.next_token();
                let token = lexer.expect_token(TokenKind::Str).map_err(CommandSyntaxError::LoadArg)?;
                Ok(Self::Load(token.loc, token.text))
            },
            TokenKind::Save => {
                lexer.next_token();
                let token = lexer.expect_token(TokenKind::Str).map_err(CommandSyntaxError::SaveArg)?;
                Ok(Self::Save(token.loc, token.text))
            }
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
                let name = lexer.expect_token(TokenKind::Ident).map_err(CommandSyntaxError::DeleteArg)?.text;
                Ok(Command::DeleteRule(keyword.loc, name))
            }
            _ => {
                let expr = Expr::parse(lexer).map_err(CommandSyntaxError::CommandStart)?;

                match lexer.peek_token().kind {
                    TokenKind::Bar => {
                        let bar = lexer.next_token();
                        let (reversed, strategy_name_token) = {
                            let token = lexer.next_token();
                            if token.kind == TokenKind::Bang {
                                (true, lexer.expect_token(TokenKind::Ident).map_err(CommandSyntaxError::StrategyName)?)
                            } else if token.kind == TokenKind::Ident {
                                (false, token)
                            } else {
                                return Err(CommandSyntaxError::StrategyName(token))
                            }
                        };
                        if let Expr::Sym(rule_name) = expr {
                            Ok(Command::ApplyRule {
                                loc: bar.loc.clone(),
                                strategy_name: strategy_name_token.text,
                                applied_rule: AppliedRule::ByName {
                                    loc: bar.loc,
                                    name: rule_name,
                                    reversed,
                                },
                            })
                        } else {
                            todo!("Report applied rule must by symbol")
                        }
                    }
                    TokenKind::Equals => {
                        let head = expr;
                        let equals = lexer.next_token();
                        let body = Expr::parse(lexer).map_err(CommandSyntaxError::AnonymousRuleBody)?;
                        lexer.expect_token(TokenKind::Bar).map_err(CommandSyntaxError::AnonymousRuleWithoutStrategy)?;
                        let (reversed, strategy_name_token) = {
                            let token = lexer.next_token();
                            if token.kind == TokenKind::Bang {
                                (true, lexer.expect_token(TokenKind::Ident).map_err(CommandSyntaxError::StrategyName)?)
                            } else if token.kind == TokenKind::Ident {
                                (false, token)
                            } else {
                                return Err(CommandSyntaxError::StrategyName(token))
                            }
                        };
                        Ok(Command::ApplyRule {
                            loc: equals.loc.clone(),
                            strategy_name: strategy_name_token.text,
                            applied_rule: if reversed {
                                AppliedRule::Anonymous {
                                    loc: equals.loc,
                                    head: body,
                                    body: head,
                                }
                            } else {
                                AppliedRule::Anonymous {
                                    loc: equals.loc,
                                    head,
                                    body,
                                }
                            }
                        })
                    }
                    TokenKind::OpenCurly  => {
                        let keyword = lexer.next_token();
                        Ok(Command::StartShaping(keyword.loc, expr))
                    }
                    TokenKind::DoubleColon => {
                        let keyword = lexer.next_token();
                        match expr {
                            Expr::Sym(name) => {
                                let head = Expr::parse(lexer).map_err(CommandSyntaxError::DefineRuleHead)?;
                                match lexer.peek_token().kind {
                                    TokenKind::OpenCurly =>  {
                                        lexer.next_token();
                                        Ok(Command::DefineRuleViaShaping {
                                            name,
                                            expr: head
                                        })
                                    }
                                    TokenKind::Equals => {
                                        lexer.next_token();
                                        let body = Expr::parse(lexer).map_err(CommandSyntaxError::DefineRuleBody)?;
                                        Ok(Command::DefineRule(
                                            keyword.loc.clone(),
                                            name,
                                            Rule::User {
                                                loc: keyword.loc,
                                                head,
                                                body,
                                            }
                                        ))
                                    }
                                    _ => Err(CommandSyntaxError::DefineRuleSep(lexer.next_token()))
                                }
                            }
                            _ => todo!("Report that we expected a symbol")
                        }
                    }
                    _ => Err(CommandSyntaxError::CommandSep(lexer.next_token()))
                }
            }
        }
    }
}

struct ShapingFrame {
    expr: Expr,
    history: Vec<Expr>,
    rule_via_shaping: Option<(String, Expr)>,
}

impl ShapingFrame {
    fn new(expr: Expr) -> Self {
        Self {
            expr,
            history: Vec::new(),
            rule_via_shaping: None,
        }
    }

    fn new_rule_via_shaping(name: String, head: Expr) -> Self {
        Self {
            expr: head.clone(),
            history: Vec::new(),
            rule_via_shaping: Some((name, head))
        }
    }
}

struct Context {
    rules: HashMap<String, Rule>,
    shaping_stack: Vec<ShapingFrame>,
    history: Vec<Command>,
    quit: bool,
}

fn pad(sink: &mut impl Write, width: usize) -> io::Result<()> {
    write!(sink, "{:>width$}", "")
}

impl Context {
    fn new() -> Self {
        let mut rules = HashMap::new();
        // TODO: you can potentially `delete` the replace rule (you should not be able to do that)
        rules.insert("replace".to_string(), Rule::Replace);
        Self {
            rules,
            shaping_stack: Default::default(),
            quit: false,
            history: Default::default(),
        }
    }

    fn calculate_padding(&self) -> usize {
        self.rules.keys().map(|s| s.len()).max().unwrap_or(0) + 1
    }

    fn save_history(&self, file_path: &str) -> Result<(), io::Error> {
        let mut sink = fs::File::create(file_path)?;
        let mut indent = 0;
        for command in self.history.iter() {
            match command {
                Command::DefineRule(_, name, rule) => match rule {
                    Rule::User{head, body, ..} => {
                        pad(&mut sink, indent*2)?;
                        writeln!(sink, "{} :: {} = {}", name, head, body)?
                    },
                    Rule::Replace => unreachable!("There is no way for the user to create such rule"),
                }
                Command::DefineRuleViaShaping {name, expr} => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "{} :: {} {{", name, expr)?;
                    indent += 1
                }
                Command::StartShaping(_, expr) => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "{} {{", expr)?;
                    indent += 1
                }
                Command::ApplyRule {strategy_name, applied_rule, ..} => {
                    pad(&mut sink, indent*2)?;
                    match applied_rule {
                        AppliedRule::ByName{name, reversed, ..} => if *reversed {
                            writeln!(sink, "{} |! {}", name, strategy_name)?
                        } else {
                            writeln!(sink, "{} | {}", name, strategy_name)?
                        },
                        AppliedRule::Anonymous{head, body, ..} => {
                            writeln!(sink, "{} = {} | {}", head, body, strategy_name)?
                        },
                    }
                }
                Command::FinishShaping(_) => {
                    indent -= 1;
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "}}")?
                }
                Command::UndoRule(_) => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "undo")?
                }
                Command::Quit => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "quit")?
                }
                Command::DeleteRule(_, name) => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "delete {}", name)?
                }
                Command::Load(_, name) => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "load \"{}\"", name)?
                }
                Command::Save(_, name) => {
                    pad(&mut sink, indent*2)?;
                    writeln!(sink, "save \"{}\"", name)?
                }
            }
        }
        Ok(())
    }

    fn process_command(&mut self, command: Command) -> Result<(), Error> {
        match command.clone() {
            Command::Load(loc, file_path) => {
                let source = match fs::read_to_string(&file_path) {
                    Ok(source) => source,
                    Err(err) => return Err(RuntimeError::CouldNotLoadFile(loc, err).into())
                };
                let mut lexer = Lexer::new(source.chars(), Some(file_path));
                while lexer.peek_token().kind != TokenKind::End {
                    // TODO: the processed command during the file loading should not be put into the history
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
            Command::DefineRuleViaShaping{name, expr, ..} => {
                let width = self.calculate_padding();
                println!("apply {name:width$} => {}", &expr);
                self.shaping_stack.push(ShapingFrame::new_rule_via_shaping(name, expr))
            },
            Command::StartShaping(loc, expr) => {
                let width = self.calculate_padding();
                println!("apply {loc:width$} => {}", &expr);
                self.shaping_stack.push(ShapingFrame::new(expr))
            },
            Command::ApplyRule {loc, strategy_name, applied_rule} => {
                let width = self.calculate_padding();
                if let Some(frame) = self.shaping_stack.last_mut() {
                    let rule =  match applied_rule {
                        AppliedRule::ByName {loc, name, reversed} => match self.rules.get(&name) {
                            Some(rule) => if reversed {
                                print!("apply {name:width$}");
                                match rule.clone() {
                                    Rule::User {loc, head, body} => Rule::User{loc, head: body, body: head},
                                    Rule::Replace => return Err(RuntimeError::IrreversibleRule(loc).into())
                                }
                            } else {
                                print!("apply {name:width$}");
                                rule.clone()
                            }

                            None => return Err(RuntimeError::RuleDoesNotExist(name, loc).into())
                        }
                        AppliedRule::Anonymous {loc, head, body} => {
                            print!("apply {loc}");
                            Rule::User {loc, head, body}
                        },
                    };

                    let new_expr = match Strategy::by_name(&strategy_name) {
                        Some(strategy) => rule.apply(&frame.expr, &strategy, &loc)?,
                        None => return Err(RuntimeError::UnknownStrategy(strategy_name, loc).into())
                    };
                    println!(" => {}", &new_expr);
                    frame.history.push(new_expr.clone());
                    frame.expr = new_expr;
                } else {
                    return Err(RuntimeError::NoShapingInPlace(loc).into());
                }
            }
            Command::FinishShaping(loc) => {
                if let Some(mut frame) = self.shaping_stack.pop() {
                    let body = frame.expr;
                    if let Some((name, head)) = frame.rule_via_shaping.take() {
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
                } else {
                    return Err(RuntimeError::NoShapingInPlace(loc).into())
                }
            }
            Command::UndoRule(loc) => {
                if let Some(frame) = self.shaping_stack.last_mut() {
                    if let Some(previous_expr) = frame.history.pop() {
                        println!(" => {}", &previous_expr);
                        frame.expr = previous_expr;
                    } else {
                        return Err(RuntimeError::EndOfHistory(loc).into())
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
            Command::Save(loc, file_path) => {
                self.save_history(&file_path).map_err(|err| RuntimeError::CouldNotSaveFile(loc.clone(), err))?;
            }
        }
        self.history.push(command);
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
                Err(err) => {
                    eprint_repl_loc_cursor(prompt, err.loc());
                    eprintln!("ERROR: {}", err);
                },
                Ok(expr) => {
                    println!("  Display:  {}", expr);
                    println!("  Debug:    {:?}", expr);
                    println!("  Unparsed: {:?}", lexer.map(|t| (t.kind, t.text)).collect::<Vec<_>>());
                }
            }
        }
    }
}


fn repl_parse_and_process_command(context: &mut Context, lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<(), Error> {
    let command = Command::parse(lexer)?;
    lexer.expect_token(TokenKind::End).map_err(CommandSyntaxError::UnparsedInput)?;
    context.process_command(command)?;
    Ok(())
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
            eprintln!("{}: ERROR: {}", err.loc(), err);
            if let Error::Runtime(RuntimeError::RuleAlreadyExists(_, _, Some(prev_loc))) = err {
                if prev_loc.file_path.is_some() {
                    eprintln!("{}: previous declaration is located here", prev_loc)
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
    let mut shaping_prompt;
    let mut prompt: &str;

    while !context.quit {
        command.clear();
        if context.shaping_stack.is_empty() {
            prompt = default_prompt;
        } else {
            shaping_prompt = format!("{}> ", context.shaping_stack.len());
            prompt = &shaping_prompt;
        }
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();
        let mut lexer = Lexer::new(command.trim().chars(), None);
        if lexer.peek_token().kind != TokenKind::End {
            if let Err(err) = repl_parse_and_process_command(&mut context, &mut lexer) {
                eprint_repl_loc_cursor(prompt, err.loc());
                eprintln!("ERROR: {}", err);
                if let Error::Runtime(RuntimeError::RuleAlreadyExists(_, _, Some(prev_loc))) = err {
                    if prev_loc.file_path.is_some() {
                        eprintln!("{}: previous declaration is located here", prev_loc)
                    }
                }
            }
        } else if let Some(frame) = context.shaping_stack.last() {
            println!(" => {}", frame.expr);
        }
    }
}

enum ReplMode {
    Normal,
    DebugNew,
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
                            "new" => config.mode = ReplMode::DebugNew,
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

fn start_new_cool_repl() {
    enum MatchSyntaxError {
        Head(expr::SyntaxError),
        Separator(Token),
        Body(expr::SyntaxError),
    }

    fn parse_match(lexer: &mut Lexer<impl Iterator<Item=char>>) -> Result<(Expr, Expr), MatchSyntaxError> {
        let head = Expr::parse(lexer).map_err(MatchSyntaxError::Head)?;
        lexer.expect_token(TokenKind::Equals).map_err(MatchSyntaxError::Separator)?;
        let body = Expr::parse(lexer).map_err(MatchSyntaxError::Body)?;
        Ok((head, body))
    }

    // TODO: check if the stdin is tty
    // If it is not maybe switch to the old/simplified REPL
    let prompt = "new> ";
    let mut stdout = stdout().into_raw_mode().unwrap();
    let stdin = stdin();
    write!(stdout, "{}", prompt).unwrap();
    stdout.flush().unwrap();

    let mut new_cool_repl: NewCoolRepl = Default::default();

    for key in stdin.keys() {
        match key.unwrap() {
            Key::Char('\n') => {
                write!(stdout, "\r\n").unwrap();
                if &new_cool_repl.take() == "quit" {
                    break
                }
            }
            Key::Ctrl('a') | Key::Home => new_cool_repl.home(),
            Key::Ctrl('e') | Key::End => new_cool_repl.end(),
            Key::Ctrl('b') | Key::Left => new_cool_repl.left_char(),
            Key::Ctrl('f') | Key::Right => new_cool_repl.right_char(),
            Key::Ctrl('n') | Key::Down => new_cool_repl.down(),
            Key::Ctrl('p') | Key::Up => new_cool_repl.up(),
            Key::Ctrl('c') => {
                write!(stdout, "^C\r\n").unwrap();
                break;
            }
            Key::Alt('b') => new_cool_repl.left_word(),
            Key::Alt('f') => new_cool_repl.right_word(),
            Key::Char(key) => {
                new_cool_repl.insert_char(key);
                new_cool_repl.popup.clear();
                if let Ok((head, body)) = parse_match(&mut Lexer::new(new_cool_repl.buffer.iter().cloned(), None)) {
                    let subexprs = find_all_subexprs(&head, &body);
                    for subexpr in subexprs {
                        new_cool_repl.popup.push(format!("{}", HighlightedSubexpr{expr: &body, subexpr}));
                    }
                }
            },
            Key::Backspace => new_cool_repl.backspace(),
            _ => {},
        }
        new_cool_repl.render(prompt, &mut stdout).unwrap();
        stdout.flush().unwrap();
    }
}

fn main() {
    let config = Config::from_iter(&mut env::args());

    if let Some(file_path) = &config.file_path {
        interpret_file(file_path)
    } else {
        match config.mode {
            ReplMode::Normal => start_repl(),
            ReplMode::DebugNew => start_new_cool_repl(),
            ReplMode::DebugParser => start_parser_debugger(),
            ReplMode::DebugLexer => start_lexer_debugger(),
        }
    }
}

// TODO: `undo` command should remove previous command from the history
// TODO: Ability to restore saved session
// TODO: Custom arbitrary operators like in Haskell
