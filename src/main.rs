use std::collections::HashMap;
use std::io::{stdin, stdout};
use std::io::Write;
use std::env;
use std::fs;
use std::io;

use termion::raw::IntoRawMode;
use termion::input::TermRead;
use termion::event::Key;

#[macro_use]
mod lexer;
mod repl;
#[macro_use]
mod expr;
mod diagnostics;

use lexer::*;
use repl::*;
use expr::*;
use diagnostics::*;

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
    fn apply(&self, expr: &mut Expr, strategy: &Strategy, apply_command_loc: &Loc, diag: &mut impl Diagnoster) -> Option<()> {
        fn apply_to_subexprs(rule: &Rule, expr: &mut Expr, strategy: &Strategy, apply_command_loc: &Loc, match_count: &mut usize, diag: &mut impl Diagnoster) -> Option<bool> {
            match expr {
                Expr::Sym(_) | Expr::Var(_) => Some(false),
                Expr::Op(_, lhs, rhs) => {
                    if apply_impl(rule, lhs, strategy, apply_command_loc, match_count, diag)? {
                        return Some(true)
                    }
                    apply_impl(rule, rhs, strategy, apply_command_loc, match_count, diag)
                }
                Expr::Fun(head, args) => {
                    if apply_impl(rule, head, strategy, apply_command_loc, match_count, diag)? {
                        return Some(true);
                    }
                    for arg in args.iter_mut() {
                        if apply_impl(rule, arg, strategy, apply_command_loc, match_count, diag)? {
                            return Some(true)
                        }
                    }
                    Some(false)
                }
            }
        }

        fn apply_impl(rule: &Rule, expr: &mut Expr, strategy: &Strategy, apply_command_loc: &Loc, match_count: &mut usize, diag: &mut impl Diagnoster) -> Option<bool> {
            match rule {
                Rule::User{loc: _, head, body} => {
                    if let Some(bindings) = head.pattern_match(expr) {
                        let resolution = strategy.matched(*match_count);
                        *match_count += 1;
                        match resolution.action {
                            Action::Apply => {
                                *expr = body.clone();
                                expr.substitute(&bindings)
                            },
                            Action::Skip => {},
                        };
                        match resolution.state {
                            State::Bail => Some(false),
                            State::Cont => apply_to_subexprs(rule, expr, strategy, apply_command_loc, match_count, diag),
                            State::Halt => Some(true),
                        }
                    } else {
                        apply_to_subexprs(rule, expr, strategy, apply_command_loc, match_count, diag)
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
                            *expr = bindings.get("Expr").expect("Variable `Expr` is present in the meta pattern").clone();
                            match Strategy::by_name(meta_strategy_name) {
                                Some(strategy) => {
                                    meta_rule.apply(expr, &strategy, apply_command_loc, diag)?;
                                    Some(false)
                                }
                                None => {
                                    diag.report(&apply_command_loc, Severity::Error, &format!("unknown rule application strategy '{}'", meta_strategy_name));
                                    None
                                }
                            }
                        } else {
                            diag.report(&apply_command_loc, Severity::Error, &format!("strategy must be a symbol but got {} {}", meta_strategy.human_name(), &meta_strategy));
                            None
                        }
                    } else {
                        apply_to_subexprs(rule, expr, strategy, apply_command_loc, match_count, diag)
                    }
                },
            }
        }

        let mut match_count = 0;
        apply_impl(self, expr, strategy, apply_command_loc, &mut match_count, diag)?;
        if match_count == 0 {
            // TODO: provide more info on "no match found" error
            diag.report(&apply_command_loc, Severity::Error, &format!("no match found"));
            return None
        }
        Some(())
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
    fn parse(lexer: &mut Lexer, diag: &mut impl Diagnoster) -> Option<Command> {
        let keyword_kind = lexer.peek_token().kind;
        let keyword_loc = lexer.peek_token().loc.clone();
        match keyword_kind {
            TokenKind::Load => {
                lexer.next_token();
                let token = lexer.expect_token(TokenKind::Str).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`load` command expects {expected_kind} as the file path, but got {actual_token} instead"));
                }).ok()?;
                Some(Self::Load(token.loc, token.text))
            },
            TokenKind::Save => {
                lexer.next_token();
                let token = lexer.expect_token(TokenKind::Str).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`save` command expects {expected_kind} as the file path, but got {actual_token} instead"));
                }).ok()?;
                Some(Self::Save(token.loc, token.text))
            }
            TokenKind::CloseCurly => {
                let keyword = lexer.next_token();
                Some(Command::FinishShaping(keyword.loc))
            }
            TokenKind::Undo => {
                let keyword = lexer.next_token();
                Some(Command::UndoRule(keyword.loc))
            }
            TokenKind::Quit => {
                lexer.next_token();
                Some(Command::Quit)
            }
            TokenKind::Delete => {
                let keyword = lexer.next_token();
                let name = lexer.expect_token(TokenKind::Ident).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`delete` command expects {expected_kind} as an argument but got {actual_token} instead"));
                }).ok()?.text;
                Some(Command::DeleteRule(keyword.loc, name))
            }
            _ => {
                let expr = Expr::parse(lexer, diag)?;

                fn report_unexpected_token_for_strategy_name(diag: &mut impl Diagnoster, expected_kind: &TokenKind, actual_token: &Token) {
                    diag.report(&actual_token.loc, Severity::Error, &format!("applied strategy name must be {expected_kind}, but we got {actual_token} instead"));
                }

                match lexer.peek_token().kind {
                    TokenKind::Bar => {
                        let bar = lexer.next_token();
                        let (reversed, strategy_name_token) = {
                            let token = lexer.next_token();
                            if token.kind == TokenKind::Bang {
                                (true, lexer.expect_token(TokenKind::Ident).map_err(|(expected_kind, actual_token)| report_unexpected_token_for_strategy_name(diag, &expected_kind, &actual_token)).ok()?)
                            } else if token.kind == TokenKind::Ident {
                                (false, token)
                            } else {
                                report_unexpected_token_for_strategy_name(diag, &TokenKind::Ident, &token);
                                return None;
                            }
                        };
                        if let Expr::Sym(rule_name) = expr {
                            Some(Command::ApplyRule {
                                loc: bar.loc.clone(),
                                strategy_name: strategy_name_token.text,
                                applied_rule: AppliedRule::ByName {
                                    loc: bar.loc,
                                    name: rule_name,
                                    reversed,
                                },
                            })
                        } else {
                            diag.report(&keyword_loc, Severity::Error, &format!("Applied rule must be a symbol but got {} instead", expr.human_name()));
                            return None
                        }
                    }
                    TokenKind::Equals => {
                        let head = expr;
                        let equals = lexer.next_token();
                        let body = Expr::parse(lexer, diag)?;
                        lexer.expect_token(TokenKind::Bar).map_err(|(expected_kind, actual_token)| {
                            diag.report(&actual_token.loc, Severity::Error, &format!("Expected {expected_kind} since you defined an annonymous rule `{head} = {body}`, which must be applied in-place. But instead of {expected_kind} we got {actual_token}"))
                        }).ok()?;
                        let (reversed, strategy_name_token) = {
                            let token = lexer.next_token();
                            if token.kind == TokenKind::Bang {
                                (true, lexer.expect_token(TokenKind::Ident).map_err(|(expected_kind, actual_token)| report_unexpected_token_for_strategy_name(diag, &expected_kind, &actual_token)).ok()?)
                            } else if token.kind == TokenKind::Ident {
                                (false, token)
                            } else {
                                report_unexpected_token_for_strategy_name(diag, &TokenKind::Ident, &token);
                                return None
                            }
                        };
                        Some(Command::ApplyRule {
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
                        Some(Command::StartShaping(keyword.loc, expr))
                    }
                    TokenKind::DoubleColon => {
                        let keyword = lexer.next_token();
                        match expr {
                            Expr::Sym(name) => {
                                let head = Expr::parse(lexer, diag)?;
                                match lexer.peek_token().kind {
                                    TokenKind::OpenCurly =>  {
                                        lexer.next_token();
                                        Some(Command::DefineRuleViaShaping {
                                            name,
                                            expr: head
                                        })
                                    }
                                    TokenKind::Equals => {
                                        lexer.next_token();
                                        let body = Expr::parse(lexer, diag)?;
                                        Some(Command::DefineRule(
                                            keyword.loc.clone(),
                                            name,
                                            Rule::User {
                                                loc: keyword.loc,
                                                head,
                                                body,
                                            }
                                        ))
                                    }
                                    _ => {
                                        let token = lexer.next_token();
                                        diag.report(&token.loc, Severity::Error, &format!("unexpected Rule Definition Separator {}", token));
                                        None
                                    }
                                }
                            }
                            _ => {
                                diag.report(&keyword.loc, Severity::Error, &format!("expected symbol"));
                                None
                            }
                        }
                    }
                    _ => {
                        let token = lexer.next_token();
                        diag.report(&token.loc, Severity::Error, "It's unclear what you want in here");
                        diag.report(&token.loc, Severity::Info, &format!("{expr} {{                     - to start shaping {expr}"));
                        diag.report(&token.loc, Severity::Info, &format!("{expr} | <strategy>          - to apply rule {expr} to the currently shaping expression"));
                        diag.report(&token.loc, Severity::Info, &format!("{expr} = <body> | <strategy> - to use {expr} as a head of an anonymous rule to apply to the currently shaping expression"));
                        diag.report(&token.loc, Severity::Info, &format!("{expr} :: <head> = <body>    - to define new rule with the name {expr}"));
                        None
                    }
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
    interactive: bool,
    rules: HashMap<String, Rule>,
    shaping_stack: Vec<ShapingFrame>,
    history: Vec<Command>,
    quit: bool,
}

fn pad(sink: &mut impl Write, width: usize) -> io::Result<()> {
    write!(sink, "{:>width$}", "")
}

impl Context {
    fn new(interactive: bool) -> Self {
        let mut rules = HashMap::new();
        // TODO: you can potentially `delete` the replace rule (you should not be able to do that)
        rules.insert("replace".to_string(), Rule::Replace);
        Self {
            interactive,
            rules,
            shaping_stack: Default::default(),
            quit: false,
            history: Default::default(),
        }
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

    fn process_file(&mut self, loc: Loc, file_path: String, diag: &mut impl Diagnoster) -> Option<()> {
        let source = match fs::read_to_string(&file_path) {
            Ok(source) => source,
            Err(err) => {
                diag.report(&loc, Severity::Error, &format!("could not load file {}: {}", file_path, err));
                return None
            }
        };
        let mut lexer = Lexer::new(source.chars().collect(), Some(file_path));
        while lexer.peek_token().kind != TokenKind::End {
            self.process_command(Command::parse(&mut lexer, diag)?, diag)?
        }
        Some(())
    }

    fn process_command(&mut self, command: Command, diag: &mut impl Diagnoster) -> Option<()> {
        match command.clone() {
            Command::Load(loc, file_path) => {
                let saved_interactive = self.interactive;
                self.interactive = false;
                self.process_file(loc, file_path, diag)?;
                self.interactive = saved_interactive;
            }
            Command::DefineRule(rule_loc, rule_name, rule) => {
                if let Some(existing_rule) = self.rules.get(&rule_name) {
                    let loc = match existing_rule {
                        Rule::User{loc, ..} => Some(loc),
                        Rule::Replace => None,
                    };
                    diag.report(&rule_loc, Severity::Error, &format!("redefinition of existing rule {}", rule_name));
                    if let Some(loc) = loc {
                        diag.report(&loc, Severity::Info, &format!("the original definition is located here"));
                    }
                    return None
                }
                diag.report(&rule_loc, Severity::Info, &format!("defined rule `{}`", &rule_name));
                self.rules.insert(rule_name, rule);
            }
            Command::DefineRuleViaShaping{name, expr, ..} => {
                println!(" => {}", &expr);
                self.shaping_stack.push(ShapingFrame::new_rule_via_shaping(name, expr))
            },
            Command::StartShaping(_loc, expr) => {
                println!(" => {}", &expr);
                self.shaping_stack.push(ShapingFrame::new(expr))
            },
            Command::ApplyRule {loc, strategy_name, applied_rule} => {
                if let Some(frame) = self.shaping_stack.last_mut() {
                    let rule =  match applied_rule {
                        AppliedRule::ByName {loc, name, reversed} => match self.rules.get(&name) {
                            Some(rule) => if reversed {
                                match rule.clone() {
                                    Rule::User {loc, head, body} => Rule::User{loc, head: body, body: head},
                                    Rule::Replace => {
                                        diag.report(&loc, Severity::Error, &format!("irreversible rule"));
                                        return None;
                                    }
                                }
                            } else {
                                rule.clone()
                            }

                            None => {
                                diag.report(&loc, Severity::Error, &format!("rule {} does not exist", name));
                                return None;
                            }
                        }
                        AppliedRule::Anonymous {loc, head, body} => Rule::User {loc, head, body},
                    };

                    match Strategy::by_name(&strategy_name) {
                        Some(strategy) => rule.apply(&mut frame.expr, &strategy, &loc, diag)?,
                        None => {
                            diag.report(&loc, Severity::Error, &format!("unknown rule application strategy '{}'", strategy_name));
                            return None
                        }
                    };
                    println!(" => {}", &frame.expr);
                    if self.interactive {
                        frame.history.push(frame.expr.clone());
                    }
                } else {
                    diag.report(&loc, Severity::Error, &format!("To apply a rule to an expression you need to first start shaping the expression, but no shaping is currently in place"));
                    diag.report(&loc, Severity::Info, &format!("<expression> {{    - to start shaping"));
                    return None
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
                            diag.report(&loc, Severity::Error, &format!("redefinition of existing rule {}", name));
                            if let Some(old_loc) = old_loc {
                                diag.report(&old_loc, Severity::Info, &format!("the original definition is located here"));
                            }
                        }
                        println!("defined rule `{}`", &name);
                        self.rules.insert(name, Rule::User {loc, head, body});
                    }
                } else {
                    diag.report(&loc, Severity::Error, "no shaping in place");
                    return None
                }
            }
            Command::UndoRule(loc) => {
                if let Some(frame) = self.shaping_stack.last_mut() {
                    if let Some(previous_expr) = frame.history.pop() {
                        println!(" => {}", &previous_expr);
                        frame.expr = previous_expr;
                    } else {
                        diag.report(&loc, Severity::Error, "end of history");
                        return None;
                    }
                } else {
                    diag.report(&loc, Severity::Error, "no shaping in place");
                    return None;
                }
            }
            Command::Quit => {
                self.quit = true;
            }
            Command::DeleteRule(loc, name) => {
                if self.rules.contains_key(&name) {
                    self.rules.remove(&name);
                } else {
                    diag.report(&loc, Severity::Error, &format!("rule {} does not exist", name));
                    return None
                }
            }
            Command::Save(loc, file_path) => {
                if let Err(err) = self.save_history(&file_path) {
                    diag.report(&loc, Severity::Error, &format!("could not save file {}: {}", file_path, err));
                    return None
                }
            }
        }
        if self.interactive {
            self.history.push(command);
        }
        Some(())
    }
}

fn start_lexer_debugger() {
    let prompt = "lexer> ";
    let mut command = String::new();
    loop {
        command.clear();
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();
        println!("Tokens: {:?}", Lexer::new(command.trim().chars().collect(), None).map(|t| (t.kind, t.text)).collect::<Vec<_>>());
    }
}

fn start_parser_debugger() {
    let prompt = "parser> ";
    let mut command = String::new();
    let mut diag = StdoutDiagnoster{};
    loop {
        command.clear();
        print!("{}", prompt);
        stdout().flush().unwrap();
        stdin().read_line(&mut command).unwrap();

        let mut lexer = Lexer::new(command.trim().chars().collect(), None);
        if lexer.peek_token().kind != TokenKind::End {
            if let Some(expr) = Expr::parse(&mut lexer, &mut diag) {
                println!("  Display:  {}", expr);
                println!("  Debug:    {:?}", expr);
                println!("  Unparsed: {:?}", lexer.map(|t| (t.kind, t.text)).collect::<Vec<_>>());
            }
        }
    }
}


fn repl_parse_and_process_command(context: &mut Context, lexer: &mut Lexer, diag: &mut impl Diagnoster) -> Option<()> {
    let command = Command::parse(lexer, diag)?;
    let token = lexer.peek_token();
    if token.kind != TokenKind::End {
        diag.report(&token.loc, Severity::Error, &format!("unexpected token {} after the End of the Command", token));
        return None;
    }
    context.process_command(command, diag)?;
    Some(())
}

fn parse_and_process_command(context: &mut Context, lexer: &mut Lexer, diag: &mut impl Diagnoster) -> Option<()> {
    let command = Command::parse(lexer, diag)?;
    context.process_command(command, diag)?;
    Some(())
}

fn interpret_file(file_path: &str) -> Option<()> {
    let mut context = Context::new(false);
    let source = fs::read_to_string(&file_path).unwrap();
    let mut lexer = Lexer::new(source.chars().collect(), Some(file_path.to_string()));
    let mut diag = StdoutDiagnoster{};
    while !context.quit && lexer.peek_token().kind != TokenKind::End {
        parse_and_process_command(&mut context, &mut lexer, &mut diag)?
    }
    Some(())
}

fn start_repl() {
    let mut diag = StdoutDiagnoster{};
    let mut context = Context::new(true);
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
        let mut lexer = Lexer::new(command.trim().chars().collect(), None);
        if lexer.peek_token().kind != TokenKind::End {
            // TODO: pointing the place of error with arrow is broken
            repl_parse_and_process_command(&mut context, &mut lexer, &mut diag);
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
    fn parse_match(lexer: &mut Lexer, diag: &mut impl Diagnoster) -> Option<(Expr, Expr)> {
        let head = Expr::parse(lexer, diag)?;
        lexer.expect_token(TokenKind::Equals).map_err(|(expected_kind, actual_token)| {
            diag.report(&actual_token.loc, Severity::Error, &format!("Expected {expected_kind} as the separator between the head and the body of the rule but got {actual_token} instead."));
        }).ok()?;
        let body = Expr::parse(lexer, diag)?;
        Some((head, body))
    }

    // TODO: check if the stdin is tty
    // If it is not maybe switch to the old/simplified REPL
    let prompt = "new> ";
    let mut stdout = stdout().into_raw_mode().unwrap();
    let stdin = stdin();
    write!(stdout, "{}", prompt).unwrap();
    stdout.flush().unwrap();

    let mut new_cool_repl: NewCoolRepl = Default::default();
    let mut diag = StdoutDiagnoster{};

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
                if let Some((head, body)) = parse_match(&mut Lexer::new(new_cool_repl.buffer.clone(), None), &mut diag) {
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
        interpret_file(file_path);
    } else {
        match config.mode {
            ReplMode::Normal => start_repl(),
            // TODO: new repl does not support Windows
            ReplMode::DebugNew => start_new_cool_repl(),
            ReplMode::DebugParser => start_parser_debugger(),
            ReplMode::DebugLexer => start_lexer_debugger(),
        }
    }
}

// TODO: `undo` command should remove previous command from the history
// TODO: Ability to restore saved session
// TODO: Custom arbitrary operators like in Haskell
// TODO: Ask if "you really want to exit" on ^C when the history is not empty
// Because you may want to `save` your history.
