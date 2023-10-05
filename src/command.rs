//! Imperative Command Language implemented on top of the Core
//! Expression-based language with Pattern Matching and Rule
//! Substitution. (see [engine](super::engine) module)

use std::io::Write;
use std::fs;
use std::io;

use super::engine::diagnostics::*;
use super::engine::lexer::*;
use super::engine::expr::*;
use super::engine::rule::*;

#[derive(Clone)]
pub enum AppliedRule {
    ByName {
        name: Token,
        reversed: bool,
    },
    Anonymous {
        loc: Loc,
        head: Expr,
        body: Expr,
    },
}

#[derive(Clone)]
pub enum Command {
    /// Define rule
    ///
    /// Example:
    /// ```noq
    /// sum_comm :: A + B = B + A
    /// ```
    DefineRule { name: Token, rule: Rule },
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
    Save(Loc, String),
    /// List all the defined rules
    List,
    /// Show the full definition of the rule including its history
    Show { name: Token },
    /// Show the history of the current shaping
    History { keyword: Token },
}

impl Command {
    pub fn parse(lexer: &mut Lexer, diag: &mut impl Diagnoster) -> Option<Command> {
        let keyword_kind = lexer.peek_token().kind;
        let keyword_loc = lexer.peek_token().loc.clone();
        match keyword_kind {
            TokenKind::Load => {
                lexer.next_token();
                let token = lexer.expect_token(TokenKind::Str).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`load` command expects {expected_kind} as the file path, but got {actual_token} instead", actual_token = actual_token.report()));
                }).ok()?;
                Some(Self::Load(token.loc, token.text))
            },
            TokenKind::Save => {
                lexer.next_token();
                let token = lexer.expect_token(TokenKind::Str).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`save` command expects {expected_kind} as the file path, but got {actual_token} instead", actual_token = actual_token.report()));
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
            TokenKind::List => {
                lexer.next_token();
                Some(Command::List)
            }
            TokenKind::History => {
                let keyword = lexer.next_token();
                Some(Command::History{keyword})
            }
            TokenKind::Show => {
                lexer.next_token();
                let name = lexer.expect_token(TokenKind::Ident).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`show` command expects {expected_kind} as the rule name, but got {actual_token} instead", actual_token = actual_token.report()));
                }).ok()?;
                Some(Command::Show{name})
            }
            TokenKind::Delete => {
                let keyword = lexer.next_token();
                let name = lexer.expect_token(TokenKind::Ident).map_err(|(expected_kind, actual_token)| {
                    diag.report(&actual_token.loc, Severity::Error, &format!("`delete` command expects {expected_kind} as an argument but got {actual_token} instead", actual_token = actual_token.report()));
                }).ok()?.text;
                Some(Command::DeleteRule(keyword.loc, name))
            }
            _ => {
                let expr = Expr::parse(lexer, diag)?;

                fn report_unexpected_token_for_strategy_name(diag: &mut impl Diagnoster, expected_kind: &TokenKind, actual_token: &Token) {
                    diag.report(&actual_token.loc, Severity::Error, &format!("applied strategy name must be {expected_kind}, but we got {actual_token} instead", actual_token = actual_token.report()));
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
                        if let Expr::Sym(name) = expr {
                            Some(Command::ApplyRule {
                                loc: bar.loc.clone(),
                                strategy_name: strategy_name_token.text,
                                applied_rule: AppliedRule::ByName { name, reversed },
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
                            diag.report(&actual_token.loc, Severity::Error, &format!("Expected {expected_kind} since you defined an annonymous rule `{head} = {body}`, which must be applied in-place. But instead of {expected_kind} we got {actual_token}", actual_token = actual_token.report()))
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
                                            name: name.text,
                                            expr: head
                                        })
                                    }
                                    TokenKind::Equals => {
                                        lexer.next_token();
                                        let body = Expr::parse(lexer, diag)?;
                                        Some(Command::DefineRule {
                                            name,
                                            rule: Rule::User {
                                                loc: keyword.loc,
                                                head,
                                                body,
                                            }
                                        })
                                    }
                                    _ => {
                                        let token = lexer.next_token();
                                        diag.report(&token.loc, Severity::Error, &format!("unexpected Rule Definition Separator {}", token.report()));
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

pub struct ShapingFrame {
    pub expr: Expr,
    history: Vec<(Expr, Command)>,
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

pub struct Context {
    interactive: bool,
    // NOTE: We don't use HashMap in here to preserve the order of the definition of the `list` command.
    // The order of the definition is very important for UX in REPL.
    // TODO: Do something about the performance when it actually starts to matter.
    // I don't think we work with too many definitions right now.
    rules: Vec<(String, (Rule, Vec<(Expr, Command)>))>,
    pub shaping_stack: Vec<ShapingFrame>,
    pub quit: bool,
}

fn get_item_by_key<'a, K, V>(assoc: &'a [(K, V)], needle: &'a K) -> Option<&'a V> where K: PartialEq<K> {
    for (key, value) in assoc.iter() {
        if key == needle {
            return Some(value)
        }
    }
    None
}

fn delete_item_by_key<'a, K, V>(assoc: &'a mut Vec<(K, V)>, needle: &'a K) -> bool where K: PartialEq<K> {
    for i in 0..assoc.len() {
        if &assoc[i].0 == needle {
            assoc.remove(i);
            return true
        }
    }
    false
}

impl Context {
    pub fn new(interactive: bool) -> Self {
        let mut rules = Vec::new();
        // TODO: you can potentially `delete` the replace rule (you should not be able to do that)
        rules.push(("replace".to_string(), (Rule::Replace, vec![])));
        Self {
            interactive,
            rules,
            shaping_stack: Default::default(),
            quit: false,
        }
    }

    fn save_history(&self, file_path: &str) -> Result<(), io::Error> {
        let mut sink = fs::File::create(file_path)?;
        for (name, (rule, history)) in self.rules.iter() {
            match rule {
                Rule::User{head, body, ..} => {
                    write!(sink, "{name} :: {head}")?;
                    if history.len() > 0 {
                        writeln!(sink, " {{")?;
                        for (_, command) in history {
                            match command {
                                Command::ApplyRule{strategy_name, applied_rule, ..} => {
                                    match applied_rule {
                                        AppliedRule::ByName { name, reversed } => {
                                            write!(sink, "    {name} |", name = name.text)?;
                                            if *reversed {
                                                write!(sink, "!")?;
                                            }
                                            writeln!(sink, " {strategy_name}")?;
                                        }
                                        AppliedRule::Anonymous{head, body, ..} => {
                                            writeln!(sink, "    {head} = {body} | {strategy_name}")?;
                                        }
                                    }
                                }
                                _ => unreachable!()
                            }
                        }
                        writeln!(sink, "}}")?;
                    } else {
                        writeln!(sink, " = {body}")?;
                    }
                }
                Rule::Replace => {}
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

    pub fn process_command(&mut self, command: Command, diag: &mut impl Diagnoster) -> Option<()> {
        match command.clone() {
            Command::Load(loc, file_path) => {
                let saved_interactive = self.interactive;
                self.interactive = false;
                self.process_file(loc, file_path, diag)?;
                self.interactive = saved_interactive;
            }
            Command::DefineRule{ name, rule } => {
                if let Some((existing_rule, _)) = get_item_by_key(&self.rules, &name.text) {
                    let loc = match existing_rule {
                        Rule::User{loc, ..} => Some(loc),
                        Rule::Replace => None,
                    };
                    diag.report(&name.loc, Severity::Error, &format!("redefinition of existing rule {}", name.text));
                    if let Some(loc) = loc {
                        diag.report(&loc, Severity::Info, &format!("the original definition is located here"));
                    }
                    return None
                }
                diag.report(&name.loc, Severity::Info, &format!("defined rule `{}`", &name.text));
                self.rules.push((name.text, (rule, vec![])));
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
                    let rule = match applied_rule {
                        AppliedRule::ByName { name, reversed } => match get_item_by_key(&self.rules, &name.text) {
                            Some((rule, _)) => if reversed {
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
                                diag.report(&loc, Severity::Error, &format!("rule {} does not exist", name.text));
                                return None;
                            }
                        }
                        AppliedRule::Anonymous {loc, head, body} => Rule::User {loc, head, body},
                    };

                    let previous_expr = frame.expr.clone();
                    match Strategy::by_name(&strategy_name) {
                        Some(strategy) => rule.apply(&mut frame.expr, &strategy, &loc, diag)?,
                        None => {
                            diag.report(&loc, Severity::Error, &format!("unknown rule application strategy '{}'", strategy_name));
                            return None
                        }
                    };
                    println!(" => {}", &frame.expr);
                    frame.history.push((previous_expr, command));
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
                        if let Some((existing_rule, _)) = get_item_by_key(&self.rules, &name) {
                            let old_loc = match existing_rule {
                                Rule::User{loc, ..} => Some(loc.clone()),
                                Rule::Replace => None,
                            };
                            diag.report(&loc, Severity::Error, &format!("redefinition of existing rule {}", name));
                            if let Some(old_loc) = old_loc {
                                diag.report(&old_loc, Severity::Info, &format!("the original definition is located here"));
                            }
                            return None
                        }
                        diag.report(&loc, Severity::Info, &format!("defined rule `{}`", &name));
                        self.rules.push((name, (Rule::User {loc, head, body}, frame.history)));
                    }
                } else {
                    diag.report(&loc, Severity::Error, "no shaping in place");
                    return None
                }
            }
            Command::UndoRule(loc) => {
                if let Some(frame) = self.shaping_stack.last_mut() {
                    if let Some((previous_expr, _)) = frame.history.pop() {
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
            Command::List => {
                for (name, rule) in self.rules.iter() {
                    if let (Rule::User{loc: _, head, body}, _) = rule {
                        println!("{name} :: {head} = {body}")
                    }
                }
            }
            Command::History{keyword} => {
                if let Some(frame) = self.shaping_stack.last() {
                    for (_, command) in frame.history.iter() {
                        match command {
                            Command::ApplyRule{strategy_name, applied_rule, ..} => {
                                match applied_rule {
                                    AppliedRule::ByName { name, reversed } => {
                                        print!("    {name} |", name = name.text);
                                        if *reversed {
                                            print!("!");
                                        }
                                        println!(" {strategy_name}");
                                    }
                                    AppliedRule::Anonymous{head, body, ..} => {
                                        println!("    {head} = {body} | {strategy_name}");
                                    }
                                }
                            }
                            _ => unreachable!()
                        }
                    }
                } else {
                    diag.report(&keyword.loc, Severity::Error, "no shaping in place");
                    return None;
                }
            }
            Command::Show{name} => {
                match get_item_by_key(&self.rules, &name.text) {
                    Some((Rule::User{head, body, ..}, history)) => {
                        print!("{name} :: {head}", name = name.text);
                        if history.len() > 0 {
                            println!(" {{");
                            for (_, command) in history {
                                match command {
                                    Command::ApplyRule{strategy_name, applied_rule, ..} => {
                                        match applied_rule {
                                            AppliedRule::ByName { name, reversed } => {
                                                print!("    {name} |", name = name.text);
                                                if *reversed {
                                                    print!("!");
                                                }
                                                println!(" {strategy_name}");
                                            }
                                            AppliedRule::Anonymous{head, body, ..} => {
                                                println!("    {head} = {body} | {strategy_name}");
                                            }
                                        }
                                    }
                                    _ => unreachable!()
                                }
                            }
                            println!("}}");
                        } else {
                            println!(" = {body}");
                        }
                    }
                    Some((Rule::Replace, _)) => {
                        println!("`replace` is a built-in rule");
                    }
                    None => {
                        diag.report(&name.loc, Severity::Error, &format!("rule `{}` does not exist", name.text));
                        return None
                    }
                }
            }
            Command::DeleteRule(loc, name) => {
                if delete_item_by_key(&mut self.rules, &name) {
                    diag.report(&loc, Severity::Info, &format!("rule `{}` has been removed", name));
                } else {
                    diag.report(&loc, Severity::Error, &format!("rule `{}` does not exist", name));
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
        Some(())
    }
}

// TODO: `undo` command should remove previous command from the history
// TODO: Ability to restore saved session
