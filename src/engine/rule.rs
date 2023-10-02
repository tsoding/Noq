use super::lexer::*;
use super::expr::*;
use super::diagnostics::*;

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
pub enum Rule {
    User {
        loc: Loc,
        head: Expr,
        body: Expr,
    },
    Replace,
}

pub enum Strategy {
    All,
    Deep,
    Nth(usize),
}

impl Strategy {
    pub fn by_name(name: &str) -> Option<Self> {
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
    pub fn apply(&self, expr: &mut Expr, strategy: &Strategy, apply_command_loc: &Loc, diag: &mut impl Diagnoster) -> Option<()> {
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
