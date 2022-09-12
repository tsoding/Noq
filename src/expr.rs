use std::fmt;
use std::collections::HashMap;

use super::lexer::*;

#[derive(Debug)]
pub enum SyntaxError {
    FunArgsStart(Token),
    FunArgsEnd(Token),
    PrimaryStart(Token),
    PrimaryEnd(Token),
}

impl SyntaxError {
    pub fn loc(&self) -> &Loc {
        match self {
            Self::FunArgsStart(token) |
            Self::FunArgsEnd(token) |
            Self::PrimaryStart(token) |
            Self::PrimaryEnd(token) => &token.loc
        }
    }
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::FunArgsStart(token) => write!(f, "expected the Start of a Functor Arguments List {}, but got {}", TokenKind::OpenParen, token),
            Self::FunArgsEnd(token) => write!(f, "expected the End of a Functor Arguments List {}, but got {}", TokenKind::CloseParen, token),
            Self::PrimaryStart(token) => write!(f, "expected the Start of a Primary Expression which is {} or {}, but got {}", TokenKind::OpenParen, TokenKind::Ident, token),
            Self::PrimaryEnd(token) => write!(f, "expected the Start of a Primary Expression which is `)`, but got {} instead", token),
        }
    }
}

// TODO: unary minus
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Mod,
    // TODO: use `=` instead of `==`, but for the current use of `=` use something else (for instance `=>`)
    Eql,
}

impl Op {
    fn from_token_kind(kind: TokenKind) -> Option<Self> {
        match kind {
            TokenKind::Plus => Some(Op::Add),
            TokenKind::Dash => Some(Op::Sub),
            TokenKind::Asterisk => Some(Op::Mul),
            TokenKind::Slash => Some(Op::Div),
            TokenKind::Caret => Some(Op::Pow),
            TokenKind::Percent => Some(Op::Mod),
            TokenKind::EqualsEquals => Some(Op::Eql),
            _ => None
        }
    }

    pub fn precedence(&self) -> usize {
        use Op::*;
        match self {
            Eql             => 0,
            Add | Sub       => 1,
            Mul | Div | Mod => 2,
            Pow             => 3,
        }
    }

    const MAX_PRECEDENCE: usize = 3;
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Eql => write!(f, "=="),
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
pub enum Expr {
    Sym(String),
    Var(String),
    Fun(Box<Expr>, Vec<Expr>),
    Op(Op, Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn substitute(&mut self, bindings: &HashMap<String, Expr>) {
        match self {
            Self::Sym(_) => {},

            Self::Var(name) => if let Some(value) = bindings.get(name) {
                *self = value.clone()
            }

            Self::Op(_, lhs, rhs) => {
                lhs.substitute(bindings);
                rhs.substitute(bindings);
            },

            Self::Fun(head, args) => {
                head.substitute(bindings);
                for arg in args {
                    arg.substitute(bindings)
                }
            }
        }
    }

    pub fn parse_ident(name: &str) -> Self {
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

    fn parse_fun_args(lexer: &mut Lexer) -> Result<Vec<Self>, SyntaxError> {
        use TokenKind::*;
        let mut args = Vec::new();
        lexer.expect_token(OpenParen).map_err(SyntaxError::FunArgsStart)?;
        if lexer.peek_token().kind == CloseParen {
            lexer.next_token();
            return Ok(args)
        }
        args.push(Self::parse(lexer)?);
        while lexer.peek_token().kind == Comma {
            lexer.next_token();
            args.push(Self::parse(lexer)?);
        }
        lexer.expect_token(CloseParen).map_err(SyntaxError::FunArgsEnd)?;
        Ok(args)
    }

    fn parse_primary(lexer: &mut Lexer) -> Result<Self, SyntaxError> {
        let mut head = {
            let token = lexer.next_token();
            match token.kind {
                TokenKind::OpenParen => {
                    let result = Self::parse(lexer)?;
                    lexer.expect_token(TokenKind::CloseParen).map_err(SyntaxError::PrimaryEnd)?;
                    result
                }

                TokenKind::Ident => {
                    Self::parse_ident(&token.text)
                },

                _ => return Err(SyntaxError::PrimaryStart(token))
            }
        };

        while lexer.peek_token().kind == TokenKind::OpenParen {
            head = Expr::Fun(Box::new(head), Self::parse_fun_args(lexer)?)
        }
        Ok(head)
    }

    fn parse_binary_operator(lexer: &mut Lexer, current_precedence: usize) -> Result<Self, SyntaxError> {
        if current_precedence > Op::MAX_PRECEDENCE {
            return Self::parse_primary(lexer)
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

    pub fn parse(lexer: &mut Lexer) -> Result<Self, SyntaxError> {
        Self::parse_binary_operator(lexer, 0)
    }

    pub fn pattern_match(&self, value: &Expr) -> Option<HashMap<String, Expr>> {
        fn pattern_match_impl(pattern: &Expr, value: &Expr, bindings: &mut HashMap<String, Expr>) -> bool {
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
        Expr::parse_ident(stringify!($name))
    };
    ($name:ident($($args:tt)*)) => {
        Expr::Fun(Box::new(Expr::parse_ident(stringify!($name))), fun_args!($($args)*))
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
                if op.precedence() <= 1 {
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

pub fn find_all_subexprs<'a>(pattern: &'a Expr, expr: &'a Expr) -> Vec<&'a Expr> {
    let mut subexprs = Vec::new();

    fn find_all_subexprs_impl<'a>(pattern: &'a Expr, expr: &'a Expr, subexprs: &mut Vec<&'a Expr>) {
        if pattern.pattern_match(expr).is_some() {
            subexprs.push(expr);
        }

        match expr {
            Expr::Fun(head, args) => {
                find_all_subexprs_impl(pattern, head, subexprs);
                for arg in args {
                    find_all_subexprs_impl(pattern, arg, subexprs);
                }
            }
            Expr::Op(_, lhs, rhs) => {
                find_all_subexprs_impl(pattern, lhs, subexprs);
                find_all_subexprs_impl(pattern, rhs, subexprs);
            }
            Expr::Sym(_) | Expr::Var(_) => {}
        }
    }

    find_all_subexprs_impl(pattern, expr, &mut subexprs);
    subexprs
}



#[cfg(test)]
mod pattern_match_tests {
    use std::collections::HashMap;

    use super::{Expr};

    #[test]
    fn anything_bindings_with_a_variable() {
        assert_bindings(expr!(A), expr!(A), vec![("A", expr!(A))]);
        assert_bindings(expr!(A), expr!(B), vec![("A", expr!(B))]);
        assert_bindings(expr!(A), expr!(f()), vec![("A", expr!(f()))]);
        assert_bindings(expr!(A), expr!(f(X)), vec![("A", expr!(f(X)))]);
        assert_bindings(expr!(A), expr!(f(X, g(Y), Z)), vec![("A", expr!(f(X, g(Y), Z)))]);
    }

    #[test]
    fn function_pattern_only_bindings_with_other_functions_with_same_name_and_number_of_args() {
        assert_no_bindings(expr!(f()), expr!(a));
        assert_no_bindings(expr!(f()), expr!(g()));
        assert_no_bindings(expr!(f(X0)), expr!(f(Y0, Y1)));

        assert_bindings(expr!(f()), expr!(f()), vec![]);
        assert_bindings(expr!(f(X0)), expr!(f(Y0)), vec![("X0", expr!(Y0))]);
    }

    #[test]
    fn test_with_same_repeated_variables() {
        assert_bindings(expr!(f(X0, X0)), expr!(f(Y0, Y0)), vec![("X0", expr!(Y0))]);
        assert_bindings(expr!(f(g(X0, X1), X0)), expr!(f(g(Y0, Y1), Y0)), vec![("X0", expr!(Y0)), ("X1", expr!(Y1))]);

        assert_no_bindings(expr!(f(X0, X0)), expr!(f(Y0, Y1)));
        assert_no_bindings(expr!(f(g(X0, X0), X1)), expr!(f(g(Y0, Y1), X1)));
    }

    #[test]
    fn test_recursive_pattern_matching() {
        assert_bindings(
            expr!(f(X0, X1)),
            expr!(f(Y0, Y1)),
            vec![("X0", expr!(Y0)), ("X1", expr!(Y1))],
        );
        assert_bindings(
            expr!(f(X0, g(X1), X2)),
            expr!(f(Y0, g(Y1), Y2)),
            vec![("X0", expr!(Y0)), ("X1", expr!(Y1)), ("X2", expr!(Y2))],
        );
        assert_bindings(
            expr!(f(X0)),
            expr!(f(g(Y0, Y1))),
            vec![("X0", expr!(g(Y0, Y1)))],
        );

        assert_no_bindings(
            expr!(f(g(X0))),
            expr!(f(g(Y0, Y1))),
        );
    }

    fn assert_bindings(pattern: Expr, with: Expr, expected_bindings: Vec<(&str, Expr)>) {
        let expected_bindings = expected_bindings
            .into_iter()
            .map(|(name, ex)| (name.to_string(), ex))
            .collect::<HashMap<String, Expr>>();

        let actual_bindings = pattern.pattern_match(&with).unwrap();
        assert_eq!(expected_bindings, actual_bindings)
    }

    fn assert_no_bindings(pattern: Expr, with: Expr) {
        assert_eq!(Option::None, pattern.pattern_match(&with));
    }
}
