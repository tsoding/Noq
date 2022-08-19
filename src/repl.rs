use std::io::Write;
use std::io;
use std::fmt;

use crossterm::terminal::{Clear, ClearType};
use crossterm::cursor;
use crossterm::style::{Color, SetForegroundColor};

use super::expr::*;

#[derive(Default)]
pub struct NewCoolRepl {
    pub buffer: Vec<char>,
    pub buffer_cursor: usize,
    pub popup: Vec<String>,
    pub popup_cursor: usize,
}

impl NewCoolRepl {
    pub fn clear(&mut self) {
        self.buffer.clear();
        self.buffer_cursor = 0;
        self.popup.clear();
        self.popup_cursor = 0;
    }

    pub fn take(&mut self) -> String {
        let result = self.buffer.iter().collect();
        self.clear();
        result
    }

    pub fn insert_char(&mut self, x: char) {
        self.buffer.insert(self.buffer_cursor, x);
        self.buffer_cursor += 1;
    }

    pub fn backspace(&mut self) {
        if self.buffer_cursor > 0 {
            self.buffer.remove(self.buffer_cursor - 1);
            self.buffer_cursor -= 1;
        }
    }

    pub fn home(&mut self) {
        self.buffer_cursor = 0;
    }

    pub fn end(&mut self) {
        self.buffer_cursor = self.buffer.len();
    }

    pub fn up(&mut self) {
        if self.popup_cursor > 0 {
            self.popup_cursor -= 1
        }
    }

    pub fn down(&mut self) {
        if self.popup_cursor < self.popup.len() - 1 {
            self.popup_cursor += 1
        }
    }

    pub fn left_word(&mut self) {
        while self.buffer_cursor > 0 && self.buffer_cursor <= self.buffer.len() && !self.buffer.get(self.buffer_cursor - 1).unwrap().is_alphanumeric() {
            self.buffer_cursor -= 1;
        }
        while self.buffer_cursor > 0 && self.buffer_cursor <= self.buffer.len() && self.buffer.get(self.buffer_cursor - 1).unwrap().is_alphanumeric() {
            self.buffer_cursor -= 1;
        }
    }

    pub fn right_word(&mut self) {
        while self.buffer_cursor < self.buffer.len() && !self.buffer.get(self.buffer_cursor).unwrap().is_alphanumeric() {
            self.buffer_cursor += 1;
        }
        while self.buffer_cursor < self.buffer.len() && self.buffer.get(self.buffer_cursor).unwrap().is_alphanumeric() {
            self.buffer_cursor += 1;
        }
    }

    pub fn left_char(&mut self) {
        if self.buffer_cursor > 0 {
            self.buffer_cursor -= 1;
        }
    }

    pub fn right_char(&mut self) {
        if self.buffer_cursor < self.buffer.len() {
            self.buffer_cursor += 1;
        }
    }

    pub fn render(&self, prompt: &str, sink: &mut impl Write) -> io::Result<()> {
        const POPUP_SIZE: usize = 5;
        let buffer: String = self.buffer.iter().collect();
        write!(sink, "\r{}{}{}\r\n", Clear(ClearType::FromCursorDown), prompt, &buffer)?;
        for (index, line) in self.popup.iter().take(POPUP_SIZE).enumerate() {
            if index == self.popup_cursor {
                write!(sink, ">")?
            } else {
                write!(sink, " ")?
            }
            write!(sink, " {}\r\n", line)?;
        }
        write!(sink, "{}{}",
               cursor::MoveUp((POPUP_SIZE.min(self.popup.len()) + 1).try_into().unwrap()),
               cursor::MoveRight((prompt.len() + self.buffer_cursor).try_into().unwrap()))?;
        Ok(())
    }
}

pub struct HighlightedSubexpr<'a> {
    pub expr: &'a Expr,
    pub subexpr: &'a Expr
}

impl<'a> fmt::Display for HighlightedSubexpr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let HighlightedSubexpr{expr, subexpr} = self;
        if expr == subexpr {
            write!(
                f,
                "{}{}{}",
                SetForegroundColor(Color::DarkGreen), 
                expr, 
                SetForegroundColor(Color::Reset)
            )
        } else {
            // TODO: get rid of duplicate code in fmt::Display instance of HighlightedSubexpr and Expr
            match expr {
                Expr::Sym(name) | Expr::Var(name) => write!(f, "{}", name),
                Expr::Fun(head, args) => {
                    match &**head {
                        Expr::Sym(name) | Expr::Var(name) => write!(f, "{}", name)?,
                        other => write!(f, "({})", HighlightedSubexpr{expr: other, subexpr})?,
                    }
                    write!(f, "(")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 { write!(f, ", ")? }
                        write!(f, "{}", HighlightedSubexpr{expr: arg, subexpr})?;
                    }
                    write!(f, ")")
                },
                Expr::Op(op, lhs, rhs) => {
                    match **lhs {
                        Expr::Op(sub_op, _, _) => if sub_op.precedence() <= op.precedence() {
                            write!(f, "({})", HighlightedSubexpr{expr: lhs, subexpr})?
                        } else {
                            write!(f, "{}", HighlightedSubexpr{expr: lhs, subexpr})?
                        }
                        _ => write!(f, "{}", HighlightedSubexpr{expr: lhs, subexpr})?
                    }
                    if op.precedence() <= 1 {
                        write!(f, " {} ", op)?;
                    } else {
                        write!(f, "{}", op)?;
                    }
                    match **rhs {
                        Expr::Op(sub_op, _, _) => if sub_op.precedence() <= op.precedence() {
                            write!(f, "({})", HighlightedSubexpr{expr: rhs, subexpr})
                        } else {
                            write!(f, "{}", HighlightedSubexpr{expr: rhs, subexpr})
                        }
                        _ => write!(f, "{}", HighlightedSubexpr{expr: rhs, subexpr})
                    }
                }
            }
        }
    }
}
