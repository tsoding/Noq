use std::io::Write;
use std::io;
use std::fmt;

use termion::clear;
use termion::cursor;
use termion::color;

use termion::event::Key;
use termion::raw::IntoRawMode;
use termion::input::TermRead;

use super::engine::diagnostics::*;
use super::engine::lexer::*;
use super::engine::expr::*;

#[derive(Default)]
struct NewCoolRepl {
    buffer: Vec<char>,
    buffer_cursor: usize,
    popup: Vec<String>,
    popup_cursor: usize,
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
        write!(sink, "\r{}{}{}\r\n", clear::AfterCursor, prompt, &buffer)?;
        for (index, line) in self.popup.iter().take(POPUP_SIZE).enumerate() {
            if index == self.popup_cursor {
                write!(sink, ">")?
            } else {
                write!(sink, " ")?
            }
            write!(sink, " {}\r\n", line)?;
        }
        write!(sink, "{}{}",
               cursor::Up((POPUP_SIZE.min(self.popup.len()) + 1).try_into().unwrap()),
               cursor::Right((prompt.len() + self.buffer_cursor).try_into().unwrap()))?;
        Ok(())
    }
}

struct HighlightedSubexpr<'a> {
    pub expr: &'a Expr,
    pub subexpr: &'a Expr
}

impl<'a> fmt::Display for HighlightedSubexpr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let HighlightedSubexpr{expr, subexpr} = self;
        if expr == subexpr {
            write!(f, "{}{}{}", color::Fg(color::Green), expr, color::Fg(color::Reset))
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

pub fn start() {
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
    let mut stdout = io::stdout().into_raw_mode().unwrap();
    let stdin = io::stdin();
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
