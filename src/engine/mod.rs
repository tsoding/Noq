//! This is the Engine responsible for Pattern Matching and Rule
//! Substitution of Noq. It's basically the implementation of the Core
//! Expression-based Language on top of which an imperative Command
//! Language is implemented. (See [command](super::command) module)

pub mod diagnostics;
#[macro_use]
pub mod lexer;
#[macro_use]
pub mod expr;
pub mod rule;
