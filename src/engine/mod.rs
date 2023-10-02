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

// TODO: Custom arbitrary operators like in Haskell
// TODO: if a rule introduces free variables we should probably demand to specify them
//   ```
//   mul_id :: A*1 = 1
//   0 {
//     B*B*1 |! mul_id
//   }
//   ```
//   results in `B*B*A*1` which is a bit unexpected. It makes more sense to expand to `B*B*B*1`.
//   Maybe you should be obligated to specify the substitutions for such variables:
//   ```
//   0 {
//     B*B*1 |! mul_id (A => B)
//   }
//   ```
