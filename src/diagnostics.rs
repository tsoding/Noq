use super::lexer::Loc;

use std::fmt;

#[derive(Copy, Clone, PartialEq)]
pub enum Severity {
    Info,
    Error,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Info => write!(f, "INFO"),
            Self::Error => write!(f, "ERROR"),
        }
    }
}

// NOTE: this trait is not needed right now but it shows the intent:
// The mechanism for reported diagnostics should be easily customizable.
// This might be important in the future.
// Or not.
// In the last case, just remove all this bs.
pub trait Diagnoster {
    fn report(&mut self, loc: &Loc, severity: Severity, message: &str);
}

pub struct StdoutDiagnoster {}

impl Diagnoster for StdoutDiagnoster {
    fn report(&mut self, loc: &Loc, severity: Severity, message: &str) {
        match loc {
            Loc::File{path, row, col} => {
                eprintln!("{}:{}:{}: {}: {}", path, row, col, severity, message);
            }
            Loc::Repl{col, line} => {
                if severity == Severity::Error {
                    eprintln!("{}", line.iter().collect::<String>());
                    eprintln!("{:>width$}^", "", width=col - 1);
                }
                eprintln!("{}: {}", severity, message);
            }
        }
    }
}
