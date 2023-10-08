use std::io::{stdin, stdout};
use std::io::Write;
use std::env;
use std::fs;

#[macro_use]
mod engine;
mod new_repl;
mod command;

use engine::diagnostics::*;
use engine::lexer::*;
use engine::expr::*;
use command::*;

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
        diag.report(&token.loc, Severity::Error, &format!("unexpected token {} after the End of the Command", token.report()));
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
    let source = fs::read_to_string(file_path).unwrap();
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
        if let 0 = stdin().read_line(&mut command).unwrap() {
            return
        }
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

fn main() {
    let config = Config::from_iter(&mut env::args());

    if let Some(file_path) = &config.file_path {
        interpret_file(file_path);
    } else {
        match config.mode {
            ReplMode::Normal => start_repl(),
            // TODO: new repl does not support Windows
            ReplMode::DebugNew => new_repl::start(),
            ReplMode::DebugParser => start_parser_debugger(),
            ReplMode::DebugLexer => start_lexer_debugger(),
        }
    }
}
