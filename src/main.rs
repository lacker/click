use std::env;
use std::fs;
use std::io::{self, IsTerminal, Read};
use std::process::ExitCode;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::from(1)
        }
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let mut expression = None;
    let mut path = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                print_usage();
                return Ok(());
            }
            "-e" | "--expr" => {
                if expression.is_some() {
                    return Err("only one -e/--expr argument is allowed".to_string());
                }
                let value = args
                    .next()
                    .ok_or_else(|| "missing expression after -e/--expr".to_string())?;
                expression = Some(value);
            }
            _ if arg.starts_with('-') && arg != "-" => {
                return Err(format!("unknown flag '{arg}'"));
            }
            _ => {
                if path.is_some() {
                    return Err("only one input file may be provided".to_string());
                }
                path = Some(arg);
            }
        }
    }

    let source = match (expression, path) {
        (Some(_), Some(_)) => {
            return Err("pass either an expression or a file path, not both".to_string());
        }
        (Some(expr), None) => expr,
        (None, Some(path)) if path == "-" => read_stdin()?,
        (None, Some(path)) => fs::read_to_string(&path)
            .map_err(|error| format!("failed to read '{path}': {error}"))?,
        (None, None) => {
            if io::stdin().is_terminal() {
                print_usage();
                return Ok(());
            }
            read_stdin()?
        }
    };

    if let Some(value) = click::run_source(&source)? {
        println!("{value}");
    }

    Ok(())
}

fn read_stdin() -> Result<String, String> {
    let mut source = String::new();
    io::stdin()
        .read_to_string(&mut source)
        .map_err(|error| format!("failed to read stdin: {error}"))?;
    Ok(source)
}

fn print_usage() {
    println!(
        "\
click 0.1.0

Usage:
  click -e EXPR
  click FILE
  click < FILE

Notes:
  A leading #! line is ignored in source files.
  If no FILE is given and stdin is not a terminal, click reads stdin."
    );
}
