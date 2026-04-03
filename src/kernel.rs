use std::fmt;

use crate::reader::{Expr, parse_program};

pub type ClickResult<T> = Result<T, String>;

type Env = Vec<(String, Value)>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Atom(String),
    Bool(bool),
    Nil,
    Cons(Box<Value>, Box<Value>),
    Closure(Closure),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closure {
    binder: String,
    body: Expr,
    env: Env,
}

impl Value {
    // Recognize the values that count as atoms for the `atom` primitive.
    fn is_atom(&self) -> bool {
        matches!(self, Value::Atom(_) | Value::Bool(_) | Value::Nil)
    }

    // Apply Click's truthiness rule: only `nil` and `false` are falsey.
    fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }
}

impl fmt::Display for Value {
    // Render kernel values back into the small Click surface notation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Atom(name) => write!(f, "{name}"),
            Value::Bool(true) => write!(f, "true"),
            Value::Bool(false) => write!(f, "false"),
            Value::Nil => write!(f, "nil"),
            Value::Cons(_, _) => format_cons(self, f),
            Value::Closure(_) => write!(f, "#<closure>"),
        }
    }
}

// Print a cons cell as either a proper list or a dotted pair.
fn format_cons(value: &Value, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(")?;

    let mut current = value;
    let mut first = true;

    loop {
        match current {
            Value::Cons(head, tail) => {
                if !first {
                    write!(f, " ")?;
                }
                write!(f, "{head}")?;
                first = false;

                match tail.as_ref() {
                    Value::Nil => {
                        write!(f, ")")?;
                        return Ok(());
                    }
                    Value::Cons(_, _) => current = tail.as_ref(),
                    other => {
                        write!(f, " . {other})")?;
                        return Ok(());
                    }
                }
            }
            _ => unreachable!("format_cons is only called for cons cells"),
        }
    }
}

/// Parse and evaluate a source string, returning the final top-level value.
pub fn run_source(source: &str) -> ClickResult<Option<Value>> {
    let exprs = parse_program(source)?;
    let env = Env::new();

    let mut last = None;
    for expr in exprs {
        last = Some(eval(&expr, &env)?);
    }

    Ok(last)
}

// Evaluate one parsed expression in the given lexical environment.
fn eval(expr: &Expr, env: &Env) -> ClickResult<Value> {
    match expr {
        Expr::Symbol(symbol) => eval_symbol(symbol),
        Expr::List(items) => eval_list(items, env),
    }
}

// Evaluate a bare symbol, which only succeeds for the built-in atomic values.
fn eval_symbol(symbol: &str) -> ClickResult<Value> {
    match symbol {
        "nil" => Ok(Value::Nil),
        "true" => Ok(Value::Bool(true)),
        "false" => Ok(Value::Bool(false)),
        _ => Err(format!("unbound atom '{symbol}'")),
    }
}

// Evaluate one tagged list form such as `quote`, `if`, `lambda`, or `app`.
fn eval_list(items: &[Expr], env: &Env) -> ClickResult<Value> {
    let Some((head, tail)) = items.split_first() else {
        return Err("cannot evaluate an empty list; use nil or quote".to_string());
    };

    let Expr::Symbol(operator) = head else {
        return Err("form heads must be keyword atoms".to_string());
    };

    match operator.as_str() {
        "quote" => {
            expect_arity(operator, tail, 1)?;
            quote_expr(&tail[0])
        }
        "if" => {
            expect_arity(operator, tail, 3)?;
            let condition = eval(&tail[0], env)?;
            if condition.is_truthy() {
                eval(&tail[1], env)
            } else {
                eval(&tail[2], env)
            }
        }
        "lambda" => {
            expect_arity(operator, tail, 2)?;
            let binder = expect_symbol(&tail[0], "lambda binder")?;
            if env.iter().any(|(name, _)| name == &binder) {
                return Err(format!("lambda binder '{binder}' is already bound"));
            }
            Ok(Value::Closure(Closure {
                binder,
                body: tail[1].clone(),
                env: env.clone(),
            }))
        }
        "var" => {
            expect_arity(operator, tail, 1)?;
            let name = expect_symbol(&tail[0], "var name")?;
            lookup_var(env, &name)
                .cloned()
                .ok_or_else(|| format!("unbound variable '{name}'"))
        }
        "app" => {
            expect_arity(operator, tail, 2)?;
            let function = eval(&tail[0], env)?;
            let arg = eval(&tail[1], env)?;
            apply(function, arg)
        }
        "atom" => {
            expect_arity(operator, tail, 1)?;
            Ok(Value::Bool(eval(&tail[0], env)?.is_atom()))
        }
        "atom_eq" => {
            expect_arity(operator, tail, 2)?;
            let left = eval(&tail[0], env)?;
            let right = eval(&tail[1], env)?;
            if !left.is_atom() || !right.is_atom() {
                return Err("atom_eq expects atom arguments".to_string());
            }
            Ok(Value::Bool(left == right))
        }
        "car" => {
            expect_arity(operator, tail, 1)?;
            match eval(&tail[0], env)? {
                Value::Cons(head, _) => Ok(*head),
                _ => Err("car expects a non-empty list".to_string()),
            }
        }
        "cdr" => {
            expect_arity(operator, tail, 1)?;
            match eval(&tail[0], env)? {
                Value::Cons(_, tail) => Ok(*tail),
                _ => Err("cdr expects a non-empty list".to_string()),
            }
        }
        "cons" => {
            expect_arity(operator, tail, 2)?;
            let head = eval(&tail[0], env)?;
            let rest = eval(&tail[1], env)?;
            Ok(Value::Cons(Box::new(head), Box::new(rest)))
        }
        _ => Err(format!("unknown form '{operator}'")),
    }
}

// Reject forms whose argument count does not match the primitive's contract.
fn expect_arity(operator: &str, args: &[Expr], expected: usize) -> ClickResult<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(format!(
            "{operator} expects {expected} argument(s), got {}",
            args.len()
        ))
    }
}

// Extract an atom name from syntax where a binder or variable name is expected.
fn expect_symbol(expr: &Expr, role: &str) -> ClickResult<String> {
    match expr {
        Expr::Symbol(symbol) => Ok(symbol.clone()),
        _ => Err(format!("{role} must be an atom")),
    }
}

// Turn parsed syntax into the corresponding quoted Click data value.
fn quote_expr(expr: &Expr) -> ClickResult<Value> {
    match expr {
        Expr::Symbol(symbol) => Ok(quote_symbol(symbol)),
        Expr::List(items) => {
            let mut result = Value::Nil;
            for item in items.iter().rev() {
                result = Value::Cons(Box::new(quote_expr(item)?), Box::new(result));
            }
            Ok(result)
        }
    }
}

// Quote one symbol, preserving the kernel's built-in atoms.
fn quote_symbol(symbol: &str) -> Value {
    match symbol {
        "nil" => Value::Nil,
        "true" => Value::Bool(true),
        "false" => Value::Bool(false),
        _ => Value::Atom(symbol.to_string()),
    }
}

// Resolve a variable name by looking through the lexical environment from the inside out.
fn lookup_var<'a>(env: &'a Env, name: &str) -> Option<&'a Value> {
    env.iter()
        .rev()
        .find(|(binding, _)| binding == name)
        .map(|(_, value)| value)
}

// Apply a function value to an argument by extending its captured environment.
fn apply(function: Value, arg: Value) -> ClickResult<Value> {
    match function {
        Value::Closure(closure) => {
            let mut next_env = closure.env;
            next_env.push((closure.binder, arg));
            eval(&closure.body, &next_env)
        }
        _ => Err("attempted to call a non-function".to_string()),
    }
}
