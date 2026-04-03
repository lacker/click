use std::fmt;
use std::collections::BTreeMap;

use crate::reader::read;

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Object {
    entries: BTreeMap<String, Value>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Atom(String),
    Bool(bool),
    Nil,
    Object(Object),
    Cons(Box<Value>, Box<Value>),
    Closure(Closure),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closure {
    binder: String,
    body: Expr,
    env: Object,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Expr {
    Symbol(String),
    List(Vec<Expr>),
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

impl Object {
    // Construct an empty object with no named entries.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    // Check whether an object currently has a value for the given key.
    pub fn has(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    // Look up the value currently stored at the given key.
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.entries.get(name)
    }

    // Return a new object with one key updated or inserted.
    pub fn with(&self, name: String, value: Value) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(name, value);
        Self { entries }
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
            Value::Object(object) => format_object(object, f),
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

// Print an object as a tagged sequence of key/value entries.
fn format_object(object: &Object, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(object")?;
    for (key, value) in &object.entries {
        write!(f, " ({key} {value})")?;
    }
    write!(f, ")")
}

/// Parse and evaluate a source string, returning the final top-level value.
pub fn run_source(source: &str) -> ClickResult<Option<Value>> {
    let exprs = read(source)?;
    let env = Object::new();

    let mut last = None;
    for expr in exprs {
        last = Some(eval(&expr, &env)?);
    }

    Ok(last)
}

// Evaluate one parsed expression in the given lexical environment.
fn eval(expr: &Expr, env: &Object) -> ClickResult<Value> {
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

// Evaluate one tagged list form such as `quote`, `object`, `lambda`, or `app`.
fn eval_list(items: &[Expr], env: &Object) -> ClickResult<Value> {
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
        "object" => {
            expect_arity(operator, tail, 0)?;
            Ok(Value::Object(Object::new()))
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
            if env.has(&binder) {
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
            env.get(&name)
                .cloned()
                .ok_or_else(|| format!("unbound variable '{name}'"))
        }
        "app" => {
            expect_arity(operator, tail, 2)?;
            let function = eval(&tail[0], env)?;
            let arg = eval(&tail[1], env)?;
            apply(function, arg)
        }
        "get" => {
            expect_arity(operator, tail, 2)?;
            let object = expect_object(eval(&tail[0], env)?, "get object")?;
            let key = expect_object_key(eval(&tail[1], env)?, "get key")?;
            object
                .get(&key)
                .cloned()
                .ok_or_else(|| format!("missing object key '{key}'"))
        }
        "with" => {
            expect_arity(operator, tail, 3)?;
            let object = expect_object(eval(&tail[0], env)?, "with object")?;
            let key = expect_object_key(eval(&tail[1], env)?, "with key")?;
            let value = eval(&tail[2], env)?;
            Ok(Value::Object(object.with(key, value)))
        }
        "has" => {
            expect_arity(operator, tail, 2)?;
            let object = expect_object(eval(&tail[0], env)?, "has object")?;
            let key = expect_object_key(eval(&tail[1], env)?, "has key")?;
            Ok(Value::Bool(object.has(&key)))
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

// Extract an object value from runtime data where one is required.
fn expect_object(value: Value, role: &str) -> ClickResult<Object> {
    match value {
        Value::Object(object) => Ok(object),
        _ => Err(format!("{role} must be an object")),
    }
}

// Extract a symbol name from a runtime value where an object key is required.
fn expect_object_key(value: Value, role: &str) -> ClickResult<String> {
    match value {
        Value::Atom(atom) => Ok(atom),
        _ => Err(format!("{role} must be a symbol")),
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

// Apply a function value to an argument by extending its captured environment.
fn apply(function: Value, arg: Value) -> ClickResult<Value> {
    match function {
        Value::Closure(closure) => {
            let next_env = closure.env.with(closure.binder, arg);
            eval(&closure.body, &next_env)
        }
        _ => Err("attempted to call a non-function".to_string()),
    }
}
