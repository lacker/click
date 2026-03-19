use std::fmt;

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Atom(String),
    Bool(bool),
    Nil,
    Cons(Box<Value>, Box<Value>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Symbol(String),
    List(Vec<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    LParen,
    RParen,
    Quote,
    Symbol(String),
}

impl Value {
    fn is_atom(&self) -> bool {
        matches!(self, Value::Atom(_) | Value::Bool(_) | Value::Nil)
    }

    fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Atom(name) => write!(f, "{name}"),
            Value::Bool(true) => write!(f, "true"),
            Value::Bool(false) => write!(f, "false"),
            Value::Nil => write!(f, "nil"),
            Value::Cons(_, _) => format_cons(self, f),
        }
    }
}

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

pub fn run_source(source: &str) -> ClickResult<Option<Value>> {
    let source = strip_shebang(source);
    let tokens = tokenize(source)?;
    let exprs = Parser::new(tokens).parse_program()?;
    let env = Vec::new();

    let mut last = None;
    for expr in exprs {
        last = Some(eval(&expr, &env)?);
    }

    Ok(last)
}

fn strip_shebang(source: &str) -> &str {
    if !source.starts_with("#!") {
        return source;
    }

    match source.find('\n') {
        Some(index) => &source[index + 1..],
        None => "",
    }
}

fn tokenize(source: &str) -> ClickResult<Vec<Token>> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            '\'' => tokens.push(Token::Quote),
            ';' => {
                while let Some(next) = chars.next() {
                    if next == '\n' {
                        break;
                    }
                }
            }
            c if c.is_whitespace() => {}
            _ => {
                let mut symbol = String::from(ch);
                while let Some(next) = chars.peek() {
                    if next.is_whitespace() || matches!(next, '(' | ')' | '\'' | ';') {
                        break;
                    }
                    symbol.push(*next);
                    chars.next();
                }
                tokens.push(Token::Symbol(symbol));
            }
        }
    }

    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, index: 0 }
    }

    fn parse_program(mut self) -> ClickResult<Vec<Expr>> {
        let mut exprs = Vec::new();
        while self.index < self.tokens.len() {
            exprs.push(self.parse_expr()?);
        }
        Ok(exprs)
    }

    fn parse_expr(&mut self) -> ClickResult<Expr> {
        let token = self
            .tokens
            .get(self.index)
            .ok_or_else(|| "unexpected end of input".to_string())?
            .clone();
        self.index += 1;

        match token {
            Token::LParen => {
                let mut items = Vec::new();
                loop {
                    match self.tokens.get(self.index) {
                        Some(Token::RParen) => {
                            self.index += 1;
                            return Ok(Expr::List(items));
                        }
                        Some(_) => items.push(self.parse_expr()?),
                        None => return Err("unterminated list".to_string()),
                    }
                }
            }
            Token::RParen => Err("unexpected ')'".to_string()),
            Token::Quote => {
                let quoted = self.parse_expr()?;
                Ok(Expr::List(vec![Expr::Symbol("quote".to_string()), quoted]))
            }
            Token::Symbol(symbol) => Ok(Expr::Symbol(symbol)),
        }
    }
}

fn eval(expr: &Expr, env: &[Value]) -> ClickResult<Value> {
    match expr {
        Expr::Symbol(symbol) => eval_symbol(symbol, env),
        Expr::List(items) => eval_list(items, env),
    }
}

fn eval_symbol(symbol: &str, env: &[Value]) -> ClickResult<Value> {
    match symbol {
        "nil" => Ok(Value::Nil),
        "true" => Ok(Value::Bool(true)),
        "false" => Ok(Value::Bool(false)),
        "stack" => Ok(env_to_value(env)),
        _ => Err(format!("unbound atom '{symbol}'")),
    }
}

fn eval_list(items: &[Expr], env: &[Value]) -> ClickResult<Value> {
    let Some((head, tail)) = items.split_first() else {
        return Err("cannot evaluate an empty list; use nil or quote".to_string());
    };

    if let Expr::Symbol(operator) = head {
        match operator.as_str() {
            "quote" => {
                expect_arity(operator, tail, 1)?;
                return quote_expr(&tail[0]);
            }
            "if" => {
                expect_arity(operator, tail, 3)?;
                let condition = eval(&tail[0], env)?;
                if condition.is_truthy() {
                    return eval(&tail[1], env);
                }
                return eval(&tail[2], env);
            }
            "lambda" => {
                expect_arity(operator, tail, 1)?;
                return Ok(make_closure(&tail[0], env)?);
            }
            "atom" => {
                expect_arity(operator, tail, 1)?;
                return Ok(Value::Bool(eval(&tail[0], env)?.is_atom()));
            }
            "atom_eq" => {
                expect_arity(operator, tail, 2)?;
                let left = eval(&tail[0], env)?;
                let right = eval(&tail[1], env)?;
                if !left.is_atom() || !right.is_atom() {
                    return Err("atom_eq expects atom arguments".to_string());
                }
                return Ok(Value::Bool(left == right));
            }
            "car" => {
                expect_arity(operator, tail, 1)?;
                return match eval(&tail[0], env)? {
                    Value::Cons(head, _) => Ok(*head),
                    _ => Err("car expects a non-empty list".to_string()),
                };
            }
            "cdr" => {
                expect_arity(operator, tail, 1)?;
                return match eval(&tail[0], env)? {
                    Value::Cons(_, tail) => Ok(*tail),
                    _ => Err("cdr expects a non-empty list".to_string()),
                };
            }
            "cons" => {
                expect_arity(operator, tail, 2)?;
                let head = eval(&tail[0], env)?;
                let rest = eval(&tail[1], env)?;
                return Ok(Value::Cons(Box::new(head), Box::new(rest)));
            }
            _ => {}
        }
    }

    let mut function = eval(head, env)?;
    for arg in tail {
        let value = eval(arg, env)?;
        function = apply(function, value)?;
    }

    Ok(function)
}

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

fn quote_symbol(symbol: &str) -> Value {
    match symbol {
        "nil" => Value::Nil,
        "true" => Value::Bool(true),
        "false" => Value::Bool(false),
        _ => Value::Atom(symbol.to_string()),
    }
}

fn env_to_value(env: &[Value]) -> Value {
    let mut result = Value::Nil;
    for value in env.iter().rev() {
        result = Value::Cons(Box::new(value.clone()), Box::new(result));
    }
    result
}

fn make_closure(body: &Expr, env: &[Value]) -> ClickResult<Value> {
    Ok(make_list(vec![
        Value::Atom("closure".to_string()),
        quote_expr(body)?,
        env_to_value(env),
    ]))
}

fn make_list(items: Vec<Value>) -> Value {
    let mut result = Value::Nil;
    for item in items.into_iter().rev() {
        result = Value::Cons(Box::new(item), Box::new(result));
    }
    result
}

fn apply(function: Value, arg: Value) -> ClickResult<Value> {
    match unpack_closure(function)? {
        Some((body, env)) => {
            let mut next_env = Vec::with_capacity(env.len() + 1);
            next_env.push(arg);
            next_env.extend(env);
            eval(&body, &next_env)
        }
        None => Err("attempted to call a non-function".to_string()),
    }
}

fn unpack_closure(value: Value) -> ClickResult<Option<(Expr, Vec<Value>)>> {
    let Value::Cons(head, tail) = value else {
        return Ok(None);
    };

    let Value::Atom(tag) = *head else {
        return Ok(None);
    };

    if tag != "closure" {
        return Ok(None);
    }

    let parts = proper_list_to_vec(*tail)?;
    if parts.len() != 2 {
        return Err("closure expects a body and an environment".to_string());
    }

    let mut parts = parts.into_iter();
    let body = value_to_expr(parts.next().expect("closure body should exist"))?;
    let env = proper_list_to_vec(parts.next().expect("closure env should exist"))
        .map_err(|_| "closure environment must be a proper list".to_string())?;

    Ok(Some((body, env)))
}

fn proper_list_to_vec(value: Value) -> ClickResult<Vec<Value>> {
    let mut current = value;
    let mut items = Vec::new();

    loop {
        match current {
            Value::Nil => return Ok(items),
            Value::Cons(head, tail) => {
                items.push(*head);
                current = *tail;
            }
            _ => return Err("expected a proper list".to_string()),
        }
    }
}

fn value_to_expr(value: Value) -> ClickResult<Expr> {
    match value {
        Value::Atom(symbol) => Ok(Expr::Symbol(symbol)),
        Value::Bool(true) => Ok(Expr::Symbol("true".to_string())),
        Value::Bool(false) => Ok(Expr::Symbol("false".to_string())),
        Value::Nil => Ok(Expr::Symbol("nil".to_string())),
        Value::Cons(_, _) => {
            let items = proper_list_to_vec(value)?
                .into_iter()
                .map(value_to_expr)
                .collect::<ClickResult<Vec<_>>>()?;
            Ok(Expr::List(items))
        }
    }
}
