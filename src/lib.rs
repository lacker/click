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
        !matches!(self, Value::Cons(_, _))
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

    let mut last = None;
    for expr in exprs {
        last = Some(eval(&expr)?);
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

fn eval(expr: &Expr) -> ClickResult<Value> {
    match expr {
        Expr::Symbol(symbol) => eval_symbol(symbol),
        Expr::List(items) => eval_list(items),
    }
}

fn eval_symbol(symbol: &str) -> ClickResult<Value> {
    match symbol {
        "nil" => Ok(Value::Nil),
        "true" => Ok(Value::Bool(true)),
        "false" => Ok(Value::Bool(false)),
        _ => Ok(Value::Atom(symbol.to_string())),
    }
}

fn eval_list(items: &[Expr]) -> ClickResult<Value> {
    let Some((head, tail)) = items.split_first() else {
        return Err("cannot evaluate an empty list; use nil or quote".to_string());
    };

    let Expr::Symbol(operator) = head else {
        return Err("the first element of a list must be an operator atom".to_string());
    };

    match operator.as_str() {
        "quote" => {
            expect_arity(operator, tail, 1)?;
            quote_expr(&tail[0])
        }
        "if" => {
            expect_arity(operator, tail, 3)?;
            let condition = eval(&tail[0])?;
            if condition.is_truthy() {
                eval(&tail[1])
            } else {
                eval(&tail[2])
            }
        }
        "atom" => {
            expect_arity(operator, tail, 1)?;
            Ok(Value::Bool(eval(&tail[0])?.is_atom()))
        }
        "atom_eq" => {
            expect_arity(operator, tail, 2)?;
            let left = eval(&tail[0])?;
            let right = eval(&tail[1])?;
            if !left.is_atom() || !right.is_atom() {
                return Err("atom_eq expects atom arguments".to_string());
            }
            Ok(Value::Bool(left == right))
        }
        "car" => {
            expect_arity(operator, tail, 1)?;
            match eval(&tail[0])? {
                Value::Cons(head, _) => Ok(*head),
                Value::Nil => Ok(Value::Nil),
                _ => Err("car expects a list".to_string()),
            }
        }
        "cdr" => {
            expect_arity(operator, tail, 1)?;
            match eval(&tail[0])? {
                Value::Cons(_, tail) => Ok(*tail),
                Value::Nil => Ok(Value::Nil),
                _ => Err("cdr expects a list".to_string()),
            }
        }
        "cons" => {
            expect_arity(operator, tail, 2)?;
            let head = eval(&tail[0])?;
            let rest = eval(&tail[1])?;
            Ok(Value::Cons(Box::new(head), Box::new(rest)))
        }
        _ => Err(format!("unknown operator '{operator}'")),
    }
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
        Expr::Symbol(symbol) => eval_symbol(symbol),
        Expr::List(items) => {
            let mut result = Value::Nil;
            for item in items.iter().rev() {
                result = Value::Cons(Box::new(quote_expr(item)?), Box::new(result));
            }
            Ok(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Value, run_source};

    fn eval(source: &str) -> Value {
        run_source(source)
            .expect("program should succeed")
            .expect("program should produce a value")
    }

    #[test]
    fn atoms_self_evaluate() {
        assert_eq!(eval("hello"), Value::Atom("hello".to_string()));
    }

    #[test]
    fn quote_builds_lists() {
        assert_eq!(eval("(quote (a b c))").to_string(), "(a b c)");
        assert_eq!(eval("'(a b c)").to_string(), "(a b c)");
    }

    #[test]
    fn atom_and_atom_eq_work_on_atoms() {
        assert_eq!(eval("(atom (quote (a b)))"), Value::Bool(false));
        assert_eq!(eval("(atom hello)"), Value::Bool(true));
        assert_eq!(eval("(atom_eq hello hello)"), Value::Bool(true));
        assert_eq!(eval("(atom_eq true false)"), Value::Bool(false));
    }

    #[test]
    fn car_cdr_and_cons_work_on_lists() {
        assert_eq!(eval("(car '(a b c))"), Value::Atom("a".to_string()));
        assert_eq!(eval("(cdr '(a b c))").to_string(), "(b c)");
        assert_eq!(eval("(cons a '(b c))").to_string(), "(a b c)");
        assert_eq!(eval("(cons a b)").to_string(), "(a . b)");
    }

    #[test]
    fn if_uses_truthiness() {
        assert_eq!(eval("(if true yes no)"), Value::Atom("yes".to_string()));
        assert_eq!(eval("(if nil yes no)"), Value::Atom("no".to_string()));
        assert_eq!(eval("(if false yes no)"), Value::Atom("no".to_string()));
        assert_eq!(eval("(if maybe yes no)"), Value::Atom("yes".to_string()));
    }

    #[test]
    fn nil_is_the_empty_list() {
        assert_eq!(eval("(car nil)"), Value::Nil);
        assert_eq!(eval("(cdr nil)"), Value::Nil);
    }

    #[test]
    fn shebang_line_is_ignored() {
        let source = "#!/usr/bin/env click\n(cons a '(b c))\n";
        assert_eq!(eval(source).to_string(), "(a b c)");
    }

    #[test]
    fn multiple_top_level_forms_return_last_value() {
        assert_eq!(
            eval("hello\n(cons a nil)\n"),
            Value::Cons(Box::new(Value::Atom("a".to_string())), Box::new(Value::Nil))
        );
    }

    #[test]
    fn atom_eq_rejects_lists() {
        let error = run_source("(atom_eq '(a) '(a))").unwrap_err();
        assert!(error.contains("atom_eq expects atom arguments"));
    }
}
