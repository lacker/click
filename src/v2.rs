use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::fmt;

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Object {
    entries: BTreeMap<Symbol, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Symbol(Symbol),
    Object(Object),
}

impl Symbol {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

impl From<String> for Symbol {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Object {
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&Term> {
        self.entries.get(key)
    }

    pub fn has(&self, key: &str) -> bool {
        self.entries.contains_key(key)
    }

    pub fn with(&self, key: impl Into<Symbol>, value: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(key.into(), value);
        Self { entries }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

impl Default for Object {
    fn default() -> Self {
        Self::new()
    }
}

impl Term {
    pub fn symbol(value: impl Into<Symbol>) -> Self {
        Self::Symbol(value.into())
    }

    pub fn object(object: Object) -> Self {
        Self::Object(object)
    }

    pub fn as_symbol(&self) -> Option<&Symbol> {
        match self {
            Term::Symbol(symbol) => Some(symbol),
            Term::Object(_) => None,
        }
    }

    pub fn as_object(&self) -> Option<&Object> {
        match self {
            Term::Symbol(_) => None,
            Term::Object(object) => Some(object),
        }
    }
}

impl From<Symbol> for Term {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}

impl From<Object> for Term {
    fn from(value: Object) -> Self {
        Self::Object(value)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Symbol(symbol) => write!(f, "{symbol}"),
            Term::Object(object) => {
                write!(f, "{{")?;
                let mut first = true;
                for (key, value) in &object.entries {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{key} {value}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

pub fn var(name: impl Into<Symbol>) -> Term {
    tagged(":var", Term::symbol(name))
}

pub fn lambda(param: impl Into<Symbol>, body: Term) -> Term {
    tagged(
        ":lambda",
        Object::new()
            .with(":param", Term::symbol(param))
            .with(":body", body)
            .into(),
    )
}

pub fn apply(function: Term, arg: Term) -> Term {
    tagged(
        ":apply",
        Object::new()
            .with(":function", function)
            .with(":arg", arg)
            .into(),
    )
}

pub fn r#match(handlers: Term, value: Term) -> Term {
    tagged(
        ":match",
        Object::new()
            .with(":handlers", handlers)
            .with(":value", value)
            .into(),
    )
}

pub fn set(object: Term, key: Term, value: Term) -> Term {
    tagged(
        ":set",
        Object::new()
            .with(":object", object)
            .with(":key", key)
            .with(":value", value)
            .into(),
    )
}

pub fn empty_env() -> Term {
    Object::new().into()
}

pub fn initial_state(expr: Term) -> Term {
    eval_state(expr, empty_env(), halt())
}

pub fn eval_state(expr: Term, env: Term, cont: Term) -> Term {
    tagged(
        ":eval",
        Object::new()
            .with(":expr", expr)
            .with(":env", env)
            .with(":cont", cont)
            .into(),
    )
}

pub fn return_state(value: Term, cont: Term) -> Term {
    tagged(
        ":ret",
        Object::new()
            .with(":value", value)
            .with(":cont", cont)
            .into(),
    )
}

pub fn halt() -> Term {
    Term::symbol(":halt")
}

fn apply_function_cont(arg: Term, env: Term, next: Term) -> Term {
    tagged(
        ":apply_function",
        Object::new()
            .with(":arg", arg)
            .with(":env", env)
            .with(":next", next)
            .into(),
    )
}

fn apply_argument_cont(function: Term, next: Term) -> Term {
    tagged(
        ":apply_argument",
        Object::new()
            .with(":function", function)
            .with(":next", next)
            .into(),
    )
}

fn set_object_cont(key: Term, value: Term, env: Term, next: Term) -> Term {
    tagged(
        ":set_object",
        Object::new()
            .with(":key", key)
            .with(":value", value)
            .with(":env", env)
            .with(":next", next)
            .into(),
    )
}

fn set_key_cont(object: Term, value: Term, env: Term, next: Term) -> Term {
    tagged(
        ":set_key",
        Object::new()
            .with(":object", object)
            .with(":value", value)
            .with(":env", env)
            .with(":next", next)
            .into(),
    )
}

fn set_value_cont(object: Term, key: Term, next: Term) -> Term {
    tagged(
        ":set_value",
        Object::new()
            .with(":object", object)
            .with(":key", key)
            .with(":next", next)
            .into(),
    )
}

fn match_handlers_cont(value: Term, env: Term, next: Term) -> Term {
    tagged(
        ":match_handlers",
        Object::new()
            .with(":value", value)
            .with(":env", env)
            .with(":next", next)
            .into(),
    )
}

fn match_value_cont(handlers: Term, env: Term, next: Term) -> Term {
    tagged(
        ":match_value",
        Object::new()
            .with(":handlers", handlers)
            .with(":env", env)
            .with(":next", next)
            .into(),
    )
}

fn match_apply_cont(payload: Term, next: Term) -> Term {
    tagged(
        ":match_apply",
        Object::new()
            .with(":payload", payload)
            .with(":next", next)
            .into(),
    )
}

pub fn step(state: &Term) -> ClickResult<Term> {
    if let Some(payload) = tagged_payload(state, ":eval") {
        return step_eval(payload);
    }
    if let Some(payload) = tagged_payload(state, ":ret") {
        return step_return(payload);
    }
    Ok(response_error(Term::symbol(":bad_state")))
}

pub fn eval(expr: &Term) -> ClickResult<Term> {
    eval_in_env(expr, &empty_env())
}

pub fn eval_in_env(expr: &Term, env: &Term) -> ClickResult<Term> {
    let mut state = eval_state(expr.clone(), env.clone(), halt());
    loop {
        let response = step(&state)?;
        if let Some(next) = tagged_payload(&response, ":continue") {
            state = next.clone();
        } else if let Some(value) = tagged_payload(&response, ":return") {
            return Ok(value.clone());
        } else if let Some(info) = tagged_payload(&response, ":error") {
            return Err(info.to_string());
        } else {
            return Err(format!("malformed step response {response}"));
        }
    }
}

fn step_eval(payload: &Term) -> ClickResult<Term> {
    let Some(fields) = payload.as_object() else {
        return Ok(response_error(Term::symbol(":bad_eval_state")));
    };
    let Some(expr) = fields.get(":expr") else {
        return Ok(response_error(Term::symbol(":bad_eval_state")));
    };
    let Some(env) = fields.get(":env") else {
        return Ok(response_error(Term::symbol(":bad_eval_state")));
    };
    let Some(cont) = fields.get(":cont") else {
        return Ok(response_error(Term::symbol(":bad_eval_state")));
    };

    match expr {
        Term::Symbol(_) => Ok(response_continue(return_state(expr.clone(), cont.clone()))),
        Term::Object(object) => {
            if let Some(name) = tagged_payload(expr, ":var") {
                let Some(name) = name.as_symbol() else {
                    return Ok(response_error(Term::symbol(":bad_var")));
                };
                let Some(env) = env.as_object() else {
                    return Ok(response_error(Term::symbol(":bad_env")));
                };
                match env.get(name.as_str()) {
                    Some(value) => Ok(response_continue(return_state(value.clone(), cont.clone()))),
                    None => Ok(response_error(Term::symbol(":unbound"))),
                }
            } else if let Some(details) = tagged_payload(expr, ":lambda") {
                let Some(details) = details.as_object() else {
                    return Ok(response_error(Term::symbol(":bad_lambda")));
                };
                let Some(param) = details.get(":param") else {
                    return Ok(response_error(Term::symbol(":bad_lambda")));
                };
                let Some(body) = details.get(":body") else {
                    return Ok(response_error(Term::symbol(":bad_lambda")));
                };
                if param.as_symbol().is_none() {
                    return Ok(response_error(Term::symbol(":bad_lambda")));
                }
                let closure = tagged(
                    ":closure",
                    Object::new()
                        .with(":param", param.clone())
                        .with(":body", body.clone())
                        .with(":env", env.clone())
                        .into(),
                );
                Ok(response_continue(return_state(closure, cont.clone())))
            } else if let Some(details) = tagged_payload(expr, ":apply") {
                let Some(details) = details.as_object() else {
                    return Ok(response_error(Term::symbol(":bad_apply")));
                };
                let Some(function) = details.get(":function") else {
                    return Ok(response_error(Term::symbol(":bad_apply")));
                };
                let Some(arg) = details.get(":arg") else {
                    return Ok(response_error(Term::symbol(":bad_apply")));
                };
                Ok(response_continue(eval_state(
                    function.clone(),
                    env.clone(),
                    apply_function_cont(arg.clone(), env.clone(), cont.clone()),
                )))
            } else if let Some(details) = tagged_payload(expr, ":set") {
                let Some(details) = details.as_object() else {
                    return Ok(response_error(Term::symbol(":bad_set")));
                };
                let Some(object_expr) = details.get(":object") else {
                    return Ok(response_error(Term::symbol(":bad_set")));
                };
                let Some(key_expr) = details.get(":key") else {
                    return Ok(response_error(Term::symbol(":bad_set")));
                };
                let Some(value_expr) = details.get(":value") else {
                    return Ok(response_error(Term::symbol(":bad_set")));
                };
                Ok(response_continue(eval_state(
                    object_expr.clone(),
                    env.clone(),
                    set_object_cont(
                        key_expr.clone(),
                        value_expr.clone(),
                        env.clone(),
                        cont.clone(),
                    ),
                )))
            } else if let Some(details) = tagged_payload(expr, ":match") {
                let Some(details) = details.as_object() else {
                    return Ok(response_error(Term::symbol(":bad_match")));
                };
                let Some(handlers_expr) = details.get(":handlers") else {
                    return Ok(response_error(Term::symbol(":bad_match")));
                };
                let Some(value_expr) = details.get(":value") else {
                    return Ok(response_error(Term::symbol(":bad_match")));
                };
                Ok(response_continue(eval_state(
                    handlers_expr.clone(),
                    env.clone(),
                    match_handlers_cont(value_expr.clone(), env.clone(), cont.clone()),
                )))
            } else {
                let _ = object;
                Ok(response_continue(return_state(expr.clone(), cont.clone())))
            }
        }
    }
}

fn step_return(payload: &Term) -> ClickResult<Term> {
    let Some(fields) = payload.as_object() else {
        return Ok(response_error(Term::symbol(":bad_return_state")));
    };
    let Some(value) = fields.get(":value") else {
        return Ok(response_error(Term::symbol(":bad_return_state")));
    };
    let Some(cont) = fields.get(":cont") else {
        return Ok(response_error(Term::symbol(":bad_return_state")));
    };

    if *cont == halt() {
        return Ok(response_return(value.clone()));
    }

    if let Some(frame) = tagged_payload(cont, ":apply_function") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(arg) = frame.get(":arg") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        return Ok(response_continue(eval_state(
            arg.clone(),
            env.clone(),
            apply_argument_cont(value.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(cont, ":apply_argument") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(function) = frame.get(":function") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        return Ok(apply_function_value(function, value, next));
    }

    if let Some(frame) = tagged_payload(cont, ":set_object") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(key) = frame.get(":key") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(value_expr) = frame.get(":value") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        return Ok(response_continue(eval_state(
            key.clone(),
            env.clone(),
            set_key_cont(value.clone(), value_expr.clone(), env.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(cont, ":set_key") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(object) = frame.get(":object") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(value_expr) = frame.get(":value") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        return Ok(response_continue(eval_state(
            value_expr.clone(),
            env.clone(),
            set_value_cont(object.clone(), value.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(cont, ":set_value") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(object) = frame.get(":object") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(key) = frame.get(":key") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(object) = object.as_object() else {
            return Ok(response_error(Term::symbol(":set_non_object")));
        };
        let Some(key) = key.as_symbol() else {
            return Ok(response_error(Term::symbol(":set_non_symbol_key")));
        };
        return Ok(response_continue(return_state(
            object.with(key.clone(), value.clone()).into(),
            next.clone(),
        )));
    }

    if let Some(frame) = tagged_payload(cont, ":match_handlers") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(value_expr) = frame.get(":value") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        return Ok(response_continue(eval_state(
            value_expr.clone(),
            env.clone(),
            match_value_cont(value.clone(), env.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(cont, ":match_value") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(handlers) = frame.get(":handlers") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(handlers) = handlers.as_object() else {
            return Ok(response_error(Term::symbol(":match_handlers_not_object")));
        };
        let Some(value_object) = value.as_object() else {
            return Ok(response_error(Term::symbol(":match_value_not_object")));
        };
        let mut overlap = None;
        for (key, handler) in &handlers.entries {
            if let Some(payload) = value_object.get(key.as_str()) {
                if overlap.is_some() {
                    return Ok(response_error(Term::symbol(":match_ambiguous")));
                }
                overlap = Some((handler.clone(), payload.clone()));
            }
        }
        let Some((handler, payload)) = overlap else {
            return Ok(response_error(Term::symbol(":match_none")));
        };
        return Ok(response_continue(eval_state(
            handler,
            env.clone(),
            match_apply_cont(payload, next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(cont, ":match_apply") {
        let Some(frame) = frame.as_object() else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(payload) = frame.get(":payload") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        let Some(next) = frame.get(":next") else {
            return Ok(response_error(Term::symbol(":bad_cont")));
        };
        return Ok(apply_function_value(value, payload, next));
    }

    Ok(response_error(Term::symbol(":bad_cont")))
}

fn apply_function_value(function: &Term, arg: &Term, next: &Term) -> Term {
    let Some(details) = tagged_payload(function, ":closure") else {
        return response_error(Term::symbol(":apply_non_closure"));
    };
    let Some(details) = details.as_object() else {
        return response_error(Term::symbol(":bad_closure"));
    };
    let Some(param) = details.get(":param") else {
        return response_error(Term::symbol(":bad_closure"));
    };
    let Some(body) = details.get(":body") else {
        return response_error(Term::symbol(":bad_closure"));
    };
    let Some(env) = details.get(":env") else {
        return response_error(Term::symbol(":bad_closure"));
    };
    let Some(param) = param.as_symbol() else {
        return response_error(Term::symbol(":bad_closure"));
    };
    let Some(env) = env.as_object() else {
        return response_error(Term::symbol(":bad_closure"));
    };
    response_continue(eval_state(
        body.clone(),
        env.with(param.clone(), arg.clone()).into(),
        next.clone(),
    ))
}

fn tagged(tag: &str, payload: Term) -> Term {
    Object::new().with(tag, payload).into()
}

fn tagged_payload<'a>(term: &'a Term, tag: &str) -> Option<&'a Term> {
    let object = term.as_object()?;
    if object.len() != 1 {
        return None;
    }
    object.get(tag)
}

fn response_continue(next: Term) -> Term {
    tagged(":continue", next)
}

fn response_return(value: Term) -> Term {
    tagged(":return", value)
}

fn response_error(info: Term) -> Term {
    tagged(":error", info)
}
