use crate::reader::{SExpr, read as read_sexprs};
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

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
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
                write!(f, "(")?;
                let mut first = true;
                for (key, value) in &object.entries {
                    if !first {
                        write!(f, " ")?;
                    }
                    first = false;
                    write!(f, "{key} {value}")?;
                }
                write!(f, ")")
            }
        }
    }
}

pub fn parse(source: &str) -> ClickResult<Term> {
    let mut terms = parse_many(source)?;
    match terms.len() {
        0 => Err("expected one Click term, found none".to_string()),
        1 => Ok(terms.remove(0)),
        count => Err(format!("expected one Click term, found {count}")),
    }
}

pub fn parse_many(source: &str) -> ClickResult<Vec<Term>> {
    read_sexprs(source)?
        .into_iter()
        .map(parse_sexpr)
        .collect::<ClickResult<Vec<_>>>()
}

pub fn quote(value: Term) -> Term {
    tagged(":quote", value)
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

pub fn get(record: Term, key: impl Into<Symbol>) -> Term {
    tagged(
        ":get",
        Object::new()
            .with(":record", record)
            .with(":key", Term::symbol(key))
            .into(),
    )
}

pub fn with(record: Term, key: impl Into<Symbol>, value: Term) -> Term {
    tagged(
        ":with",
        Object::new()
            .with(":record", record)
            .with(":key", Term::symbol(key))
            .with(":value", value)
            .into(),
    )
}

pub fn has(record: Term, key: impl Into<Symbol>) -> Term {
    tagged(
        ":has",
        Object::new()
            .with(":record", record)
            .with(":key", Term::symbol(key))
            .into(),
    )
}

pub fn equal(left: Term, right: Term) -> Term {
    tagged(
        ":equal",
        Object::new()
            .with(":left", left)
            .with(":right", right)
            .into(),
    )
}

pub fn if_expr(cond: Term, then_expr: Term, else_expr: Term) -> Term {
    tagged(
        ":if",
        Object::new()
            .with(":cond", cond)
            .with(":then", then_expr)
            .with(":else", else_expr)
            .into(),
    )
}

pub fn empty_env() -> Term {
    Object::new().into()
}

pub fn halt() -> Term {
    Term::symbol(":halt")
}

pub fn initial_state(expr: Term) -> Term {
    eval_state(expr, empty_env(), halt())
}

pub fn eval_state(expr: Term, env: Term, continuation: Term) -> Term {
    tagged(
        ":eval",
        Object::new()
            .with(":expr", expr)
            .with(":env", env)
            .with(":continuation", continuation)
            .into(),
    )
}

pub fn continue_state(value: Term, continuation: Term) -> Term {
    tagged(
        ":continue",
        Object::new()
            .with(":value", value)
            .with(":continuation", continuation)
            .into(),
    )
}

pub fn closure(param: impl Into<Symbol>, body: Term, env: Term) -> Term {
    tagged(
        ":closure",
        Object::new()
            .with(":param", Term::symbol(param))
            .with(":body", body)
            .with(":env", env)
            .into(),
    )
}

pub fn cek_step(state: &Term) -> ClickResult<Term> {
    if let Some(payload) = tagged_payload(state, ":eval") {
        return step_eval(payload);
    }
    if let Some(payload) = tagged_payload(state, ":continue") {
        return step_continue(payload);
    }
    Ok(outcome_error(tagged(":bad_eval_state", state.clone())))
}

pub fn step(state: &Term) -> ClickResult<Term> {
    cek_step(state)
}

pub fn eval(expr: &Term) -> ClickResult<Term> {
    eval_in_env(expr, &empty_env())
}

pub fn eval_in_env(expr: &Term, env: &Term) -> ClickResult<Term> {
    let mut state = eval_state(expr.clone(), env.clone(), halt());
    loop {
        let outcome = cek_step(&state)?;
        if let Some(next) = tagged_payload(&outcome, ":next") {
            state = next.clone();
        } else if let Some(value) = tagged_payload(&outcome, ":return") {
            return Ok(value.clone());
        } else if let Some(info) = tagged_payload(&outcome, ":error") {
            return Err(info.to_string());
        } else {
            return Err(format!("malformed eval outcome {outcome}"));
        }
    }
}

pub fn equal_claim(left: Term, right: Term) -> Term {
    tagged(
        ":equal",
        Object::new()
            .with(":left", left)
            .with(":right", right)
            .into(),
    )
}

pub fn step_equals_claim(input: Term, output: Term) -> Term {
    tagged(
        ":step-equals",
        Object::new()
            .with(":input", input)
            .with(":output", output)
            .into(),
    )
}

pub fn returns_claim(input: Term, value: Term) -> Term {
    tagged(
        ":returns",
        Object::new()
            .with(":input", input)
            .with(":value", value)
            .into(),
    )
}

pub fn equal_structural_proof() -> Term {
    tagged(":equal-structural", Object::new().into())
}

pub fn step_proof() -> Term {
    tagged(":step", Object::new().into())
}

pub fn returns_return_proof(step_proof: Term, equal_proof: Term) -> Term {
    tagged(
        ":returns-return",
        Object::new()
            .with(":step", step_proof)
            .with(":equal", equal_proof)
            .into(),
    )
}

pub fn returns_next_proof(step_proof: Term, rest_proof: Term) -> Term {
    tagged(
        ":returns-next",
        Object::new()
            .with(":step", step_proof)
            .with(":rest", rest_proof)
            .into(),
    )
}

pub fn check(claim: &Term, proof: &Term) -> Term {
    match check_inner(claim, proof) {
        Ok(()) => Term::symbol(":ok"),
        Err(info) => outcome_error(info),
    }
}

fn step_eval(payload: &Term) -> ClickResult<Term> {
    let Some(fields) = payload.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_eval_state")));
    };
    let Some(expr) = fields.get(":expr") else {
        return Ok(outcome_error(Term::symbol(":bad_eval_state")));
    };
    let Some(env) = fields.get(":env") else {
        return Ok(outcome_error(Term::symbol(":bad_eval_state")));
    };
    let Some(continuation) = fields.get(":continuation") else {
        return Ok(outcome_error(Term::symbol(":bad_eval_state")));
    };

    match expr {
        Term::Symbol(_) => Ok(outcome_error(tagged(":not-an-expr", expr.clone()))),
        Term::Object(_) => {
            if let Some(value) = tagged_payload(expr, ":quote") {
                Ok(outcome_next(continue_state(
                    value.clone(),
                    continuation.clone(),
                )))
            } else if let Some(name) = tagged_payload(expr, ":var") {
                step_var(name, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":lambda") {
                step_lambda(details, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":apply") {
                step_apply(details, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":get") {
                step_get(details, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":with") {
                step_with(details, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":has") {
                step_has(details, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":equal") {
                step_equal(details, env, continuation)
            } else if let Some(details) = tagged_payload(expr, ":if") {
                step_if(details, env, continuation)
            } else {
                Ok(outcome_error(tagged(":not-an-expr", expr.clone())))
            }
        }
    }
}

fn step_var(name: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(name) = name.as_symbol() else {
        return Ok(outcome_error(Term::symbol(":bad_var")));
    };
    let Some(env) = env.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_env")));
    };
    match env.get(name.as_str()) {
        Some(value) => Ok(outcome_next(continue_state(
            value.clone(),
            continuation.clone(),
        ))),
        None => Ok(outcome_error(tagged(
            ":unbound",
            Term::symbol(name.clone()),
        ))),
    }
}

fn step_lambda(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_lambda")));
    };
    let Some(param) = details.get(":param") else {
        return Ok(outcome_error(Term::symbol(":bad_lambda")));
    };
    let Some(body) = details.get(":body") else {
        return Ok(outcome_error(Term::symbol(":bad_lambda")));
    };
    let Some(param) = param.as_symbol() else {
        return Ok(outcome_error(Term::symbol(":bad_lambda")));
    };
    Ok(outcome_next(continue_state(
        closure(param.clone(), body.clone(), env.clone()),
        continuation.clone(),
    )))
}

fn step_apply(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_apply")));
    };
    let Some(function) = details.get(":function") else {
        return Ok(outcome_error(Term::symbol(":bad_apply")));
    };
    let Some(arg) = details.get(":arg") else {
        return Ok(outcome_error(Term::symbol(":bad_apply")));
    };
    Ok(outcome_next(eval_state(
        function.clone(),
        env.clone(),
        after_function_cont(arg.clone(), env.clone(), continuation.clone()),
    )))
}

fn step_get(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_get")));
    };
    let Some(record) = details.get(":record") else {
        return Ok(outcome_error(Term::symbol(":bad_get")));
    };
    let Some(key) = details.get(":key") else {
        return Ok(outcome_error(Term::symbol(":bad_get")));
    };
    let Some(key) = key.as_symbol() else {
        return Ok(outcome_error(Term::symbol(":bad_get")));
    };
    Ok(outcome_next(eval_state(
        record.clone(),
        env.clone(),
        after_get_cont(key.clone(), continuation.clone()),
    )))
}

fn step_with(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_with")));
    };
    let Some(record) = details.get(":record") else {
        return Ok(outcome_error(Term::symbol(":bad_with")));
    };
    let Some(key) = details.get(":key") else {
        return Ok(outcome_error(Term::symbol(":bad_with")));
    };
    let Some(value) = details.get(":value") else {
        return Ok(outcome_error(Term::symbol(":bad_with")));
    };
    let Some(key) = key.as_symbol() else {
        return Ok(outcome_error(Term::symbol(":bad_with")));
    };
    Ok(outcome_next(eval_state(
        record.clone(),
        env.clone(),
        after_with_record_cont(
            key.clone(),
            value.clone(),
            env.clone(),
            continuation.clone(),
        ),
    )))
}

fn step_has(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_has")));
    };
    let Some(record) = details.get(":record") else {
        return Ok(outcome_error(Term::symbol(":bad_has")));
    };
    let Some(key) = details.get(":key") else {
        return Ok(outcome_error(Term::symbol(":bad_has")));
    };
    let Some(key) = key.as_symbol() else {
        return Ok(outcome_error(Term::symbol(":bad_has")));
    };
    Ok(outcome_next(eval_state(
        record.clone(),
        env.clone(),
        after_has_cont(key.clone(), continuation.clone()),
    )))
}

fn step_equal(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_equal")));
    };
    let Some(left) = details.get(":left") else {
        return Ok(outcome_error(Term::symbol(":bad_equal")));
    };
    let Some(right) = details.get(":right") else {
        return Ok(outcome_error(Term::symbol(":bad_equal")));
    };
    Ok(outcome_next(eval_state(
        left.clone(),
        env.clone(),
        after_equal_left_cont(right.clone(), env.clone(), continuation.clone()),
    )))
}

fn step_if(details: &Term, env: &Term, continuation: &Term) -> ClickResult<Term> {
    let Some(details) = details.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_if")));
    };
    let Some(cond) = details.get(":cond") else {
        return Ok(outcome_error(Term::symbol(":bad_if")));
    };
    let Some(then_expr) = details.get(":then") else {
        return Ok(outcome_error(Term::symbol(":bad_if")));
    };
    let Some(else_expr) = details.get(":else") else {
        return Ok(outcome_error(Term::symbol(":bad_if")));
    };
    Ok(outcome_next(eval_state(
        cond.clone(),
        env.clone(),
        after_if_cont(
            then_expr.clone(),
            else_expr.clone(),
            env.clone(),
            continuation.clone(),
        ),
    )))
}

fn step_continue(payload: &Term) -> ClickResult<Term> {
    let Some(fields) = payload.as_object() else {
        return Ok(outcome_error(Term::symbol(":bad_continue_state")));
    };
    let Some(value) = fields.get(":value") else {
        return Ok(outcome_error(Term::symbol(":bad_continue_state")));
    };
    let Some(continuation) = fields.get(":continuation") else {
        return Ok(outcome_error(Term::symbol(":bad_continue_state")));
    };

    if *continuation == halt() {
        return Ok(outcome_return(value.clone()));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-function") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(arg) = frame.get(":arg") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        return Ok(outcome_next(eval_state(
            arg.clone(),
            env.clone(),
            after_argument_cont(value.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-argument") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(function) = frame.get(":function") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        return Ok(apply_function_value(function, value, next));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-get") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = frame.get(":key") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = key.as_symbol() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        return Ok(get_record_field(value, key, next));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-with-record") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = frame.get(":key") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(value_expr) = frame.get(":value") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = key.as_symbol() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        if value.as_object().is_none() {
            return Ok(outcome_error(tagged(":not-a-record", value.clone())));
        }
        return Ok(outcome_next(eval_state(
            value_expr.clone(),
            env.clone(),
            after_with_value_cont(value.clone(), key.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-with-value") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(record) = frame.get(":record") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = frame.get(":key") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(record) = record.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = key.as_symbol() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        return Ok(outcome_next(continue_state(
            record.with(key.clone(), value.clone()).into(),
            next.clone(),
        )));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-has") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = frame.get(":key") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(key) = key.as_symbol() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let result = match value.as_object() {
            Some(record) if record.has(key.as_str()) => Term::symbol(":true"),
            _ => Term::symbol(":false"),
        };
        return Ok(outcome_next(continue_state(result, next.clone())));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-equal-left") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(right) = frame.get(":right") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        return Ok(outcome_next(eval_state(
            right.clone(),
            env.clone(),
            after_equal_right_cont(value.clone(), next.clone()),
        )));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-equal-right") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(left) = frame.get(":left") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let result = if left == value { ":true" } else { ":false" };
        return Ok(outcome_next(continue_state(
            Term::symbol(result),
            next.clone(),
        )));
    }

    if let Some(frame) = tagged_payload(continuation, ":after-if") {
        let Some(frame) = frame.as_object() else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(then_expr) = frame.get(":then-branch") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(else_expr) = frame.get(":else-branch") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(env) = frame.get(":env") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let Some(next) = frame.get(":then") else {
            return Ok(outcome_error(Term::symbol(":bad_continuation")));
        };
        let branch = if value == &Term::symbol(":true") {
            then_expr
        } else if value == &Term::symbol(":false") {
            else_expr
        } else {
            return Ok(outcome_error(tagged(":bad-condition", value.clone())));
        };
        return Ok(outcome_next(eval_state(
            branch.clone(),
            env.clone(),
            next.clone(),
        )));
    }

    Ok(outcome_error(Term::symbol(":bad_continuation")))
}

fn get_record_field(record: &Term, key: &Symbol, continuation: &Term) -> Term {
    let Some(record) = record.as_object() else {
        return outcome_error(tagged(":not-a-record", record.clone()));
    };
    let Some(value) = record.get(key.as_str()) else {
        return outcome_error(tagged(":missing-field", Term::symbol(key.clone())));
    };
    outcome_next(continue_state(value.clone(), continuation.clone()))
}

fn apply_function_value(function: &Term, arg: &Term, continuation: &Term) -> Term {
    let Some(details) = tagged_payload(function, ":closure") else {
        return outcome_error(tagged(":not-a-function", function.clone()));
    };
    let Some(details) = details.as_object() else {
        return outcome_error(Term::symbol(":bad_closure"));
    };
    let Some(param) = details.get(":param") else {
        return outcome_error(Term::symbol(":bad_closure"));
    };
    let Some(body) = details.get(":body") else {
        return outcome_error(Term::symbol(":bad_closure"));
    };
    let Some(env) = details.get(":env") else {
        return outcome_error(Term::symbol(":bad_closure"));
    };
    let Some(param) = param.as_symbol() else {
        return outcome_error(Term::symbol(":bad_closure"));
    };
    let Some(env) = env.as_object() else {
        return outcome_error(Term::symbol(":bad_closure"));
    };
    outcome_next(eval_state(
        body.clone(),
        env.with(param.clone(), arg.clone()).into(),
        continuation.clone(),
    ))
}

fn after_function_cont(arg: Term, env: Term, next: Term) -> Term {
    tagged(
        ":after-function",
        Object::new()
            .with(":arg", arg)
            .with(":env", env)
            .with(":then", next)
            .into(),
    )
}

fn after_argument_cont(function: Term, next: Term) -> Term {
    tagged(
        ":after-argument",
        Object::new()
            .with(":function", function)
            .with(":then", next)
            .into(),
    )
}

fn after_get_cont(key: Symbol, next: Term) -> Term {
    tagged(
        ":after-get",
        Object::new()
            .with(":key", Term::symbol(key))
            .with(":then", next)
            .into(),
    )
}

fn after_with_record_cont(key: Symbol, value: Term, env: Term, next: Term) -> Term {
    tagged(
        ":after-with-record",
        Object::new()
            .with(":key", Term::symbol(key))
            .with(":value", value)
            .with(":env", env)
            .with(":then", next)
            .into(),
    )
}

fn after_with_value_cont(record: Term, key: Symbol, next: Term) -> Term {
    tagged(
        ":after-with-value",
        Object::new()
            .with(":record", record)
            .with(":key", Term::symbol(key))
            .with(":then", next)
            .into(),
    )
}

fn after_has_cont(key: Symbol, next: Term) -> Term {
    tagged(
        ":after-has",
        Object::new()
            .with(":key", Term::symbol(key))
            .with(":then", next)
            .into(),
    )
}

fn after_equal_left_cont(right: Term, env: Term, next: Term) -> Term {
    tagged(
        ":after-equal-left",
        Object::new()
            .with(":right", right)
            .with(":env", env)
            .with(":then", next)
            .into(),
    )
}

fn after_equal_right_cont(left: Term, next: Term) -> Term {
    tagged(
        ":after-equal-right",
        Object::new().with(":left", left).with(":then", next).into(),
    )
}

fn after_if_cont(then_expr: Term, else_expr: Term, env: Term, next: Term) -> Term {
    tagged(
        ":after-if",
        Object::new()
            .with(":then-branch", then_expr)
            .with(":else-branch", else_expr)
            .with(":env", env)
            .with(":then", next)
            .into(),
    )
}

fn check_inner(claim: &Term, proof: &Term) -> Result<(), Term> {
    if let Some(payload) = tagged_payload(claim, ":equal") {
        return check_equal(payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":step-equals") {
        return check_step_equals(payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":returns") {
        return check_returns(payload, proof);
    }
    Err(tagged(":unknown-claim", claim.clone()))
}

fn check_equal(payload: &Term, proof: &Term) -> Result<(), Term> {
    require_empty_proof(proof, ":equal-structural")?;
    let fields = required_object(payload, ":bad_equal_claim")?;
    let left = required_field(fields, ":left", ":bad_equal_claim")?;
    let right = required_field(fields, ":right", ":bad_equal_claim")?;
    if left == right {
        Ok(())
    } else {
        Err(tagged(
            ":object-not-equal",
            Object::new()
                .with(":left", left.clone())
                .with(":right", right.clone())
                .into(),
        ))
    }
}

fn check_step_equals(payload: &Term, proof: &Term) -> Result<(), Term> {
    require_empty_proof(proof, ":step")?;
    let (input, expected) = step_claim_fields(payload)?;
    let actual = cek_step(input).map_err(Term::symbol)?;
    if &actual == expected {
        Ok(())
    } else {
        Err(tagged(
            ":step-mismatch",
            Object::new()
                .with(":actual", actual)
                .with(":expected", expected.clone())
                .into(),
        ))
    }
}

fn check_returns(payload: &Term, proof: &Term) -> Result<(), Term> {
    if let Some(details) = tagged_payload(proof, ":returns-return") {
        return check_returns_return(payload, details);
    }
    if let Some(details) = tagged_payload(proof, ":returns-next") {
        return check_returns_next(payload, details);
    }
    Err(tagged(":bad_proof", proof.clone()))
}

fn check_returns_return(payload: &Term, details: &Term) -> Result<(), Term> {
    let (input, expected) = returns_claim_fields(payload)?;
    let details = required_object(details, ":bad_returns_return_proof")?;
    let step_proof = required_field(details, ":step", ":bad_returns_return_proof")?;
    let equal_proof = required_field(details, ":equal", ":bad_returns_return_proof")?;
    let outcome = cek_step(input).map_err(Term::symbol)?;
    let Some(actual) = tagged_payload(&outcome, ":return") else {
        return Err(tagged(":expected-return", outcome));
    };
    let actual = actual.clone();
    check_inner(&step_equals_claim(input.clone(), outcome), step_proof)?;
    check_inner(&equal_claim(actual, expected.clone()), equal_proof)
}

fn check_returns_next(payload: &Term, details: &Term) -> Result<(), Term> {
    let (input, expected) = returns_claim_fields(payload)?;
    let details = required_object(details, ":bad_returns_next_proof")?;
    let step_proof = required_field(details, ":step", ":bad_returns_next_proof")?;
    let rest_proof = required_field(details, ":rest", ":bad_returns_next_proof")?;
    let outcome = cek_step(input).map_err(Term::symbol)?;
    let Some(next) = tagged_payload(&outcome, ":next") else {
        return Err(tagged(":expected-next", outcome));
    };
    let next = next.clone();
    check_inner(&step_equals_claim(input.clone(), outcome), step_proof)?;
    check_inner(&returns_claim(next, expected.clone()), rest_proof)
}

fn step_claim_fields(payload: &Term) -> Result<(&Term, &Term), Term> {
    let fields = required_object(payload, ":bad_step_claim")?;
    let input = required_field(fields, ":input", ":bad_step_claim")?;
    let output = required_field(fields, ":output", ":bad_step_claim")?;
    Ok((input, output))
}

fn returns_claim_fields(payload: &Term) -> Result<(&Term, &Term), Term> {
    let fields = required_object(payload, ":bad_returns_claim")?;
    let input = required_field(fields, ":input", ":bad_returns_claim")?;
    let value = required_field(fields, ":value", ":bad_returns_claim")?;
    Ok((input, value))
}

fn require_empty_proof(proof: &Term, tag: &str) -> Result<(), Term> {
    let Some(payload) = tagged_payload(proof, tag) else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    let Some(object) = payload.as_object() else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    if object.is_empty() {
        Ok(())
    } else {
        Err(tagged(":bad_proof", proof.clone()))
    }
}

fn required_object<'a>(term: &'a Term, error: &str) -> Result<&'a Object, Term> {
    term.as_object().ok_or_else(|| Term::symbol(error))
}

fn required_field<'a>(object: &'a Object, field: &str, error: &str) -> Result<&'a Term, Term> {
    object.get(field).ok_or_else(|| Term::symbol(error))
}

fn parse_sexpr(expr: SExpr) -> ClickResult<Term> {
    match expr {
        SExpr::Symbol(symbol) => Ok(Term::symbol(symbol.to_string())),
        SExpr::List(items) => parse_object(items),
    }
}

fn parse_object(items: Vec<SExpr>) -> ClickResult<Term> {
    if items.len() % 2 != 0 {
        return Err("objects must contain key/value pairs".to_string());
    }

    let mut object = Object::new();
    let mut items = items.into_iter();
    while let Some(key_expr) = items.next() {
        let value_expr = items
            .next()
            .expect("object parsing should advance in key/value pairs");
        let SExpr::Symbol(key) = key_expr else {
            return Err("object keys must be symbols".to_string());
        };
        let key = key.to_string();
        if object.has(&key) {
            return Err(format!("duplicate object key '{key}'"));
        }
        object = object.with(key, parse_sexpr(value_expr)?);
    }
    Ok(object.into())
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

fn outcome_next(next: Term) -> Term {
    tagged(":next", next)
}

fn outcome_return(value: Term) -> Term {
    tagged(":return", value)
}

fn outcome_error(info: Term) -> Term {
    tagged(":error", info)
}
