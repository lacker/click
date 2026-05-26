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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    claims: BTreeMap<Symbol, Term>,
    definitions: BTreeMap<Symbol, Term>,
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

impl Context {
    pub fn new() -> Self {
        Self {
            claims: BTreeMap::new(),
            definitions: BTreeMap::new(),
        }
    }

    pub fn with_claim(&self, name: impl Into<Symbol>, claim: Term) -> Self {
        let mut claims = self.claims.clone();
        claims.insert(name.into(), claim);
        Self {
            claims,
            definitions: self.definitions.clone(),
        }
    }

    pub fn with_definition(&self, name: impl Into<Symbol>, value: Term) -> Self {
        let mut definitions = self.definitions.clone();
        definitions.insert(name.into(), value);
        Self {
            claims: self.claims.clone(),
            definitions,
        }
    }

    pub fn get_claim(&self, name: &str) -> Option<&Term> {
        self.claims.get(name)
    }

    pub fn get_definition(&self, name: &str) -> Option<&Term> {
        self.definitions.get(name)
    }
}

impl Default for Context {
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

pub fn terminates_claim(input: Term) -> Term {
    tagged(":terminates", Object::new().with(":input", input).into())
}

pub fn true_claim() -> Term {
    tagged(":true", Object::new().into())
}

pub fn false_claim() -> Term {
    tagged(":false", Object::new().into())
}

pub fn and_claim(left: Term, right: Term) -> Term {
    tagged(
        ":and",
        Object::new()
            .with(":left", left)
            .with(":right", right)
            .into(),
    )
}

pub fn or_claim(left: Term, right: Term) -> Term {
    tagged(
        ":or",
        Object::new()
            .with(":left", left)
            .with(":right", right)
            .into(),
    )
}

pub fn not_claim(claim: Term) -> Term {
    tagged(":not", claim)
}

pub fn implies_claim(if_claim: Term, then_claim: Term) -> Term {
    tagged(
        ":implies",
        Object::new()
            .with(":if", if_claim)
            .with(":then", then_claim)
            .into(),
    )
}

pub fn forall_claim(var: impl Into<Symbol>, claim: Term) -> Term {
    tagged(
        ":forall",
        Object::new()
            .with(":var", Term::symbol(var))
            .with(":claim", claim)
            .into(),
    )
}

pub fn exists_claim(var: impl Into<Symbol>, claim: Term) -> Term {
    tagged(
        ":exists",
        Object::new()
            .with(":var", Term::symbol(var))
            .with(":claim", claim)
            .into(),
    )
}

pub fn logic_var(name: impl Into<Symbol>) -> Term {
    tagged(":logic-var", Term::symbol(name))
}

pub fn empty_context() -> Context {
    Context::new()
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

pub fn use_proof(name: impl Into<Symbol>) -> Term {
    tagged(":use", Term::symbol(name))
}

pub fn true_intro_proof() -> Term {
    tagged(":true-intro", Object::new().into())
}

pub fn false_elim_proof(proof: Term) -> Term {
    tagged(":false-elim", Object::new().with(":proof", proof).into())
}

pub fn and_intro_proof(left: Term, right: Term) -> Term {
    tagged(
        ":and-intro",
        Object::new()
            .with(":left", left)
            .with(":right", right)
            .into(),
    )
}

pub fn and_left_proof(proof: Term) -> Term {
    tagged(":and-left", proof)
}

pub fn and_right_proof(proof: Term) -> Term {
    tagged(":and-right", proof)
}

pub fn or_left_proof(proof: Term) -> Term {
    tagged(":or-left", proof)
}

pub fn or_right_proof(proof: Term) -> Term {
    tagged(":or-right", proof)
}

pub fn or_elim_proof(proof: Term, left: Term, right: Term) -> Term {
    tagged(
        ":or-elim",
        Object::new()
            .with(":proof", proof)
            .with(":left", left)
            .with(":right", right)
            .into(),
    )
}

pub fn not_intro_proof(assume: impl Into<Symbol>, body: Term) -> Term {
    tagged(
        ":not-intro",
        Object::new()
            .with(":assume", Term::symbol(assume))
            .with(":body", body)
            .into(),
    )
}

pub fn not_elim_proof(not_proof: Term, positive: Term) -> Term {
    tagged(
        ":not-elim",
        Object::new()
            .with(":not", not_proof)
            .with(":positive", positive)
            .into(),
    )
}

pub fn implies_intro_proof(assume: impl Into<Symbol>, body: Term) -> Term {
    tagged(
        ":implies-intro",
        Object::new()
            .with(":assume", Term::symbol(assume))
            .with(":body", body)
            .into(),
    )
}

pub fn implies_elim_proof(function: Term, arg: Term) -> Term {
    tagged(
        ":implies-elim",
        Object::new()
            .with(":function", function)
            .with(":arg", arg)
            .into(),
    )
}

pub fn forall_intro_proof(var: impl Into<Symbol>, body: Term) -> Term {
    tagged(
        ":forall-intro",
        Object::new()
            .with(":var", Term::symbol(var))
            .with(":body", body)
            .into(),
    )
}

pub fn forall_elim_proof(proof: Term, value: Term) -> Term {
    tagged(
        ":forall-elim",
        Object::new()
            .with(":proof", proof)
            .with(":value", value)
            .into(),
    )
}

pub fn exists_intro_proof(value: Term, proof: Term) -> Term {
    tagged(
        ":exists-intro",
        Object::new()
            .with(":value", value)
            .with(":proof", proof)
            .into(),
    )
}

pub fn exists_elim_proof(proof: Term, witness: impl Into<Symbol>, body: Term) -> Term {
    tagged(
        ":exists-elim",
        Object::new()
            .with(":proof", proof)
            .with(":witness", Term::symbol(witness))
            .with(":body", body)
            .into(),
    )
}

pub fn rewrite_proof(equal: Term, body: Term) -> Term {
    tagged(
        ":rewrite",
        Object::new()
            .with(":equal", equal)
            .with(":body", body)
            .into(),
    )
}

pub fn unfold_proof(name: impl Into<Symbol>) -> Term {
    tagged(":unfold", Term::symbol(name))
}

pub fn check(claim: &Term, proof: &Term) -> Term {
    check_in_context(&Context::new(), claim, proof)
}

pub fn check_in_context(context: &Context, claim: &Term, proof: &Term) -> Term {
    match check_inner(context, claim, proof) {
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

fn check_inner(context: &Context, claim: &Term, proof: &Term) -> Result<(), Term> {
    if check_inferred(context, claim, proof)? {
        return Ok(());
    }

    if let Some(name) = tagged_payload(proof, ":use") {
        return check_use(context, claim, name);
    }
    if let Some(details) = tagged_payload(proof, ":false-elim") {
        return check_false_elim(context, details);
    }
    if let Some(details) = tagged_payload(proof, ":or-elim") {
        return check_or_elim(context, claim, details);
    }
    if let Some(details) = tagged_payload(proof, ":exists-elim") {
        return check_exists_elim(context, claim, details);
    }
    if let Some(details) = tagged_payload(proof, ":rewrite") {
        return check_rewrite(context, claim, details);
    }
    if let Some(name) = tagged_payload(proof, ":unfold") {
        return check_unfold(context, claim, name);
    }

    if let Some(payload) = tagged_payload(claim, ":true") {
        return check_true(payload, proof);
    }
    if tagged_payload(claim, ":false").is_some() {
        return Err(tagged(":bad_proof", proof.clone()));
    }
    if let Some(payload) = tagged_payload(claim, ":equal") {
        return check_equal(payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":step-equals") {
        return check_step_equals(payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":returns") {
        return check_returns(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":terminates") {
        return check_terminates(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":and") {
        return check_and(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":or") {
        return check_or(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":not") {
        return check_not(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":implies") {
        return check_implies(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":forall") {
        return check_forall(context, payload, proof);
    }
    if let Some(payload) = tagged_payload(claim, ":exists") {
        return check_exists(context, payload, proof);
    }
    Err(tagged(":unknown-claim", claim.clone()))
}

fn check_inferred(context: &Context, claim: &Term, proof: &Term) -> Result<bool, Term> {
    match infer_claim(context, proof) {
        Ok(inferred) => Ok(&inferred == claim),
        Err(error) if tagged_payload(&error, ":cannot-infer").is_some() => Ok(false),
        Err(error) => Err(error),
    }
}

fn check_use(context: &Context, claim: &Term, name: &Term) -> Result<(), Term> {
    let Some(name) = name.as_symbol() else {
        return Err(tagged(":bad_use", name.clone()));
    };
    let Some(known) = context.get_claim(name.as_str()) else {
        return Err(tagged(":unknown-name", Term::symbol(name.clone())));
    };
    if known == claim {
        Ok(())
    } else {
        Err(tagged(
            ":claim-mismatch",
            Object::new()
                .with(":actual", known.clone())
                .with(":expected", claim.clone())
                .into(),
        ))
    }
}

fn check_true(payload: &Term, proof: &Term) -> Result<(), Term> {
    require_empty_payload(payload, ":bad_true_claim")?;
    require_empty_proof(proof, ":true-intro")
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

fn check_returns(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    if let Some(details) = tagged_payload(proof, ":returns-return") {
        return check_returns_return(context, payload, details);
    }
    if let Some(details) = tagged_payload(proof, ":returns-next") {
        return check_returns_next(context, payload, details);
    }
    Err(tagged(":bad_proof", proof.clone()))
}

fn check_returns_return(context: &Context, payload: &Term, details: &Term) -> Result<(), Term> {
    let (input, expected) = returns_claim_fields(payload)?;
    let details = required_object(details, ":bad_returns_return_proof")?;
    let step_proof = required_field(details, ":step", ":bad_returns_return_proof")?;
    let equal_proof = required_field(details, ":equal", ":bad_returns_return_proof")?;
    let outcome = cek_step(input).map_err(Term::symbol)?;
    let Some(actual) = tagged_payload(&outcome, ":return") else {
        return Err(tagged(":expected-return", outcome));
    };
    let actual = actual.clone();
    check_inner(
        context,
        &step_equals_claim(input.clone(), outcome),
        step_proof,
    )?;
    check_inner(context, &equal_claim(actual, expected.clone()), equal_proof)
}

fn check_returns_next(context: &Context, payload: &Term, details: &Term) -> Result<(), Term> {
    let (input, expected) = returns_claim_fields(payload)?;
    let details = required_object(details, ":bad_returns_next_proof")?;
    let step_proof = required_field(details, ":step", ":bad_returns_next_proof")?;
    let rest_proof = required_field(details, ":rest", ":bad_returns_next_proof")?;
    let outcome = cek_step(input).map_err(Term::symbol)?;
    let Some(next) = tagged_payload(&outcome, ":next") else {
        return Err(tagged(":expected-next", outcome));
    };
    let next = next.clone();
    check_inner(
        context,
        &step_equals_claim(input.clone(), outcome),
        step_proof,
    )?;
    check_inner(context, &returns_claim(next, expected.clone()), rest_proof)
}

fn check_terminates(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    let fields = required_object(payload, ":bad_terminates_claim")?;
    let input = required_field(fields, ":input", ":bad_terminates_claim")?;
    let value_var = Symbol::from(":value");
    let claim = exists_claim(
        value_var.clone(),
        returns_claim(input.clone(), logic_var(value_var)),
    );
    check_inner(context, &claim, proof)
}

fn check_and(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    let fields = required_object(payload, ":bad_and_claim")?;
    let left = required_field(fields, ":left", ":bad_and_claim")?;
    let right = required_field(fields, ":right", ":bad_and_claim")?;
    let Some(details) = tagged_payload(proof, ":and-intro") else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    let details = required_object(details, ":bad_and_intro_proof")?;
    let left_proof = required_field(details, ":left", ":bad_and_intro_proof")?;
    let right_proof = required_field(details, ":right", ":bad_and_intro_proof")?;
    check_inner(context, left, left_proof)?;
    check_inner(context, right, right_proof)
}

fn check_or(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    let fields = required_object(payload, ":bad_or_claim")?;
    let left = required_field(fields, ":left", ":bad_or_claim")?;
    let right = required_field(fields, ":right", ":bad_or_claim")?;
    if let Some(left_proof) = tagged_payload(proof, ":or-left") {
        return check_inner(context, left, left_proof);
    }
    if let Some(right_proof) = tagged_payload(proof, ":or-right") {
        return check_inner(context, right, right_proof);
    }
    Err(tagged(":bad_proof", proof.clone()))
}

fn check_not(context: &Context, claim: &Term, proof: &Term) -> Result<(), Term> {
    let Some(details) = tagged_payload(proof, ":not-intro") else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    let details = required_object(details, ":bad_not_intro_proof")?;
    let assume = required_symbol_field(details, ":assume", ":bad_not_intro_proof")?;
    let body = required_field(details, ":body", ":bad_not_intro_proof")?;
    let context = context.with_claim(assume.clone(), claim.clone());
    check_inner(&context, &false_claim(), body)
}

fn check_implies(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    let fields = required_object(payload, ":bad_implies_claim")?;
    let if_claim = required_field(fields, ":if", ":bad_implies_claim")?;
    let then_claim = required_field(fields, ":then", ":bad_implies_claim")?;
    let Some(details) = tagged_payload(proof, ":implies-intro") else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    let details = required_object(details, ":bad_implies_intro_proof")?;
    let assume = required_symbol_field(details, ":assume", ":bad_implies_intro_proof")?;
    let body = required_field(details, ":body", ":bad_implies_intro_proof")?;
    let context = context.with_claim(assume.clone(), if_claim.clone());
    check_inner(&context, then_claim, body)
}

fn check_forall(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    let fields = required_object(payload, ":bad_forall_claim")?;
    let claim_var = required_symbol_field(fields, ":var", ":bad_forall_claim")?;
    let claim_body = required_field(fields, ":claim", ":bad_forall_claim")?;
    let Some(details) = tagged_payload(proof, ":forall-intro") else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    let details = required_object(details, ":bad_forall_intro_proof")?;
    let proof_var = required_symbol_field(details, ":var", ":bad_forall_intro_proof")?;
    let body = required_field(details, ":body", ":bad_forall_intro_proof")?;
    let target = substitute_logic_var(claim_body, claim_var, &logic_var(proof_var.clone()));
    check_inner(context, &target, body)
}

fn check_exists(context: &Context, payload: &Term, proof: &Term) -> Result<(), Term> {
    let fields = required_object(payload, ":bad_exists_claim")?;
    let var = required_symbol_field(fields, ":var", ":bad_exists_claim")?;
    let claim = required_field(fields, ":claim", ":bad_exists_claim")?;
    let Some(details) = tagged_payload(proof, ":exists-intro") else {
        return Err(tagged(":bad_proof", proof.clone()));
    };
    let details = required_object(details, ":bad_exists_intro_proof")?;
    let value = required_field(details, ":value", ":bad_exists_intro_proof")?;
    let proof = required_field(details, ":proof", ":bad_exists_intro_proof")?;
    let target = substitute_logic_var(claim, var, value);
    check_inner(context, &target, proof)
}

fn check_false_elim(context: &Context, details: &Term) -> Result<(), Term> {
    let details = required_object(details, ":bad_false_elim_proof")?;
    let proof = required_field(details, ":proof", ":bad_false_elim_proof")?;
    check_inner(context, &false_claim(), proof)
}

fn check_or_elim(context: &Context, claim: &Term, details: &Term) -> Result<(), Term> {
    let details = required_object(details, ":bad_or_elim_proof")?;
    let proof = required_field(details, ":proof", ":bad_or_elim_proof")?;
    let left_proof = required_field(details, ":left", ":bad_or_elim_proof")?;
    let right_proof = required_field(details, ":right", ":bad_or_elim_proof")?;
    let disjunction = infer_claim(context, proof)?;
    let Some(payload) = tagged_payload(&disjunction, ":or") else {
        return Err(tagged(":expected-or", disjunction));
    };
    let fields = required_object(payload, ":bad_or_claim")?;
    let left = required_field(fields, ":left", ":bad_or_claim")?;
    let right = required_field(fields, ":right", ":bad_or_claim")?;
    check_inner(
        context,
        &implies_claim(left.clone(), claim.clone()),
        left_proof,
    )?;
    check_inner(
        context,
        &implies_claim(right.clone(), claim.clone()),
        right_proof,
    )
}

fn check_exists_elim(context: &Context, claim: &Term, details: &Term) -> Result<(), Term> {
    let details = required_object(details, ":bad_exists_elim_proof")?;
    let proof = required_field(details, ":proof", ":bad_exists_elim_proof")?;
    let witness = required_symbol_field(details, ":witness", ":bad_exists_elim_proof")?;
    let body = required_field(details, ":body", ":bad_exists_elim_proof")?;
    let exists_claim = infer_claim(context, proof)?;
    let Some(payload) = tagged_payload(&exists_claim, ":exists") else {
        return Err(tagged(":expected-exists", exists_claim));
    };
    let fields = required_object(payload, ":bad_exists_claim")?;
    let var = required_symbol_field(fields, ":var", ":bad_exists_claim")?;
    let body_claim = required_field(fields, ":claim", ":bad_exists_claim")?;
    let witness_claim = substitute_logic_var(body_claim, var, &logic_var(witness.clone()));
    let context = context.with_claim(witness.clone(), witness_claim);
    check_inner(&context, claim, body)
}

fn check_rewrite(context: &Context, claim: &Term, details: &Term) -> Result<(), Term> {
    let details = required_object(details, ":bad_rewrite_proof")?;
    let equal_proof = required_field(details, ":equal", ":bad_rewrite_proof")?;
    let body = required_field(details, ":body", ":bad_rewrite_proof")?;
    let equality = infer_claim(context, equal_proof)?;
    let Some(payload) = tagged_payload(&equality, ":equal") else {
        return Err(tagged(":expected-equality", equality));
    };
    let fields = required_object(payload, ":bad_equal_claim")?;
    let left = required_field(fields, ":left", ":bad_equal_claim")?;
    let right = required_field(fields, ":right", ":bad_equal_claim")?;
    let left_to_right = replace_term(claim, left, right);
    if check_inner(context, &left_to_right, body).is_ok() {
        return Ok(());
    }
    let right_to_left = replace_term(claim, right, left);
    check_inner(context, &right_to_left, body)
}

fn check_unfold(context: &Context, claim: &Term, name: &Term) -> Result<(), Term> {
    let Some(name) = name.as_symbol() else {
        return Err(tagged(":bad_unfold", name.clone()));
    };
    let Some(definition) = context.get_definition(name.as_str()) else {
        return Err(tagged(":unknown-name", Term::symbol(name.clone())));
    };
    let name = Term::symbol(name.clone());
    check_inner(context, claim, &equal_structural_proof()).or_else(|_| {
        if claim == &equal_claim(name.clone(), definition.clone())
            || claim == &equal_claim(definition.clone(), name)
        {
            Ok(())
        } else {
            Err(tagged(":bad_unfold_target", claim.clone()))
        }
    })
}

fn infer_claim(context: &Context, proof: &Term) -> Result<Term, Term> {
    if let Some(name) = tagged_payload(proof, ":use") {
        let Some(name) = name.as_symbol() else {
            return Err(tagged(":bad_use", name.clone()));
        };
        return context
            .get_claim(name.as_str())
            .cloned()
            .ok_or_else(|| tagged(":unknown-name", Term::symbol(name.clone())));
    }
    if let Some(payload) = tagged_payload(proof, ":true-intro") {
        require_empty_payload(payload, ":bad_true_intro_proof")?;
        return Ok(true_claim());
    }
    if let Some(details) = tagged_payload(proof, ":and-intro") {
        let details = required_object(details, ":bad_and_intro_proof")?;
        let left = infer_claim(
            context,
            required_field(details, ":left", ":bad_and_intro_proof")?,
        )?;
        let right = infer_claim(
            context,
            required_field(details, ":right", ":bad_and_intro_proof")?,
        )?;
        return Ok(and_claim(left, right));
    }
    if let Some(proof) = tagged_payload(proof, ":and-left") {
        let claim = infer_claim(context, proof)?;
        let Some(payload) = tagged_payload(&claim, ":and") else {
            return Err(tagged(":expected-and", claim));
        };
        let fields = required_object(payload, ":bad_and_claim")?;
        return Ok(required_field(fields, ":left", ":bad_and_claim")?.clone());
    }
    if let Some(proof) = tagged_payload(proof, ":and-right") {
        let claim = infer_claim(context, proof)?;
        let Some(payload) = tagged_payload(&claim, ":and") else {
            return Err(tagged(":expected-and", claim));
        };
        let fields = required_object(payload, ":bad_and_claim")?;
        return Ok(required_field(fields, ":right", ":bad_and_claim")?.clone());
    }
    if let Some(details) = tagged_payload(proof, ":not-elim") {
        let details = required_object(details, ":bad_not_elim_proof")?;
        let not_proof = required_field(details, ":not", ":bad_not_elim_proof")?;
        let positive = required_field(details, ":positive", ":bad_not_elim_proof")?;
        let not_claim = infer_claim(context, not_proof)?;
        let Some(positive_claim) = tagged_payload(&not_claim, ":not") else {
            return Err(tagged(":expected-not", not_claim));
        };
        check_inner(context, positive_claim, positive)?;
        return Ok(false_claim());
    }
    if let Some(details) = tagged_payload(proof, ":implies-elim") {
        let details = required_object(details, ":bad_implies_elim_proof")?;
        let function = required_field(details, ":function", ":bad_implies_elim_proof")?;
        let arg = required_field(details, ":arg", ":bad_implies_elim_proof")?;
        let function_claim = infer_claim(context, function)?;
        let Some(payload) = tagged_payload(&function_claim, ":implies") else {
            return Err(tagged(":expected-implies", function_claim));
        };
        let fields = required_object(payload, ":bad_implies_claim")?;
        let if_claim = required_field(fields, ":if", ":bad_implies_claim")?;
        let then_claim = required_field(fields, ":then", ":bad_implies_claim")?;
        check_inner(context, if_claim, arg)?;
        return Ok(then_claim.clone());
    }
    if let Some(details) = tagged_payload(proof, ":forall-elim") {
        let details = required_object(details, ":bad_forall_elim_proof")?;
        let proof = required_field(details, ":proof", ":bad_forall_elim_proof")?;
        let value = required_field(details, ":value", ":bad_forall_elim_proof")?;
        let claim = infer_claim(context, proof)?;
        let Some(payload) = tagged_payload(&claim, ":forall") else {
            return Err(tagged(":expected-forall", claim));
        };
        let fields = required_object(payload, ":bad_forall_claim")?;
        let var = required_symbol_field(fields, ":var", ":bad_forall_claim")?;
        let body = required_field(fields, ":claim", ":bad_forall_claim")?;
        return Ok(substitute_logic_var(body, var, value));
    }
    Err(tagged(":cannot-infer", proof.clone()))
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

fn required_symbol_field<'a>(
    object: &'a Object,
    field: &str,
    error: &str,
) -> Result<&'a Symbol, Term> {
    required_field(object, field, error)?
        .as_symbol()
        .ok_or_else(|| Term::symbol(error))
}

fn require_empty_payload(payload: &Term, error: &str) -> Result<(), Term> {
    let object = required_object(payload, error)?;
    if object.is_empty() {
        Ok(())
    } else {
        Err(Term::symbol(error))
    }
}

fn substitute_logic_var(term: &Term, var: &Symbol, replacement: &Term) -> Term {
    if let Some(name) = tagged_payload(term, ":logic-var").and_then(Term::as_symbol) {
        if name == var {
            return replacement.clone();
        }
    }

    match term {
        Term::Symbol(_) => term.clone(),
        Term::Object(object) => {
            let mut substituted = Object::new();
            for (key, value) in &object.entries {
                substituted =
                    substituted.with(key.clone(), substitute_logic_var(value, var, replacement));
            }
            substituted.into()
        }
    }
}

fn replace_term(term: &Term, from: &Term, to: &Term) -> Term {
    if term == from {
        return to.clone();
    }

    match term {
        Term::Symbol(_) => term.clone(),
        Term::Object(object) => {
            let mut replaced = Object::new();
            for (key, value) in &object.entries {
                replaced = replaced.with(key.clone(), replace_term(value, from, to));
            }
            replaced.into()
        }
    }
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
