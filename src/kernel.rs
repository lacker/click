use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::reader::read;

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    names: BTreeMap<Symbol, Name>,
    values: BTreeMap<Name, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Object {
    entries: BTreeMap<Symbol, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeMap {
    entries: BTreeMap<Name, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    Def {
        name: Name,
        value: Term,
    },
    Check {
        actual: Term,
        expected: Term,
    },
    Theorem {
        name: Name,
        actual: Term,
        expected: Term,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    id: usize,
    symbol: Symbol,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term(TermKind);

#[derive(Clone, Debug, PartialEq, Eq)]
enum TermKind {
    Type,
    BoolType,
    NilType,
    ObjectType(Object),
    Arrow {
        arg_type: Box<Term>,
        return_type: Box<Term>,
    },
    Nil,
    Bool(bool),
    Object(Object),
    Var(Name),
    If {
        condition: Box<Term>,
        then_branch: Box<Term>,
        else_branch: Box<Term>,
    },
    Lambda {
        binder: Name,
        body: Box<Term>,
    },
    App {
        function: Box<Term>,
        arg: Box<Term>,
    },
    Get {
        object: Box<Term>,
        key: Symbol,
    },
    With {
        object: Box<Term>,
        key: Symbol,
        value: Box<Term>,
    },
    Has {
        object: Box<Term>,
        key: Symbol,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SExpr {
    Symbol(Symbol),
    List(Vec<SExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepResult {
    Value(Term),
    Reduced(Term),
}

static NEXT_NAME_ID: AtomicUsize = AtomicUsize::new(0);

impl Symbol {
    fn as_str(&self) -> &str {
        &self.0
    }
}

impl Name {
    pub fn fresh(symbol: Symbol) -> Self {
        Self {
            id: NEXT_NAME_ID.fetch_add(1, Ordering::Relaxed),
            symbol,
        }
    }

    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }
}

impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl From<String> for Symbol {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.symbol.fmt(f)
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
    pub fn get(&self, name: &str) -> Option<&Term> {
        self.entries.get(name)
    }

    // Return a new object with one key updated or inserted.
    pub fn with(&self, name: Symbol, value: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(name, value);
        Self { entries }
    }
}

impl TypeMap {
    // Construct an empty type environment.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    // Look up the type assigned to one name.
    pub fn get(&self, name: &Name) -> Option<&Term> {
        self.entries.get(name)
    }

    // Return a new environment extended with one name/type assignment.
    pub fn with(&self, name: Name, r#type: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(name, r#type);
        Self { entries }
    }
}

impl Term {
    // Structural constructors should stay in kernel objects where possible.
    // Names refer to values; symbols remain selectors such as object keys.
    pub fn r#type() -> Self {
        Self(TermKind::Type)
    }

    pub fn bool_type() -> Self {
        Self(TermKind::BoolType)
    }

    pub fn nil_type() -> Self {
        Self(TermKind::NilType)
    }

    pub fn object_type(object: Object) -> Self {
        Self(TermKind::ObjectType(object))
    }

    pub fn arrow(arg_type: Term, return_type: Term) -> Self {
        Self(TermKind::Arrow {
            arg_type: Box::new(arg_type),
            return_type: Box::new(return_type),
        })
    }

    pub fn nil() -> Self {
        Self(TermKind::Nil)
    }

    pub fn bool(value: bool) -> Self {
        Self(TermKind::Bool(value))
    }

    pub fn object(object: Object) -> Self {
        Self(TermKind::Object(object))
    }

    pub fn var(name: Name) -> Self {
        Self(TermKind::Var(name))
    }

    pub fn lambda(binder: Name, body: Term) -> Self {
        Self::lowered_lambda(binder, body)
    }

    pub fn r#if(condition: Term, then_branch: Term, else_branch: Term) -> Self {
        Self(TermKind::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }

    pub fn app(function: Term, arg: Term) -> Self {
        Self(TermKind::App {
            function: Box::new(function),
            arg: Box::new(arg),
        })
    }

    pub fn get(object: Term, key: Symbol) -> Self {
        Self(TermKind::Get {
            object: Box::new(object),
            key,
        })
    }

    pub fn with(object: Term, key: Symbol, value: Term) -> Self {
        Self(TermKind::With {
            object: Box::new(object),
            key,
            value: Box::new(value),
        })
    }

    pub fn has(object: Term, key: Symbol) -> Self {
        Self(TermKind::Has {
            object: Box::new(object),
            key,
        })
    }

    fn lowered_lambda(binder: Name, body: Term) -> Self {
        Self(TermKind::Lambda {
            binder,
            body: Box::new(body),
        })
    }

    fn kind(&self) -> &TermKind {
        &self.0
    }

    fn into_kind(self) -> TermKind {
        self.0
    }
}

impl Context {
    // Construct an empty top-level context with no named definitions.
    pub fn new() -> Self {
        Self {
            names: BTreeMap::new(),
            values: BTreeMap::new(),
        }
    }

    // Look up the value currently bound to a top-level name.
    pub fn get(&self, name: &Name) -> Option<&Term> {
        self.values.get(name)
    }
}

/// Parse a source string, declare any top-level definitions, and evaluate the
/// final top-level expression.
pub fn run_source(source: &str) -> ClickResult<Option<Term>> {
    let exprs = read(source)?;
    let mut context = Context::new();

    let mut last = None;
    for expr in exprs {
        match declaration_from_expr(&expr, &context)? {
            Some(declaration) => context = declare(&context, declaration)?,
            None => {
                let term = term_from_expr(&expr, &[], &context)?;
                last = Some(eval(&term, context.values())?);
            }
        }
    }

    Ok(last)
}

/// Check and apply one top-level declaration, producing an extended context.
pub fn declare(context: &Context, declaration: Declaration) -> ClickResult<Context> {
    match declaration {
        Declaration::Def { name, value } => {
            if context.has_symbol(name.symbol()) {
                return Err(format!(
                    "definition '{}' is already declared",
                    name.symbol()
                ));
            }
            let evaluated = eval(&value, context.values())?;
            Ok(context.with_value(name, evaluated))
        }
        Declaration::Check { actual, expected } => {
            let actual = eval(&actual, context.values())?;
            let expected = eval(&expected, context.values())?;
            expect_equal(&actual, &expected, "check")?;
            Ok(context.clone())
        }
        Declaration::Theorem {
            name,
            actual,
            expected,
        } => {
            if context.has_symbol(name.symbol()) {
                return Err(format!(
                    "definition '{}' is already declared",
                    name.symbol()
                ));
            }
            let actual = eval(&actual, context.values())?;
            let expected = eval(&expected, context.values())?;
            expect_equal(&actual, &expected, "theorem")?;
            Ok(context.with_value(name, actual))
        }
    }
}

/// Reduce one well-scoped kernel term by a single operational step.
pub fn step(context: &Context, term: &Term) -> ClickResult<StepResult> {
    step_in_context(term, context.values())
}

/// Compute the type of one kernel term relative to an explicit name/type map.
pub fn type_of(types: &TypeMap, term: &Term) -> ClickResult<Term> {
    type_of_in_context(term, types)
}

// Private implementation stuff goes below here, to keep this file organized.

impl Term {
    // Apply Click's truthiness rule: only `nil` and `false` are falsey.
    fn is_truthy(&self) -> bool {
        !matches!(self.kind(), TermKind::Nil | TermKind::Bool(false))
    }

    // Recognize canonical terms that need no further evaluation.
    fn is_value(&self) -> bool {
        matches!(
            self.kind(),
            TermKind::Type
                | TermKind::BoolType
                | TermKind::NilType
                | TermKind::ObjectType(_)
                | TermKind::Arrow { .. }
                | TermKind::Nil
                | TermKind::Bool(_)
                | TermKind::Object(_)
                | TermKind::Lambda { .. }
        )
    }
}

impl Context {
    // Return the value environment visible to evaluation.
    fn values(&self) -> &BTreeMap<Name, Term> {
        &self.values
    }

    fn resolve_symbol(&self, symbol: &Symbol) -> Option<Name> {
        self.names.get(symbol).cloned()
    }

    fn has_symbol(&self, symbol: &Symbol) -> bool {
        self.names.contains_key(symbol)
    }

    // Return a new context extended with one evaluated top-level definition.
    fn with_value(&self, name: Name, value: Term) -> Self {
        let mut names = self.names.clone();
        names.insert(name.symbol().clone(), name.clone());
        let mut values = self.values.clone();
        values.insert(name, value);
        Self { names, values }
    }
}

impl fmt::Display for Term {
    // Render kernel values back into the small Click surface notation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Type => write!(f, "Type"),
            TermKind::BoolType => write!(f, "Bool"),
            TermKind::NilType => write!(f, "Nil"),
            TermKind::ObjectType(object) => {
                write!(f, "(object-type")?;
                for (key, value) in &object.entries {
                    write!(f, " ({key} {value})")?;
                }
                write!(f, ")")
            }
            TermKind::Arrow {
                arg_type,
                return_type,
            } => write!(f, "(arrow {arg_type} {return_type})"),
            TermKind::Nil => write!(f, "nil"),
            TermKind::Bool(true) => write!(f, "true"),
            TermKind::Bool(false) => write!(f, "false"),
            TermKind::Object(object) => format_object(object, f),
            TermKind::Lambda { .. } => write!(f, "#<function>"),
            TermKind::Var(name) => write!(f, "(var {name})"),
            TermKind::If {
                condition,
                then_branch,
                else_branch,
            } => write!(f, "(if {condition} {then_branch} {else_branch})"),
            TermKind::App { function, arg } => write!(f, "(app {function} {arg})"),
            TermKind::Get { object, key } => write!(f, "(get {object} {key})"),
            TermKind::With { object, key, value } => {
                write!(f, "(with {object} {key} {value})")
            }
            TermKind::Has { object, key } => write!(f, "(has {object} {key})"),
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

// Recognize top-level declaration forms and convert them into kernel declarations.
fn declaration_from_expr(expr: &SExpr, context: &Context) -> ClickResult<Option<Declaration>> {
    let SExpr::List(items) = expr else {
        return Ok(None);
    };

    let Some((head, tail)) = items.split_first() else {
        return Ok(None);
    };

    let SExpr::Symbol(operator) = head else {
        return Ok(None);
    };

    match operator.as_str() {
        "def" => {
            expect_arity(operator.as_str(), tail, 2)?;
            let name = Name::fresh(expect_symbol(&tail[0], "def name")?);
            Ok(Some(Declaration::Def {
                name,
                value: term_from_expr(&tail[1], &[], context)?,
            }))
        }
        "check" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Some(Declaration::Check {
                actual: term_from_expr(&tail[0], &[], context)?,
                expected: term_from_expr(&tail[1], &[], context)?,
            }))
        }
        "theorem" => {
            expect_arity(operator.as_str(), tail, 3)?;
            let name = Name::fresh(expect_symbol(&tail[0], "theorem name")?);
            Ok(Some(Declaration::Theorem {
                name,
                actual: term_from_expr(&tail[1], &[], context)?,
                expected: term_from_expr(&tail[2], &[], context)?,
            }))
        }
        _ => Ok(None),
    }
}

// Lower one surface expression into a well-scoped kernel term.
fn term_from_expr(expr: &SExpr, scope: &[(Symbol, Name)], context: &Context) -> ClickResult<Term> {
    match expr {
        SExpr::Symbol(symbol) => match symbol.as_str() {
            "Type" => Ok(Term::r#type()),
            "Bool" => Ok(Term::bool_type()),
            "Nil" => Ok(Term::nil_type()),
            "nil" => Ok(Term::nil()),
            "true" => Ok(Term::bool(true)),
            "false" => Ok(Term::bool(false)),
            _ => Err(format!("unbound atom '{symbol}'")),
        },
        SExpr::List(items) => term_from_list(items, scope, context),
    }
}

// Lower one tagged list form such as `object`, `lambda`, or `app`.
fn term_from_list(
    items: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Term> {
    let Some((head, tail)) = items.split_first() else {
        return Err("cannot evaluate an empty list; use nil".to_string());
    };

    let SExpr::Symbol(operator) = head else {
        return Err("form heads must be keyword atoms".to_string());
    };

    match operator.as_str() {
        "quote" => Err("quote is no longer supported in the kernel".to_string()),
        "def" => Err("def is only valid as a top-level declaration".to_string()),
        "check" => Err("check is only valid as a top-level declaration".to_string()),
        "theorem" => Err("theorem is only valid as a top-level declaration".to_string()),
        "object" => {
            expect_arity(operator.as_str(), tail, 0)?;
            Ok(Term::object(Object::new()))
        }
        "object-type" => {
            expect_arity(operator.as_str(), tail, 0)?;
            Ok(Term::object_type(Object::new()))
        }
        "arrow" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::arrow(
                term_from_expr(&tail[0], scope, context)?,
                term_from_expr(&tail[1], scope, context)?,
            ))
        }
        "if" => {
            expect_arity(operator.as_str(), tail, 3)?;
            Ok(Term::r#if(
                term_from_expr(&tail[0], scope, context)?,
                term_from_expr(&tail[1], scope, context)?,
                term_from_expr(&tail[2], scope, context)?,
            ))
        }
        "lambda" => term_from_lambda(tail, scope, context),
        "var" => term_from_var(tail, scope, context),
        "app" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::app(
                term_from_expr(&tail[0], scope, context)?,
                term_from_expr(&tail[1], scope, context)?,
            ))
        }
        "get" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::get(
                term_from_expr(&tail[0], scope, context)?,
                expect_symbol(&tail[1], "get key")?,
            ))
        }
        "with" => {
            expect_arity(operator.as_str(), tail, 3)?;
            Ok(Term::with(
                term_from_expr(&tail[0], scope, context)?,
                expect_symbol(&tail[1], "with key")?,
                term_from_expr(&tail[2], scope, context)?,
            ))
        }
        "has" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::has(
                term_from_expr(&tail[0], scope, context)?,
                expect_symbol(&tail[1], "has key")?,
            ))
        }
        "atom" | "atom_eq" | "car" | "cdr" | "cons" => {
            Err(format!("{operator} is no longer supported in the kernel"))
        }
        _ => Err(format!("unknown form '{operator}'")),
    }
}

// Lower a `lambda` body under one more local binder.
fn term_from_lambda(
    args: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Term> {
    expect_arity("lambda", args, 2)?;
    let binder_symbol = expect_symbol(&args[0], "lambda binder")?;
    let binder = Name::fresh(binder_symbol.clone());
    let mut inner_scope = scope.to_vec();
    inner_scope.push((binder_symbol, binder.clone()));
    Ok(Term::lowered_lambda(
        binder,
        term_from_expr(&args[1], &inner_scope, context)?,
    ))
}

// Resolve a surface `var` into either a local name or a known global name.
fn term_from_var(args: &[SExpr], scope: &[(Symbol, Name)], context: &Context) -> ClickResult<Term> {
    expect_arity("var", args, 1)?;
    let symbol = expect_symbol(&args[0], "var name")?;

    if let Some(name) = local_name(scope, &symbol) {
        Ok(Term::var(name))
    } else if let Some(name) = context.resolve_symbol(&symbol) {
        Ok(Term::var(name))
    } else {
        Err(format!("unbound variable '{symbol}'"))
    }
}

// Find the innermost local name with the given surface symbol.
fn local_name(scope: &[(Symbol, Name)], symbol: &Symbol) -> Option<Name> {
    scope
        .iter()
        .rev()
        .find(|(binder, _)| binder == symbol)
        .map(|(_, name)| name.clone())
}

// Reject top-level assertions whose evaluated values do not match.
fn expect_equal(actual: &Term, expected: &Term, role: &str) -> ClickResult<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{role} failed: expected {expected}, got {actual}"))
    }
}

// Reject forms whose argument count does not match the primitive's contract.
fn expect_arity(operator: &str, args: &[SExpr], expected: usize) -> ClickResult<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(format!(
            "{operator} expects {expected} argument(s), got {}",
            args.len()
        ))
    }
}

// Extract an atom name from syntax where a binder or object key is expected.
fn expect_symbol(expr: &SExpr, role: &str) -> ClickResult<Symbol> {
    match expr {
        SExpr::Symbol(symbol) => Ok(symbol.clone()),
        _ => Err(format!("{role} must be an atom")),
    }
}

// Evaluate one well-scoped kernel term by iterating single reduction steps.
fn eval(term: &Term, globals: &BTreeMap<Name, Term>) -> ClickResult<Term> {
    let mut current = term.clone();
    loop {
        match step_in_context(&current, globals)? {
            StepResult::Value(value) => return Ok(value),
            StepResult::Reduced(next) => current = next,
        }
    }
}

// Internal one-step reduction under the current top-level value environment.
fn step_in_context(term: &Term, globals: &BTreeMap<Name, Term>) -> ClickResult<StepResult> {
    match term.kind() {
        TermKind::Type => Ok(StepResult::Value(Term::r#type())),
        TermKind::BoolType => Ok(StepResult::Value(Term::bool_type())),
        TermKind::NilType => Ok(StepResult::Value(Term::nil_type())),
        TermKind::ObjectType(object) => Ok(StepResult::Value(Term::object_type(object.clone()))),
        TermKind::Arrow {
            arg_type,
            return_type,
        } => Ok(StepResult::Value(Term::arrow(
            (**arg_type).clone(),
            (**return_type).clone(),
        ))),
        TermKind::Nil => Ok(StepResult::Value(Term::nil())),
        TermKind::Bool(value) => Ok(StepResult::Value(Term::bool(*value))),
        TermKind::Object(object) => Ok(StepResult::Value(Term::object(object.clone()))),
        TermKind::Var(name) => globals
            .get(name)
            .cloned()
            .map(StepResult::Reduced)
            .ok_or_else(|| format!("unbound variable '{name}'")),
        TermKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            if condition.is_value() {
                if condition.is_truthy() {
                    Ok(StepResult::Reduced((**then_branch).clone()))
                } else {
                    Ok(StepResult::Reduced((**else_branch).clone()))
                }
            } else {
                Ok(StepResult::Reduced(Term::r#if(
                    step_reduct(condition, globals)?,
                    (**then_branch).clone(),
                    (**else_branch).clone(),
                )))
            }
        }
        TermKind::Lambda { binder, body } => Ok(StepResult::Value(Term::lowered_lambda(
            binder.clone(),
            (**body).clone(),
        ))),
        TermKind::App { function, arg } => {
            if !function.is_value() {
                Ok(StepResult::Reduced(Term::app(
                    step_reduct(function, globals)?,
                    (**arg).clone(),
                )))
            } else if !arg.is_value() {
                Ok(StepResult::Reduced(Term::app(
                    (**function).clone(),
                    step_reduct(arg, globals)?,
                )))
            } else {
                let rendered = function.to_string();
                match function.kind() {
                    TermKind::Lambda { binder, body } => {
                        Ok(StepResult::Reduced(instantiate(binder, body, arg)))
                    }
                    _ => Err(format!("attempted to call a non-function: {rendered}")),
                }
            }
        }
        TermKind::Get { object, key } => {
            if !object.is_value() {
                Ok(StepResult::Reduced(Term::get(
                    step_reduct(object, globals)?,
                    key.clone(),
                )))
            } else {
                let object = expect_object((**object).clone(), "get object")?;
                object
                    .get(key.as_str())
                    .cloned()
                    .map(StepResult::Reduced)
                    .ok_or_else(|| format!("missing object key '{key}'"))
            }
        }
        TermKind::With { object, key, value } => {
            if !object.is_value() {
                Ok(StepResult::Reduced(Term::with(
                    step_reduct(object, globals)?,
                    key.clone(),
                    (**value).clone(),
                )))
            } else if !value.is_value() {
                Ok(StepResult::Reduced(Term::with(
                    (**object).clone(),
                    key.clone(),
                    step_reduct(value, globals)?,
                )))
            } else {
                let object = expect_object((**object).clone(), "with object")?;
                Ok(StepResult::Reduced(Term::object(
                    object.with(key.clone(), (**value).clone()),
                )))
            }
        }
        TermKind::Has { object, key } => {
            if !object.is_value() {
                Ok(StepResult::Reduced(Term::has(
                    step_reduct(object, globals)?,
                    key.clone(),
                )))
            } else {
                let object = expect_object((**object).clone(), "has object")?;
                Ok(StepResult::Reduced(Term::bool(object.has(key.as_str()))))
            }
        }
    }
}

// Take one step and extract the reduct, rejecting terms that are already values.
fn step_reduct(term: &Term, globals: &BTreeMap<Name, Term>) -> ClickResult<Term> {
    match step_in_context(term, globals)? {
        StepResult::Reduced(next) => Ok(next),
        StepResult::Value(value) => Err(format!("expected a reducible term, got {value}")),
    }
}

// Extract an object value from runtime data where one is required.
fn expect_object(term: Term, role: &str) -> ClickResult<Object> {
    let rendered = term.to_string();
    match term.into_kind() {
        TermKind::Object(object) => Ok(object),
        _ => Err(format!("{role} must be an object, got {rendered}")),
    }
}

// Substitute an argument for one bound name in a lambda body.
fn instantiate(binder: &Name, body: &Term, arg: &Term) -> Term {
    substitute_name(body, binder, arg)
}

// Replace one bound name with a term, respecting shadowing beneath lambdas.
fn substitute_name(term: &Term, binder: &Name, replacement: &Term) -> Term {
    match term.kind() {
        TermKind::Type => Term::r#type(),
        TermKind::BoolType => Term::bool_type(),
        TermKind::NilType => Term::nil_type(),
        TermKind::ObjectType(object) => {
            Term::object_type(substitute_object(object, binder, replacement))
        }
        TermKind::Arrow {
            arg_type,
            return_type,
        } => Term::arrow(
            substitute_name(arg_type, binder, replacement),
            substitute_name(return_type, binder, replacement),
        ),
        TermKind::Nil => Term::nil(),
        TermKind::Bool(value) => Term::bool(*value),
        TermKind::Object(object) => Term::object(substitute_object(object, binder, replacement)),
        TermKind::Var(name) => {
            if name == binder {
                replacement.clone()
            } else {
                Term::var(name.clone())
            }
        }
        TermKind::If {
            condition,
            then_branch,
            else_branch,
        } => Term::r#if(
            substitute_name(condition, binder, replacement),
            substitute_name(then_branch, binder, replacement),
            substitute_name(else_branch, binder, replacement),
        ),
        TermKind::Lambda {
            binder: inner,
            body,
        } => {
            if inner == binder {
                Term::lowered_lambda(inner.clone(), (**body).clone())
            } else {
                Term::lowered_lambda(inner.clone(), substitute_name(body, binder, replacement))
            }
        }
        TermKind::App { function, arg } => Term::app(
            substitute_name(function, binder, replacement),
            substitute_name(arg, binder, replacement),
        ),
        TermKind::Get { object, key } => {
            Term::get(substitute_name(object, binder, replacement), key.clone())
        }
        TermKind::With { object, key, value } => Term::with(
            substitute_name(object, binder, replacement),
            key.clone(),
            substitute_name(value, binder, replacement),
        ),
        TermKind::Has { object, key } => {
            Term::has(substitute_name(object, binder, replacement), key.clone())
        }
    }
}

fn substitute_object(object: &Object, binder: &Name, replacement: &Term) -> Object {
    let entries = object
        .entries
        .iter()
        .map(|(key, value)| (key.clone(), substitute_name(value, binder, replacement)))
        .collect();
    Object { entries }
}

fn type_of_in_context(term: &Term, types: &TypeMap) -> ClickResult<Term> {
    match term.kind() {
        TermKind::Type => Ok(Term::r#type()),
        TermKind::BoolType | TermKind::NilType | TermKind::Arrow { .. } => Ok(Term::r#type()),
        TermKind::ObjectType(object) => {
            for value in object.entries.values() {
                expect_equal(
                    &type_of_in_context(value, types)?,
                    &Term::r#type(),
                    "object-type",
                )?;
            }
            Ok(Term::r#type())
        }
        TermKind::Nil => Ok(Term::nil_type()),
        TermKind::Bool(_) => Ok(Term::bool_type()),
        TermKind::Object(object) => type_of_object(object, types),
        TermKind::Var(name) => types
            .get(name)
            .cloned()
            .ok_or_else(|| format!("missing type for variable '{name}'")),
        TermKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let _condition_type = type_of_in_context(condition, types)?;
            let then_type = type_of_in_context(then_branch, types)?;
            let else_type = type_of_in_context(else_branch, types)?;
            expect_equal(&then_type, &else_type, "if")?;
            Ok(then_type)
        }
        TermKind::Lambda { binder, body } => {
            let binder_type = types
                .get(binder)
                .cloned()
                .ok_or_else(|| format!("missing type for lambda binder '{binder}'"))?;
            let body_type = type_of_in_context(body, types)?;
            Ok(Term::arrow(binder_type, body_type))
        }
        TermKind::App { function, arg } => {
            let function_type = type_of_in_context(function, types)?;
            let TermKind::Arrow {
                arg_type,
                return_type,
            } = function_type.kind()
            else {
                return Err(format!(
                    "cannot apply a non-function term of type {function_type}"
                ));
            };
            let actual_arg_type = type_of_in_context(arg, types)?;
            expect_equal(&actual_arg_type, arg_type, "app argument")?;
            Ok((**return_type).clone())
        }
        TermKind::Get { object, key } => {
            let object_type = type_of_in_context(object, types)?;
            let fields = expect_object_type(&object_type, "get object type")?;
            fields
                .get(key.as_str())
                .cloned()
                .ok_or_else(|| format!("missing object type for key '{key}'"))
        }
        TermKind::With { object, key, value } => {
            let object_type = type_of_in_context(object, types)?;
            let fields = expect_object_type(&object_type, "with object type")?;
            let value_type = type_of_in_context(value, types)?;
            Ok(Term::object_type(fields.with(key.clone(), value_type)))
        }
        TermKind::Has { object, .. } => {
            let object_type = type_of_in_context(object, types)?;
            let _fields = expect_object_type(&object_type, "has object type")?;
            Ok(Term::bool_type())
        }
    }
}

fn type_of_object(object: &Object, types: &TypeMap) -> ClickResult<Term> {
    let mut fields = Object::new();
    for (key, value) in &object.entries {
        fields = fields.with(key.clone(), type_of_in_context(value, types)?);
    }
    Ok(Term::object_type(fields))
}

fn expect_object_type(term: &Term, role: &str) -> ClickResult<Object> {
    match term.kind() {
        TermKind::ObjectType(object) => Ok(object.clone()),
        _ => Err(format!("{role} must be an object type, got {term}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_term(source: &str, context: &Context) -> Term {
        let exprs = read(source).expect("source should parse");
        assert_eq!(exprs.len(), 1, "test helper expects exactly one expression");
        term_from_expr(&exprs[0], &[], context).expect("expression should lower")
    }

    #[test]
    fn step_stops_after_one_beta_reduction() {
        let term = parse_term(
            "(app (lambda x (app (lambda y (var y)) (var x))) true)",
            &Context::new(),
        );

        match step_in_context(&term, &BTreeMap::new()).expect("step should succeed") {
            StepResult::Reduced(next) => assert_eq!(next.to_string(), "(app #<function> true)"),
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }

    #[test]
    fn step_chooses_an_if_branch_without_evaluating_it_further() {
        let term = parse_term(
            "(if true (app (lambda x (var x)) false) nil)",
            &Context::new(),
        );

        match step_in_context(&term, &BTreeMap::new()).expect("step should succeed") {
            StepResult::Reduced(next) => assert_eq!(next.to_string(), "(app #<function> false)"),
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }

    #[test]
    fn step_reduces_the_function_side_of_an_application_first() {
        let term = parse_term(
            "(app (if true (lambda x (var x)) nil) (app (lambda y (var y)) false))",
            &Context::new(),
        );

        match step_in_context(&term, &BTreeMap::new()).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(
                    next.to_string(),
                    "(app #<function> (app #<function> false))"
                )
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }
}
