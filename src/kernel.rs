use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::fmt;

use crate::reader::read;

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    values: Object,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Object {
    entries: BTreeMap<Symbol, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    Def {
        name: Symbol,
        value: Term,
    },
    Check {
        actual: Term,
        expected: Term,
    },
    Theorem {
        name: Symbol,
        actual: Term,
        expected: Term,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term(TermKind);

#[derive(Clone, Debug, PartialEq, Eq)]
enum TermKind {
    Nil,
    Bool(bool),
    Object(Object),
    Local(usize),
    Global(Symbol),
    If {
        condition: Box<Term>,
        then_branch: Box<Term>,
        else_branch: Box<Term>,
    },
    Lambda {
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

impl Symbol {
    fn as_str(&self) -> &str {
        &self.0
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
}

impl Term {
    // Public constructors only cover binder-free surface terms. Lowered locals
    // remain internal until there is a binder-safe host-side term API.
    pub fn nil() -> Self {
        Self(TermKind::Nil)
    }

    pub fn bool(value: bool) -> Self {
        Self(TermKind::Bool(value))
    }

    pub fn object(object: Object) -> Self {
        Self(TermKind::Object(object))
    }

    pub fn global(name: Symbol) -> Self {
        Self(TermKind::Global(name))
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

    fn local(index: usize) -> Self {
        Self(TermKind::Local(index))
    }

    fn lambda(body: Term) -> Self {
        Self(TermKind::Lambda {
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
            values: Object::new(),
        }
    }

    // Look up the value currently bound to a top-level name.
    pub fn get(&self, name: &str) -> Option<&Term> {
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
        match declaration_from_expr(&expr, context.values())? {
            Some(declaration) => context = declare(&context, declaration)?,
            None => {
                let term = term_from_expr(&expr, &[], context.values())?;
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
            if context.values.has(name.as_str()) {
                return Err(format!("definition '{name}' is already declared"));
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
            if context.values.has(name.as_str()) {
                return Err(format!("definition '{name}' is already declared"));
            }
            let actual = eval(&actual, context.values())?;
            let expected = eval(&expected, context.values())?;
            expect_equal(&actual, &expected, "theorem")?;
            Ok(context.with_value(name, actual))
        }
    }
}

// Private implementation stuff goes below here, to keep this file organized.

impl Term {
    // Apply Click's truthiness rule: only `nil` and `false` are falsey.
    fn is_truthy(&self) -> bool {
        !matches!(self.kind(), TermKind::Nil | TermKind::Bool(false))
    }
}

impl Object {
    // Return a new object with one key updated or inserted.
    fn with(&self, name: Symbol, value: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(name, value);
        Self { entries }
    }
}

impl Context {
    // Return the value environment visible to evaluation.
    fn values(&self) -> &Object {
        &self.values
    }

    // Return a new context extended with one evaluated top-level definition.
    fn with_value(&self, name: Symbol, value: Term) -> Self {
        Self {
            values: self.values.with(name, value),
        }
    }
}

impl fmt::Display for Term {
    // Render kernel values back into the small Click surface notation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Nil => write!(f, "nil"),
            TermKind::Bool(true) => write!(f, "true"),
            TermKind::Bool(false) => write!(f, "false"),
            TermKind::Object(object) => format_object(object, f),
            TermKind::Lambda { .. } => write!(f, "#<function>"),
            TermKind::Local(index) => write!(f, "#<local {index}>"),
            TermKind::Global(name) => write!(f, "(var {name})"),
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
fn declaration_from_expr(expr: &SExpr, globals: &Object) -> ClickResult<Option<Declaration>> {
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
            let name = expect_symbol(&tail[0], "def name")?;
            Ok(Some(Declaration::Def {
                name,
                value: term_from_expr(&tail[1], &[], globals)?,
            }))
        }
        "check" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Some(Declaration::Check {
                actual: term_from_expr(&tail[0], &[], globals)?,
                expected: term_from_expr(&tail[1], &[], globals)?,
            }))
        }
        "theorem" => {
            expect_arity(operator.as_str(), tail, 3)?;
            let name = expect_symbol(&tail[0], "theorem name")?;
            Ok(Some(Declaration::Theorem {
                name,
                actual: term_from_expr(&tail[1], &[], globals)?,
                expected: term_from_expr(&tail[2], &[], globals)?,
            }))
        }
        _ => Ok(None),
    }
}

// Lower one surface expression into a well-scoped kernel term.
fn term_from_expr(expr: &SExpr, scope: &[Symbol], globals: &Object) -> ClickResult<Term> {
    match expr {
        SExpr::Symbol(symbol) => match symbol.as_str() {
            "nil" => Ok(Term::nil()),
            "true" => Ok(Term::bool(true)),
            "false" => Ok(Term::bool(false)),
            _ => Err(format!("unbound atom '{symbol}'")),
        },
        SExpr::List(items) => term_from_list(items, scope, globals),
    }
}

// Lower one tagged list form such as `object`, `lambda`, or `app`.
fn term_from_list(items: &[SExpr], scope: &[Symbol], globals: &Object) -> ClickResult<Term> {
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
        "if" => {
            expect_arity(operator.as_str(), tail, 3)?;
            Ok(Term::r#if(
                term_from_expr(&tail[0], scope, globals)?,
                term_from_expr(&tail[1], scope, globals)?,
                term_from_expr(&tail[2], scope, globals)?,
            ))
        }
        "lambda" => term_from_lambda(tail, scope, globals),
        "var" => term_from_var(tail, scope, globals),
        "app" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::app(
                term_from_expr(&tail[0], scope, globals)?,
                term_from_expr(&tail[1], scope, globals)?,
            ))
        }
        "get" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::get(
                term_from_expr(&tail[0], scope, globals)?,
                expect_symbol(&tail[1], "get key")?,
            ))
        }
        "with" => {
            expect_arity(operator.as_str(), tail, 3)?;
            Ok(Term::with(
                term_from_expr(&tail[0], scope, globals)?,
                expect_symbol(&tail[1], "with key")?,
                term_from_expr(&tail[2], scope, globals)?,
            ))
        }
        "has" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::has(
                term_from_expr(&tail[0], scope, globals)?,
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
fn term_from_lambda(args: &[SExpr], scope: &[Symbol], globals: &Object) -> ClickResult<Term> {
    expect_arity("lambda", args, 2)?;
    let binder = expect_symbol(&args[0], "lambda binder")?;
    let mut inner_scope = scope.to_vec();
    inner_scope.push(binder);
    Ok(Term::lambda(term_from_expr(
        &args[1],
        &inner_scope,
        globals,
    )?))
}

// Resolve a surface `var` into either a local index or a known global name.
fn term_from_var(args: &[SExpr], scope: &[Symbol], globals: &Object) -> ClickResult<Term> {
    expect_arity("var", args, 1)?;
    let name = expect_symbol(&args[0], "var name")?;

    if let Some(index) = local_index(scope, &name) {
        Ok(Term::local(index))
    } else if globals.has(name.as_str()) {
        Ok(Term::global(name))
    } else {
        Err(format!("unbound variable '{name}'"))
    }
}

// Find the de Bruijn index for the innermost binder with the given name.
fn local_index(scope: &[Symbol], name: &Symbol) -> Option<usize> {
    scope.iter().rev().position(|binder| binder == name)
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

// Evaluate one well-scoped kernel term in the current top-level context.
fn eval(term: &Term, globals: &Object) -> ClickResult<Term> {
    match term.kind() {
        TermKind::Nil => Ok(Term::nil()),
        TermKind::Bool(value) => Ok(Term::bool(*value)),
        TermKind::Object(object) => Ok(Term::object(object.clone())),
        TermKind::Local(index) => Err(format!("encountered unbound local index {index}")),
        TermKind::Global(name) => globals
            .get(name.as_str())
            .cloned()
            .ok_or_else(|| format!("unbound variable '{name}'")),
        TermKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let condition = eval(condition, globals)?;
            if condition.is_truthy() {
                eval(then_branch, globals)
            } else {
                eval(else_branch, globals)
            }
        }
        TermKind::Lambda { body } => Ok(Term::lambda((**body).clone())),
        TermKind::App { function, arg } => {
            let function = eval(function, globals)?;
            let arg = eval(arg, globals)?;
            apply(function, arg, globals)
        }
        TermKind::Get { object, key } => {
            let object = expect_object(eval(object, globals)?, "get object")?;
            object
                .get(key.as_str())
                .cloned()
                .ok_or_else(|| format!("missing object key '{key}'"))
        }
        TermKind::With { object, key, value } => {
            let object = expect_object(eval(object, globals)?, "with object")?;
            let value = eval(value, globals)?;
            Ok(Term::object(object.with(key.clone(), value)))
        }
        TermKind::Has { object, key } => {
            let object = expect_object(eval(object, globals)?, "has object")?;
            Ok(Term::bool(object.has(key.as_str())))
        }
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

// Apply a function value by substituting the argument into its body.
fn apply(function: Term, arg: Term, globals: &Object) -> ClickResult<Term> {
    let rendered = function.to_string();
    match function.into_kind() {
        TermKind::Lambda { body } => {
            let body = instantiate(&body, &arg);
            eval(&body, globals)
        }
        _ => Err(format!("attempted to call a non-function: {rendered}")),
    }
}

// Substitute an argument for local index 0 in a lambda body.
fn instantiate(body: &Term, arg: &Term) -> Term {
    let arg = shift(arg, 1, 0);
    let body = substitute(body, 0, &arg);
    shift(&body, -1, 0)
}

// Shift local indices above the cutoff by a signed amount.
fn shift(term: &Term, amount: isize, cutoff: usize) -> Term {
    match term.kind() {
        TermKind::Nil => Term::nil(),
        TermKind::Bool(value) => Term::bool(*value),
        TermKind::Object(object) => Term::object(object.clone()),
        TermKind::Local(index) => {
            if *index < cutoff {
                Term::local(*index)
            } else {
                let index = index
                    .checked_add_signed(amount)
                    .expect("de Bruijn shift underflowed");
                Term::local(index)
            }
        }
        TermKind::Global(name) => Term::global(name.clone()),
        TermKind::If {
            condition,
            then_branch,
            else_branch,
        } => Term::r#if(
            shift(condition, amount, cutoff),
            shift(then_branch, amount, cutoff),
            shift(else_branch, amount, cutoff),
        ),
        TermKind::Lambda { body } => Term::lambda(shift(body, amount, cutoff + 1)),
        TermKind::App { function, arg } => {
            Term::app(shift(function, amount, cutoff), shift(arg, amount, cutoff))
        }
        TermKind::Get { object, key } => Term::get(shift(object, amount, cutoff), key.clone()),
        TermKind::With { object, key, value } => Term::with(
            shift(object, amount, cutoff),
            key.clone(),
            shift(value, amount, cutoff),
        ),
        TermKind::Has { object, key } => Term::has(shift(object, amount, cutoff), key.clone()),
    }
}

// Replace one local index with a term, adjusting beneath binders as needed.
fn substitute(term: &Term, depth: usize, replacement: &Term) -> Term {
    match term.kind() {
        TermKind::Nil => Term::nil(),
        TermKind::Bool(value) => Term::bool(*value),
        TermKind::Object(object) => Term::object(object.clone()),
        TermKind::Local(index) => {
            if *index == depth {
                shift(replacement, depth as isize, 0)
            } else {
                Term::local(*index)
            }
        }
        TermKind::Global(name) => Term::global(name.clone()),
        TermKind::If {
            condition,
            then_branch,
            else_branch,
        } => Term::r#if(
            substitute(condition, depth, replacement),
            substitute(then_branch, depth, replacement),
            substitute(else_branch, depth, replacement),
        ),
        TermKind::Lambda { body } => Term::lambda(substitute(body, depth + 1, replacement)),
        TermKind::App { function, arg } => Term::app(
            substitute(function, depth, replacement),
            substitute(arg, depth, replacement),
        ),
        TermKind::Get { object, key } => {
            Term::get(substitute(object, depth, replacement), key.clone())
        }
        TermKind::With { object, key, value } => Term::with(
            substitute(object, depth, replacement),
            key.clone(),
            substitute(value, depth, replacement),
        ),
        TermKind::Has { object, key } => {
            Term::has(substitute(object, depth, replacement), key.clone())
        }
    }
}
