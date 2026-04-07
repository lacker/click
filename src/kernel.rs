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
    entries: BTreeMap<String, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    Def {
        name: String,
        value: Term,
    },
    Check {
        actual: Term,
        expected: Term,
    },
    Theorem {
        name: String,
        actual: Term,
        expected: Term,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Nil,
    Bool(bool),
    Object(Object),
    Local(usize),
    Global(String),
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
        key: String,
    },
    With {
        object: Box<Term>,
        key: String,
        value: Box<Term>,
    },
    Has {
        object: Box<Term>,
        key: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SExpr {
    Symbol(String),
    List(Vec<SExpr>),
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
            if context.values.has(&name) {
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
            if context.values.has(&name) {
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
        !matches!(self, Term::Nil | Term::Bool(false))
    }
}

impl Object {
    // Return a new object with one key updated or inserted.
    fn with(&self, name: String, value: Term) -> Self {
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
    fn with_value(&self, name: String, value: Term) -> Self {
        Self {
            values: self.values.with(name, value),
        }
    }
}

impl fmt::Display for Term {
    // Render kernel values back into the small Click surface notation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Nil => write!(f, "nil"),
            Term::Bool(true) => write!(f, "true"),
            Term::Bool(false) => write!(f, "false"),
            Term::Object(object) => format_object(object, f),
            Term::Lambda { .. } => write!(f, "#<function>"),
            Term::Local(index) => write!(f, "#<local {index}>"),
            Term::Global(name) => write!(f, "(var {name})"),
            Term::If {
                condition,
                then_branch,
                else_branch,
            } => write!(f, "(if {condition} {then_branch} {else_branch})"),
            Term::App { function, arg } => write!(f, "(app {function} {arg})"),
            Term::Get { object, key } => write!(f, "(get {object} {key})"),
            Term::With { object, key, value } => write!(f, "(with {object} {key} {value})"),
            Term::Has { object, key } => write!(f, "(has {object} {key})"),
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
            expect_arity(operator, tail, 2)?;
            let name = expect_symbol(&tail[0], "def name")?;
            Ok(Some(Declaration::Def {
                name,
                value: term_from_expr(&tail[1], &[], globals)?,
            }))
        }
        "check" => {
            expect_arity(operator, tail, 2)?;
            Ok(Some(Declaration::Check {
                actual: term_from_expr(&tail[0], &[], globals)?,
                expected: term_from_expr(&tail[1], &[], globals)?,
            }))
        }
        "theorem" => {
            expect_arity(operator, tail, 3)?;
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
fn term_from_expr(expr: &SExpr, scope: &[String], globals: &Object) -> ClickResult<Term> {
    match expr {
        SExpr::Symbol(symbol) => match symbol.as_str() {
            "nil" => Ok(Term::Nil),
            "true" => Ok(Term::Bool(true)),
            "false" => Ok(Term::Bool(false)),
            _ => Err(format!("unbound atom '{symbol}'")),
        },
        SExpr::List(items) => term_from_list(items, scope, globals),
    }
}

// Lower one tagged list form such as `object`, `lambda`, or `app`.
fn term_from_list(items: &[SExpr], scope: &[String], globals: &Object) -> ClickResult<Term> {
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
            expect_arity(operator, tail, 0)?;
            Ok(Term::Object(Object::new()))
        }
        "if" => {
            expect_arity(operator, tail, 3)?;
            Ok(Term::If {
                condition: Box::new(term_from_expr(&tail[0], scope, globals)?),
                then_branch: Box::new(term_from_expr(&tail[1], scope, globals)?),
                else_branch: Box::new(term_from_expr(&tail[2], scope, globals)?),
            })
        }
        "lambda" => term_from_lambda(tail, scope, globals),
        "var" => term_from_var(tail, scope, globals),
        "app" => {
            expect_arity(operator, tail, 2)?;
            Ok(Term::App {
                function: Box::new(term_from_expr(&tail[0], scope, globals)?),
                arg: Box::new(term_from_expr(&tail[1], scope, globals)?),
            })
        }
        "get" => {
            expect_arity(operator, tail, 2)?;
            Ok(Term::Get {
                object: Box::new(term_from_expr(&tail[0], scope, globals)?),
                key: expect_symbol(&tail[1], "get key")?,
            })
        }
        "with" => {
            expect_arity(operator, tail, 3)?;
            Ok(Term::With {
                object: Box::new(term_from_expr(&tail[0], scope, globals)?),
                key: expect_symbol(&tail[1], "with key")?,
                value: Box::new(term_from_expr(&tail[2], scope, globals)?),
            })
        }
        "has" => {
            expect_arity(operator, tail, 2)?;
            Ok(Term::Has {
                object: Box::new(term_from_expr(&tail[0], scope, globals)?),
                key: expect_symbol(&tail[1], "has key")?,
            })
        }
        "atom" | "atom_eq" | "car" | "cdr" | "cons" => {
            Err(format!("{operator} is no longer supported in the kernel"))
        }
        _ => Err(format!("unknown form '{operator}'")),
    }
}

// Lower a `lambda` body under one more local binder.
fn term_from_lambda(args: &[SExpr], scope: &[String], globals: &Object) -> ClickResult<Term> {
    expect_arity("lambda", args, 2)?;
    let binder = expect_symbol(&args[0], "lambda binder")?;
    let mut inner_scope = scope.to_vec();
    inner_scope.push(binder);
    Ok(Term::Lambda {
        body: Box::new(term_from_expr(&args[1], &inner_scope, globals)?),
    })
}

// Resolve a surface `var` into either a local index or a known global name.
fn term_from_var(args: &[SExpr], scope: &[String], globals: &Object) -> ClickResult<Term> {
    expect_arity("var", args, 1)?;
    let name = expect_symbol(&args[0], "var name")?;

    if let Some(index) = local_index(scope, &name) {
        Ok(Term::Local(index))
    } else if globals.has(&name) {
        Ok(Term::Global(name))
    } else {
        Err(format!("unbound variable '{name}'"))
    }
}

// Find the de Bruijn index for the innermost binder with the given name.
fn local_index(scope: &[String], name: &str) -> Option<usize> {
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
fn expect_symbol(expr: &SExpr, role: &str) -> ClickResult<String> {
    match expr {
        SExpr::Symbol(symbol) => Ok(symbol.clone()),
        _ => Err(format!("{role} must be an atom")),
    }
}

// Evaluate one well-scoped kernel term in the current top-level context.
fn eval(term: &Term, globals: &Object) -> ClickResult<Term> {
    match term {
        Term::Nil => Ok(Term::Nil),
        Term::Bool(value) => Ok(Term::Bool(*value)),
        Term::Object(object) => Ok(Term::Object(object.clone())),
        Term::Local(index) => Err(format!("encountered unbound local index {index}")),
        Term::Global(name) => globals
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unbound variable '{name}'")),
        Term::If {
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
        Term::Lambda { body } => Ok(Term::Lambda {
            body: Box::new((**body).clone()),
        }),
        Term::App { function, arg } => {
            let function = eval(function, globals)?;
            let arg = eval(arg, globals)?;
            apply(function, arg, globals)
        }
        Term::Get { object, key } => {
            let object = expect_object(eval(object, globals)?, "get object")?;
            object
                .get(key)
                .cloned()
                .ok_or_else(|| format!("missing object key '{key}'"))
        }
        Term::With { object, key, value } => {
            let object = expect_object(eval(object, globals)?, "with object")?;
            let value = eval(value, globals)?;
            Ok(Term::Object(object.with(key.clone(), value)))
        }
        Term::Has { object, key } => {
            let object = expect_object(eval(object, globals)?, "has object")?;
            Ok(Term::Bool(object.has(key)))
        }
    }
}

// Extract an object value from runtime data where one is required.
fn expect_object(term: Term, role: &str) -> ClickResult<Object> {
    match term {
        Term::Object(object) => Ok(object),
        _ => Err(format!("{role} must be an object")),
    }
}

// Apply a function value by substituting the argument into its body.
fn apply(function: Term, arg: Term, globals: &Object) -> ClickResult<Term> {
    match function {
        Term::Lambda { body } => {
            let body = instantiate(&body, &arg);
            eval(&body, globals)
        }
        _ => Err("attempted to call a non-function".to_string()),
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
    match term {
        Term::Nil => Term::Nil,
        Term::Bool(value) => Term::Bool(*value),
        Term::Object(object) => Term::Object(object.clone()),
        Term::Local(index) => {
            if *index < cutoff {
                Term::Local(*index)
            } else {
                let index = index
                    .checked_add_signed(amount)
                    .expect("de Bruijn shift underflowed");
                Term::Local(index)
            }
        }
        Term::Global(name) => Term::Global(name.clone()),
        Term::If {
            condition,
            then_branch,
            else_branch,
        } => Term::If {
            condition: Box::new(shift(condition, amount, cutoff)),
            then_branch: Box::new(shift(then_branch, amount, cutoff)),
            else_branch: Box::new(shift(else_branch, amount, cutoff)),
        },
        Term::Lambda { body } => Term::Lambda {
            body: Box::new(shift(body, amount, cutoff + 1)),
        },
        Term::App { function, arg } => Term::App {
            function: Box::new(shift(function, amount, cutoff)),
            arg: Box::new(shift(arg, amount, cutoff)),
        },
        Term::Get { object, key } => Term::Get {
            object: Box::new(shift(object, amount, cutoff)),
            key: key.clone(),
        },
        Term::With { object, key, value } => Term::With {
            object: Box::new(shift(object, amount, cutoff)),
            key: key.clone(),
            value: Box::new(shift(value, amount, cutoff)),
        },
        Term::Has { object, key } => Term::Has {
            object: Box::new(shift(object, amount, cutoff)),
            key: key.clone(),
        },
    }
}

// Replace one local index with a term, adjusting beneath binders as needed.
fn substitute(term: &Term, depth: usize, replacement: &Term) -> Term {
    match term {
        Term::Nil => Term::Nil,
        Term::Bool(value) => Term::Bool(*value),
        Term::Object(object) => Term::Object(object.clone()),
        Term::Local(index) => {
            if *index == depth {
                shift(replacement, depth as isize, 0)
            } else {
                Term::Local(*index)
            }
        }
        Term::Global(name) => Term::Global(name.clone()),
        Term::If {
            condition,
            then_branch,
            else_branch,
        } => Term::If {
            condition: Box::new(substitute(condition, depth, replacement)),
            then_branch: Box::new(substitute(then_branch, depth, replacement)),
            else_branch: Box::new(substitute(else_branch, depth, replacement)),
        },
        Term::Lambda { body } => Term::Lambda {
            body: Box::new(substitute(body, depth + 1, replacement)),
        },
        Term::App { function, arg } => Term::App {
            function: Box::new(substitute(function, depth, replacement)),
            arg: Box::new(substitute(arg, depth, replacement)),
        },
        Term::Get { object, key } => Term::Get {
            object: Box::new(substitute(object, depth, replacement)),
            key: key.clone(),
        },
        Term::With { object, key, value } => Term::With {
            object: Box::new(substitute(object, depth, replacement)),
            key: key.clone(),
            value: Box::new(substitute(value, depth, replacement)),
        },
        Term::Has { object, key } => Term::Has {
            object: Box::new(substitute(object, depth, replacement)),
            key: key.clone(),
        },
    }
}
