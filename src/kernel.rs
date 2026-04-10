use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::reader::read;

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    names: BTreeMap<Symbol, Name>,
    values: NameMap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fields {
    entries: BTreeMap<Symbol, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Branches {
    entries: BTreeMap<Symbol, CaseBranch>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NameMap {
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
struct CaseBranch {
    binder: Name,
    body: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TermKind {
    Type,
    RecordType(Fields),
    SumType(Fields),
    Arrow {
        arg_type: Box<Term>,
        return_type: Box<Term>,
    },
    Record(Fields),
    Variant {
        tag: Symbol,
        value: Box<Term>,
        sum_type: Fields,
    },
    Var(Name),
    Lambda {
        binder: Name,
        body: Box<Term>,
    },
    App {
        function: Box<Term>,
        arg: Box<Term>,
    },
    Case {
        scrutinee: Box<Term>,
        branches: Branches,
    },
    Get {
        record: Box<Term>,
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

impl Fields {
    // Construct an empty labeled term map.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    // Check whether the map currently has a value for the given key.
    pub fn has(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    // Look up the value currently stored at the given key.
    pub fn get(&self, name: &str) -> Option<&Term> {
        self.entries.get(name)
    }

    // Return a new map with one key updated or inserted.
    pub fn with(&self, name: Symbol, value: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(name, value);
        Self { entries }
    }
}

impl Branches {
    // Construct an empty tagged branch map.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    // Check whether the map currently has a branch for the given tag.
    pub fn has(&self, tag: &str) -> bool {
        self.entries.contains_key(tag)
    }

    // Return a new branch map with one branch updated or inserted.
    pub fn with(&self, tag: Symbol, binder: Name, body: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(tag, CaseBranch { binder, body });
        Self { entries }
    }

    fn get(&self, tag: &str) -> Option<&CaseBranch> {
        self.entries.get(tag)
    }
}

impl NameMap {
    // Construct an empty name assignment.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    // Look up the term assigned to one name.
    pub fn get(&self, name: &Name) -> Option<&Term> {
        self.entries.get(name)
    }

    // Return a new assignment extended with one name/term entry.
    pub fn with(&self, name: Name, term: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(name, term);
        Self { entries }
    }
}

impl Term {
    // Structural constructors should stay in kernel objects where possible.
    // Names refer to values; symbols remain selectors such as record fields and sum tags.
    pub fn r#type() -> Self {
        Self(TermKind::Type)
    }

    pub fn record_type(fields: Fields) -> Self {
        Self(TermKind::RecordType(fields))
    }

    pub fn sum_type(fields: Fields) -> Self {
        Self(TermKind::SumType(fields))
    }

    pub fn arrow(arg_type: Term, return_type: Term) -> Self {
        Self(TermKind::Arrow {
            arg_type: Box::new(arg_type),
            return_type: Box::new(return_type),
        })
    }

    pub fn record(fields: Fields) -> Self {
        Self(TermKind::Record(fields))
    }

    pub fn variant(tag: Symbol, value: Term, sum_type: Fields) -> Self {
        Self(TermKind::Variant {
            tag,
            value: Box::new(value),
            sum_type,
        })
    }

    pub fn var(name: Name) -> Self {
        Self(TermKind::Var(name))
    }

    pub fn lambda(binder: Name, body: Term) -> Self {
        Self::lowered_lambda(binder, body)
    }

    pub fn app(function: Term, arg: Term) -> Self {
        Self(TermKind::App {
            function: Box::new(function),
            arg: Box::new(arg),
        })
    }

    pub fn case(scrutinee: Term, branches: Branches) -> Self {
        Self(TermKind::Case {
            scrutinee: Box::new(scrutinee),
            branches,
        })
    }

    pub fn get(record: Term, key: Symbol) -> Self {
        Self(TermKind::Get {
            record: Box::new(record),
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
            values: NameMap::new(),
        }
    }

    // Look up the value currently bound to a top-level name.
    pub fn get(&self, name: &Name) -> Option<&Term> {
        self.values.get(name)
    }

    // Expose the current top-level value assignment.
    pub fn values(&self) -> &NameMap {
        &self.values
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
pub fn step(values: &NameMap, term: &Term) -> ClickResult<StepResult> {
    step_in_names(term, values)
}

/// Compute the type of one kernel term relative to an explicit name/type map.
pub fn type_of(names: &NameMap, term: &Term) -> ClickResult<Term> {
    type_of_in_names(term, names)
}

// Private implementation stuff goes below here, to keep this file organized.

impl Term {
    // Recognize canonical terms that need no further evaluation.
    fn is_value(&self) -> bool {
        matches!(
            self.kind(),
            TermKind::Type
                | TermKind::RecordType(_)
                | TermKind::SumType(_)
                | TermKind::Arrow { .. }
                | TermKind::Record(_)
                | TermKind::Variant { .. }
                | TermKind::Lambda { .. }
        )
    }
}

impl Context {
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
        let values = self.values.with(name, value);
        Self { names, values }
    }
}

impl fmt::Display for Term {
    // Render kernel values back into the small Click surface notation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Type => write!(f, "Type"),
            TermKind::RecordType(fields) => format_fields("record-type", fields, f),
            TermKind::SumType(fields) => format_fields("sum-type", fields, f),
            TermKind::Arrow {
                arg_type,
                return_type,
            } => write!(f, "(arrow {arg_type} {return_type})"),
            TermKind::Record(fields) => format_fields("record", fields, f),
            TermKind::Variant {
                tag,
                value,
                sum_type,
            } => {
                write!(f, "(variant {tag} {value} ")?;
                format_fields("sum-type", sum_type, f)?;
                write!(f, ")")
            }
            TermKind::Lambda { .. } => write!(f, "#<function>"),
            TermKind::Var(name) => write!(f, "(var {name})"),
            TermKind::App { function, arg } => write!(f, "(app {function} {arg})"),
            TermKind::Case {
                scrutinee,
                branches,
            } => format_case(scrutinee, branches, f),
            TermKind::Get { record, key } => write!(f, "(get {record} {key})"),
        }
    }
}

// Print one labeled term map with its tag.
fn format_fields(tag: &str, fields: &Fields, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({tag}")?;
    for (key, value) in &fields.entries {
        write!(f, " ({key} {value})")?;
    }
    write!(f, ")")
}

fn format_case(scrutinee: &Term, branches: &Branches, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(case {scrutinee}")?;
    for (tag, branch) in &branches.entries {
        write!(f, " ({tag} {} {})", branch.binder, branch.body)?;
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
            _ => Err(format!("unbound atom '{symbol}'")),
        },
        SExpr::List(items) => term_from_list(items, scope, context),
    }
}

// Lower one tagged list form such as `record`, `lambda`, or `app`.
fn term_from_list(
    items: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Term> {
    let Some((head, tail)) = items.split_first() else {
        return Err("cannot evaluate an empty list".to_string());
    };

    let SExpr::Symbol(operator) = head else {
        return Err("form heads must be keyword atoms".to_string());
    };

    match operator.as_str() {
        "quote" => Err("quote is no longer supported in the kernel".to_string()),
        "def" => Err("def is only valid as a top-level declaration".to_string()),
        "check" => Err("check is only valid as a top-level declaration".to_string()),
        "theorem" => Err("theorem is only valid as a top-level declaration".to_string()),
        "record" => Ok(Term::record(fields_from_entries(tail, scope, context)?)),
        "record-type" => Ok(Term::record_type(fields_from_entries(
            tail, scope, context,
        )?)),
        "sum-type" => Ok(Term::sum_type(fields_from_entries(tail, scope, context)?)),
        "variant" => term_from_variant(tail, scope, context),
        "arrow" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::arrow(
                term_from_expr(&tail[0], scope, context)?,
                term_from_expr(&tail[1], scope, context)?,
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
        "case" => term_from_case(tail, scope, context),
        "get" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::get(
                term_from_expr(&tail[0], scope, context)?,
                expect_symbol(&tail[1], "get key")?,
            ))
        }
        "if" | "with" | "has" | "atom" | "atom_eq" | "car" | "cdr" | "cons" => {
            Err(format!("{operator} is no longer supported in the kernel"))
        }
        _ => Err(format!("unknown form '{operator}'")),
    }
}

fn fields_from_entries(
    items: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Fields> {
    let mut fields = Fields::new();
    for item in items {
        let SExpr::List(parts) = item else {
            return Err("field entries must be lists".to_string());
        };
        if parts.len() != 2 {
            return Err("field entries must have exactly two parts".to_string());
        }
        let key = expect_symbol(&parts[0], "field key")?;
        let value = term_from_expr(&parts[1], scope, context)?;
        fields = fields.with(key, value);
    }
    Ok(fields)
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

fn term_from_variant(
    args: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Term> {
    expect_arity("variant", args, 3)?;
    let tag = expect_symbol(&args[0], "variant tag")?;
    let value = term_from_expr(&args[1], scope, context)?;
    let sum_type = term_from_expr(&args[2], scope, context)?;
    let TermKind::SumType(fields) = sum_type.kind() else {
        return Err("variant expects an explicit sum-type term".to_string());
    };
    Ok(Term::variant(tag, value, fields.clone()))
}

fn term_from_case(
    args: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Term> {
    expect_min_arity("case", args, 2)?;
    let scrutinee = term_from_expr(&args[0], scope, context)?;
    let mut branches = Branches::new();
    for branch_expr in &args[1..] {
        let SExpr::List(parts) = branch_expr else {
            return Err("case branches must be lists".to_string());
        };
        if parts.len() != 3 {
            return Err("case branches must have exactly three parts".to_string());
        }
        let tag = expect_symbol(&parts[0], "case branch tag")?;
        if branches.has(tag.as_str()) {
            return Err(format!("duplicate case branch '{tag}'"));
        }
        let binder_symbol = expect_symbol(&parts[1], "case branch binder")?;
        let binder = Name::fresh(binder_symbol.clone());
        let mut inner_scope = scope.to_vec();
        inner_scope.push((binder_symbol, binder.clone()));
        let body = term_from_expr(&parts[2], &inner_scope, context)?;
        branches = branches.with(tag, binder, body);
    }
    Ok(Term::case(scrutinee, branches))
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

fn expect_min_arity(operator: &str, args: &[SExpr], minimum: usize) -> ClickResult<()> {
    if args.len() >= minimum {
        Ok(())
    } else {
        Err(format!(
            "{operator} expects at least {minimum} argument(s), got {}",
            args.len()
        ))
    }
}

// Extract an atom name from syntax where a binder, field, or tag is expected.
fn expect_symbol(expr: &SExpr, role: &str) -> ClickResult<Symbol> {
    match expr {
        SExpr::Symbol(symbol) => Ok(symbol.clone()),
        _ => Err(format!("{role} must be an atom")),
    }
}

// Evaluate one well-scoped kernel term by iterating single reduction steps.
fn eval(term: &Term, globals: &NameMap) -> ClickResult<Term> {
    let mut current = term.clone();
    loop {
        match step_in_names(&current, globals)? {
            StepResult::Value(value) => return Ok(value),
            StepResult::Reduced(next) => current = next,
        }
    }
}

// Internal one-step reduction under the current top-level value environment.
fn step_in_names(term: &Term, globals: &NameMap) -> ClickResult<StepResult> {
    match term.kind() {
        TermKind::Type => Ok(StepResult::Value(Term::r#type())),
        TermKind::RecordType(fields) => {
            if fields_are_values(fields) {
                Ok(StepResult::Value(Term::record_type(fields.clone())))
            } else {
                Ok(StepResult::Reduced(Term::record_type(step_fields(
                    fields, globals,
                )?)))
            }
        }
        TermKind::SumType(fields) => {
            if fields_are_values(fields) {
                Ok(StepResult::Value(Term::sum_type(fields.clone())))
            } else {
                Ok(StepResult::Reduced(Term::sum_type(step_fields(
                    fields, globals,
                )?)))
            }
        }
        TermKind::Arrow {
            arg_type,
            return_type,
        } => Ok(StepResult::Value(Term::arrow(
            (**arg_type).clone(),
            (**return_type).clone(),
        ))),
        TermKind::Record(fields) => {
            if fields_are_values(fields) {
                Ok(StepResult::Value(Term::record(fields.clone())))
            } else {
                Ok(StepResult::Reduced(Term::record(step_fields(
                    fields, globals,
                )?)))
            }
        }
        TermKind::Variant {
            tag,
            value,
            sum_type,
        } => {
            if !fields_are_values(sum_type) {
                Ok(StepResult::Reduced(Term::variant(
                    tag.clone(),
                    (**value).clone(),
                    step_fields(sum_type, globals)?,
                )))
            } else if !value.is_value() {
                Ok(StepResult::Reduced(Term::variant(
                    tag.clone(),
                    step_reduct(value, globals)?,
                    sum_type.clone(),
                )))
            } else {
                Ok(StepResult::Value(Term::variant(
                    tag.clone(),
                    (**value).clone(),
                    sum_type.clone(),
                )))
            }
        }
        TermKind::Var(name) => globals
            .get(name)
            .cloned()
            .map(StepResult::Reduced)
            .ok_or_else(|| format!("unbound variable '{name}'")),
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
        TermKind::Case {
            scrutinee,
            branches,
        } => {
            if !scrutinee.is_value() {
                Ok(StepResult::Reduced(Term::case(
                    step_reduct(scrutinee, globals)?,
                    branches.clone(),
                )))
            } else {
                let rendered = scrutinee.to_string();
                match scrutinee.kind() {
                    TermKind::Variant { tag, value, .. } => {
                        let branch = branches
                            .get(tag.as_str())
                            .ok_or_else(|| format!("missing case branch '{tag}'"))?;
                        Ok(StepResult::Reduced(instantiate(
                            &branch.binder,
                            &branch.body,
                            value,
                        )))
                    }
                    _ => Err(format!("case scrutinee must be a variant, got {rendered}")),
                }
            }
        }
        TermKind::Get { record, key } => {
            if !record.is_value() {
                Ok(StepResult::Reduced(Term::get(
                    step_reduct(record, globals)?,
                    key.clone(),
                )))
            } else {
                let fields = expect_record((**record).clone(), "get record")?;
                fields
                    .get(key.as_str())
                    .cloned()
                    .map(StepResult::Reduced)
                    .ok_or_else(|| format!("missing record key '{key}'"))
            }
        }
    }
}

// Take one step and extract the reduct, rejecting terms that are already values.
fn step_reduct(term: &Term, globals: &NameMap) -> ClickResult<Term> {
    match step_in_names(term, globals)? {
        StepResult::Reduced(next) => Ok(next),
        StepResult::Value(value) => Err(format!("expected a reducible term, got {value}")),
    }
}

fn fields_are_values(fields: &Fields) -> bool {
    fields.entries.values().all(Term::is_value)
}

fn step_fields(fields: &Fields, globals: &NameMap) -> ClickResult<Fields> {
    let mut stepped = fields.clone();
    for value in stepped.entries.values_mut() {
        if !value.is_value() {
            *value = step_reduct(value, globals)?;
            return Ok(stepped);
        }
    }
    Err("expected a reducible field entry".to_string())
}

// Extract a record value from runtime data where one is required.
fn expect_record(term: Term, role: &str) -> ClickResult<Fields> {
    let rendered = term.to_string();
    match term.into_kind() {
        TermKind::Record(fields) => Ok(fields),
        _ => Err(format!("{role} must be a record, got {rendered}")),
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
        TermKind::RecordType(fields) => {
            Term::record_type(substitute_fields(fields, binder, replacement))
        }
        TermKind::SumType(fields) => Term::sum_type(substitute_fields(fields, binder, replacement)),
        TermKind::Arrow {
            arg_type,
            return_type,
        } => Term::arrow(
            substitute_name(arg_type, binder, replacement),
            substitute_name(return_type, binder, replacement),
        ),
        TermKind::Record(fields) => Term::record(substitute_fields(fields, binder, replacement)),
        TermKind::Variant {
            tag,
            value,
            sum_type,
        } => Term::variant(
            tag.clone(),
            substitute_name(value, binder, replacement),
            substitute_fields(sum_type, binder, replacement),
        ),
        TermKind::Var(name) => {
            if name == binder {
                replacement.clone()
            } else {
                Term::var(name.clone())
            }
        }
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
        TermKind::Case {
            scrutinee,
            branches,
        } => Term::case(
            substitute_name(scrutinee, binder, replacement),
            substitute_branches(branches, binder, replacement),
        ),
        TermKind::Get { record, key } => {
            Term::get(substitute_name(record, binder, replacement), key.clone())
        }
    }
}

fn substitute_fields(fields: &Fields, binder: &Name, replacement: &Term) -> Fields {
    let entries = fields
        .entries
        .iter()
        .map(|(key, value)| (key.clone(), substitute_name(value, binder, replacement)))
        .collect();
    Fields { entries }
}

fn substitute_branches(branches: &Branches, binder: &Name, replacement: &Term) -> Branches {
    let entries = branches
        .entries
        .iter()
        .map(|(tag, branch)| {
            let body = if branch.binder == *binder {
                branch.body.clone()
            } else {
                substitute_name(&branch.body, binder, replacement)
            };
            (
                tag.clone(),
                CaseBranch {
                    binder: branch.binder.clone(),
                    body,
                },
            )
        })
        .collect();
    Branches { entries }
}

fn type_of_in_names(term: &Term, types: &NameMap) -> ClickResult<Term> {
    match term.kind() {
        TermKind::Type => Ok(Term::r#type()),
        TermKind::Arrow { .. } => Ok(Term::r#type()),
        TermKind::RecordType(fields) => expect_fields_are_types(fields, types, "record-type"),
        TermKind::SumType(fields) => expect_fields_are_types(fields, types, "sum-type"),
        TermKind::Record(fields) => type_of_record(fields, types),
        TermKind::Variant {
            tag,
            value,
            sum_type,
        } => {
            expect_fields_are_types(sum_type, types, "sum-type")?;
            let expected_payload_type = sum_type
                .get(tag.as_str())
                .cloned()
                .ok_or_else(|| format!("missing sum-type branch '{tag}'"))?;
            let actual_payload_type = type_of_in_names(value, types)?;
            expect_equal(
                &actual_payload_type,
                &expected_payload_type,
                "variant payload",
            )?;
            Ok(Term::sum_type(sum_type.clone()))
        }
        TermKind::Var(name) => types
            .get(name)
            .cloned()
            .ok_or_else(|| format!("missing type for variable '{name}'")),
        TermKind::Lambda { binder, body } => {
            let binder_type = types
                .get(binder)
                .cloned()
                .ok_or_else(|| format!("missing type for lambda binder '{binder}'"))?;
            let body_type = type_of_in_names(body, types)?;
            Ok(Term::arrow(binder_type, body_type))
        }
        TermKind::App { function, arg } => {
            let function_type = type_of_in_names(function, types)?;
            let TermKind::Arrow {
                arg_type,
                return_type,
            } = function_type.kind()
            else {
                return Err(format!(
                    "cannot apply a non-function term of type {function_type}"
                ));
            };
            let actual_arg_type = type_of_in_names(arg, types)?;
            expect_equal(&actual_arg_type, arg_type, "app argument")?;
            Ok((**return_type).clone())
        }
        TermKind::Case {
            scrutinee,
            branches,
        } => {
            let scrutinee_type = type_of_in_names(scrutinee, types)?;
            let sum_fields = expect_sum_type(&scrutinee_type, "case scrutinee type")?;
            let mut branch_result_type = None;

            for (tag, payload_type) in &sum_fields.entries {
                let branch = branches
                    .get(tag.as_str())
                    .ok_or_else(|| format!("missing case branch '{tag}'"))?;
                let branch_type = type_of_in_names(
                    &branch.body,
                    &types.with(branch.binder.clone(), payload_type.clone()),
                )?;
                if let Some(expected_type) = &branch_result_type {
                    expect_equal(&branch_type, expected_type, "case branches")?;
                } else {
                    branch_result_type = Some(branch_type);
                }
            }

            for tag in branches.entries.keys() {
                if !sum_fields.has(tag.as_str()) {
                    return Err(format!("unexpected case branch '{tag}'"));
                }
            }

            branch_result_type.ok_or_else(|| "cannot infer the type of an empty case".to_string())
        }
        TermKind::Get { record, key } => {
            let record_type = type_of_in_names(record, types)?;
            let fields = expect_record_type(&record_type, "get record type")?;
            fields
                .get(key.as_str())
                .cloned()
                .ok_or_else(|| format!("missing record type for key '{key}'"))
        }
    }
}

fn expect_fields_are_types(fields: &Fields, types: &NameMap, role: &str) -> ClickResult<Term> {
    for value in fields.entries.values() {
        expect_equal(&type_of_in_names(value, types)?, &Term::r#type(), role)?;
    }
    Ok(Term::r#type())
}

fn type_of_record(fields: &Fields, types: &NameMap) -> ClickResult<Term> {
    let mut field_types = Fields::new();
    for (key, value) in &fields.entries {
        field_types = field_types.with(key.clone(), type_of_in_names(value, types)?);
    }
    Ok(Term::record_type(field_types))
}

fn expect_record_type(term: &Term, role: &str) -> ClickResult<Fields> {
    match term.kind() {
        TermKind::RecordType(fields) => Ok(fields.clone()),
        _ => Err(format!("{role} must be a record type, got {term}")),
    }
}

fn expect_sum_type(term: &Term, role: &str) -> ClickResult<Fields> {
    match term.kind() {
        TermKind::SumType(fields) => Ok(fields.clone()),
        _ => Err(format!("{role} must be a sum type, got {term}")),
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
            "(app (lambda x (app (lambda y (var y)) (var x))) (record))",
            &Context::new(),
        );

        match step_in_names(&term, &NameMap::new()).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(next.to_string(), "(app #<function> (record))")
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }

    #[test]
    fn step_chooses_a_case_branch_without_evaluating_it_further() {
        let term = parse_term(
            "(case (variant left (record) (sum-type (left (record-type)) (right (record-type)))) (left x (app (lambda y (var y)) (record))) (right z (record (other (record)))))",
            &Context::new(),
        );

        match step_in_names(&term, &NameMap::new()).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(next.to_string(), "(app #<function> (record))")
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }

    #[test]
    fn step_reduces_the_function_side_of_an_application_first() {
        let term = parse_term(
            "(app (case (variant left (record) (sum-type (left (record-type)) (right (record-type)))) (left x (lambda y (var y))) (right z (record))) (app (lambda y (var y)) (record)))",
            &Context::new(),
        );

        match step_in_names(&term, &NameMap::new()).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(
                    next.to_string(),
                    "(app #<function> (app #<function> (record)))"
                )
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }
}
