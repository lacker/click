use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

pub type ClickResult<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolMap {
    entries: BTreeMap<Symbol, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NameMap {
    entries: BTreeMap<Name, Term>,
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
    RecordType(SymbolMap),
    SumType(SymbolMap),
    Pi {
        binder: Name,
        arg_type: Box<Term>,
        return_type: Box<Term>,
    },
    Record(SymbolMap),
    Variant {
        tag: Symbol,
        value: Box<Term>,
        sum_type: SymbolMap,
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
    Match {
        scrutinee: Box<Term>,
        handlers: SymbolMap,
    },
    Get {
        record: Box<Term>,
        key: Symbol,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepResult {
    Value(Term),
    Reduced(Term),
}

static NEXT_NAME_ID: AtomicUsize = AtomicUsize::new(0);
const ANONYMOUS_NAME_ID: usize = usize::MAX;

impl Symbol {
    pub(crate) fn as_str(&self) -> &str {
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

    fn anonymous() -> Self {
        Self {
            id: ANONYMOUS_NAME_ID,
            symbol: Symbol::from("_"),
        }
    }

    fn is_anonymous(&self) -> bool {
        self.id == ANONYMOUS_NAME_ID
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

impl SymbolMap {
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

    pub fn record_type(fields: SymbolMap) -> Self {
        Self(TermKind::RecordType(fields))
    }

    pub fn sum_type(fields: SymbolMap) -> Self {
        Self(TermKind::SumType(fields))
    }

    pub fn pi(binder: Name, arg_type: Term, return_type: Term) -> Self {
        Self(TermKind::Pi {
            binder,
            arg_type: Box::new(arg_type),
            return_type: Box::new(return_type),
        })
    }

    pub fn arrow(arg_type: Term, return_type: Term) -> Self {
        Self::pi(Name::anonymous(), arg_type, return_type)
    }

    pub fn record(fields: SymbolMap) -> Self {
        Self(TermKind::Record(fields))
    }

    pub fn variant(tag: Symbol, value: Term, sum_type: SymbolMap) -> Self {
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

    pub fn r#match(scrutinee: Term, handlers: SymbolMap) -> Self {
        Self(TermKind::Match {
            scrutinee: Box::new(scrutinee),
            handlers,
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

    pub(crate) fn sum_type_fields(&self) -> Option<&SymbolMap> {
        match self.kind() {
            TermKind::SumType(fields) => Some(fields),
            _ => None,
        }
    }

    fn kind(&self) -> &TermKind {
        &self.0
    }

    fn into_kind(self) -> TermKind {
        self.0
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

impl Term {
    // Recognize canonical terms that need no further evaluation.
    fn is_value(&self) -> bool {
        matches!(
            self.kind(),
            TermKind::Type
                | TermKind::RecordType(_)
                | TermKind::SumType(_)
                | TermKind::Pi { .. }
                | TermKind::Record(_)
                | TermKind::Variant { .. }
                | TermKind::Lambda { .. }
        )
    }
}

impl fmt::Display for Term {
    // Render kernel values back into the small Click surface notation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Type => write!(f, "Type"),
            TermKind::RecordType(fields) => format_symbol_map("record-type", fields, f),
            TermKind::SumType(fields) => format_symbol_map("sum-type", fields, f),
            TermKind::Pi {
                binder,
                arg_type,
                return_type,
            } => {
                if binder.is_anonymous() {
                    write!(f, "(arrow {arg_type} {return_type})")
                } else {
                    write!(f, "(pi {binder} {arg_type} {return_type})")
                }
            }
            TermKind::Record(fields) => format_symbol_map("record", fields, f),
            TermKind::Variant {
                tag,
                value,
                sum_type,
            } => {
                write!(f, "(variant {tag} {value} ")?;
                format_symbol_map("sum-type", sum_type, f)?;
                write!(f, ")")
            }
            TermKind::Lambda { .. } => write!(f, "#<function>"),
            TermKind::Var(name) => write!(f, "(var {name})"),
            TermKind::App { function, arg } => write!(f, "(app {function} {arg})"),
            TermKind::Match {
                scrutinee,
                handlers,
            } => format_match(scrutinee, handlers, f),
            TermKind::Get { record, key } => write!(f, "(get {record} {key})"),
        }
    }
}

// Print one labeled term map with its tag.
fn format_symbol_map(tag: &str, fields: &SymbolMap, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({tag}")?;
    for (key, value) in &fields.entries {
        write!(f, " ({key} {value})")?;
    }
    write!(f, ")")
}

fn format_match(scrutinee: &Term, handlers: &SymbolMap, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(match {scrutinee}")?;
    for (tag, handler) in &handlers.entries {
        write!(f, " ({tag} {handler})")?;
    }
    write!(f, ")")
}

// Internal one-step reduction under the current top-level value environment.
fn step_in_names(term: &Term, globals: &NameMap) -> ClickResult<StepResult> {
    match term.kind() {
        TermKind::Type => Ok(StepResult::Value(Term::r#type())),
        TermKind::RecordType(fields) => {
            if symbol_map_values_are_values(fields) {
                Ok(StepResult::Value(Term::record_type(fields.clone())))
            } else {
                Ok(StepResult::Reduced(Term::record_type(step_symbol_map(
                    fields, globals,
                )?)))
            }
        }
        TermKind::SumType(fields) => {
            if symbol_map_values_are_values(fields) {
                Ok(StepResult::Value(Term::sum_type(fields.clone())))
            } else {
                Ok(StepResult::Reduced(Term::sum_type(step_symbol_map(
                    fields, globals,
                )?)))
            }
        }
        TermKind::Pi {
            binder,
            arg_type,
            return_type,
        } => Ok(StepResult::Value(Term::pi(
            binder.clone(),
            (**arg_type).clone(),
            (**return_type).clone(),
        ))),
        TermKind::Record(fields) => {
            if symbol_map_values_are_values(fields) {
                Ok(StepResult::Value(Term::record(fields.clone())))
            } else {
                Ok(StepResult::Reduced(Term::record(step_symbol_map(
                    fields, globals,
                )?)))
            }
        }
        TermKind::Variant {
            tag,
            value,
            sum_type,
        } => {
            if !symbol_map_values_are_values(sum_type) {
                Ok(StepResult::Reduced(Term::variant(
                    tag.clone(),
                    (**value).clone(),
                    step_symbol_map(sum_type, globals)?,
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
        TermKind::Match {
            scrutinee,
            handlers,
        } => {
            if !scrutinee.is_value() {
                Ok(StepResult::Reduced(Term::r#match(
                    step_reduct(scrutinee, globals)?,
                    handlers.clone(),
                )))
            } else {
                let rendered = scrutinee.to_string();
                match scrutinee.kind() {
                    TermKind::Variant { tag, value, .. } => {
                        let handler = handlers
                            .get(tag.as_str())
                            .cloned()
                            .ok_or_else(|| format!("missing match handler '{tag}'"))?;
                        Ok(StepResult::Reduced(Term::app(handler, (**value).clone())))
                    }
                    _ => Err(format!("match scrutinee must be a variant, got {rendered}")),
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

fn symbol_map_values_are_values(fields: &SymbolMap) -> bool {
    fields.entries.values().all(Term::is_value)
}

fn step_symbol_map(fields: &SymbolMap, globals: &NameMap) -> ClickResult<SymbolMap> {
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
fn expect_record(term: Term, role: &str) -> ClickResult<SymbolMap> {
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
            Term::record_type(substitute_symbol_map(fields, binder, replacement))
        }
        TermKind::SumType(fields) => {
            Term::sum_type(substitute_symbol_map(fields, binder, replacement))
        }
        TermKind::Pi {
            binder: inner,
            arg_type,
            return_type,
        } => {
            let arg_type = substitute_name(arg_type, binder, replacement);
            if inner == binder {
                Term::pi(inner.clone(), arg_type, (**return_type).clone())
            } else {
                Term::pi(
                    inner.clone(),
                    arg_type,
                    substitute_name(return_type, binder, replacement),
                )
            }
        }
        TermKind::Record(fields) => {
            Term::record(substitute_symbol_map(fields, binder, replacement))
        }
        TermKind::Variant {
            tag,
            value,
            sum_type,
        } => Term::variant(
            tag.clone(),
            substitute_name(value, binder, replacement),
            substitute_symbol_map(sum_type, binder, replacement),
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
        TermKind::Match {
            scrutinee,
            handlers,
        } => Term::r#match(
            substitute_name(scrutinee, binder, replacement),
            substitute_symbol_map(handlers, binder, replacement),
        ),
        TermKind::Get { record, key } => {
            Term::get(substitute_name(record, binder, replacement), key.clone())
        }
    }
}

fn substitute_symbol_map(fields: &SymbolMap, binder: &Name, replacement: &Term) -> SymbolMap {
    let entries = fields
        .entries
        .iter()
        .map(|(key, value)| (key.clone(), substitute_name(value, binder, replacement)))
        .collect();
    SymbolMap { entries }
}

fn occurs_name(term: &Term, target: &Name) -> bool {
    match term.kind() {
        TermKind::Type => false,
        TermKind::RecordType(fields) | TermKind::SumType(fields) | TermKind::Record(fields) => {
            occurs_name_in_symbol_map(fields, target)
        }
        TermKind::Pi {
            binder,
            arg_type,
            return_type,
        } => {
            occurs_name(arg_type, target) || (binder != target && occurs_name(return_type, target))
        }
        TermKind::Variant {
            value, sum_type, ..
        } => occurs_name(value, target) || occurs_name_in_symbol_map(sum_type, target),
        TermKind::Var(name) => name == target,
        TermKind::Lambda { binder, body } => binder != target && occurs_name(body, target),
        TermKind::App { function, arg } => {
            occurs_name(function, target) || occurs_name(arg, target)
        }
        TermKind::Match {
            scrutinee,
            handlers,
        } => occurs_name(scrutinee, target) || occurs_name_in_symbol_map(handlers, target),
        TermKind::Get { record, .. } => occurs_name(record, target),
    }
}

fn occurs_name_in_symbol_map(fields: &SymbolMap, target: &Name) -> bool {
    fields
        .entries
        .values()
        .any(|value| occurs_name(value, target))
}

fn type_of_in_names(term: &Term, types: &NameMap) -> ClickResult<Term> {
    match term.kind() {
        TermKind::Type => Ok(Term::r#type()),
        TermKind::Pi {
            binder,
            arg_type,
            return_type,
        } => {
            expect_equal(
                &type_of_in_names(arg_type, types)?,
                &Term::r#type(),
                "pi argument type",
            )?;
            expect_equal(
                &type_of_in_names(
                    return_type,
                    &types.with(binder.clone(), (**arg_type).clone()),
                )?,
                &Term::r#type(),
                "pi return type",
            )?;
            Ok(Term::r#type())
        }
        TermKind::RecordType(fields) => {
            expect_symbol_map_terms_are_types(fields, types, "record-type")
        }
        TermKind::SumType(fields) => expect_symbol_map_terms_are_types(fields, types, "sum-type"),
        TermKind::Record(fields) => type_of_record(fields, types),
        TermKind::Variant {
            tag,
            value,
            sum_type,
        } => {
            expect_symbol_map_terms_are_types(sum_type, types, "sum-type")?;
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
            if occurs_name(&body_type, binder) {
                Ok(Term::pi(binder.clone(), binder_type, body_type))
            } else {
                Ok(Term::arrow(binder_type, body_type))
            }
        }
        TermKind::App { function, arg } => {
            let function_type = type_of_in_names(function, types)?;
            let TermKind::Pi {
                binder,
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
            Ok(substitute_name(return_type, binder, arg))
        }
        TermKind::Match {
            scrutinee,
            handlers,
        } => {
            let scrutinee_type = type_of_in_names(scrutinee, types)?;
            let sum_fields = expect_sum_type(&scrutinee_type, "match scrutinee type")?;
            let mut handler_result_type = None;

            for (tag, payload_type) in &sum_fields.entries {
                let handler = handlers
                    .get(tag.as_str())
                    .ok_or_else(|| format!("missing match handler '{tag}'"))?;
                let result_type = type_of_match_handler(handler, payload_type, types, tag)?;
                if let Some(expected_type) = &handler_result_type {
                    expect_equal(&result_type, expected_type, "match handlers")?;
                } else {
                    handler_result_type = Some(result_type);
                }
            }

            for tag in handlers.entries.keys() {
                if !sum_fields.has(tag.as_str()) {
                    return Err(format!("unexpected match handler '{tag}'"));
                }
            }

            handler_result_type.ok_or_else(|| "cannot infer the type of an empty match".to_string())
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

fn type_of_match_handler(
    handler: &Term,
    payload_type: &Term,
    types: &NameMap,
    tag: &Symbol,
) -> ClickResult<Term> {
    match handler.kind() {
        TermKind::Lambda { binder, body } => {
            let result_type =
                type_of_in_names(body, &types.with(binder.clone(), payload_type.clone()))?;
            if occurs_name(&result_type, binder) {
                Err(format!(
                    "match handler '{tag}' result type cannot depend on its argument"
                ))
            } else {
                Ok(result_type)
            }
        }
        _ => {
            let handler_type = type_of_in_names(handler, types)?;
            let TermKind::Pi {
                binder,
                arg_type,
                return_type,
            } = handler_type.kind()
            else {
                return Err(format!(
                    "match handler '{tag}' must have a function type, got {handler_type}"
                ));
            };
            expect_equal(
                arg_type,
                payload_type,
                &format!("match handler '{tag}' argument"),
            )?;
            if occurs_name(return_type, binder) {
                Err(format!(
                    "match handler '{tag}' result type cannot depend on its argument"
                ))
            } else {
                Ok((**return_type).clone())
            }
        }
    }
}

fn expect_symbol_map_terms_are_types(
    fields: &SymbolMap,
    types: &NameMap,
    role: &str,
) -> ClickResult<Term> {
    for value in fields.entries.values() {
        expect_equal(&type_of_in_names(value, types)?, &Term::r#type(), role)?;
    }
    Ok(Term::r#type())
}

fn type_of_record(fields: &SymbolMap, types: &NameMap) -> ClickResult<Term> {
    let mut field_types = SymbolMap::new();
    for (key, value) in &fields.entries {
        field_types = field_types.with(key.clone(), type_of_in_names(value, types)?);
    }
    Ok(Term::record_type(field_types))
}

fn expect_equal(actual: &Term, expected: &Term, role: &str) -> ClickResult<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{role} failed: expected {expected}, got {actual}"))
    }
}

fn expect_record_type(term: &Term, role: &str) -> ClickResult<SymbolMap> {
    match term.kind() {
        TermKind::RecordType(fields) => Ok(fields.clone()),
        _ => Err(format!("{role} must be a record type, got {term}")),
    }
}

pub(crate) fn expect_sum_type(term: &Term, role: &str) -> ClickResult<SymbolMap> {
    match term.kind() {
        TermKind::SumType(fields) => Ok(fields.clone()),
        _ => Err(format!("{role} must be a sum type, got {term}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unit_record() -> Term {
        Term::record(SymbolMap::new())
    }

    fn unit_record_type() -> Term {
        Term::record_type(SymbolMap::new())
    }

    fn boolish_sum_type() -> SymbolMap {
        SymbolMap::new()
            .with(Symbol::from("left"), unit_record_type())
            .with(Symbol::from("right"), unit_record_type())
    }

    #[test]
    fn step_stops_after_one_beta_reduction() {
        let x = Name::fresh(Symbol::from("x"));
        let y = Name::fresh(Symbol::from("y"));
        let term = Term::app(
            Term::lambda(
                x.clone(),
                Term::app(Term::lambda(y.clone(), Term::var(y)), Term::var(x)),
            ),
            unit_record(),
        );

        match step(&NameMap::new(), &term).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(next.to_string(), "(app #<function> (record))")
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }

    #[test]
    fn step_chooses_a_match_branch_without_evaluating_it_further() {
        let x = Name::fresh(Symbol::from("x"));
        let z = Name::fresh(Symbol::from("z"));
        let term = Term::r#match(
            Term::variant(Symbol::from("left"), unit_record(), boolish_sum_type()),
            SymbolMap::new()
                .with(
                    Symbol::from("left"),
                    Term::lambda(
                        x,
                        Term::app(
                            Term::lambda(Name::fresh(Symbol::from("y")), unit_record()),
                            unit_record(),
                        ),
                    ),
                )
                .with(
                    Symbol::from("right"),
                    Term::lambda(
                        z,
                        Term::record(SymbolMap::new().with(Symbol::from("other"), unit_record())),
                    ),
                ),
        );

        match step(&NameMap::new(), &term).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(next.to_string(), "(app #<function> (record))")
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }

    #[test]
    fn step_reduces_the_function_side_of_an_application_first() {
        let x = Name::fresh(Symbol::from("x"));
        let z = Name::fresh(Symbol::from("z"));
        let outer_arg = Term::app(
            Term::lambda(Name::fresh(Symbol::from("y")), unit_record()),
            unit_record(),
        );
        let term = Term::app(
            Term::r#match(
                Term::variant(Symbol::from("left"), unit_record(), boolish_sum_type()),
                SymbolMap::new()
                    .with(
                        Symbol::from("left"),
                        Term::lambda(
                            x,
                            Term::lambda(Name::fresh(Symbol::from("y")), unit_record()),
                        ),
                    )
                    .with(Symbol::from("right"), Term::lambda(z, unit_record())),
            ),
            outer_arg,
        );

        match step(&NameMap::new(), &term).expect("step should succeed") {
            StepResult::Reduced(next) => {
                assert_eq!(
                    next.to_string(),
                    "(app (app #<function> (record)) (app #<function> (record)))"
                )
            }
            StepResult::Value(value) => panic!("expected a reduction step, got value {value}"),
        }
    }
}
