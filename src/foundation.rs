use std::collections::BTreeMap;

use crate::kernel::{ClickResult, Name, NameMap, StepResult, Symbol, SymbolMap, Term, step};
use crate::reader::{SExpr, read};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    names: BTreeMap<Symbol, Name>,
    values: NameMap,
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
        "record" => Ok(Term::record(symbol_map_from_entries(tail, scope, context)?)),
        "record-type" => Ok(Term::record_type(symbol_map_from_entries(
            tail, scope, context,
        )?)),
        "sum-type" => Ok(Term::sum_type(symbol_map_from_entries(
            tail, scope, context,
        )?)),
        "pi" => term_from_pi(tail, scope, context),
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
        "match" => term_from_match(tail, scope, context),
        "get" => {
            expect_arity(operator.as_str(), tail, 2)?;
            Ok(Term::get(
                term_from_expr(&tail[0], scope, context)?,
                expect_symbol(&tail[1], "get key")?,
            ))
        }
        "case" => Err("case is no longer supported in the kernel; use match".to_string()),
        "if" | "with" | "has" | "atom" | "atom_eq" | "car" | "cdr" | "cons" => {
            Err(format!("{operator} is no longer supported in the kernel"))
        }
        _ => Err(format!("unknown form '{operator}'")),
    }
}

fn symbol_map_from_entries(
    items: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<SymbolMap> {
    let mut fields = SymbolMap::new();
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
    Ok(Term::lambda(
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
    let Some(fields) = sum_type.sum_type_fields() else {
        return Err("variant expects an explicit sum-type term".to_string());
    };
    Ok(Term::variant(tag, value, fields.clone()))
}

fn term_from_pi(args: &[SExpr], scope: &[(Symbol, Name)], context: &Context) -> ClickResult<Term> {
    expect_arity("pi", args, 3)?;
    let binder_symbol = expect_symbol(&args[0], "pi binder")?;
    let binder = Name::fresh(binder_symbol.clone());
    let arg_type = term_from_expr(&args[1], scope, context)?;
    let mut inner_scope = scope.to_vec();
    inner_scope.push((binder_symbol, binder.clone()));
    let return_type = term_from_expr(&args[2], &inner_scope, context)?;
    Ok(Term::pi(binder, arg_type, return_type))
}

fn term_from_match(
    args: &[SExpr],
    scope: &[(Symbol, Name)],
    context: &Context,
) -> ClickResult<Term> {
    expect_min_arity("match", args, 2)?;
    let scrutinee = term_from_expr(&args[0], scope, context)?;
    let mut handlers = SymbolMap::new();
    for handler_expr in &args[1..] {
        let SExpr::List(parts) = handler_expr else {
            return Err("match handlers must be lists".to_string());
        };
        if parts.len() != 2 {
            return Err("match handlers must have exactly two parts".to_string());
        }
        let tag = expect_symbol(&parts[0], "match handler tag")?;
        if handlers.has(tag.as_str()) {
            return Err(format!("duplicate match handler '{tag}'"));
        }
        let handler = term_from_expr(&parts[1], scope, context)?;
        handlers = handlers.with(tag, handler);
    }
    Ok(Term::r#match(scrutinee, handlers))
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
        match step(globals, &current)? {
            StepResult::Value(value) => return Ok(value),
            StepResult::Reduced(next) => current = next,
        }
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
    fn lowering_rejects_non_sum_variant_annotations() {
        assert_eq!(
            run_source("(variant left (record) (record-type))").expect_err("variant should fail"),
            "variant expects an explicit sum-type term"
        );
    }

    #[test]
    fn lowering_resolves_nested_binders() {
        let term = parse_term("(lambda x (lambda y (var x)))", &Context::new());
        assert_eq!(term.to_string(), "#<function>");
    }

    #[test]
    fn lowering_resolves_pi_binders_in_the_codomain() {
        let term = parse_term("(pi x Type (var x))", &Context::new());
        assert_eq!(term.to_string(), "(pi x Type (var x))");
    }

    #[test]
    fn declare_uses_public_kernel_step_to_evaluate_values() {
        let answer = Name::fresh(Symbol::from("answer"));
        let context = declare(
            &Context::new(),
            Declaration::Def {
                name: answer.clone(),
                value: Term::app(
                    Term::lambda(
                        Name::fresh(Symbol::from("x")),
                        Term::record(SymbolMap::new()),
                    ),
                    Term::record(SymbolMap::new()),
                ),
            },
        )
        .expect("definition should succeed");

        assert_eq!(
            context.get(&answer).expect("definition should be stored"),
            &Term::record(SymbolMap::new())
        );
    }
}
