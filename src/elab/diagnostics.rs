//! Source-level rendering helpers for elaboration diagnostics.

use crate::{
    Computation, FALSE_SYMBOL, LAMBDA_KIND_SYMBOL, LIST_KIND_SYMBOL, Name, ProofContext, Prop,
    RUNTIME_ERROR, SYMBOL_KIND_SYMBOL, Symbol, TRUE_SYMBOL,
};

use super::source::PrettyEnv;

const DIAGNOSTIC_VALUE_LIMIT: usize = 240;

pub(super) fn compact_debug(value: &impl std::fmt::Debug) -> String {
    let mut text = format!("{value:?}");
    if text.chars().count() <= DIAGNOSTIC_VALUE_LIMIT {
        return text;
    }

    let cutoff = text
        .char_indices()
        .nth(DIAGNOSTIC_VALUE_LIMIT)
        .map(|(index, _)| index)
        .unwrap_or(text.len());
    text.truncate(cutoff);
    text.push_str("...");
    text
}

fn compact_source(text: String) -> String {
    if text.chars().count() <= DIAGNOSTIC_VALUE_LIMIT {
        return text;
    }

    let mut text = text;
    let cutoff = text
        .char_indices()
        .nth(DIAGNOSTIC_VALUE_LIMIT)
        .map(|(index, _)| index)
        .unwrap_or(text.len());
    text.truncate(cutoff);
    text.push_str("...");
    text
}

pub(super) fn symbol_source(symbol: Symbol, pretty: &PrettyEnv) -> String {
    if let Some(spelling) = pretty.symbol(symbol) {
        return spelling.to_owned();
    }

    match symbol {
        TRUE_SYMBOL => ":true".to_owned(),
        FALSE_SYMBOL => ":false".to_owned(),
        SYMBOL_KIND_SYMBOL => ":symbol".to_owned(),
        LAMBDA_KIND_SYMBOL => ":lambda".to_owned(),
        LIST_KIND_SYMBOL => ":list".to_owned(),
        _ => format!("%s{}", symbol.0),
    }
}

pub(super) fn name_source(name: Name, pretty: &PrettyEnv) -> String {
    if let Some(spelling) = pretty.computation(name) {
        return spelling.to_owned();
    }
    if let Some(spelling) = pretty.theorem(name) {
        return spelling.to_owned();
    }

    format!("#n{}", name.0)
}

fn computation_source(computation: &Computation, pretty: &PrettyEnv) -> String {
    match computation {
        Computation::Apply { function, argument } => {
            format!(
                "({} {})",
                computation_source(function, pretty),
                computation_source(argument, pretty)
            )
        }
        Computation::Lambda(lambda) => {
            format!(
                "(lambda {} {})",
                symbol_source(lambda.parameter, pretty),
                computation_source(&lambda.body, pretty)
            )
        }
        Computation::Nil => "nil".to_owned(),
        Computation::Cons { head, tail } => {
            format!(
                "(cons {} {})",
                computation_source(head, pretty),
                computation_source(tail, pretty)
            )
        }
        Computation::Head(list) => format!("(head {})", computation_source(list, pretty)),
        Computation::Tail(list) => format!("(tail {})", computation_source(list, pretty)),
        Computation::ListCase(list_case) => {
            format!(
                "(list-case {} {} {} {})",
                computation_source(&list_case.list, pretty),
                computation_source(&list_case.nil, pretty),
                symbol_source(list_case.cons, pretty),
                computation_source(&list_case.cons_case, pretty)
            )
        }
        Computation::If {
            condition,
            then_branch,
            else_branch,
        } => {
            format!(
                "(if {} {} {})",
                computation_source(condition, pretty),
                computation_source(then_branch, pretty),
                computation_source(else_branch, pretty)
            )
        }
        Computation::SymbolEq { left, right } => {
            format!(
                "(symbol-eq {} {})",
                computation_source(left, pretty),
                computation_source(right, pretty)
            )
        }
        Computation::ValueKind(value) => {
            format!("(value-kind {})", computation_source(value, pretty))
        }
        Computation::Ref(name) => name_source(*name, pretty),
        Computation::Error(error) if *error == RUNTIME_ERROR => "(error 0)".to_owned(),
        Computation::Error(error) => format!("(error {})", error.0),
        Computation::Diverge => "diverge".to_owned(),
        Computation::Var(symbol) => symbol_source(*symbol, pretty),
        Computation::Quote(symbol) => format!("(quote {})", symbol_source(*symbol, pretty)),
    }
}

fn prop_source(prop: &Prop, pretty: &PrettyEnv) -> String {
    match prop {
        Prop::Absurd => "(absurd)".to_owned(),
        Prop::Equal(left, right) => {
            format!(
                "(equal {} {})",
                computation_source(left, pretty),
                computation_source(right, pretty)
            )
        }
        Prop::IsValue(computation) => {
            format!("(is-value {})", computation_source(computation, pretty))
        }
        Prop::IsList(computation) => {
            format!("(is-list {})", computation_source(computation, pretty))
        }
        Prop::IsEffect(computation) => {
            format!("(is-effect {})", computation_source(computation, pretty))
        }
        Prop::IsOutcome(computation) => {
            format!("(is-outcome {})", computation_source(computation, pretty))
        }
        Prop::Implies(premise, conclusion) => {
            format!(
                "(implies {} {})",
                prop_source(premise, pretty),
                prop_source(conclusion, pretty)
            )
        }
        Prop::ForAll { variable, body } => {
            format!(
                "(forall {} {})",
                symbol_source(*variable, pretty),
                prop_source(body, pretty)
            )
        }
        Prop::Exists { variable, body } => {
            format!(
                "(exists {} {})",
                symbol_source(*variable, pretty),
                prop_source(body, pretty)
            )
        }
        Prop::And(left, right) => {
            format!(
                "(and {} {})",
                prop_source(left, pretty),
                prop_source(right, pretty)
            )
        }
        Prop::Or(left, right) => {
            format!(
                "(or {} {})",
                prop_source(left, pretty),
                prop_source(right, pretty)
            )
        }
    }
}

pub(super) fn compact_computation_source(computation: &Computation, pretty: &PrettyEnv) -> String {
    compact_source(computation_source(computation, pretty))
}

pub(super) fn compact_prop_source(prop: &Prop, pretty: &PrettyEnv) -> String {
    compact_source(prop_source(prop, pretty))
}

pub(super) fn prop_diagnostic(label: &str, prop: &Prop, pretty: &PrettyEnv) -> String {
    format!(
        "{label}.source: {}\n{label}.debug: {}",
        compact_prop_source(prop, pretty),
        compact_debug(prop)
    )
}

pub(super) fn computation_diagnostic(
    label: &str,
    computation: &Computation,
    pretty: &PrettyEnv,
) -> String {
    format!(
        "{label}.source: {}\n{label}.debug: {}",
        compact_computation_source(computation, pretty),
        compact_debug(computation)
    )
}

pub(super) fn context_diagnostic(
    label: &str,
    context: &ProofContext,
    pretty: &PrettyEnv,
) -> String {
    if context.is_empty() {
        return format!("{label}: (empty)");
    }

    let mut facts = context.iter().collect::<Vec<_>>();
    facts.sort_by_key(|(symbol, _)| symbol.0);
    let mut lines = vec![format!("{label}:")];
    for (symbol, prop) in facts {
        lines.push(format!(
            "  {}: {}",
            symbol_source(*symbol, pretty),
            compact_prop_source(prop, pretty)
        ));
    }
    lines.join("\n")
}
