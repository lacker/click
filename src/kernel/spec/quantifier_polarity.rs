//! UNTESTED RECOVERY PROTOTYPE: quantifier-prefix polarity only.
//! See roadmap/unspellable-facts.md before continuing or publishing.
//!
//! Refuting an existential checks every candidate; refuting a universal
//! selects one defined counterexample. This prototype selects the binder
//! before lowering its body. It is not the complete definedness migration.

use super::*;

struct Binder {
    universal: bool,
    data: SpecUniversalBinder,
}

fn binder(proposition: &SpecProposition) -> Option<(Binder, &SpecProposition)> {
    use SpecProposition::*;
    let (universal, name, variable, sort, body) = match proposition {
        ForAllInteger { name, variable, body } | ExistsInteger { name, variable, body } =>
            (matches!(proposition, ForAllInteger { .. }), name, *variable, Sort::Integer, body),
        ForAllAlgebraic { name, variable, algebraic_type, body }
        | ExistsAlgebraic { name, variable, algebraic_type, body } =>
            (matches!(proposition, ForAllAlgebraic { .. }), name, *variable, Sort::Algebraic(algebraic_type.clone()), body),
        ForAllInt32 { name, variable, body } | ExistsInt32 { name, variable, body } =>
            (matches!(proposition, ForAllInt32 { .. }), name, *variable, Sort::CInt32, body),
        ForAllMachineInteger { name, variable, integer_type, body }
        | ExistsMachineInteger { name, variable, integer_type, body } =>
            (matches!(proposition, ForAllMachineInteger { .. }), name, *variable, Sort::machine_integer(*integer_type), body),
        ForAllPointer { name, variable, c_type, body }
        | ExistsPointer { name, variable, c_type, body } =>
            (matches!(proposition, ForAllPointer { .. }), name, *variable, Sort::CPointer(*c_type), body),
        _ => return None,
    };
    Some((Binder {
        universal,
        data: SpecUniversalBinder {
            name: name.clone(),
            variable,
            pointer: matches!(&sort, Sort::CPointer(_)),
            integer: matches!(&sort, Sort::Integer),
            sort,
        },
    }, body))
}

pub(super) fn lower_prefix(
    scope: SpecScope<'_>,
    proposition: &SpecProposition,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<Vec<SpecPropositionPath>>> {
    let mut body = proposition;
    let mut negative = false;
    let mut binders = Vec::new();
    let mut quantified_assumptions = assumptions.clone();
    loop {
        if let SpecProposition::Not(inner) = body {
            negative = !negative;
            body = inner;
            continue;
        }
        let Some((mut binder, inner)) = binder(body) else { break };
        binder.universal ^= negative;
        for fact in machine_quantifier_range_facts(&binder.data.sort, binder.data.variable) {
            quantified_assumptions = quantified_assumptions.assume_proposition(fact.proposition().clone());
        }
        binders.push(binder);
        body = inner;
    }
    if binders.is_empty() {
        return Ok(None);
    }
    let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope, body, &quantified_assumptions, budget,
    )?;
    if negative {
        paths = paths.into_iter().map(wrap_spec_negation_path).collect();
    }
    for binder in binders.into_iter().rev() {
        let Binder { universal, data } = binder;
        if universal {
            paths = paths.into_iter().map(|path| wrap_spec_universal_path(path, &data)).collect();
        } else {
            let range_facts = machine_quantifier_range_facts(&data.sort, data.variable);
            for path in &mut paths {
                let mut facts = range_facts.clone();
                facts.append(&mut path.facts);
                path.facts = facts;
            }
            paths = vec![existential::ScopedExistential::new(data.name, data.variable, data.sort, paths).into_checked_path()];
        }
    }
    Ok(Some(paths))
}
