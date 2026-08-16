use super::*;
use crate::kernel::prove_c_function_contract_predicate_unfolding;

/// Checks the existing deterministic `unfold predicate` transition.
///
/// Keeping this judgment outside tactic dispatch gives explicit source replay
/// and the checked Proof API one operation to audit. This extraction does not
/// change which facts or contract-entry derivations the transition accepts.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_unfold_predicate(
    replay: &mut TacticReplayState,
    state: &CState,
    available_pure_facts: &mut Vec<Proposition>,
    name: &String,
    function: &CFunction,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    if predicate_environment.get(name).is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
        )));
    }
    if !replay.unfolded_predicates.contains(name) {
        replay.unfolded_predicates.push(name.clone());
    }
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let surface_unfoldings = available_pure_facts
        .iter()
        .filter_map(|kernel| {
            let Proposition::Predicate {
                name: kernel_name, ..
            } = kernel
            else {
                return None;
            };
            if kernel_name != name {
                return None;
            }
            let ClickProposition::PredicateCall {
                name: surface_name,
                arguments: surface_arguments,
            } = replay.surface_propositions.surface(kernel).ok()?
            else {
                return None;
            };
            let definition = predicate_environment.get(surface_name)?;
            let surface =
                instantiate_click_predicate_definition(definition, surface_arguments).ok()?;
            let unfolded = unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                std::slice::from_ref(name),
                kernel,
                &assumptions,
            )
            .ok()?;
            Some((kernel.clone(), surface, unfolded))
        })
        .collect::<Vec<_>>();
    *available_pure_facts = unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        std::slice::from_ref(name),
        available_pure_facts,
    )
    .map_err(|message| {
        ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
    })?;
    for (predicate, surface, kernel) in surface_unfoldings {
        replay
            .surface_propositions
            .record_lowering(&surface, &kernel)?;
        let contract_unfolding = replay
            .frontier
            .execution_start_state
            .as_ref()
            .is_none_or(|start| start == state)
            .then(|| {
                prove_c_function_contract_predicate_unfolding(
                    state,
                    function,
                    arguments,
                    &predicate,
                    &kernel,
                    &assumptions,
                )
            })
            .flatten();
        if let Some(derivation) = contract_unfolding {
            if !replay
                .function_entry_execution_prerequisites
                .contains(&kernel)
            {
                replay
                    .function_entry_execution_prerequisites
                    .push(kernel.clone());
            }
            if !replay.function_entry_derivations.contains(&derivation) {
                replay.function_entry_derivations.push(derivation);
            }
        }
    }
    Ok(())
}
