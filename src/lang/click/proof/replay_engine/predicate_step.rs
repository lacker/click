use super::*;
use crate::kernel::prove_c_function_contract_predicate_unfolding;

/// Checks the existing deterministic `unfold predicate` transition against
/// the persistent facts owned by `Proof`.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_unfold_predicate_facts(
    replay: &mut TacticReplayState,
    state: &CState,
    available_pure_facts: &ProofFacts,
    name: &String,
    function: &CFunction,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<ProofFacts, ClickError> {
    if predicate_environment.get(name).is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
        )));
    }
    if !replay.unfolded_predicates.contains(name) {
        replay.unfolded_predicates.push(name.clone());
    }
    let assumptions = available_pure_facts.assumptions();
    let surface_unfoldings = available_pure_facts
        .mentioning_predicate(name)
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
                assumptions,
            )
            .ok()?;
            Some((kernel.clone(), surface, unfolded))
        })
        .collect::<Vec<_>>();
    let mut facts = available_pure_facts.clone();
    for proposition in available_pure_facts.mentioning_predicate(name) {
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            std::slice::from_ref(name),
            proposition,
            assumptions,
        )
        .map_err(|message| {
            ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
        })?;
        if &unfolded != proposition {
            facts = facts.with_fact(unfolded);
        }
    }
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
                    assumptions,
                )
            })
            .flatten();
        if let Some(derivation) = contract_unfolding {
            replay
                .function_entry_execution_prerequisites
                .insert(kernel.clone());
            replay.function_entry_derivations.insert(derivation);
        }
    }
    Ok(facts)
}
