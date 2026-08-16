use super::*;
use crate::kernel::prove_c_function_contract_predicate_unfolding;

pub(in crate::lang::click::proof) struct CheckedPredicateUnfold {
    pub(in crate::lang::click::proof) facts: ProofFacts,
    pub(in crate::lang::click::proof) added_facts: Vec<Proposition>,
    pub(in crate::lang::click::proof) added_function_entry_prerequisites: Vec<Proposition>,
    pub(in crate::lang::click::proof) added_function_entry_derivations: Vec<Theorem>,
    pub(in crate::lang::click::proof) added_unfolded_predicates: Vec<String>,
}

pub(in crate::lang::click::proof) struct CheckedPredicateFactUnfold {
    pub(in crate::lang::click::proof) facts: ProofFacts,
    pub(in crate::lang::click::proof) added_facts: Vec<Proposition>,
}

/// Applies one named predicate definition to only the indexed facts that
/// mention it. This is the proposition-level semantic core shared by pure,
/// point, and execution-frontier proof objects.
pub(in crate::lang::click::proof) fn check_unfold_predicate_in_facts(
    available: &ProofFacts,
    name: &String,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CheckedPredicateFactUnfold, ClickError> {
    if predicate_environment.get(name).is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
        )));
    }
    let assumptions = available.assumptions();
    let mut facts = available.clone();
    let mut added_facts = Vec::new();
    for proposition in available.mentioning_predicate(name) {
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
        if &unfolded != proposition && !facts.contains(&unfolded) {
            facts = facts.with_fact(unfolded.clone());
            added_facts.push(unfolded);
        }
    }
    Ok(CheckedPredicateFactUnfold { facts, added_facts })
}

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
) -> Result<CheckedPredicateUnfold, ClickError> {
    let checked_facts = check_unfold_predicate_in_facts(
        available_pure_facts,
        name,
        predicate_environment,
        click_function_environment,
        claim_label,
        tactic_index,
    )?;
    let mut added_unfolded_predicates = Vec::new();
    if !replay.unfolded_predicates.contains(name) {
        replay.unfolded_predicates.push(name.clone());
        added_unfolded_predicates.push(name.clone());
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
    let mut added_function_entry_prerequisites = Vec::new();
    let mut added_function_entry_derivations = Vec::new();
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
            if replay
                .function_entry_execution_prerequisites
                .insert(kernel.clone())
            {
                added_function_entry_prerequisites.push(kernel);
            }
            if replay.function_entry_derivations.insert(derivation.clone()) {
                added_function_entry_derivations.push(derivation);
            }
        }
    }
    Ok(CheckedPredicateUnfold {
        facts: checked_facts.facts,
        added_facts: checked_facts.added_facts,
        added_function_entry_prerequisites,
        added_function_entry_derivations,
        added_unfolded_predicates,
    })
}
