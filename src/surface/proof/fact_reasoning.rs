//! Language diagnostics and smart-search policy over kernel proof-fact reasoning.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) use crate::kernel::proof::fact_reasoning::*;

pub(super) fn negate_click_proposition(proposition: &ClickProposition) -> ClickProposition {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ClickProposition::Comparison {
            left: left.clone(),
            operator: match operator {
                ComparisonOperator::Equal => ComparisonOperator::NotEqual,
                ComparisonOperator::NotEqual => ComparisonOperator::Equal,
                ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
                ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
                ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
                ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
            },
            right: right.clone(),
        },
        ClickProposition::Not(body) => body.as_ref().clone(),
        proposition => ClickProposition::Not(Box::new(proposition.clone())),
    }
}

pub(super) fn facts_for_direct_surface_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = Vec::new();
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        facts.extend(
            conjuncts
                .into_iter()
                .filter(|&proposition| is_direct_surface_lowering_fact(proposition))
                .cloned(),
        );
    }
    facts.sort();
    facts.dedup();
    facts
}

pub(super) fn is_direct_surface_lowering_fact(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
            | Proposition::CResourceContains { .. }
            | Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
    )
}

pub(super) fn facts_for_direct_derivation_lowering(
    propositions: &[Proposition],
) -> Vec<Proposition> {
    let mut facts = facts_for_direct_surface_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            let direct_condition = matches!(
                proposition,
                Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
            ) || matches!(proposition, Proposition::ConditionIs(_, _))
                && !c_condition_fact_has_memory(proposition);
            if direct_condition && !facts.contains(proposition) {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

/// Facts that may establish that a restricted simplifier's surface goal and
/// premises are defined without performing an equality step on its behalf.
/// Array bounds are part of expression lowering; equalities remain available
/// only through the explicitly listed `simp() using` premises.
pub(super) fn facts_for_restricted_simp_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_direct_surface_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            if matches!(
                proposition,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(_, _)
                        | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                        | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                        | ConditionTerm::Bitvector32SignedGreaterEqual(_, _),
                    _,
                )
            ) && !facts.contains(proposition)
            {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

pub(super) fn facts_for_smart_have_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_direct_derivation_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                proposition
            else {
                continue;
            };
            let is_atomic_alias = matches!(
                (left.as_ref(), right.as_ref()),
                (
                    Bitvector32Term::MemoryLoad(_, _),
                    Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
                ) | (
                    Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                    Bitvector32Term::MemoryLoad(_, _)
                )
            );
            if is_atomic_alias && !facts.contains(proposition) {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

pub(super) fn facts_for_simple_goal_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_smart_have_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            let include = match proposition {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(_, _)
                    | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                    | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                    | ConditionTerm::Bitvector32SignedGreaterEqual(_, _)
                    | ConditionTerm::PointerOffsetEqual(_, _),
                    _,
                ) => true,
                // A false-polarity atomic alias decides branch conditions
                // (`if (p[i] == x)`) whose negative arm the goal's `If` terms
                // still carry; the smart-have set only admits the true polarity.
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), false) => {
                    matches!(
                        (left.as_ref(), right.as_ref()),
                        (
                            Bitvector32Term::MemoryLoad(_, _),
                            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
                        ) | (
                            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                            Bitvector32Term::MemoryLoad(_, _)
                        )
                    )
                }
                _ => false,
            };
            if include && !facts.contains(proposition) {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

fn minimize_derivation_premises(
    initial: PropositionDerivation,
    derive: impl Fn(&[Proposition]) -> Option<PropositionDerivation>,
) -> Result<PropositionDerivation, ClickError> {
    fn remove_group(
        selected: Vec<Proposition>,
        candidates: &[Proposition],
        derive: &impl Fn(&[Proposition]) -> Option<PropositionDerivation>,
    ) -> Result<Vec<Proposition>, ClickError> {
        check_verification_deadline()?;
        let candidate_set = candidates.iter().collect::<BTreeSet<_>>();
        let reduced = selected
            .iter()
            .filter(|premise| !candidate_set.contains(premise))
            .cloned()
            .collect::<Vec<_>>();
        if !reduced.is_empty() && derive(&reduced).is_some() {
            return Ok(reduced);
        }
        if candidates.len() <= 1 {
            return Ok(selected);
        }
        let middle = candidates.len() / 2;
        let selected = remove_group(selected, &candidates[..middle], derive)?;
        remove_group(selected, &candidates[middle..], derive)
    }

    let candidates = initial.context_premises();
    let selected = remove_group(candidates.clone(), &candidates, &derive)?;
    check_verification_deadline()?;
    Ok(derive(&selected).unwrap_or(initial))
}

pub(super) fn minimal_proposition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Result<Option<PropositionDerivation>, ClickError> {
    if !proposition_has_contextual_derivation_rules(proposition) {
        return Ok(None);
    }
    if matches!(proposition, Proposition::ConditionIs(_, _)) {
        return search_condition_derivation(proposition, available);
    }
    let derive = |facts: &[Proposition]| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_proposition(proposition)
            .or_else(|| assumptions.derive_simp_proposition(proposition))
    };
    check_verification_deadline()?;
    let Some(initial) = derive(available) else {
        check_verification_deadline()?;
        return Ok(None);
    };
    check_verification_deadline()?;
    Ok(Some(minimize_derivation_premises(initial, derive)?))
}

fn condition_search_budget_error(proposition: &Proposition, candidate_count: usize) -> ClickError {
    ClickError::new(format!(
        "condition-certificate premise search exceeded the active verification budget\n  target: {}\n  ambient condition facts: {candidate_count}\n  context: {}\nprovide the exact premises with simple tactics to continue",
        describe_pure_fact(proposition, &[], &[]),
        crate::instrumentation::deadline_context(),
    ))
}

pub(super) fn describe_condition_search_miss(
    proposition: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let candidate_count = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .count();
    format!(
        "condition-certificate premise search did not derive {} from {candidate_count} ambient condition facts: {}; smart search tries individual facts and pairs and is heuristic, so split the execution into smaller steps or provide the exact premises with simple tactics",
        describe_pure_fact(proposition, parameters, arguments),
        describe_pure_facts(
            &available
                .iter()
                .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
                .cloned()
                .collect::<Vec<_>>()
        ),
    )
}

pub(super) fn describe_derivation_failure(
    proposition: &Proposition,
    available: &[Proposition],
) -> String {
    if matches!(proposition, Proposition::ConditionIs(_, _)) {
        describe_condition_search_miss(proposition, available, &[], &[])
    } else {
        bounded_debug(proposition)
    }
}

fn check_condition_search_budget(
    proposition: &Proposition,
    candidate_count: usize,
) -> Result<(), ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        Err(condition_search_budget_error(proposition, candidate_count))
    } else {
        Ok(())
    }
}

pub(in crate::surface) fn search_condition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Result<Option<PropositionDerivation>, ClickError> {
    let candidates = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .collect::<Vec<_>>();
    check_condition_search_budget(proposition, candidates.len())?;
    let derive = |facts: &[Proposition]| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_atomic_proposition(proposition)
            .or_else(|| assumptions.derive_simp_atomic_proposition(proposition))
    };
    for fact in &candidates {
        check_condition_search_budget(proposition, candidates.len())?;
        if let Some(derivation) = derive(std::slice::from_ref(*fact)) {
            check_condition_search_budget(proposition, candidates.len())?;
            return Ok(Some(derivation));
        }
        check_condition_search_budget(proposition, candidates.len())?;
    }
    let goal_variables = crate::kernel::condition_fact_variables(proposition);
    let candidate_variables = candidates
        .iter()
        .map(|fact| crate::kernel::condition_fact_variables(fact))
        .collect::<Vec<_>>();
    let mut variable_buckets = BTreeMap::<Variable, Vec<usize>>::new();
    let mut goal_connected = Vec::new();
    for (index, variables) in candidate_variables.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        if variables
            .iter()
            .any(|variable| goal_variables.contains(variable))
        {
            goal_connected.push(index);
        }
        for variable in variables {
            variable_buckets.entry(*variable).or_default().push(index);
        }
    }
    let mut candidate_pairs = BTreeSet::new();
    for bucket in variable_buckets.values() {
        for (position, first) in bucket.iter().enumerate() {
            for second in &bucket[position + 1..] {
                crate::instrumentation::record_deterministic_work(1);
                candidate_pairs.insert((*first.min(second), *first.max(second)));
            }
        }
    }
    for (position, first) in goal_connected.iter().enumerate() {
        for second in &goal_connected[position + 1..] {
            crate::instrumentation::record_deterministic_work(1);
            candidate_pairs.insert((*first.min(second), *first.max(second)));
        }
    }
    for (first, second) in candidate_pairs {
        check_condition_search_budget(proposition, candidates.len())?;
        if let Some(derivation) = derive(&[candidates[first].clone(), candidates[second].clone()]) {
            check_condition_search_budget(proposition, candidates.len())?;
            return Ok(Some(derivation));
        }
        check_condition_search_budget(proposition, candidates.len())?;
    }
    if candidates.is_empty() {
        return Ok(None);
    }
    check_condition_search_budget(proposition, candidates.len())?;
    let complete = candidates
        .iter()
        .map(|fact| (*fact).clone())
        .collect::<Vec<_>>();
    let Some(initial) = derive(&complete) else {
        check_condition_search_budget(proposition, candidates.len())?;
        return Ok(None);
    };
    check_condition_search_budget(proposition, candidates.len())?;
    Ok(Some(minimize_derivation_premises(initial, derive)?))
}
