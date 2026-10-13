//! Language diagnostics and smart-search policy over kernel proof-fact reasoning.

use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) use crate::kernel::proof::fact_reasoning::*;

pub(super) fn negate_click_proposition(proposition: &ClickProposition) -> ClickProposition {
    match proposition {
        ClickProposition::Comparison {
            operator: ComparisonOperator::In,
            ..
        } => ClickProposition::Not(Box::new(proposition.clone())),
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
                ComparisonOperator::In => unreachable!("handled above"),
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
        Proposition::CValidPlace { .. }
            | Proposition::CMemoryReadDefined { .. }
            | Proposition::CMemoryInitialized { .. }
            | Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
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
                    Bitvector32Term::MemoryLoad(_, _, _),
                    Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
                ) | (
                    Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                    Bitvector32Term::MemoryLoad(_, _, _)
                )
            );
            if is_atomic_alias && !facts.contains(proposition) {
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
        describe_pure_fact(proposition, ParameterBinding::default()),
        crate::instrumentation::deadline_context(),
    ))
}

pub(in crate::surface) fn describe_condition_search_miss(
    proposition: &Proposition,
    available: &[Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let candidates = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .cloned()
        .collect::<Vec<_>>();
    // The goal and every premise searched are spelled with their operands,
    // through the same names, so the reader can see what was compared.
    format!(
        "condition-certificate premise search did not derive `{}` from {} ambient condition facts: {}; smart search tries individual facts and pairs and is heuristic, so split the execution into smaller steps or provide the exact premises with simple tactics",
        crate::surface::diagnostics::describe_stated_fact(proposition, parameter_binding),
        candidates.len(),
        crate::surface::diagnostics::describe_pure_facts_for_diagnostic(
            &candidates,
            parameter_binding
        ),
    )
}

/// Why a statement's premise had no checkable derivation, spelled over the
/// locals of `state`, the state the statement runs from.
pub(super) fn describe_derivation_failure(
    proposition: &Proposition,
    available: &[Proposition],
    state: &CState,
    environment: &CExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
) -> String {
    let (parameters, arguments) = crate::surface::diagnostics::local_naming_tables(state);
    if let Proposition::ConditionIs(condition, value) = proposition {
        // A condition the consulted facts decide against is refuted, not
        // underived: a narrowing bound the facts contradict, say. The
        // search's miss is then not the news, and neither smaller steps nor
        // listed premises would supply the condition.
        let consulted = available
            .iter()
            .cloned()
            .fold(PureFactContext::new(), PureFactContext::assume_proposition);
        if consulted.decide(condition) == Some(!*value) {
            return crate::surface::diagnostics::describe_refuted_condition(
                proposition,
                available,
                ParameterBinding::new(&parameters, &arguments),
            );
        }
        describe_condition_search_miss(
            proposition,
            available,
            ParameterBinding::new(&parameters, &arguments),
        )
    } else if matches!(
        proposition,
        Proposition::Predicate { name, .. }
            if crate::kernel::CFunctionContract::surface_name_from_predicate(name).is_some()
    ) {
        // A named-contract prerequisite the kernel refused is where the
        // automatic formation route ends. Print the explicit theorem that
        // replaces it rather than only the refusal.
        describe_pure_fact_with_environment(
            proposition,
            ParameterBinding::new(&parameters, &arguments),
            environment,
            predicate_environment,
        )
    } else {
        // Every other shape goes through the same bounded sentence the rest
        // of the proof diagnostics use. `Debug` here dumped the kernel
        // proposition, schemas and snapshots included.
        describe_pure_fact(proposition, ParameterBinding::new(&parameters, &arguments))
    }
}

/// The most facts a source-term prerequisite refusal lists.
const PREREQUISITE_FACT_LIMIT: usize = 6;

/// [`describe_derivation_failure`] for a prerequisite of executing
/// `statement`, stated in the source terms of the C operation that needed it
/// when it is one a proof supplies through ordinary facts: an access's
/// element bound, or a bounds check the C frontend lowered to an assertion.
/// Each names the source condition that was not shown and the consulted
/// facts about its variables, leaving out `path_facts`, the assumptions of
/// the refused path itself (on an assertion's failing path, the negation of
/// what it asserts). Every other prerequisite keeps the generic sentence.
pub(super) fn describe_statement_prerequisite_failure(
    proposition: &Proposition,
    available: &[Proposition],
    path_facts: &[Proposition],
    state: &CState,
    statement: &CStatement,
    environment: &CExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
) -> String {
    let consulted = available
        .iter()
        .filter(|fact| !path_facts.contains(fact))
        .cloned()
        .collect::<Vec<_>>();
    let refusal = describe_access_bound_prerequisite(proposition, &consulted, state, statement)
        .or_else(|| describe_assertion_prerequisite(proposition, &consulted, state, statement))
        .unwrap_or_else(|| {
            describe_derivation_failure(
                proposition,
                available,
                state,
                environment,
                predicate_environment,
            )
        });
    format!(
        "{refusal}{}",
        crate::surface::diagnostics::describe_c_statement_site()
    )
}

/// "the store to `items[i]` may write outside `items`: could not show
/// `0 <= i && i < 4` from the facts ...", then the C operation.
fn describe_access_bound_prerequisite(
    proposition: &Proposition,
    available: &[Proposition],
    state: &CState,
    statement: &CStatement,
) -> Option<String> {
    let (access, verb, memory, pointer, byte_width) = match proposition {
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => ("store to", "write", memory, pointer, *byte_width),
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } => ("read of", "read", memory, base, bytes.as_const()?),
        _ => return None,
    };
    let (parameters, arguments) = crate::surface::diagnostics::local_naming_tables(state);
    let object = crate::surface::diagnostics::describe_memory_block(
        &pointer.block,
        ParameterBinding::new(&parameters, &arguments),
    )?;
    let bound = crate::kernel::memory_access_element_bound(memory, pointer, byte_width)?;
    let spell = |term: &Bitvector32Term| {
        let spelled = crate::surface::diagnostics::describe_bitvector_with_context(
            term,
            ParameterBinding::new(&parameters, &arguments),
        );
        match spelled
            .strip_prefix('(')
            .and_then(|inner| inner.strip_suffix(')'))
        {
            Some(inner) if balanced_parentheses(inner) => inner.to_string(),
            _ => spelled,
        }
    };
    let (index, count) = (spell(&bound.index), spell(&bound.count));
    let element = if bound.stride == byte_width {
        format!("`{object}[{index}]`")
    } else {
        format!(
            "{byte_width} bytes of element `{object}[{index}]` ({}-byte elements)",
            bound.stride
        )
    };
    // The locals the index is written over, which the consulted facts must
    // mention to bear on it.
    let names = index
        .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .filter(|word| word.starts_with(|first: char| first.is_ascii_alphabetic() || first == '_'))
        .collect::<Vec<_>>();
    // A source statement can lower to several kernel ones (a bounds check
    // before the access); name the store itself when there is one.
    let mut operation = statement;
    let mut pending = vec![statement];
    while let Some(next) = pending.pop() {
        match next {
            CStatement::Scope { body } => pending.push(body),
            CStatement::Seq(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            CStatement::Store { .. } | CStatement::TypedStore { .. } if verb == "write" => {
                operation = next;
                break;
            }
            _ => {}
        }
    }
    let bound = format!("0 <= {index} && {index} < {count}");
    let reason = if names.is_empty() {
        format!("`{bound}` does not hold")
    } else {
        format!(
            "could not show `{bound}` from {}",
            describe_consulted_facts_mentioning(available, state, &names)
        )
    };
    Some(format!(
        "the {access} {element} may {verb} outside `{object}`: {reason}\n  C operation: {}",
        crate::surface::diagnostics::describe_c_statement_head(operation),
    ))
}

/// A bounds check the C frontend lowered to `assert`, refused on the path
/// where its condition is false: the prerequisite left there is the
/// truthiness obligation `0 = 1`, and the condition is what a proof must
/// show.
fn describe_assertion_prerequisite(
    proposition: &Proposition,
    available: &[Proposition],
    state: &CState,
    statement: &CStatement,
) -> Option<String> {
    // The truthiness obligation an assertion leaves on its false path.
    if !matches!(
        proposition,
        Proposition::Equal(Term::CValue(_), Term::CValue(one)) if *one == int32(1)
    ) {
        return None;
    }
    let mut pending = vec![statement];
    let condition = loop {
        match pending.pop()? {
            CStatement::Scope { body } => pending.push(body),
            CStatement::Seq(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            CStatement::Assert { condition, .. } => break condition,
            _ => {}
        }
    };
    let mut names = Vec::new();
    collect_c_expression_variables(condition, &mut names);
    let names = names.iter().map(String::as_str).collect::<Vec<_>>();
    let condition = describe_c_conjunction(condition);
    // A check over constants alone is simply false: no fact bears on it.
    if names.is_empty() {
        return Some(format!("`{condition}` does not hold"));
    }
    Some(format!(
        "could not show `{condition}` from {}",
        describe_consulted_facts_mentioning(available, state, &names)
    ))
}

/// A condition as a proof states it: a conjunction joined by `&&` without
/// the expression printer's parentheses around each operand.
fn describe_c_conjunction(condition: &CExpression) -> String {
    if let CExpression::And(left, right) = condition {
        return format!(
            "{} && {}",
            describe_c_conjunction(left),
            describe_c_conjunction(right)
        );
    }
    let rendered = crate::surface::diagnostics::describe_c_expression(condition);
    match rendered
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))
    {
        Some(inner) if balanced_parentheses(inner) => inner.to_string(),
        _ => rendered,
    }
}

fn balanced_parentheses(text: &str) -> bool {
    let mut depth = 0usize;
    for character in text.chars() {
        match character {
            '(' => depth += 1,
            ')' => match depth.checked_sub(1) {
                Some(next) => depth = next,
                None => return false,
            },
            _ => {}
        }
    }
    depth == 0
}

fn collect_c_expression_variables(expression: &CExpression, names: &mut Vec<String>) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            CExpression::Variable(name) => {
                if !names.contains(name) {
                    names.push(name.clone());
                }
            }
            CExpression::Value(_) | CExpression::FunctionAddress(_) => {}
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::AddressOf(expression)
            | CExpression::CheckedObjectAddress(expression)
            | CExpression::MemberAddress {
                object: expression, ..
            }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::PointerAligned {
                pointer: expression,
                ..
            }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression)
            | CExpression::Load(expression)
            | CExpression::TypedLoad {
                pointer: expression,
                ..
            } => pending.push(expression),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            crate::kernel::binary_c_expression!(left, right) => {
                pending.push(right);
                pending.push(left);
            }
        }
    }
}

/// The consulted condition facts whose source spelling names one of `names`,
/// bounded, as `the facts `a`, `b``.
fn describe_consulted_facts_mentioning(
    available: &[Proposition],
    state: &CState,
    names: &[&str],
) -> String {
    let mentions = |text: &str| {
        text.split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .any(|word| names.contains(&word))
    };
    let mut described = Vec::new();
    let mut omitted = 0usize;
    for fact in available {
        if !matches!(fact, Proposition::ConditionIs(_, _)) {
            continue;
        }
        let text = crate::surface::diagnostics::describe_stated_fact_over_locals(fact, state);
        if !mentions(&text) || described.contains(&text) {
            continue;
        }
        if described.len() == PREREQUISITE_FACT_LIMIT {
            omitted += 1;
            continue;
        }
        described.push(text);
    }
    if described.is_empty() {
        let names = names
            .iter()
            .map(|name| format!("`{name}`"))
            .collect::<Vec<_>>()
            .join(", ");
        return format!("no fact about {names}");
    }
    let mut listed = described
        .iter()
        .map(|fact| format!("`{fact}`"))
        .collect::<Vec<_>>()
        .join(", ");
    if omitted > 0 {
        listed.push_str(&format!(" and {omitted} more"));
    }
    let noun = if described.len() == 1 && omitted == 0 {
        "the fact"
    } else {
        "the facts"
    };
    format!("{noun} {listed}")
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
