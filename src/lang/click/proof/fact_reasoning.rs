use super::*;

pub(super) fn exact_fact_is_available(required: &Proposition, available: &[Proposition]) -> bool {
    exact_fact_is_available_across_effects(required, available, &[])
}

/// Availability where the required spelling may have been lowered at a later
/// program point than the available one: `framing` supplies the recorded
/// memory-effect facts that let the kernel see the two snapshots agree at the
/// loaded pointers.
///
/// `framing` never contributes a fact of its own — candidates come only from
/// `available` — so this cannot make an unestablished premise available.
pub(super) fn exact_fact_is_available_across_effects(
    required: &Proposition,
    available: &[Proposition],
    framing: &[ExecutionPureFact],
) -> bool {
    available
        .iter()
        .any(|fact| exact_fact_contains_conjunct(fact, required))
        || snapshot_bridged_fact_is_available(required, available, framing)
}

/// Second chance for a required condition that failed exact matching only
/// because its load atoms carry different memory snapshots than the available
/// spelling — the same fact reached through a different program point.
///
/// The cheap snapshot-blind structural filter picks candidates; the kernel's
/// snapshot-bridging prover decides them under the available facts plus
/// `framing`. Structure must match exactly, so a candidate that survives both
/// is the same fact, not a weaker one. Kept off the hot path: exact matching
/// runs first and assumptions are built only once a candidate exists.
pub(super) fn snapshot_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    framing: &[ExecutionPureFact],
) -> bool {
    let Some((required_condition, candidates)) = snapshot_blind_candidates(required, available)
    else {
        return false;
    };
    let assumptions = assumptions_from_propositions(available);
    snapshot_bridge_proves(&required_condition, &candidates, assumptions, framing)
}

/// `snapshot_bridged_fact_is_available` where the caller already holds the
/// assumption context the bridge should reason in.
///
/// Candidates still come only from `available`, so widening the assumptions
/// cannot make an unlisted fact available — the wider context only decides
/// whether two spellings denote one fact.
pub(super) fn snapshot_bridged_fact_is_available_under(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &Assumptions,
    framing: &[ExecutionPureFact],
) -> bool {
    let Some((required_condition, candidates)) = snapshot_blind_candidates(required, available)
    else {
        return false;
    };
    snapshot_bridge_proves(
        &required_condition,
        &candidates,
        assumptions.clone(),
        framing,
    )
}

/// Normalises `required` and collects the available conjuncts that could be
/// the same condition under a different memory snapshot. `None` when there is
/// nothing to bridge, which keeps the caller off the expensive path.
fn snapshot_blind_candidates(
    required: &Proposition,
    available: &[Proposition],
) -> Option<(ConditionTerm, Vec<ConditionTerm>)> {
    let normalized_required = normalize_direct_atomic_memory_loads(required);
    let Proposition::ConditionIs(required_condition, required_value) = normalized_required else {
        return None;
    };
    let mut candidates = Vec::new();
    for fact in available {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(fact, &mut conjuncts);
        for conjunct in conjuncts {
            if !matches!(conjunct, Proposition::ConditionIs(_, value) if *value == required_value) {
                continue;
            }
            let Proposition::ConditionIs(condition, _) =
                normalize_direct_atomic_memory_loads(conjunct)
            else {
                continue;
            };
            if conditions_equal_ignoring_memories(&condition, &required_condition) {
                candidates.push(condition);
            }
        }
    }
    (!candidates.is_empty()).then_some((required_condition, candidates))
}

fn snapshot_bridge_proves(
    required_condition: &ConditionTerm,
    candidates: &[ConditionTerm],
    assumptions: Assumptions,
    framing: &[ExecutionPureFact],
) -> bool {
    let assumptions = framing.iter().fold(assumptions, |assumptions, fact| {
        assumptions.assume_proposition(fact.proposition().clone())
    });
    candidates.iter().any(|candidate| {
        assumptions.conditions_equal_modulo_proven_snapshots(candidate, required_condition)
    })
}

pub(super) fn exact_fact_contains_conjunct(fact: &Proposition, required: &Proposition) -> bool {
    condition_polarity_equivalent(fact, required)
        || matches!(fact, Proposition::And(left, right)
            if exact_fact_contains_conjunct(left, required)
                || exact_fact_contains_conjunct(right, required))
}

pub(super) fn propositions_are_exact_negations(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
                || matches!(
                    (body.as_ref(), proposition),
                    (
                        Proposition::ConditionIs(left_condition, left_value),
                        Proposition::ConditionIs(right_condition, right_value),
                    ) if left_condition == right_condition && left_value == right_value
                )
        }
        _ => false,
    }
}

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

pub(in crate::lang::click) fn condition_polarity_equivalent(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            matches!(
                (
                    canonical_order_condition(left_condition, *left_value),
                    canonical_order_condition(right_condition, *right_value),
                ),
                (Some(left), Some(right)) if left == right
            )
        }
        (Proposition::Not(negated), Proposition::ConditionIs(right_condition, right_value)) => {
            matches!(
                negated.as_ref(),
                Proposition::ConditionIs(left_condition, left_value)
                    if left_condition == right_condition && left_value != right_value
            )
        }
        (Proposition::ConditionIs(left_condition, left_value), Proposition::Not(negated)) => {
            matches!(
                negated.as_ref(),
                Proposition::ConditionIs(right_condition, right_value)
                    if left_condition == right_condition && left_value != right_value
            )
        }
        _ => false,
    }
}

fn canonical_order_condition(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        _ => None,
    }
}

pub(super) fn quantified_replay_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let required = normalize_direct_atomic_memory_loads(required);
    if !matches!(required, Proposition::ForAll { .. }) {
        return None;
    }
    available.iter().find_map(|fact| {
        let fact = normalize_direct_atomic_memory_loads(fact);
        if !matches!(fact, Proposition::ForAll { .. }) {
            return None;
        }
        let forward = assumptions_from_propositions(std::slice::from_ref(&fact))
            .derive_simp_proposition(&required)
            .is_some();
        let reverse = assumptions_from_propositions(std::slice::from_ref(&required))
            .derive_simp_proposition(&fact)
            .is_some();
        (forward && reverse).then_some(fact)
    })
}

pub(super) fn quantified_binder_equivalent(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        (
            Proposition::Exists {
                name: left_name,
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::Exists {
                name: right_name,
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_name == right_name
                && left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        _ => false,
    }
}

/// `quantified_binder_equivalent` sees through ONE binder renaming; a nested
/// quantifier needs the rename applied at every level.
///
/// Certificate generation compares a spelling it lowers itself against a fact
/// the drain lowered separately, and the two lowerings mint different binder
/// variables, so a nested `forall` fact is only recognizable up to renaming.
/// This is a generation-side recognizer: it decides which surface spelling to
/// WRITE, never whether a proof is accepted. The written spelling still has to
/// satisfy `derivation.replay` and then the replay judgment itself, both of
/// which instantiate quantifiers rather than compare them structurally.
/// Applies `normalize_direct_atomic_memory_loads` below the propositional
/// connectives and quantifier binders it does not itself descend through, so
/// two lowerings of one fact whose load memories differ only by
/// load-irrelevant blocks or cells (the canonical-load-memory relation)
/// compare equal. Deterministic and assumption-free, like the leaf
/// normalization it delegates to.
fn normalize_quantified_memory_loads(proposition: &Proposition, depth: usize) -> Proposition {
    if depth == 0 {
        return proposition.clone();
    }
    let recurse = |body: &Proposition| Box::new(normalize_quantified_memory_loads(body, depth - 1));
    match proposition {
        Proposition::And(left, right) => Proposition::And(recurse(left), recurse(right)),
        Proposition::Or(left, right) => Proposition::Or(recurse(left), recurse(right)),
        Proposition::Implies(left, right) => Proposition::Implies(recurse(left), recurse(right)),
        Proposition::Not(body) => Proposition::Not(recurse(body)),
        Proposition::ForAll { var, sort, body } => Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: recurse(body),
        },
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: recurse(body),
        },
        other => normalize_direct_atomic_memory_loads(other),
    }
}

/// Generation-side equality up to assumption-free canonical load spelling.
/// A selected spelling still has to replay from its own lowered proposition,
/// so this can broaden candidate recognition without broadening acceptance.
pub(super) fn propositions_match_up_to_canonical_loads(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    left == right
        || normalize_quantified_memory_loads(left, 64)
            == normalize_quantified_memory_loads(right, 64)
}

/// See the doc comment below: a generation-side recognizer only. Besides the
/// per-level binder renaming, bodies are also compared after canonical-load
/// normalization, because the drain records facts with canonicalized load
/// snapshots while a fresh lowering of the same spelling reads through the
/// retained program-point state, whose memory still carries load-irrelevant
/// local cells.
pub(super) fn nested_quantified_binder_equivalent(
    left: &Proposition,
    right: &Proposition,
    depth: usize,
) -> bool {
    nested_quantified_binder_equivalent_exact(left, right, depth)
        || nested_quantified_binder_equivalent_exact(
            &normalize_quantified_memory_loads(left, 64),
            &normalize_quantified_memory_loads(right, 64),
            depth,
        )
}

fn nested_quantified_binder_equivalent_exact(
    left: &Proposition,
    right: &Proposition,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    if quantified_binder_equivalent(left, right) {
        return true;
    }
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && nested_quantified_binder_equivalent_exact(
                    &substitute_int32_variable_in_proposition(
                        left_body,
                        *left_var,
                        Bitvector32Term::Variable(*right_var),
                    ),
                    right_body,
                    depth - 1,
                )
        }
        _ => false,
    }
}

pub(super) fn pure_fact_is_replay_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    available.contains(required)
        || materialization_equivalent_available_fact(required, available).is_some()
        || available
            .iter()
            .any(|fact| quantified_binder_equivalent(required, fact))
        || quantified_replay_equivalent_available_fact(required, available).is_some()
}

pub(super) fn atomic_conjuncts<'a>(
    proposition: &'a Proposition,
    output: &mut Vec<&'a Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            atomic_conjuncts(left, output);
            atomic_conjuncts(right, output);
        }
        proposition => output.push(proposition),
    }
}

pub(super) fn materialization_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    fn matching_conjunct(
        fact: &Proposition,
        required: &Proposition,
        normalized_required: &Proposition,
    ) -> Option<Proposition> {
        if fact == required || normalize_direct_atomic_memory_loads(fact) == *normalized_required {
            return Some(fact.clone());
        }
        let Proposition::And(left, right) = fact else {
            return None;
        };
        matching_conjunct(left, required, normalized_required)
            .or_else(|| matching_conjunct(right, required, normalized_required))
    }

    let normalized_required = normalize_direct_atomic_memory_loads(required);
    available
        .iter()
        .find_map(|fact| matching_conjunct(fact, required, &normalized_required))
}

/// Cheap membership for explicit replay certificates with many premises.
///
/// `frame using` used to rescan and renormalize the full proof context for
/// every named fact. Large, otherwise-simple certificates therefore became
/// quadratic. The index covers the overwhelmingly common exact and
/// materialization-equivalent cases; callers retain their semantic fallbacks
/// for snapshot bridging and polarity-equivalent spellings.
pub(super) struct ExactReplayFactIndex {
    exact: std::collections::BTreeSet<Proposition>,
    materialized: std::collections::BTreeSet<Proposition>,
}

impl ExactReplayFactIndex {
    pub(super) fn new(available: &[Proposition]) -> Self {
        let mut exact = std::collections::BTreeSet::new();
        let mut materialized = std::collections::BTreeSet::new();
        for fact in available {
            let mut conjuncts = Vec::new();
            atomic_conjuncts(fact, &mut conjuncts);
            for conjunct in conjuncts {
                exact.insert(conjunct.clone());
                materialized.insert(normalize_direct_atomic_memory_loads(conjunct));
            }
        }
        Self {
            exact,
            materialized,
        }
    }

    pub(super) fn contains(&self, required: &Proposition) -> bool {
        self.exact.contains(required)
            || self
                .materialized
                .contains(&normalize_direct_atomic_memory_loads(required))
    }
}

pub(super) fn directly_matching_separation_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let Proposition::CResourceSeparate {
        left: required_left,
        right: required_right,
    } = required
    else {
        return None;
    };
    let assumptions = assumptions_from_propositions(available);
    available.iter().find_map(|fact| {
        let Proposition::CResourceSeparate { left, right } = fact else {
            return None;
        };
        let same_orientation = c_resources_directly_match(left, required_left, &assumptions)
            && c_resources_directly_match(right, required_right, &assumptions);
        let reverse_orientation = c_resources_directly_match(left, required_right, &assumptions)
            && c_resources_directly_match(right, required_left, &assumptions);
        (same_orientation || reverse_orientation).then(|| fact.clone())
    })
}

pub(super) fn directly_covering_loadability_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    matches!(required, Proposition::CMemoryLoadable { .. }).then_some(())?;
    available.iter().find_map(|fact| {
        matches!(fact, Proposition::CMemoryLoadable { .. })
            .then(|| {
                assumptions_from_propositions(std::slice::from_ref(fact))
                    .derive_atomic_proposition(required)
                    .map(|_| fact.clone())
            })
            .flatten()
    })
}

pub(super) fn proposition_has_contextual_derivation_rules(proposition: &Proposition) -> bool {
    !matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapLifetimeRetired { .. }
    )
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
    let mut selected = initial.context_premises().to_vec();
    let mut index = 0;
    while index < selected.len() {
        check_verification_deadline()?;
        let mut reduced = selected.clone();
        reduced.remove(index);
        if derive(&reduced).is_some() {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    check_verification_deadline()?;
    Ok(derive(&selected))
}

pub(super) fn minimal_simp_proposition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Result<Option<PropositionDerivation>, ClickError> {
    if !proposition_has_contextual_derivation_rules(proposition) {
        return Ok(None);
    }
    let derive = |facts: &[Proposition]| {
        assumptions_from_propositions(facts).derive_simp_proposition(proposition)
    };
    check_verification_deadline()?;
    let Some(initial) = derive(available) else {
        check_verification_deadline()?;
        return Ok(None);
    };
    let mut selected = initial.context_premises().to_vec();
    let mut index = 0;
    while index < selected.len() {
        check_verification_deadline()?;
        let mut reduced = selected.clone();
        reduced.remove(index);
        if derive(&reduced).is_some() {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    check_verification_deadline()?;
    Ok(derive(&selected))
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

pub(in crate::lang::click) fn search_condition_derivation(
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
    for (left_index, left) in candidates.iter().enumerate() {
        for right in &candidates[left_index + 1..] {
            check_condition_search_budget(proposition, candidates.len())?;
            if let Some(derivation) = derive(&[(*left).clone(), (*right).clone()]) {
                check_condition_search_budget(proposition, candidates.len())?;
                return Ok(Some(derivation));
            }
            check_condition_search_budget(proposition, candidates.len())?;
        }
    }
    Ok(None)
}


pub(super) fn exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    let left = normalize_direct_atomic_memory_loads(left);
    let right = normalize_direct_atomic_memory_loads(right);
    normalized_exact_facts_directly_conflict(&left, &right)
}

fn normalized_exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (Proposition::And(first, second), _) => {
            normalized_exact_facts_directly_conflict(first, right)
                || normalized_exact_facts_directly_conflict(second, right)
        }
        (_, Proposition::And(first, second)) => {
            normalized_exact_facts_directly_conflict(left, first)
                || normalized_exact_facts_directly_conflict(left, second)
        }
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
        }
        _ => false,
    }
}

pub(super) fn fact_conflicts_with_assumptions(
    fact: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            fact_conflicts_with_assumptions(left, assumptions)
                || fact_conflicts_with_assumptions(right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => assumptions.proves(body),
        fact => assumptions.proves(&Proposition::Not(Box::new(fact.clone()))),
    }
}

pub(super) fn assumptions_for_direct_fact_transport(propositions: &[Proposition]) -> Assumptions {
    fn collect(proposition: &Proposition, facts: &mut Vec<Proposition>) {
        match proposition {
            Proposition::ConditionIs(_, _)
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapLifetimeRetired { .. }
            | Proposition::CResourceSeparate { .. } => facts.push(proposition.clone()),
            Proposition::And(left, right) => {
                collect(left, facts);
                collect(right, facts);
            }
            _ => {}
        }
    }

    let mut facts = Vec::new();
    for proposition in propositions {
        collect(proposition, &mut facts);
    }
    assumptions_from_propositions(&facts)
}

pub(super) fn facts_for_direct_surface_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = Vec::new();
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        facts.extend(
            conjuncts
                .into_iter()
                .filter(|&proposition| {
                    matches!(
                        proposition,
                        Proposition::CMemoryLoadable { .. }
                            | Proposition::CMemoryCanStore { .. }
                            | Proposition::CMemoryDisjoint { .. }
                            | Proposition::CResourceSeparate { .. }
                            | Proposition::CResourceContains { .. }
                            | Proposition::CMemoryMutatesOnly { .. }
                            | Proposition::CMemoryEffectSummary { .. }
                            | Proposition::CHeapLifetimeRetired { .. }
                    )
                })
                .cloned(),
        );
    }
    facts.sort();
    facts.dedup();
    facts
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
