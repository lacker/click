mod computation;
mod intervals;
mod known_bridges;
mod machine_ranges;
pub(in crate::kernel) use computation::{
    closed_algebraic_if_comparison, closed_integer_if_comparison, is_literal_value_if_guard_root,
    literal_value_if_guard, reduce_known_int32_match_comparison,
};
pub(crate) use computation::{computes_leaf, trivial_condition_value};
pub(in crate::kernel) use known_bridges::known_uint32_from_defined_bytes;
pub(crate) use known_bridges::literal_mask_bounds;
pub(crate) use known_bridges::{
    is_quotient_remainder_order, known_bridge_leaf, known_shifted_one, pointer_projection_source,
};

use crate::kernel::CompareRelation;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::*;

pub(crate) fn normalizes_context_free(goal: &Proposition) -> bool {
    if let Some(reduced) = closed_algebraic_if_comparison(goal)
        && normalizes_context_free(&reduced)
    {
        return true;
    }
    if let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = goal {
        let reduced_left = super::term_rewrite::TermRewrite::normalize_algebraic(left.old_form());
        let reduced_right = super::term_rewrite::TermRewrite::normalize_algebraic(right.old_form());
        if reduced_left.is_some() || reduced_right.is_some() {
            return normalizes_context_free_reduced(&Proposition::Equal(
                Term::Algebraic(reduced_left.map(Into::into).unwrap_or_else(|| left.clone())),
                Term::Algebraic(
                    reduced_right
                        .map(Into::into)
                        .unwrap_or_else(|| right.clone()),
                ),
            ));
        }
    }
    normalizes_context_free_reduced(goal)
}

fn normalizes_context_free_reduced(goal: &Proposition) -> bool {
    if let Proposition::ConditionIs(condition, expected) = goal
        && let Some(actual) = condition.operand_view().closed_float_predicate_value()
    {
        return actual == *expected;
    }
    if let Some(holds) =
        crate::kernel::spec::checks_retained_sequence_comparison(goal, true, |condition, truth| {
            normalizes_context_free_reduced(&Proposition::condition_is(condition.clone(), truth))
        })
    {
        return holds;
    }
    // A guarded proposition whose guard has no model, or a universal over
    // one, is context-free: `intro` exposes the guard and `contradiction`
    // closes it. This is a planning judgment only; lowering keeps such a
    // guarded obligation, so written proofs still see the guard.
    if vacuously_guarded(goal) {
        return true;
    }
    if let Proposition::ConditionIs(condition, value) = goal {
        if let Some(root) = condition.root()
            && let KernelTermNode::IntegerCompare {
                operator:
                    operator @ (IntegerComparisonOperator::Equal | IntegerComparisonOperator::NotEqual),
                arguments: [left, right],
            } = root.node()
            && let (KernelTermNode::Fold(left), KernelTermNode::Fold(right)) =
                (left.node(), right.node())
            && super::fact_keys::retained_folds_alpha_equivalent(left, right) == Some(true)
        {
            return *value == (*operator == IntegerComparisonOperator::Equal);
        }
        match condition.old_form() {
            OldConditionTerm::IntegerEqual(left, right) if left == right => return *value,
            OldConditionTerm::IntegerNotEqual(left, right) if left == right => return !*value,
            OldConditionTerm::IntegerEqual(left, right)
                if super::fact_keys::integer_terms_alpha_equivalent(left, right) == Some(true) =>
            {
                return *value;
            }
            OldConditionTerm::IntegerNotEqual(left, right)
                if super::fact_keys::integer_terms_alpha_equivalent(left, right) == Some(true) =>
            {
                return !*value;
            }
            _ => {}
        }
    }
    if crate::kernel::reasoning::path_facts::solve_builtin_prop(goal) {
        return true;
    }
    if let Proposition::ConditionIs(condition, expected) = goal
        && let Some(actual) = computation::known_int32_match_comparison_value(condition.old_form())
    {
        return actual == *expected;
    }
    if let Proposition::ConditionIs(condition, value) = goal
        && let Some(equal) = computation::machine_affine_equality(
            condition.old_form(),
            crate::kernel::eval::canonical_term,
        )
    {
        return equal == *value;
    }
    if let Proposition::ConditionIs(condition, value) = goal
        && let Some(holds) = computation::integer_affine_comparison(condition.old_form())
    {
        return holds == *value;
    }
    if let Proposition::ConditionIs(condition, true) = goal
        && computation::integer_distribution_step(condition.old_form())
    {
        return true;
    }
    if let Proposition::ConditionIs(condition, value) = goal
        && let Some(holds) = computation::integer_linear_comparison(condition.old_form())
    {
        return holds == *value;
    }
    if let Proposition::ConditionIs(condition, value) = goal
        && let Some(holds) = computation::integer_operation_bound_comparison(condition.old_form())
    {
        return holds == *value;
    }
    // Constructor congruence is definitional reduction over the goal's own
    // structure: two applications of one constructor are equal when their
    // corresponding fields are. The walk is bounded by the goal.
    if let Some(fields) = crate::kernel::assumptions::algebraic_constructor_field_equalities(goal)
        && !fields.is_empty()
    {
        return fields.iter().all(normalizes_context_free);
    }
    // No premises, so what remains is the atomic theory on the empty
    // context. The ambient legs of the relocated planner -- fact lookup,
    // case splits over disjunction facts, universal instantiation,
    // singleton substitution, the inconsistency fallback -- are vacuous
    // here by construction.
    SelectedFacts::from_propositions(&[]).proves_atomic_for_derivation(goal, false)
}

fn vacuously_guarded(goal: &Proposition) -> bool {
    match goal {
        Proposition::Implies(antecedent, _) => {
            crate::kernel::reasoning::path_facts::conjunction_order_facts_are_inconsistent(
                antecedent,
            )
        }
        Proposition::ForAll { body, .. } => vacuously_guarded(body),
        _ => false,
    }
}

/// Transitional leaf check for structural-normalization migration:
/// top-level conjunction, disjunction, and implication construction must be
/// explicit, while the remaining logical constructors continue through the
/// compatibility path below.
pub(crate) fn normalizes_context_free_leaf(goal: &Proposition) -> bool {
    if matches!(
        goal,
        Proposition::And(_, _)
            | Proposition::Or(_, _)
            | Proposition::Implies(_, _)
            | Proposition::ForAll { .. }
            | Proposition::Exists { .. }
    ) {
        return false;
    }
    normalizes_context_free(goal)
}

/// Whether one enumerated instance of a finite universal is discharged
/// without a proof search.
///
/// `enumerate` names its instances, so checking them is structural: a
/// conjunction splits, an instance guard that folds to true is consumed, and
/// every leaf must be an exactly available fact or close through the
/// normalization leaf. A leaf that is itself a quantifier is a further proof
/// step, not something this enumeration discharges.
pub(crate) fn enumerated_instance_is_discharged(
    instance: &Proposition,
    facts: &super::PureFactStore,
) -> bool {
    if facts.contains(instance) {
        return true;
    }
    match instance {
        Proposition::And(left, right) => {
            enumerated_instance_is_discharged(left, facts)
                && enumerated_instance_is_discharged(right, facts)
        }
        Proposition::Implies(guard, conclusion) => {
            // A guard this instantiation folds to false makes the instance
            // vacuous; one that folds to true leaves the conclusion.
            instance_guard_folds_to_false(guard)
                || instance_guard_folds_to_true(guard)
                    && enumerated_instance_is_discharged(conclusion, facts)
        }
        _ => normalizes_context_free_leaf(instance),
    }
}

/// Whether an instance guard folds to true with no ambient fact and no
/// logical search: conjunction splits structurally and each conjunct closes
/// through the normalization leaf.
fn instance_guard_folds_to_true(guard: &Proposition) -> bool {
    match guard {
        Proposition::And(left, right) => {
            instance_guard_folds_to_true(left) && instance_guard_folds_to_true(right)
        }
        _ => normalizes_context_free_leaf(guard),
    }
}

/// Whether an instance guard folds to false the same way: one false conjunct
/// refutes a conjunction, and a disjunction needs both sides refuted. Each
/// leaf is refuted through the normalization leaf on its negation.
pub(crate) fn instance_guard_folds_to_false(guard: &Proposition) -> bool {
    match guard {
        Proposition::And(left, right) => {
            instance_guard_folds_to_false(left) || instance_guard_folds_to_false(right)
        }
        Proposition::Or(left, right) => {
            instance_guard_folds_to_false(left) && instance_guard_folds_to_false(right)
        }
        _ => normalizes_context_free_leaf(&Proposition::Not(Box::new(guard.clone()))),
    }
}

pub(crate) use crate::kernel::spec::is_single_normalization_condition;

/// Reduce checked, explicitly cited conditions and equalities established by
/// the current trusted graph, then normalize the resulting leaf.
/// Graph queries use the maintained context; they never scan ambient facts.
pub(crate) fn normalize_using_conditions(
    goal: &Proposition,
    premises: &[Proposition],
    facts: &super::PureFactStore,
) -> Result<(), ConditionalNormalizationError> {
    if let Proposition::ResourceSeparate { left, right } = goal
        && (matches!(left.as_ref(), Resource::Footprint(_))
            || matches!(right.as_ref(), Resource::Footprint(_)))
    {
        let mut selected = PureFactContext::new();
        // Keep the checked address congruence used by ordinary normalization.
        // Resource authority below still comes only from the written premises.
        selected.equality_graph = facts.assumptions().equality_graph.clone();
        for (index, premise) in premises.iter().enumerate() {
            if !facts.available(premise) && !crate::kernel::proposition_holds_without_facts(premise)
            {
                return Err(ConditionalNormalizationError::UnavailablePremise(index));
            }
            let mut pending = vec![premise];
            while let Some(part) = pending.pop() {
                crate::instrumentation::record_deterministic_work(1);
                if let Proposition::And(left, right) = part {
                    pending.push(right);
                    pending.push(left);
                } else {
                    selected = selected.assume_proposition(
                        crate::kernel::region_footprint::byte_premise(part)
                            .ok_or(ConditionalNormalizationError::DoesNotNormalize)?,
                    );
                }
            }
        }
        return crate::kernel::region_footprint::separate_using(left, right, &selected)
            .then_some(())
            .ok_or(ConditionalNormalizationError::DoesNotNormalize);
    }
    // Validate every explicit citation before a local interval reduction.
    // Successful endpoint checks need no general rewriting context or its
    // mirrored condition forms over each increasingly large machine term.
    for (index, premise) in premises.iter().enumerate() {
        if !listed_condition_available(premise, facts) {
            return Err(ConditionalNormalizationError::UnavailablePremise(index));
        }
    }
    if PureFactContext::checks_listed_signed_order_chain(goal, premises)
        || intervals::reduces_one_operation(goal, premises)
        || super::arithmetic_special::checks_selected_float_bounds(goal, premises)
        || matches!(premises, [premise] if
            super::arithmetic_special::word_order_excludes_literal(goal, premise)
                || super::arithmetic_special::odd_product_nonzero_requirement(goal)
                    .is_some_and(|required| order_claim_equivalent(premise, &required)))
    {
        return Ok(());
    }
    // Ordinary cited rewrites and bounds take their established fast path.
    // Specialized rules are a fallback, so a simple equality does not pay for
    // conversion and matching against unrelated arithmetic rule shapes.
    let ordinary = normalize_condition_selection(goal, premises, facts);
    if ordinary.is_ok() || !super::arithmetic_special::normalizes_selected(goal, premises) {
        ordinary
    } else {
        Ok(())
    }
}

pub(super) fn listed_condition_available(
    premise: &Proposition,
    facts: &super::PureFactStore,
) -> bool {
    facts.available(premise)
        || crate::kernel::listed_premise_holds(premise, |fact| facts.available(fact))
        || order_claim_forms(premise)
            .iter()
            .any(|form| facts.available(form))
}

fn normalize_condition_selection(
    goal: &Proposition,
    premises: &[Proposition],
    facts: &super::PureFactStore,
) -> Result<(), ConditionalNormalizationError> {
    let mut conditions = std::collections::HashMap::new();
    // Keep graph admission in source order. Its bounded pointer fragment may
    // retain different coordinates after a block merge; hash iteration must
    // not choose whether the same certificate checks.
    let mut admission_order = Vec::new();
    // Equality is symmetric; signed comparisons also have an exact mirrored
    // spelling with swapped operands. Retain those spellings so
    // `normalize using` can close the same condition in either orientation.
    // This is deliberately
    // built from the cited premises only; it never searches ambient facts.
    let mut integer_alpha_conditions: std::collections::HashMap<
        u64,
        Vec<(super::fact_keys::IntegerEqualityAlphaKey, bool)>,
    > = std::collections::HashMap::new();
    for (index, premise) in premises.iter().enumerate() {
        // A complete arithmetic domain supplies its two ordinary bounds.
        // Keep shared operands intact; no private overflow spelling is needed.
        let sequence = crate::kernel::spec::retained_sequence_equalities(premise);
        let leaves = if let Some(sequence) = &sequence {
            sequence.iter().collect()
        } else if crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(
            premise,
        )
        .is_some()
        {
            let Proposition::And(first, second) = premise else {
                unreachable!()
            };
            vec![first.as_ref(), second.as_ref()]
        } else {
            vec![premise]
        };
        for premise in leaves {
            let (condition, value) = crate::kernel::spec::proposition_as_single_condition(premise)
                .ok_or(ConditionalNormalizationError::UnsupportedPremise(index))?;
            let previous = conditions.insert(condition.clone(), value);
            if previous.is_some_and(|previous| previous != value) {
                return Err(ConditionalNormalizationError::UnsupportedPremise(index));
            }
            if previous.is_none() {
                admission_order.push((condition.clone(), value));
            }
            // Every spelling of the cited claim states it: an order claim's
            // complement and mirrored direction, and an equality's mirrored
            // orientation, in every family (`int32`, the 64-bit and narrower
            // machine types, `Integer`, pointers). A fixed set per premise.
            for form in order_claim_forms(premise) {
                let Some((spelled, spelled_value)) =
                    crate::kernel::spec::proposition_as_single_condition(&form)
                else {
                    continue;
                };
                let previous = conditions.insert(spelled.clone(), spelled_value);
                if previous.is_some_and(|previous| previous != spelled_value) {
                    return Err(ConditionalNormalizationError::UnsupportedPremise(index));
                }
                if previous.is_none() {
                    admission_order.push((spelled, spelled_value));
                }
            }
            // Exact condition lookup above handles ordinary scalar terms.  Fold
            // binders can be freshly allocated while lowering the cited premise
            // and the goal, so retain a checked state-aware alpha index for
            // the same two orientations.  The fingerprint is charged before it
            // becomes a map key; collision candidates are checked with the
            // bounded key comparator below.
            if value && let OldConditionTerm::IntegerEqual(left, right) = &condition {
                for condition in [
                    OldConditionTerm::IntegerEqual(left.clone(), right.clone()),
                    OldConditionTerm::IntegerEqual(right.clone(), left.clone()),
                ] {
                    let proposition = Proposition::condition_is(condition, true);
                    let Some(key) = super::fact_keys::integer_equality_alpha_key(&proposition)
                    else {
                        continue;
                    };
                    let Some(fingerprint) = key.checked_fingerprint() else {
                        continue;
                    };
                    integer_alpha_conditions
                        .entry(fingerprint)
                        .or_default()
                        .push((key, value));
                }
            }
        }
    }
    // A single reverse-key lookup is enough for the common case.  If the
    // separately lowered fold has fresh binder IDs, use the checked alpha
    // bucket instead of scanning all cited conditions.  Only a top-level
    // atomic goal is admitted here; compound goals still follow the ordinary
    // explicit structural normalizer below.
    let goal_condition = crate::kernel::spec::proposition_as_single_condition(goal);
    if let Some((condition, goal_value)) = goal_condition.as_ref()
        && *goal_value
        && let OldConditionTerm::IntegerEqual(_, _) = condition
        && !conditions.contains_key(condition)
    {
        let proposition = Proposition::condition_is(condition.clone(), true);
        if let Some(key) = super::fact_keys::integer_equality_alpha_key(&proposition)
            && let Some(fingerprint) = key.checked_fingerprint()
            && let Some(candidates) = integer_alpha_conditions.get(&fingerprint)
        {
            for (candidate, value) in candidates {
                match candidate.checked_eq(&key) {
                    Some(true) => {
                        conditions.insert(condition.clone(), *value);
                        admission_order.push((condition.clone(), *value));
                        break;
                    }
                    Some(false) => {}
                    None => break,
                }
            }
        }
    }
    // Native orders can be the lowered form of written Integer observations.
    // Use their unique order reading, retaining the actual operand handles.
    // No fact selection is involved: at most four explicit bounds are read.
    if matches!(&(premises.len(), goal), (2, condition_source @ Proposition::ConditionIs(_, true))
        if matches!(condition_source.old_condition(), Some((OldConditionTerm::IntegerEqual(..), _))))
        || matches!(&(premises.len(), goal), (4, condition_source @ Proposition::ConditionIs(_, true))
            if matches!(condition_source.old_condition(), Some((OldConditionTerm::IntegerLessEqual(..), _))))
    {
        let bounds = premises
            .iter()
            .map(|premise| {
                let reading =
                    crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                        premise,
                    )
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| premise.clone());
                match reading {
                    ref condition_source_0 @ Proposition::ConditionIs(_, true)
                        if let Some((OldConditionTerm::IntegerGreaterEqual(a, b), _)) =
                            condition_source_0.old_condition() =>
                    {
                        Proposition::condition_is(
                            OldConditionTerm::IntegerLessEqual(b.clone(), a.clone()),
                            true,
                        )
                    }
                    other => other,
                }
            })
            .collect::<Vec<_>>();
        if bounds.len() == 2
            && (super::integer_operation_identity::check(0, &[0, 1], &bounds, goal).is_ok()
                || super::integer_cast_identity::check(0, &[0, 1], &bounds, goal).is_ok())
        {
            return Ok(());
        }
        if bounds.len() == 4
            && super::integer_product_bounds::check(0, &[0, 1, 2, 3], &bounds, goal).is_ok()
        {
            return Ok(());
        }
    }
    // Rule L-Eq through a cited `Bool` equality (Stage 5): `a == b` with
    // truth `t` and `a` cited or constant gives `b`, and the other way. One
    // pass over the cited premises; nothing ambient is read.
    let cited_equations = admission_order
        .iter()
        .filter_map(|(condition, value)| match condition {
            OldConditionTerm::BoolEqual(left, right) => {
                Some((left.as_ref().clone(), right.as_ref().clone(), *value))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    for (left, right, equal) in cited_equations {
        let truth =
            |operand: &OldConditionTerm,
             conditions: &std::collections::HashMap<OldConditionTerm, bool>| {
                match operand {
                    OldConditionTerm::Constant(value) => Some(*value),
                    operand => conditions.get(operand).copied(),
                }
            };
        for (known, other) in [(&left, &right), (&right, &left)] {
            if let Some(known) = truth(known, &conditions)
                && truth(other, &conditions).is_none()
            {
                conditions.insert(other.clone(), known == equal);
                admission_order.push((other.clone(), known == equal));
            }
        }
    }
    // A goal that is itself one cited condition, in any of the spellings
    // recorded above, is decided by it. This is the only route for an
    // algebraic equality goal, which is an equality of terms rather than a
    // condition the reduction below visits.
    if let Some((condition, value)) = goal_condition.as_ref()
        && let Some(cited) = conditions.get(condition)
    {
        return if cited == value {
            Ok(())
        } else {
            Err(ConditionalNormalizationError::DoesNotNormalize)
        };
    }
    // Legacy callers can still ask the private overflow question. Its
    // ordinary bounds must both be among the cited conditions; never rebuild
    // an overflow predicate from shared arithmetic in a premise.
    if let Some((condition @ OldConditionTerm::Overflows { .. }, false)) = goal_condition.as_ref() {
        let bounds = crate::kernel::machine_integer::definedness::integer_bounds_of_definedness(
            &Proposition::condition_is(condition.clone(), false),
        );
        if !bounds.is_empty()
            && bounds.iter().all(|bound| {
                crate::kernel::spec::proposition_as_single_condition(bound)
                    .is_some_and(|(condition, truth)| conditions.get(&condition) == Some(&truth))
            })
        {
            return Ok(());
        }
    }
    // Build the index for the explicit premise selection once. Ordinary
    // condition rewrites retain their direct indexed lookup and never build
    // a graph from an ambient map.
    let mut selected = PureFactContext::new();
    for (condition, value) in admission_order {
        crate::instrumentation::record_deterministic_work(1);
        selected = selected.assume_condition(condition, value);
    }
    if crate::kernel::spec::checks_retained_sequence_comparison(goal, true, |condition, truth| {
        selected.decide(condition) == Some(truth)
    }) == Some(true)
    {
        return Ok(());
    }
    if let Some((
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    )) = goal_condition.as_ref()
        && crate::kernel::memory_history::wide_read_has_recorded_value(left, right, &selected)
    {
        return Ok(());
    }
    if let Some((
        OldConditionTerm::Compare {
            format:
                MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16
                | MachineIntegerType::Int32
                | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    )) = goal_condition.as_ref()
        && crate::kernel::memory_history::narrow_read_has_recorded_value(left, right, &selected)
    {
        return Ok(());
    }
    if let Proposition::MemoryReadDefined {
        memory,
        pointer,
        value_type,
        ..
    } = goal
        && crate::kernel::memory_history::read_is_of_a_recorded_store(
            memory,
            pointer,
            *value_type,
            &selected,
        )
    {
        return Ok(());
    }
    if let Some((OldConditionTerm::AddressEqual(left, right), true)) = goal_condition.as_ref()
        && crate::kernel::memory_history::pointer_read_has_recorded_value(left, right, &selected)
    {
        return Ok(());
    }
    // An offset match only proves numeric equality. A complete pointer goal
    // also needs its provenance and bounds, including any opaque bounds owner.
    if let Some((
        condition @ (OldConditionTerm::AddressEqual(..) | OldConditionTerm::AddressOffsetEqual(..)),
        true,
    )) = goal_condition.as_ref()
        && let Some((left, right)) = condition.pointer_offset_sides()
        && (crate::kernel::reasoning::memory_resolution::pointer_offsets_proven_equal_for_memory_resolution(
            left, right, &selected,
        ) || offsets_equal_by_cited_index_sum(left, right, &selected))
    {
        return Ok(());
    }
    let reduced = super::term_rewrite::TermRewrite::for_cited_conditions_with_context(
        &conditions,
        &selected,
        facts.assumptions(),
    )
    .proposition(goal);
    // A comparison with a constant follows from cited conditions on the same
    // term (`a <= 5` gives `a <= 10`, and `n == 0` gives `n != 1`), in every
    // family: the selected context holds only the cited conditions, so this
    // consults nothing else.
    if let Some((condition, value)) = crate::kernel::spec::proposition_as_single_condition(&reduced)
        && let Some(subject) = constant_comparison_subject(&condition)
        && conditions
            .keys()
            .any(|cited| constant_comparison_subject(cited).as_ref() == Some(&subject))
        && selected.decide(&condition) == Some(value)
    {
        return Ok(());
    }
    normalizes_context_free_leaf(&reduced)
        .then_some(())
        .ok_or(ConditionalNormalizationError::DoesNotNormalize)
}

/// Two offsets that differ by two element indices on one side and one on the
/// other, at one element width, are one displacement when a cited premise
/// states that the one index's exact `Integer` value is the sum of the other
/// two: `(p + i) + j` and `p + k` from `to_integer(k) == to_integer(i) +
/// to_integer(j)`. One of `i` and `j` may be a constant byte offset of whole
/// elements. Offsets are exact sums of index times width, so this holds
/// for every index type; a native sum would not, because it may wrap.
/// Shared addends cancel in one pass over both offsets, and the premise is
/// found by exact lookup in the cited-premises context, so nothing else is
/// read.
fn offsets_equal_by_cited_index_sum(
    left: &AddressOffset,
    right: &AddressOffset,
    selected: &PureFactContext,
) -> bool {
    fn addends<'a>(offset: &'a AddressOffset, out: &mut Vec<&'a AddressOffset>) {
        let mut pending = vec![offset];
        while let Some(offset) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset.view() {
                OffsetView::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                _ => out.push(offset),
            }
        }
    }
    // An index and its observation: the offset is `index * width` exactly.
    fn scaled(offset: &AddressOffset) -> Option<(IntegerTerm, i64)> {
        let (ty, value, width) = match offset.view() {
            OffsetView::Int32Scaled { index, byte_width } => {
                (MachineIntegerType::Int32, index, byte_width)
            }
            OffsetView::Int64Scaled {
                index,
                byte_width,
                unsigned,
            } => (
                if unsigned {
                    MachineIntegerType::UInt64
                } else {
                    MachineIntegerType::Int64
                },
                index,
                byte_width,
            ),
            _ => return None,
        };
        (width >= 1)
            .then(|| value.operand_view().observe(ty))
            .flatten()
            .map(|index| (index, width))
    }
    let mut left_addends = Vec::new();
    addends(left, &mut left_addends);
    let mut right_addends = Vec::new();
    addends(right, &mut right_addends);
    let mut shared = std::collections::HashMap::<&AddressOffset, usize>::new();
    for addend in &left_addends {
        *shared.entry(*addend).or_default() += 1;
    }
    let mut rest_right = Vec::new();
    for addend in right_addends {
        match shared.get_mut(addend) {
            Some(count) if *count > 0 => *count -= 1,
            _ => rest_right.push(addend),
        }
    }
    let mut rest_left = Vec::new();
    for addend in left_addends {
        if let Some(count) = shared.get_mut(addend)
            && *count > 0
        {
            *count -= 1;
            rest_left.push(addend);
        }
    }
    let (pair, single) = match (rest_left.as_slice(), rest_right.as_slice()) {
        ([first, second], [single]) | ([single], [first, second]) => ([*first, *second], *single),
        _ => return false,
    };
    let Some((total, width)) = scaled(single) else {
        return false;
    };
    // A constant addend of the pair is a whole number of elements at the
    // indices' width, `(p + i) + 3` for three bytes: its exact index.
    let index = |offset: &AddressOffset| match offset.view() {
        OffsetView::Constant(bytes) if bytes >= 0 && bytes % width == 0 => {
            Some((IntegerTerm::constant((bytes / width).into()), width))
        }
        _ => scaled(offset),
    };
    let (Some((first, first_width)), Some((second, second_width))) =
        (index(pair[0]), index(pair[1]))
    else {
        return false;
    };
    if first_width != width || second_width != width {
        return false;
    }
    [
        IntegerTerm::add(first.clone(), second.clone()),
        IntegerTerm::add(second, first),
    ]
    .into_iter()
    .flat_map(|sum| {
        [
            OldConditionTerm::IntegerEqual(total.clone().into(), sum.clone().into()),
            OldConditionTerm::IntegerEqual(sum.into(), total.clone().into()),
        ]
    })
    .any(|equality| {
        crate::instrumentation::record_deterministic_work(1);
        selected.exact_condition_value(&equality) == Some(true)
    })
}

/// The term `condition` compares with a constant, when it is an order
/// comparison, equality, or disequality with a constant on exactly one side.
/// `normalize using` decides such a goal only from cited conditions on that
/// same term, so it never combines different terms the way `arithmetic`
/// does.
fn constant_comparison_subject(condition: &OldConditionTerm) -> Option<ConstantComparisonSubject> {
    fn retained_subject(mut operand: MachineOperandView<'_>) -> ConstantComparisonSubject {
        if let Some((MachineCastSpelling::Generic, source, destination, child)) = operand.cast()
            && matches!(
                (source, destination),
                (MachineIntegerType::Int32, MachineIntegerType::UInt32)
                    | (MachineIntegerType::UInt32, MachineIntegerType::Int32)
            )
        {
            operand = child;
        }
        let identity = match operand {
            MachineOperandView::Old(term) => {
                SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, term.clone())
            }
            MachineOperandView::Shared(term) if term.machine_conversion_leaf().is_some() => {
                SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    term.machine_conversion_leaf()
                        .expect("opaque subject")
                        .clone(),
                )
            }
            MachineOperandView::Shared(term) => SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                term.with_machine_observation_type(MachineIntegerType::Int32),
            )
            .expect("machine comparison subject"),
        };
        ConstantComparisonSubject::Machine(identity)
    }
    // Retained machine comparisons are spelled as Integer observations. Their
    // selected subject is still the same word as a native cited comparison.
    if let Some(view) =
        crate::kernel::machine_integer::comparison::structural_comparison_view(condition)
    {
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        match (left.literal().is_some(), right.literal().is_some()) {
            (false, true) => return Some(retained_subject(left)),
            (true, false) => return Some(retained_subject(right)),
            _ => {}
        }
    }
    // A constant of any format: an 8- or 16-bit comparison is native
    // (rule K8) and keeps its own constant's format.
    let machine_constant = |term: &OldMachineTerm| matches!(term, OldMachineTerm::Constant { .. });
    // σ keeps its operand's bits: a cited condition on `x` selects a
    // comparison of σ(x) and the reverse, decided in the selected context,
    // which relates the two (the difference graph's σ link, R0). The
    // subject is a key; the terms keep their σ. One match on the root.
    let subject =
        |term: &OldMachineTerm| retained_subject(MachineOperandView::Old(term.sign_cast32_bits()));
    let machine = |left: &OldMachineTerm, right: &OldMachineTerm| match (
        machine_constant(left),
        machine_constant(right),
    ) {
        (false, true) => Some(subject(left)),
        (true, false) => Some(subject(right)),
        _ => None,
    };
    let integer = |left: &SharedIntegerTerm, right: &SharedIntegerTerm| match (
        left.as_const().is_some(),
        right.as_const().is_some(),
    ) {
        (false, true) => Some(ConstantComparisonSubject::Integer(left.id())),
        (true, false) => Some(ConstantComparisonSubject::Integer(right.id())),
        _ => None,
    };
    match condition {
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => machine(left, right),
        OldConditionTerm::IntegerEqual(left, right)
        | OldConditionTerm::IntegerNotEqual(left, right) => integer(left, right),
        _ => match order_condition_parts(condition)?.1 {
            OrderOperands::Machine(_, left, right) => machine(&left, &right),
            OrderOperands::Integer(left, right) => integer(&left, &right),
        },
    }
}

#[derive(PartialEq)]
enum ConstantComparisonSubject {
    Machine(SharedMachineIntegerTerm),
    Integer(u64),
}

#[derive(Debug)]
pub(crate) enum ConditionalNormalizationError {
    UnavailablePremise(#[cfg_attr(not(test), allow(dead_code))] usize),
    UnsupportedPremise(#[cfg_attr(not(test), allow(dead_code))] usize),
    DoesNotNormalize,
}

pub(crate) enum ForallInstantiationError {
    RequiresUniversal,
    /// The argument's carrier is not the binder's sort.
    ArgumentSort,
    MissingGuard(Proposition),
    /// The body could not be substituted at the argument, such as an
    /// `Integer` binder under a carrier the pure substitution does not enter.
    SubstitutionRefused(String),
}

/// The value `instantiate` specializes a universal at, in the binder's own
/// carrier: a machine integer, a mathematical `Integer`, or a pointer value
/// with its subobject provenance.
#[derive(Clone, Debug)]
pub(crate) enum InstanceArgument {
    Machine(OldMachineTerm),
    Integer(IntegerTerm),
    Pointer(Pointer),
}

pub(crate) fn discharge_instantiated_guards(
    instantiated: Proposition,
    premises: &[Proposition],
) -> Result<(Vec<Proposition>, Proposition), ForallInstantiationError> {
    let premise_assumptions = assumptions_from_propositions(premises);
    let mut premise_conjuncts = Vec::new();
    for premise in premises {
        atomic_conjuncts(premise, &mut premise_conjuncts);
    }
    let premise_conjuncts = premise_conjuncts.into_iter().cloned().collect::<Vec<_>>();
    let discharges = |conjunct: &Proposition| {
        normalizes_context_free(conjunct)
            || premise_conjuncts.iter().any(|premise| {
                premise == conjunct || condition_polarity_equivalent(premise, conjunct)
            })
            || premise_assumptions.proves_atomic_for_derivation(conjunct, false)
            || premise_assumptions.proves_atomic_for_derivation(conjunct, true)
    };
    let mut guards = Vec::new();
    let mut current = instantiated;
    while let Proposition::Implies(guard, body) = current {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(&guard, &mut conjuncts);
        if let Some(missing) = conjuncts.iter().find(|conjunct| !discharges(conjunct)) {
            return Err(ForallInstantiationError::MissingGuard((*missing).clone()));
        }
        guards.push(*guard);
        current = *body;
    }
    Ok((guards, current))
}

/// The body of `quantified` with its binder replaced by `argument`: the
/// instance `instantiate` adds, guards included. The argument must be in the
/// binder's carrier: an `int32` or `uint64` binder takes a machine value of
/// that width, an `Integer` binder an `Integer` term, and a pointer binder a
/// pointer its type (and original object class) accepts.
pub(crate) fn instantiate_universal(
    quantified: &Proposition,
    argument: &InstanceArgument,
) -> Result<Proposition, ForallInstantiationError> {
    let Proposition::ForAll {
        var, sort, body, ..
    } = quantified
    else {
        return Err(ForallInstantiationError::RequiresUniversal);
    };
    let uint64 = Sort::ProgramInteger(crate::kernel::MachineIntegerType::UInt64);
    match (sort, argument) {
        (sort, InstanceArgument::Machine(value))
            if *sort == Sort::ProgramInt32 || *sort == uint64 =>
        {
            Ok(substitute_int32_variable_in_proposition(
                body,
                **var,
                value.clone(),
            ))
        }
        (Sort::Integer, InstanceArgument::Integer(value)) => {
            crate::kernel::substitute_integer_variable_in_pure_proposition(body, **var, value)
                .map_err(|error| ForallInstantiationError::SubstitutionRefused(error.to_string()))
        }
        (Sort::ProgramPointer(program_type), InstanceArgument::Pointer(pointer))
            if program_type.accepts(&ProgramValue::Pointer(pointer.clone())) =>
        {
            crate::kernel::substitute_pointer_value_in_proposition(body, **var, pointer)
                .map_err(ForallInstantiationError::SubstitutionRefused)
        }
        (Sort::ProgramObjectPointer(program_type, class), InstanceArgument::Pointer(pointer))
            if crate::kernel::AlgebraicValueType::ObjectPointer(*program_type, class.clone())
                .accepts_program_value(&ProgramValue::Pointer(pointer.clone())) =>
        {
            crate::kernel::substitute_pointer_value_in_proposition(body, **var, pointer)
                .map_err(ForallInstantiationError::SubstitutionRefused)
        }
        _ => Err(ForallInstantiationError::ArgumentSort),
    }
}

/// The conclusion of `quantified` at `argument` once `premises` discharge
/// each instantiated guard. It is the substituted body itself, constructed
/// here; nothing re-derives or re-compares it.
pub(crate) fn check_forall_instantiation(
    quantified: &Proposition,
    argument: &InstanceArgument,
    premises: &[Proposition],
) -> Result<Proposition, ForallInstantiationError> {
    let instantiated = instantiate_universal(quantified, argument)?;
    discharge_instantiated_guards(instantiated, premises).map(|(_, conclusion)| conclusion)
}

fn assumptions_from_propositions(propositions: &[Proposition]) -> SelectedFacts<'static> {
    crate::kernel::reasoning::path_facts::count_context_rebuild_entries(propositions.len());
    SelectedFacts::from_propositions(propositions)
}

pub(crate) fn is_implicit_fact_transport_context(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::MemoryLoadable { .. }
            | Proposition::MemoryCanStore { .. }
            | Proposition::ResourceSeparate { .. }
    )
}

/// The fixed set of condition forms accepted by
/// `condition_polarity_equivalent`. Callers can probe an exact index for these
/// instead of maintaining another project-sized index.
pub(crate) fn condition_polarity_forms(proposition: &Proposition) -> Vec<Proposition> {
    polarity_forms_by(proposition, canonical_order_condition)
}

/// The fixed set of condition forms accepted by [`order_claim_equivalent`]:
/// [`condition_polarity_forms`] extended to every order family. The explicit
/// closers (`known`, and the written step that adds the goal under its
/// other spelling) probe an exact index for these; the planners and
/// availability paths keep [`condition_polarity_forms`].
pub(crate) fn order_claim_forms(proposition: &Proposition) -> Vec<Proposition> {
    let mut forms = polarity_forms_by(proposition, canonical_order_claim);
    if let Some((wide, operator, left, right, value)) = float_comparison_parts(proposition) {
        crate::instrumentation::record_deterministic_work(1);
        let comparison = FloatCondition::Comparison {
            operator: mirrored_float_operator(operator),
            left: Box::new(right.clone()),
            right: Box::new(left.clone()),
        };
        let condition = if wide {
            OldConditionTerm::Float64(comparison)
        } else {
            OldConditionTerm::Float32(comparison)
        };
        forms.push(Proposition::condition_is(condition.clone(), value));
        forms.push(Proposition::Not(Box::new(Proposition::condition_is(
            condition, !value,
        ))));
    }
    forms
}

/// Float orders have mirrored spellings, but NaNs forbid complementing an
/// order when its truth polarity changes. Keep width and polarity exact.
fn float_comparison_parts(
    mut proposition: &Proposition,
) -> Option<(
    bool,
    ComparisonOperator,
    &OldMachineTerm,
    &OldMachineTerm,
    bool,
)> {
    let mut negated = false;
    while let Proposition::Not(body) = proposition {
        proposition = body;
        negated = !negated;
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let (wide, comparison) = match condition.old_form() {
        OldConditionTerm::Float32(comparison) => (false, comparison),
        OldConditionTerm::Float64(comparison) => (true, comparison),
        _ => return None,
    };
    let FloatCondition::Comparison {
        operator,
        left,
        right,
    } = comparison
    else {
        return None;
    };
    Some((wide, *operator, left, right, *value ^ negated))
}

fn mirrored_float_operator(operator: ComparisonOperator) -> ComparisonOperator {
    use ComparisonOperator::*;
    match operator {
        Equal => Equal,
        NotEqual => NotEqual,
        LessThan => GreaterThan,
        LessEqual => GreaterEqual,
        GreaterThan => LessThan,
        GreaterEqual => LessEqual,
    }
}

fn polarity_forms_by(
    proposition: &Proposition,
    canonical: fn(&OldConditionTerm, bool) -> Option<CanonicalOrderCondition>,
) -> Vec<Proposition> {
    let Some((condition, value)) =
        crate::kernel::spec::proposition_as_single_condition(proposition)
    else {
        return Vec::new();
    };
    let mut conditions = vec![(condition, value)];
    if let Some(CanonicalOrderCondition { operands, strict }) =
        canonical(&conditions[0].0, conditions[0].1)
    {
        // The four spellings of one order claim: the canonical direction at
        // both polarities, and the mirrored direction at both polarities.
        let mirrored = operands.clone().mirrored();
        let mut equivalent = if strict {
            vec![
                (operands.clone().condition(OrderOperator::LessThan), true),
                (operands.condition(OrderOperator::GreaterEqual), false),
                (mirrored.clone().condition(OrderOperator::LessEqual), false),
                (mirrored.condition(OrderOperator::GreaterThan), true),
            ]
        } else {
            vec![
                (operands.clone().condition(OrderOperator::LessEqual), true),
                (operands.condition(OrderOperator::GreaterThan), false),
                (mirrored.clone().condition(OrderOperator::LessThan), false),
                (mirrored.condition(OrderOperator::GreaterEqual), true),
            ]
        };
        conditions.append(&mut equivalent);
    }
    // Exact Integer equality and disequality are two spellings of one
    // condition at opposite polarities, before mirroring either orientation.
    let integer_opposites = conditions
        .iter()
        .filter_map(|(condition, value)| match condition {
            OldConditionTerm::IntegerEqual(a, b) => Some((
                OldConditionTerm::IntegerNotEqual(a.clone(), b.clone()),
                !value,
            )),
            OldConditionTerm::IntegerNotEqual(a, b) => {
                Some((OldConditionTerm::IntegerEqual(a.clone(), b.clone()), !value))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    conditions.extend(integer_opposites);
    // An equality or disequality states one claim in either orientation
    // (`b != a` for `a != b`), as an order claim does in its mirrored
    // direction: one more exact lookup per spelling.
    let mirrored = conditions
        .iter()
        .filter_map(|(condition, value)| {
            match crate::kernel::primitives::mirrored_equality(&Proposition::condition_is(
                condition.clone(),
                *value,
            )) {
                Some(Proposition::ConditionIs(condition, value)) => {
                    Some((condition.old_form().clone(), value))
                }
                _ => None,
            }
        })
        .collect::<Vec<_>>();
    conditions.extend(mirrored);
    let mut forms = Vec::new();
    for (condition, value) in conditions {
        if let OldConditionTerm::AlgebraicEqual(left, right) = &condition {
            let equality = Proposition::Equal(
                Term::Algebraic((*left.clone()).into()),
                Term::Algebraic((*right.clone()).into()),
            );
            forms.push(if value {
                equality
            } else {
                Proposition::Not(Box::new(equality))
            });
        }
        let direct = Proposition::condition_is(condition.clone(), value);
        if !forms.contains(&direct) {
            forms.push(direct);
        }
        let negated = Proposition::Not(Box::new(Proposition::condition_is(condition, !value)));
        if !forms.contains(&negated) {
            forms.push(negated);
        }
    }
    forms
}

pub(crate) fn exact_fact_is_available(
    required: &Proposition,
    available: &(impl super::PropositionSource + ?Sized),
) -> bool {
    available.exact_available(required)
}

/// Check an explicit list of theorem premises or checked conclusions.
/// Native/shared equality aliases belong at these explicit checking boundaries;
/// exposing them to general candidate matching creates new search branches.
/// Traverse each listed conjunction once, without rebuilding a fact context.
pub(crate) fn listed_comparison_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    let required_alpha = std::cell::OnceCell::new();
    let mut pending = available.iter().collect::<Vec<_>>();
    while let Some(fact) = pending.pop() {
        if fact == required {
            return true;
        }
        if let Proposition::And(left, right) = fact {
            pending.extend([right.as_ref(), left.as_ref()]);
            continue;
        }
        if exact_fact_contains_conjunct(fact, required) {
            return true;
        }
        // Fold binders are freshly allocated by each lowering. Compare only
        // the selected root-fold atoms, using the existing state-aware key;
        // opaque memories stay identities rather than structural cache keys.
        if let Some((required_key, fingerprint)) = required_alpha.get_or_init(|| {
            let key = super::fact_keys::integer_condition_alpha_key(required)?;
            let fingerprint = key.checked_fingerprint()?;
            Some((key, fingerprint))
        }) && let Some(key) = super::fact_keys::integer_condition_alpha_key(fact)
            && key.checked_fingerprint() == Some(*fingerprint)
            && key.checked_eq(required_key) == Some(true)
        {
            return true;
        }
        let flatten = crate::kernel::spec::proposition_as_single_condition;
        if let (Some((a, av)), Some((b, bv))) = (flatten(fact), flatten(required))
            && retained_comparison_equivalent(&a, av, &b, bv, true)
        {
            return true;
        }
    }
    false
}

/// Match an explicitly selected fact across an equality representation boundary.
pub(crate) fn listed_equality_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    let Some((condition, _)) = crate::kernel::spec::proposition_as_single_condition(required)
    else {
        return false;
    };
    crate::kernel::machine_integer::comparison::structural_comparison_view(&condition)
        .is_some_and(|view| view.relation == CompareRelation::Equal)
        && listed_comparison_fact_is_available(required, available)
}

/// Structural proposition equality whose condition leaves are decided by the
/// kernel's state bridge: two forms of one compound fact whose load
/// atoms carry different certified states. Structure must match exactly,
/// so this never accepts a weaker or stronger proposition.
pub(crate) fn propositions_equal_modulo_proven_states(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && assumptions.conditions_equal_modulo_proven_states(
                    left_condition.old_form(),
                    right_condition.old_form(),
                )
        }
        (Proposition::Implies(left_a, left_b), Proposition::Implies(right_a, right_b)) => {
            propositions_equal_modulo_proven_states(left_a, right_a, assumptions)
                && propositions_equal_modulo_proven_states(left_b, right_b, assumptions)
        }
        (Proposition::And(left_a, left_b), Proposition::And(right_a, right_b))
        | (Proposition::Or(left_a, left_b), Proposition::Or(right_a, right_b)) => {
            propositions_equal_modulo_proven_states(left_a, right_a, assumptions)
                && propositions_equal_modulo_proven_states(left_b, right_b, assumptions)
        }
        (Proposition::Not(left_body), Proposition::Not(right_body)) => {
            propositions_equal_modulo_proven_states(left_body, right_body, assumptions)
        }
        // Separations compare part-wise; the work lives in a never-inlined
        // helper because this function participates in deep proposition
        // recursion where added frame bytes overflow the stack.
        (
            left @ Proposition::ResourceSeparate { .. },
            right @ Proposition::ResourceSeparate { .. },
        ) => separations_equal_modulo_proven_states(left, right, assumptions),
        _ => false,
    }
}

/// Proves that one already-selected structural candidate is the same fact as
/// `required` across certified memory states. Candidate selection remains
/// the caller's responsibility; this operation never searches a context.
/// Resolves load variables in comparison term positions only:
/// condition terms and pointer offsets, never descending into embedded
/// memory states. The full resolver walks whole states and is far too
/// expensive for per-candidate comparison paths.
fn expand_load_variables_shallow(bits: &OldMachineTerm) -> OldMachineTerm {
    match bits {
        OldMachineTerm::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            crate::kernel::registered_load_term_for_variable(variable)
                .unwrap_or_else(|| bits.clone())
        }
        binary_term!(Bits32 @ format32, Add, left, right) => binary_node!(
                @ *format32,
                Add,
            Box::new(expand_load_variables_shallow(left)),
            Box::new(expand_load_variables_shallow(right)),
        ),
        binary_term!(Bits32 @ format32, Subtract, left, right) => binary_node!(
                @ *format32,
                Subtract,
            Box::new(expand_load_variables_shallow(left)),
            Box::new(expand_load_variables_shallow(right)),
        ),
        binary_term!(Bits32 @ format32, Multiply, left, right) => binary_node!(
                @ *format32,
                Multiply,
            Box::new(expand_load_variables_shallow(left)),
            Box::new(expand_load_variables_shallow(right)),
        ),
        _ => bits.clone(),
    }
}

fn expand_offset_load_variables_shallow(value: &AddressOffset) -> AddressOffset {
    match value.view() {
        OffsetView::Int32Scaled {
            index: value,
            byte_width,
        } => {
            let next = crate::kernel::memory_history::map_shared_pointer_index_with_descent(
                &value,
                |leaf| Some(expand_load_variables_shallow(leaf)),
                crate::kernel::proof::equality_rewrite::rebuild_transported_machine_node,
                |node| {
                    matches!(
                        node.node(),
                        crate::kernel::KernelTermNode::MachineBinary {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            operator: crate::kernel::MachineBinaryOp::Add
                                | crate::kernel::MachineBinaryOp::Subtract
                                | crate::kernel::MachineBinaryOp::Multiply,
                            ..
                        }
                    )
                },
            )
            .unwrap_or_else(|| value.clone());
            AddressOffset::int32_scaled(next, byte_width)
        }
        OffsetView::Add(left, right) => AddressOffset::raw_add(
            expand_offset_load_variables_shallow(left),
            expand_offset_load_variables_shallow(right),
        ),
        _ => value.clone(),
    }
}

/// Bridged availability for a separation, reasoning in the assumption
/// context the caller supplies.
///
/// Candidates still come only from `available`, so widening the assumptions
/// cannot make an unlisted fact available — the wider context only decides
/// whether two forms denote one fact.
/// A separation required at one state is available when an available
/// separation names the same regions modulo the certified frame. Condition
/// facts use [`condition_bridged_fact_is_available`] for the same purpose.
pub(crate) fn separation_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
    framing: &(impl ExecutionFactSource + ?Sized),
) -> bool {
    matches!(required, Proposition::ResourceSeparate { .. })
        && separation_bridged_available(required, available, assumptions, framing)
}

pub(crate) fn exact_fact_contains_conjunct(fact: &Proposition, required: &Proposition) -> bool {
    condition_polarity_equivalent(fact, required)
        || matches!((fact, required),
            (Proposition::ForAll { .. }, Proposition::ForAll { .. })
            | (Proposition::Exists { .. }, Proposition::Exists { .. })
            if quantified_binder_equivalent(fact, required))
        || matches!(fact, Proposition::And(left, right)
            if exact_fact_contains_conjunct(left, required)
                || exact_fact_contains_conjunct(right, required))
}

pub(crate) fn propositions_are_exact_negations(left: &Proposition, right: &Proposition) -> bool {
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

/// Whether two propositions are one condition fact: the same condition at
/// the same polarity, a condition and its negation at opposite polarities,
/// or one 32-bit signed order claim under two spellings (`a <= b` and
/// `b >= a`, `a < b` and `not (a >= b)`). This is the equivalence every
/// availability path and planner accepts; [`order_claim_equivalent`] extends
/// it to the other order families for the explicit closers.
pub(crate) fn condition_polarity_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    // Compound membership descends through its leaves. Do not normalize
    // the whole remaining conjunction at every recursive membership step.
    let atomic = |mut proposition: &Proposition| {
        while let Proposition::Not(body) = proposition {
            proposition = body;
        }
        matches!(
            proposition,
            Proposition::ConditionIs(..)
                | Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        )
    };
    if !atomic(left) || !atomic(right) {
        return false;
    }
    if polarity_equivalent_by(left, right, canonical_order_condition) {
        return true;
    }
    let left_comparison = crate::kernel::arithmetic_comparison_form(left);
    let right_comparison = crate::kernel::arithmetic_comparison_form(right);
    polarity_equivalent_by(
        left_comparison.as_ref().unwrap_or(left),
        right_comparison.as_ref().unwrap_or(right),
        canonical_order_condition,
    )
}

/// [`condition_polarity_equivalent`] over every order family the kernel
/// lowers to: 32-bit and 64-bit machine orders and the `Integer` order. Each
/// side is normalized once and the results compared; nothing is searched.
pub(crate) fn order_claim_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if polarity_equivalent_by(left, right, canonical_order_claim) {
        return true;
    }
    match (float_comparison_parts(left), float_comparison_parts(right)) {
        (Some((lw, lo, ll, lr, lv)), Some((rw, ro, rl, rr, rv))) => {
            lw == rw && lv == rv && mirrored_float_operator(lo) == ro && ll == rr && lr == rl
        }
        _ => false,
    }
}

fn polarity_equivalent_by(
    left: &Proposition,
    right: &Proposition,
    canonical: fn(&OldConditionTerm, bool) -> Option<CanonicalOrderCondition>,
) -> bool {
    if left == right {
        return true;
    }
    // A negated condition fact is the same total boolean condition with the
    // opposite expected value; flattening lets one form compare against
    // the other and against the canonical order form of either.
    let flatten = crate::kernel::spec::proposition_as_single_condition;
    let (Some((left_condition, left_value)), Some((right_condition, right_value))) =
        (flatten(left), flatten(right))
    else {
        return false;
    };
    if left_condition == right_condition && left_value == right_value {
        return true;
    }
    // A call's native reading may retain exact producer handles in numeric
    // arguments. Re-lowering the same call produces fresh exact handles but
    // the existing typed application identity still names the same value.
    // Keep comparison format, direction, polarity and all other syntax exact.
    if left_value == right_value
        && let (
            OldConditionTerm::Compare {
                format: af,
                relation: ar,
                left: al,
                right: ab,
            },
            OldConditionTerm::Compare {
                format: bf,
                relation: br,
                left: bl,
                right: bb,
            },
        ) = (&left_condition, &right_condition)
        && (af, ar) == (bf, br)
        && [(al, bl), (ab, bb)].into_iter().all(|(a, b)| {
            a == b
                || match (a.as_ref(), b.as_ref()) {
                    (
                        OldMachineTerm::ClickFunctionApplication {
                            name: an,
                            arguments: aa,
                        },
                        OldMachineTerm::ClickFunctionApplication {
                            name: bn,
                            arguments: ba,
                        },
                    ) if an == bn => {
                        crate::kernel::SharedPureApplication::intern(an.clone(), aa.clone())
                            == crate::kernel::SharedPureApplication::intern(bn.clone(), ba.clone())
                    }
                    _ => false,
                }
        })
    {
        return true;
    }
    // A retained order observation and its native comparison are the same typed
    // claim. Read their syntax identities; never export a shared operand or
    // consult proof facts to recover the native spelling.
    if retained_comparison_equivalent(
        &left_condition,
        left_value,
        &right_condition,
        right_value,
        false,
    ) {
        return true;
    }
    matches!(
        (
            canonical(&left_condition, left_value),
            canonical(&right_condition, right_value),
        ),
        (Some(left), Some(right)) if left == right
    )
}

/// Exact written comparison direction and polarity, across native/shared carriers.
/// Native arithmetic imports reuse their syntax memo; shared keys retain IDs.
/// Thus repeated growing shared queries do not revisit the expression DAG.
fn retained_comparison_equivalent(
    left: &OldConditionTerm,
    left_value: bool,
    right: &OldConditionTerm,
    right_value: bool,
    include_equality: bool,
) -> bool {
    use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey;
    use crate::kernel::machine_integer::comparison::structural_comparison_view;
    // This bridge is only for different representations. Existing same-form
    // matching must not import every unsuccessful native comparison into the
    // shared arena during proof search.
    if matches!(left, OldConditionTerm::Compare { .. })
        == matches!(right, OldConditionTerm::Compare { .. })
    {
        return false;
    }
    let (Some(left), Some(right)) = (
        structural_comparison_view(left),
        structural_comparison_view(right),
    ) else {
        return false;
    };
    // Automatic matching retains its existing order-only bridge. Equality
    // aliases are consumed by explicit listed-premise checking below, not by
    // speculative rewrite/transport candidate generation.
    if left.relation == CompareRelation::Equal && !include_equality {
        return false;
    }
    if left.relation != right.relation
        || (left_value ^ left.negated) != (right_value ^ right.negated)
    {
        return false;
    }
    // Equality compares words, including their negated spellings; signedness
    // only distinguishes order claims. The source and requested operands must
    // still have exactly the same syntax at the same width.
    let format = if left.relation == CompareRelation::Equal
        && left.format.format().bits() == right.format.format().bits()
    {
        match left.format.format().bits() {
            32 => MachineIntegerType::Int32,
            64 => MachineIntegerType::Int64,
            _ => return false,
        }
    } else if left.format == right.format {
        left.format
    } else {
        return false;
    };
    left.operands.iter().zip(&right.operands).all(|(a, b)| {
        let (a, b) = (a.operand_view(), b.operand_view());
        // A variable is its name, and cannot have the syntax of a compound
        // operand. Avoid re-interning fixed-size leaves at every failed
        // selected-premise comparison in smart search.
        match (a.variable(), b.variable()) {
            (Some(a), Some(b)) => return a == b,
            (Some(_), None) | (None, Some(_)) => return false,
            _ => {}
        }
        match (a.literal(), b.literal()) {
            (Some(a), Some(b)) if a == b => return true,
            (Some(_), None) | (None, Some(_)) => return false,
            _ => {}
        }
        ScalarOperandKey::for_format(format, a) == ScalarOperandKey::for_format(format, b)
    })
}

/// The comparison an order condition spells, before its polarity and
/// direction are normalized away.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OrderOperator {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

/// The two sides of an order condition, tagged with the order they are
/// compared in. Every family the kernel lowers an order to is here: a
/// machine order at its format (`int32`, `uint32`, `int64`, `uint64`), and
/// the mathematical `Integer` order. Sides from different families are never
/// one claim.
#[derive(Clone, Debug, PartialEq, Eq)]
enum OrderOperands {
    Machine(MachineIntegerType, Box<OldMachineTerm>, Box<OldMachineTerm>),
    Integer(SharedIntegerTerm, SharedIntegerTerm),
}

impl OrderOperands {
    /// The same sides read from the other end: `b ? a` for `a ? b`.
    fn mirrored(self) -> Self {
        match self {
            Self::Machine(format, left, right) => Self::Machine(format, right, left),
            Self::Integer(left, right) => Self::Integer(right, left),
        }
    }

    /// The condition comparing these sides with `operator` in their family.
    fn condition(self, operator: OrderOperator) -> OldConditionTerm {
        use OrderOperator::*;
        match (self, operator) {
            (Self::Machine(format, left, right), operator) => OldConditionTerm::Compare {
                format,
                relation: match operator {
                    LessThan => CompareRelation::LessThan,
                    LessEqual => CompareRelation::LessEqual,
                    GreaterThan => CompareRelation::GreaterThan,
                    GreaterEqual => CompareRelation::GreaterEqual,
                },
                left,
                right,
            },
            (Self::Integer(l, r), LessThan) => OldConditionTerm::IntegerLessThan(l, r),
            (Self::Integer(l, r), LessEqual) => OldConditionTerm::IntegerLessEqual(l, r),
            (Self::Integer(l, r), GreaterThan) => OldConditionTerm::IntegerGreaterThan(l, r),
            (Self::Integer(l, r), GreaterEqual) => OldConditionTerm::IntegerGreaterEqual(l, r),
        }
    }
}

/// One order claim in its canonical direction: `left < right` when `strict`,
/// otherwise `left <= right`. `a <= b`, `b >= a`, `not (a > b)` and
/// `not (b < a)` all normalize to the same value, so two conditions are the
/// same claim exactly when their canonical forms are equal. This is a
/// normalization of the condition at hand, not a search.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CanonicalOrderCondition {
    operands: OrderOperands,
    strict: bool,
}

/// Splits an order condition into its operator and typed sides; `None` for
/// any condition that is not an order (equalities, overflow checks, ...).
fn order_condition_parts(condition: &OldConditionTerm) -> Option<(OrderOperator, OrderOperands)> {
    use OrderOperator::*;
    Some(match condition {
        OldConditionTerm::Compare {
            format:
                format @ (MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16
                | MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64),
            relation,
            left: l,
            right: r,
        } => (
            match relation {
                CompareRelation::LessThan => LessThan,
                CompareRelation::LessEqual => LessEqual,
                CompareRelation::GreaterThan => GreaterThan,
                CompareRelation::GreaterEqual => GreaterEqual,
                CompareRelation::Equal => return None,
            },
            OrderOperands::Machine(*format, l.clone(), r.clone()),
        ),
        OldConditionTerm::IntegerLessThan(l, r) => {
            (LessThan, OrderOperands::Integer(l.clone(), r.clone()))
        }
        OldConditionTerm::IntegerLessEqual(l, r) => {
            (LessEqual, OrderOperands::Integer(l.clone(), r.clone()))
        }
        OldConditionTerm::IntegerGreaterThan(l, r) => {
            (GreaterThan, OrderOperands::Integer(l.clone(), r.clone()))
        }
        OldConditionTerm::IntegerGreaterEqual(l, r) => {
            (GreaterEqual, OrderOperands::Integer(l.clone(), r.clone()))
        }
        _ => return None,
    })
}

/// The canonical order claim of a 32-bit order condition, signed or
/// unsigned, and `None` for every other condition. This is the
/// normalization every availability path and planner shares, unchanged from
/// before the other families were normalized; see [`canonical_order_claim`]
/// for those.
fn canonical_order_condition(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<CanonicalOrderCondition> {
    canonical_order_claim(condition, value).filter(|claim| {
        matches!(
            claim.operands,
            OrderOperands::Machine(MachineIntegerType::Int32 | MachineIntegerType::UInt32, ..)
        )
    })
}

/// The canonical order claim of an order condition in any family.
fn canonical_order_claim(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<CanonicalOrderCondition> {
    let (operator, operands) = order_condition_parts(condition)?;
    // A false `a < b` is `b <= a`, and a true `a >= b` is `b <= a`: each
    // operator at each polarity names one direction and one strictness.
    Some(match (operator, value) {
        (OrderOperator::LessThan, true) | (OrderOperator::GreaterEqual, false) => {
            CanonicalOrderCondition {
                operands,
                strict: true,
            }
        }
        (OrderOperator::LessThan, false) | (OrderOperator::GreaterEqual, true) => {
            CanonicalOrderCondition {
                operands: operands.mirrored(),
                strict: false,
            }
        }
        (OrderOperator::LessEqual, true) | (OrderOperator::GreaterThan, false) => {
            CanonicalOrderCondition {
                operands,
                strict: false,
            }
        }
        (OrderOperator::LessEqual, false) | (OrderOperator::GreaterThan, true) => {
            CanonicalOrderCondition {
                operands: operands.mirrored(),
                strict: true,
            }
        }
    })
}

pub(crate) fn quantified_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    if !matches!(required, Proposition::ForAll { .. }) {
        return None;
    }
    available
        .iter()
        .find(|fact| quantified_binder_equivalent(required, fact))
        .cloned()
}

/// Compare bodies after both binders have been renamed to one fresh name.
/// Walk only their logical spine. Nested scopes and non-order leaves retain
/// structural equality, including the states produced by substitution.
fn substituted_body_retained_order_equivalent(left: &Proposition, right: &Proposition) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left, right) {
            (Proposition::And(a, b), Proposition::And(c, d))
            | (Proposition::Or(a, b), Proposition::Or(c, d))
            | (Proposition::Implies(a, b), Proposition::Implies(c, d)) => {
                pending.push((a, c));
                pending.push((b, d));
            }
            (Proposition::Not(a), Proposition::Not(b)) => pending.push((a, b)),
            (Proposition::ConditionIs(a, av), Proposition::ConditionIs(b, bv)) => {
                if (av != bv || a != b)
                    && !retained_comparison_equivalent(a.old_form(), *av, b.old_form(), *bv, false)
                {
                    return false;
                }
            }
            _ if left == right => {}
            _ => return false,
        }
    }
    true
}

pub(crate) fn quantified_binder_equivalent(left: &Proposition, right: &Proposition) -> bool {
    // A quantifier's binder is numbered by its height, so two quantifiers
    // with one binder, sort and body are the same up to their display names.
    if let (
        Proposition::ForAll {
            var: lv,
            sort: ls,
            body: lb,
            ..
        },
        Proposition::ForAll {
            var: rv,
            sort: rs,
            body: rb,
            ..
        },
    )
    | (
        Proposition::Exists {
            var: lv,
            sort: ls,
            body: lb,
            ..
        },
        Proposition::Exists {
            var: rv,
            sort: rs,
            body: rb,
            ..
        },
    ) = (left, right)
        && lv == rv
        && ls == rs
        && lb == rb
    {
        return true;
    }
    let left_comparison = super::term_rewrite::TermRewrite::arithmetic_comparison(left);
    let right_comparison = super::term_rewrite::TermRewrite::arithmetic_comparison(right);
    let left = left_comparison.as_ref().unwrap_or(left);
    let right = right_comparison.as_ref().unwrap_or(right);
    // A guarded quantifier matches when the guards are identical and the
    // quantified conclusions are binder-equivalent. A guard can itself
    // quantify variables; its typed alpha identity preserves its states,
    // free variables, and sorts while allowing those local binders to differ.
    let (mut left, mut right) = (left, right);
    let mut guarded = false;
    while let (
        Proposition::Implies(left_guard, left_body),
        Proposition::Implies(right_guard, right_body),
    ) = (left, right)
    {
        if left_guard != right_guard
            && !super::propositions_are_alpha_equal(left_guard, right_guard)
        {
            return false;
        }
        (left, right) = (left_body, right_body);
        guarded = true;
    }
    if guarded && left == right {
        return true;
    }
    if let (Some(left_key), Some(right_key)) = (
        super::fact_keys::quantified_algebraic_captured_array_identity_key(left),
        super::fact_keys::quantified_algebraic_captured_array_identity_key(right),
    ) {
        return left_key == right_key;
    }
    // A loadability premise carries an exact memory state. Compare the
    // selected typed alpha keys before falling back to int32 substitution;
    // the latter would clone and rewrite the entire opaque memory state.
    if let Some(equivalent) = super::fact_keys::state_quantified_alpha_equivalent(left, right) {
        return equivalent;
    }
    // A supported structural mismatch is definitive; do not substitute or
    // search to turn it into an equivalence. Loaded bodies use the state-aware
    // key below; unsupported fragments retain the existing structural check.
    if let (Some(left_key), Some(right_key)) = (
        super::fact_keys::memory_free_quantified_key(left),
        super::fact_keys::memory_free_quantified_key(right),
    ) {
        return left_key == right_key
            && super::fact_keys::predicate_states_share_storage(left, right);
    }
    // The memory-free key deliberately excludes reads. For supported loaded
    // bodies use the same comparison identities with exact retained states,
    // rather than requiring native and shared comparison nodes to be equal.
    if let Some(equivalent) =
        super::fact_keys::selected_state_quantified_alpha_equivalent(left, right)
    {
        return equivalent;
    }
    let (left_var, left_sort, left_body, right_var, right_sort, right_body) = match (left, right) {
        (
            Proposition::ForAll {
                var: lv,
                sort: ls,
                body: lb,
                ..
            },
            Proposition::ForAll {
                var: rv,
                sort: rs,
                body: rb,
                ..
            },
        )
        | (
            Proposition::Exists {
                var: lv,
                sort: ls,
                body: lb,
                ..
            },
            Proposition::Exists {
                var: rv,
                sort: rs,
                body: rb,
                ..
            },
        ) => (*lv, ls, lb.as_ref(), *rv, rs, rb.as_ref()),
        _ => return false,
    };
    if left_sort != right_sort {
        return false;
    }
    if left_var == right_var {
        return substituted_body_retained_order_equivalent(left_body, right_body);
    }
    // Neither binder name is necessarily fresh in the other body: it can
    // already occur freely inside a retained memory state. Compare both
    // substitutions at a name absent from both bodies and their binders.
    // This legacy path retains its state traversal; indexed fast paths above
    // do not collect variables or substitute retained states.
    let mut reserved = crate::kernel::proposition_variables(left);
    reserved.extend(crate::kernel::proposition_variables(right));
    let fresh = KernelVariableGenerator::fresh_for(0, reserved).next();
    match left_sort {
        Sort::Algebraic(ty) => {
            let replacement = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Variable(fresh),
            };
            crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
                left_body,
                *left_var,
                &replacement,
            ) == crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
                right_body,
                *right_var,
                &replacement,
            )
        }
        _ => {
            let left = substitute_int32_variable_in_proposition(
                left_body,
                *left_var,
                OldMachineTerm::Variable(fresh),
            );
            let right = substitute_int32_variable_in_proposition(
                right_body,
                *right_var,
                OldMachineTerm::Variable(fresh),
            );
            substituted_body_retained_order_equivalent(&left, &right)
        }
    }
}

pub(crate) fn atomic_conjuncts<'a>(
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

/// The available fact, or conjunct of one, exactly equal to `required`.
pub(crate) fn exactly_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    fn matching_conjunct(fact: &Proposition, required: &Proposition) -> Option<Proposition> {
        if fact == required {
            return Some(fact.clone());
        }
        let Proposition::And(left, right) = fact else {
            return None;
        };
        matching_conjunct(left, required).or_else(|| matching_conjunct(right, required))
    }

    available
        .iter()
        .find_map(|fact| matching_conjunct(fact, required))
}

pub(crate) fn directly_matching_separation_fact(
    required: &Proposition,
    available: &(impl super::PropositionSource + ?Sized),
) -> Option<Proposition> {
    let assumptions = available.pure_context();
    directly_matching_separation_fact_under(required, available, &assumptions)
}

/// `directly_matching_separation_fact` where the caller already holds the
/// assumption context the match should reason in (for example the available
/// facts plus recorded execution effect facts, which let the bounded resource
/// matcher see that two load terms from different states denote one
/// pointer). Candidates still come only from `available`, so widening the
/// assumptions cannot make an unlisted fact available.
pub(crate) fn directly_matching_separation_fact_under(
    required: &Proposition,
    available: &(impl super::PropositionSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<Proposition> {
    let Proposition::ResourceSeparate {
        left: required_left,
        right: required_right,
    } = required
    else {
        return None;
    };
    available.propositions().find_map(|fact| {
        let Proposition::ResourceSeparate { left, right } = fact else {
            return None;
        };
        let same_orientation = resources_directly_match(left, required_left, assumptions)
            && resources_directly_match(right, required_right, assumptions);
        let reverse_orientation = resources_directly_match(left, required_right, assumptions)
            && resources_directly_match(right, required_left, assumptions);
        (same_orientation || reverse_orientation).then(|| fact.clone())
    })
}

pub(crate) fn directly_covering_loadability_fact(
    required: &Proposition,
    available: &(impl super::PropositionSource + ?Sized),
) -> Option<Proposition> {
    matches!(required, Proposition::MemoryLoadable { .. }).then_some(())?;
    available.propositions().find_map(|fact| {
        matches!(fact, Proposition::MemoryLoadable { .. })
            .then(|| {
                assumptions_from_propositions(std::slice::from_ref(fact))
                    .proves_atomic_for_derivation(required, false)
                    .then(|| fact.clone())
            })
            .flatten()
    })
}

/// Whether two exact facts directly contradict each other. Execution steps
/// decide this against a whole fact list through the list's conjunct index
/// (`PureFactList::directly_conflicts_with`); this pairwise form is its
/// specification, which the list's tests check it against.
#[cfg(test)]
pub(crate) fn exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    let left = left.clone();
    let right = right.clone();
    normalized_exact_facts_directly_conflict(&left, &right)
}

#[cfg(test)]
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

/// Whether `fact` is refuted by the assumptions, by the retained exact
/// routes only.
///
/// The walk is structural over `fact`: a conjunction conflicts when one
/// conjunct does, and each leaf's negation must be exactly available, decided
/// by the frozen condition checker on a bare condition, or settled by a
/// retained atomic memory/resource checker. There is no logical search, so a
/// contradiction that needs a derivation is reported as "no conflict" and the
/// fact stays; the consumers all treat this as a suppression or vacuity hint.
pub(crate) fn fact_conflicts_with_assumptions(
    fact: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let refuted = |goal: Proposition| {
        crate::kernel::prelude::required_obligation_is_exactly_discharged(assumptions, &goal)
    };
    match fact {
        Proposition::And(left, right) => {
            fact_conflicts_with_assumptions(left, assumptions)
                || fact_conflicts_with_assumptions(right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            refuted(Proposition::condition_is(condition.clone(), !value))
        }
        Proposition::Not(body) => refuted(body.as_ref().clone()),
        fact => refuted(Proposition::Not(Box::new(fact.clone()))),
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn listed_signed_order_chain_requires_connected_edges_and_strictness() {
        use super::*;

        let terms = [701, 702, 703, 704].map(|id| OldMachineTerm::Variable(Variable(id)));
        let order = |from: usize, to: usize, strict| {
            let left = terms[from].clone();
            let right = terms[to].clone();
            Proposition::condition_is(
                if strict {
                    OldConditionTerm::signed_less_than(left, right)
                } else {
                    OldConditionTerm::signed_less_equal(left, right)
                },
                true,
            )
        };
        let goal = order(0, 3, true);
        let chain = [order(0, 1, false), order(1, 2, true), order(2, 3, false)];
        assert!(PureFactContext::checks_listed_signed_order_chain(
            &goal, &chain
        ));
        assert!(!PureFactContext::checks_listed_signed_order_chain(
            &goal,
            &chain[..2]
        ));
        let weak = [chain[0].clone(), order(1, 2, false), chain[2].clone()];
        assert!(!PureFactContext::checks_listed_signed_order_chain(
            &goal, &weak
        ));
    }

    #[test]
    fn retained_atomic_comparison_matching_needs_no_operand_imports() {
        use super::*;
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let x = OldMachineTerm::Variable(Variable(1005250));
        let y = OldMachineTerm::Variable(Variable(1005251));
        let observed = |word| IntegerTerm::Machine(SharedMachineIntegerTerm::intern(format, word));
        let retained =
            OldConditionTerm::integer_less_than(observed(x.clone()), observed(y.clone()));
        let native = OldConditionTerm::signed_less_than(x, y);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                assert!(retained_comparison_equivalent(
                    &native, true, &retained, true, false
                ));
                assert!(!retained_comparison_equivalent(
                    &native, false, &retained, true, false
                ));
            }
        });
        assert_eq!(
            work, 0,
            "fixed-size atom matching should not import operands"
        );
    }

    #[test]
    fn listed_remainder_disequality_does_not_expand_general_candidate_matching() {
        use super::*;
        use crate::kernel::machine_integer::comparison::retained_arithmetic_comparison;
        let remainder = OldMachineTerm::machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Remainder,
            OldMachineTerm::Variable(Variable(1005290)),
            OldMachineTerm::constant(2),
        );
        let native = OldConditionTerm::equal(remainder, OldMachineTerm::constant(0));
        let shared = retained_arithmetic_comparison(&native).unwrap();
        let written = Proposition::condition_is(native, false);
        let retained = Proposition::condition_is(shared.clone(), false);
        assert!(!exact_fact_is_available(
            &written,
            std::slice::from_ref(&retained)
        ));
        assert!(listed_comparison_fact_is_available(
            &written,
            std::slice::from_ref(&retained)
        ));
        assert!(listed_comparison_fact_is_available(
            &retained,
            std::slice::from_ref(&written)
        ));
        assert!(!listed_comparison_fact_is_available(
            &Proposition::condition_is(shared, true),
            &[written]
        ));
    }

    #[test]
    fn exact_premises_match_retained_machine_comparisons() {
        use super::*;
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        let _session = VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let constant = |n| match format {
                MachineIntegerType::Int32 => OldMachineTerm::constant(n as u32),
                _ => OldMachineTerm::uint64_constant(n),
            };
            let native = OldMachineTerm::machine_binary(
                format,
                MachineBinaryOp::Subtract,
                OldMachineTerm::Variable(Variable(1005200)),
                constant(1),
            );
            let root = KernelTermImport::default()
                .machine_arithmetic(format, &native)
                .unwrap();
            let bound = constant(17);
            let exports = KernelTermExport::machine_export_count();
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
            ] {
                let written = Proposition::condition_is(
                    OldConditionTerm::machine_compare(
                        format,
                        relation,
                        native.clone(),
                        bound.clone(),
                    ),
                    true,
                );
                let retained = condition_for_operand_views(
                    format,
                    relation,
                    [V::Shared(&root), V::Old(&bound)],
                );
                let required = Proposition::condition_is(retained.clone(), true);
                assert!(
                    listed_comparison_fact_is_available(&required, std::slice::from_ref(&written)),
                    "{format:?} {relation:?}: {required:?} versus {written:?}"
                );
                assert!(listed_comparison_fact_is_available(&written, &[required]));
                let negative_written = match &written {
                    Proposition::ConditionIs(c, _) => Proposition::condition_is(c.clone(), false),
                    _ => unreachable!(),
                };
                assert!(listed_comparison_fact_is_available(
                    &Proposition::condition_is(retained.clone(), false),
                    &[negative_written]
                ));
                assert!(!listed_comparison_fact_is_available(
                    &Proposition::condition_is(retained, false),
                    std::slice::from_ref(&written)
                ));
                let changed = condition_for_operand_views(
                    format,
                    relation,
                    [V::Shared(&root), V::Old(&constant(18))],
                );
                assert!(!listed_comparison_fact_is_available(
                    &Proposition::condition_is(changed, true),
                    &[written]
                ));
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
    use super::*;
    use crate::kernel::proof::facts::PureFactStore;
    use crate::kernel::proof::quantified_equivalence_index_key;
    use crate::kernel::{
        Address, AddressBase, AddressOffset, MemoryRange, ProgramValue, Resource, SymbolicMemory,
        Variable, intern_memory, load_variable_for_cell_with_origin,
    };

    fn footprint_alias_fixture() -> (Proposition, Proposition, Proposition) {
        use crate::kernel::{ExecutionPureFact, ExecutionState};
        let actual = Address::symbolic(Variable(96_140));
        let named = Address::symbolic(Variable(96_141));
        let kept = Address::symbolic(Variable(96_142));
        let before = ExecutionState::new();
        let after = before.clone().with_memory(
            before
                .memory()
                .clone()
                .store(actual.clone(), crate::kernel::uint8(1u32)),
        );
        let effect = ExecutionPureFact::certified(Proposition::MemoryMutatesOnly {
            before: before.memory().clone(),
            before_point: Default::default(),
            after: after.memory().clone(),
            after_point: Default::default(),
            writes: vec![(actual.clone(), crate::kernel::AccessExtent::from(1))],
        });
        let footprint = Resource::Footprint(crate::kernel::RegionFootprint::transition(
            "byte store".into(),
            &before,
            &after,
            &vec![effect],
        ));
        let range = |pointer, bytes: u32| {
            Resource::Memory(MemoryRange::new_with_element_width(
                pointer,
                0u32.into(),
                bytes.into(),
                1,
            ))
        };
        let separation = Proposition::ResourceSeparate {
            left: Box::new(range(named.clone(), 1)),
            right: Box::new(range(kept.clone(), 8)),
        };
        let goal = Proposition::ResourceSeparate {
            left: Box::new(footprint),
            right: Box::new(range(kept, 8)),
        };
        (
            goal,
            separation,
            Proposition::condition_is(OldConditionTerm::address_equal(actual, named), true),
        )
    }

    #[test]
    fn footprint_normalization_uses_scoped_addresses_but_only_selected_separation() {
        let _session = crate::kernel::VerificationSession::enter();
        let (goal, separation, alias) = footprint_alias_fixture();
        let parent = PureFactStore::from_ordered(std::slice::from_ref(&separation));
        let branch = parent.with_fact(alias);
        assert!(
            normalize_using_conditions(&goal, std::slice::from_ref(&separation), &branch).is_ok()
        );
        assert!(normalize_using_conditions(&goal, &[], &branch).is_err());
        assert!(
            normalize_using_conditions(&goal, std::slice::from_ref(&separation), &parent).is_err()
        );
        let mut short = separation.clone();
        let Proposition::ResourceSeparate { right, .. } = &mut short else {
            unreachable!()
        };
        **right = Resource::Memory(MemoryRange::new_with_element_width(
            Address::symbolic(Variable(96_142)),
            0u32.into(),
            4u32.into(),
            1,
        ));
        let branch = branch.with_fact(short.clone());
        assert!(normalize_using_conditions(&goal, &[short], &branch).is_err());
    }

    #[test]
    fn context_free_normalization_checks_uint64_constant_disequality() {
        let equality = OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::uint64_constant(1)),
            right: Box::new(OldMachineTerm::uint64_constant(0)),
        };
        assert!(normalizes_context_free_leaf(&Proposition::condition_is(
            equality.clone(),
            false,
        )));
        assert!(!normalizes_context_free_leaf(&Proposition::condition_is(
            equality, true,
        )));

        let same_bits = OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::uint64_constant(u64::MAX)),
            right: Box::new(OldMachineTerm::int64_constant(-1)),
        };
        assert!(normalizes_context_free_leaf(&Proposition::condition_is(
            same_bits, true,
        )));

        let symbolic = OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(Variable(90_000))),
            right: Box::new(OldMachineTerm::uint64_constant(0)),
        };
        assert!(!normalizes_context_free_leaf(&Proposition::condition_is(
            symbolic, false,
        )));
    }

    #[test]
    fn quantified_structural_matching_preserves_scope_and_rejects_logic() {
        let eq = |a, b| {
            Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(a)),
                    OldMachineTerm::Variable(Variable(b)),
                ),
                true,
            )
        };
        let forall = |v, body| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                Variable(v),
                Sort::ProgramInt32,
                body,
            )
        };
        let nested = forall(1, forall(2, eq(1, 2)));
        assert!(quantified_binder_equivalent(
            &nested,
            &forall(3, forall(4, eq(3, 4)))
        ));
        assert!(!quantified_binder_equivalent(
            &nested,
            &forall(3, forall(3, eq(3, 3)))
        ));
        assert!(!quantified_binder_equivalent(
            &forall(1, eq(1, 3)),
            &forall(3, eq(3, 3))
        ));
        assert!(!quantified_binder_equivalent(
            &forall(1, eq(1, 7)),
            &forall(2, eq(2, 8))
        ));
        // A shadowing binder must not change the binding of its sibling.
        let left = forall(
            1,
            Proposition::And(Box::new(forall(1, eq(1, 1))), Box::new(eq(1, 7))),
        );
        let right = forall(
            2,
            Proposition::And(Box::new(forall(3, eq(3, 3))), Box::new(eq(2, 7))),
        );
        assert!(quantified_binder_equivalent(&left, &right));
        let exists = crate::kernel::quantifiers::test_exists(
            "witness".into(),
            Variable(2),
            Sort::ProgramInt32,
            eq(2, 2),
        );
        assert!(!quantified_binder_equivalent(&forall(1, eq(1, 1)), &exists));
        let reflexive = forall(1, eq(1, 1));
        let wrong_sort = crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(1),
            Sort::ProgramInt64,
            eq(1, 1),
        );
        assert!(!quantified_binder_equivalent(&reflexive, &wrong_sort));
        let tautology = forall(
            2,
            Proposition::condition_is(OldConditionTerm::Constant(true), true),
        );
        assert!(
            quantified_equivalent_available_fact(&tautology, &[reflexive]).is_none(),
            "logical equivalence is not binder renaming"
        );
    }

    #[test]
    fn quantified_memory_free_key_rejects_raw_and_registered_loads() {
        let pointer = Address::new("p".into(), AddressOffset::constant(0));
        let before = intern_memory(SymbolicMemory::new().with_block("p", 4));
        let after = intern_memory(before.as_ref().clone().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(9)),
        ));
        let quantified = |memory: SharedMemory, named: bool| {
            let load = if named {
                OldMachineTerm::Variable(load_variable_for_cell_with_origin(
                    &memory,
                    &pointer,
                    crate::kernel::LoadKind::Int32,
                    crate::kernel::load_access_width_or_widest(&memory, &pointer),
                    &memory,
                ))
            } else {
                crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::at(&memory),
                    pointer.clone(),
                    crate::kernel::LoadKind::Int32,
                )
            };
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                Variable(1),
                Sort::ProgramInt32,
                Proposition::condition_is(
                    OldConditionTerm::equal(load, OldMachineTerm::Variable(Variable(1))),
                    true,
                ),
            )
        };
        for named in [false, true] {
            let left = quantified(before.clone(), named);
            let right = quantified(after.clone(), named);
            assert!(super::super::fact_keys::memory_free_quantified_key(&left).is_none());
            assert_eq!(
                quantified_equivalence_index_key(&left),
                quantified_equivalence_index_key(&right)
            );
            assert!(!quantified_binder_equivalent(&left, &right));
        }
    }

    #[test]
    fn quantified_registered_load_renames_binder_without_renaming_unrelated_state() {
        let nested_cell = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::raw_add(
                AddressOffset::raw_add(
                    AddressOffset::scaled_int32_node(
                        OldMachineTerm::Variable(Variable(100_000)),
                        4,
                    ),
                    AddressOffset::constant(8),
                ),
                AddressOffset::constant(4),
            ),
        );
        let memory = intern_memory(SymbolicMemory::new().store(
            nested_cell.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        let quantified = |retained_state: &crate::kernel::SharedMemory, binder: Variable| {
            let pointer = Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(binder), 4),
            );
            let load = load_variable_for_cell_with_origin(
                retained_state,
                &pointer,
                crate::kernel::LoadKind::Int32,
                4,
                retained_state,
            );
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                binder,
                Sort::ProgramInt32,
                Proposition::condition_is(
                    OldConditionTerm::equal(
                        OldMachineTerm::Variable(load),
                        OldMachineTerm::constant(7),
                    ),
                    true,
                ),
            )
        };
        let available = quantified(&memory, Variable(3_200_000));
        let requested = quantified(&memory, Variable(2_000_000));
        assert!(
            PureFactStore::from_ordered(&[available])
                .matching_quantified_fact(&requested)
                .is_some()
        );
        let changed = intern_memory(memory.as_ref().clone().store(
            nested_cell,
            ProgramValue::Int32(OldMachineTerm::constant(9)),
        ));
        assert!(!quantified_binder_equivalent(
            &requested,
            &quantified(&changed, Variable(3_200_000)),
        ));
    }

    #[test]
    fn quantified_binder_comparison_respects_occurrences_inside_states() {
        let pointer = Address::new("cell".into(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new().with_block("cell", 4).store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(11))),
        );
        let proposition = |binder| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                Variable(binder),
                Sort::ProgramInt32,
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(crate::kernel::OldMachineTerm::read_named(
                            crate::kernel::ProgramPoint::of_memory(&memory),
                            pointer.clone(),
                            crate::kernel::LoadKind::Int32,
                        )),
                        right: Box::new(OldMachineTerm::Variable(Variable(binder))),
                    },
                    true,
                ),
            )
        };
        // Both formulas name the same state, but 11 is bound inside its
        // stored value only in the first formula. SymbolicMemory state identity plus an
        // outer-binder key cannot establish their equivalence.
        assert!(!quantified_binder_equivalent(
            &proposition(11),
            &proposition(22)
        ));
    }

    #[test]
    fn canonical_origin_transport_uses_explicit_memory_derivations() {
        let preserved = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let written = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(4));
        let before = SymbolicMemory::new();
        let after = before.clone().store(
            written.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let assumptions =
            PureFactContext::new().assume_proposition(Proposition::MemoryMutatesOnly {
                before: before.clone(),
                before_point: Default::default(),
                after: after.clone(),
                after_point: Default::default(),
                writes: vec![(written, crate::kernel::AccessExtent::from(4))],
            });
        // The canonical memories are the cells' versions. SymbolicMemory states that
        // differ only by a declared block or a write to another cell share
        // a version, so a synthetic marker block would not separate these
        // load variables; a write to the queried cell does (the second pair).
        // Both sides are the same four-byte access; the question under test
        // is the version, not the width.
        let left = load_variable_for_cell_with_origin(
            &intern_memory(before.clone()),
            &preserved,
            crate::kernel::LoadKind::Int32,
            4,
            &intern_memory(before.clone()),
        );
        let right = load_variable_for_cell_with_origin(
            &intern_memory(after.clone()),
            &preserved,
            crate::kernel::LoadKind::Int32,
            4,
            &intern_memory(after.clone()),
        );

        let unchanged = OriginsUnchanged::new(&assumptions).decide(
            OldMachineTerm::Variable(left),
            OldMachineTerm::Variable(right),
        );
        assert!(
            unchanged,
            "the effect fact should transport the preserved cell"
        );

        // Also force state comparison with a write to the queried cell.
        // The explicit derivation check must reject this pair without entering
        // the global state-comparison planner.
        let loaded = preserved;
        let changed_before = SymbolicMemory::new().store(
            loaded.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let changed_after = changed_before.clone().store(
            loaded.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(2)),
        );
        let changed_left = load_variable_for_cell_with_origin(
            &intern_memory(changed_before.clone()),
            &loaded,
            crate::kernel::LoadKind::Int32,
            4,
            &intern_memory(changed_before),
        );
        let changed_right = load_variable_for_cell_with_origin(
            &intern_memory(changed_after.clone()),
            &loaded,
            crate::kernel::LoadKind::Int32,
            4,
            &intern_memory(changed_after),
        );
        assert_ne!(
            changed_left, changed_right,
            "a write to the cell separates its names"
        );
        let (changed_unchanged, events) = crate::instrumentation::collect(|| {
            OriginsUnchanged::new(&PureFactContext::new()).decide(
                OldMachineTerm::Variable(changed_left),
                OldMachineTerm::Variable(changed_right),
            )
        });
        assert!(
            !changed_unchanged,
            "a write to the loaded cell must not be transported as unchanged"
        );
        assert!(
            !events.iter().any(|event| matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "state comparison: bounded alias"
            )),
            "explicit origin transport must not plan a state comparison: {events:#?}"
        );
    }

    #[test]
    fn quantified_check_key_is_alpha_invariant_and_preserves_free_variables() {
        let quantified = |outer: Variable, inner: Variable, free: Variable, name: &str| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                outer,
                Sort::ProgramInt32,
                Proposition::And(
                    Box::new(Proposition::condition_is(
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(OldMachineTerm::Variable(outer)),
                            right: Box::new(OldMachineTerm::Variable(free)),
                        },
                        true,
                    )),
                    Box::new(crate::kernel::quantifiers::test_exists(
                        name.to_string(),
                        inner,
                        Sort::ProgramInt32,
                        Proposition::condition_is(
                            OldConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::Equal,
                                left: Box::new(OldMachineTerm::Variable(inner)),
                                right: Box::new(OldMachineTerm::Variable(outer)),
                            },
                            true,
                        ),
                    )),
                ),
            )
        };

        let left = quantified(Variable(0), Variable(1), Variable(7), "left name");
        let renamed = quantified(
            Variable(10_000),
            Variable(20_000),
            Variable(7),
            "right name",
        );
        let different_free = quantified(
            Variable(10_000),
            Variable(20_000),
            Variable(8),
            "right name",
        );

        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&renamed),
            "binder identities and existential display names are not semantic"
        );
        assert_ne!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&different_free),
            "free variable identities remain part of the key"
        );
    }

    /// `have result == 1 implies forall (k) { ... }` and the claim it
    /// discharges lower the same guarded quantifier with independent fresh
    /// binders. An explicit `known` must find the alpha-equivalent fact
    /// through the quantified index, and must still refuse a different guard
    /// or a different quantified body.
    #[test]
    fn guarded_quantifier_matches_its_alpha_variant_only() {
        let guard = |value: u32| {
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(OldMachineTerm::Variable(Variable(1))),
                    right: Box::new(OldMachineTerm::constant(value)),
                },
                true,
            )
        };
        let guarded = |guard: Proposition, binder: Variable, bound: Variable| {
            Proposition::Implies(
                Box::new(guard),
                Box::new(crate::kernel::quantifiers::test_forall(
                    Default::default(),
                    binder,
                    Sort::ProgramInt32,
                    Proposition::condition_is(
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessThan,
                            left: Box::new(OldMachineTerm::Variable(binder)),
                            right: Box::new(OldMachineTerm::Variable(bound)),
                        },
                        true,
                    ),
                )),
            )
        };
        let fact = guarded(guard(1), Variable(2_000_000), Variable(7));
        let renamed = guarded(guard(1), Variable(3_100_000), Variable(7));
        let other_guard = guarded(guard(0), Variable(3_100_000), Variable(7));
        let other_body = guarded(guard(1), Variable(3_100_000), Variable(8));

        assert!(quantified_equivalence_index_key(&fact).is_some());
        assert_eq!(
            quantified_equivalence_index_key(&fact),
            quantified_equivalence_index_key(&renamed)
        );
        assert!(quantified_binder_equivalent(&fact, &renamed));
        assert!(!quantified_binder_equivalent(&fact, &other_guard));
        assert!(!quantified_binder_equivalent(&fact, &other_body));
        assert!(
            quantified_equivalence_index_key(&guard(1)).is_none(),
            "an unquantified implication keeps its exact lookup"
        );

        let facts = PureFactStore::from_ordered(std::slice::from_ref(&fact));
        assert!(facts.pure_known_available(&renamed));
        assert!(!facts.pure_known_available(&other_guard));
        assert!(!facts.pure_known_available(&other_body));
    }

    #[test]
    fn algebraic_binder_renaming_with_structural_reads_uses_its_own_sort() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Fuel".into());
        let before = intern_memory(SymbolicMemory::new().with_block("p", 4));
        let pointer = Address::new("p".into(), AddressOffset::constant(0));
        let after = intern_memory(before.memory().clone().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        ));
        let make = |binder, argument, memory: SharedMemory| {
            crate::kernel::quantifiers::test_exists(
                "fuel".into(),
                Variable(binder),
                Sort::Algebraic(ty.clone()),
                Proposition::condition_is(
                    OldConditionTerm::equal(
                        OldMachineTerm::ClickFunctionApplication {
                            name: "observe".into(),
                            arguments: vec![PureFunctionArgument::Algebraic(AlgebraicTerm {
                                algebraic_type: ty.clone(),
                                node: AlgebraicTermNode::Variable(Variable(argument)),
                            })],
                        },
                        crate::kernel::OldMachineTerm::read_named(
                            ProgramPoint::at(&memory),
                            pointer.clone(),
                            LoadKind::Int32,
                        ),
                    ),
                    true,
                ),
            )
        };
        let original = make(70_200, 70_200, before.clone());
        assert!(quantified_binder_equivalent(
            &original,
            &make(70_201, 70_201, before.clone())
        ));
        assert!(!quantified_binder_equivalent(
            &original,
            &make(70_201, 70_200, before)
        ));
        assert!(!quantified_binder_equivalent(
            &original,
            &make(70_201, 70_201, after)
        ));
    }

    #[test]
    fn quantified_check_key_sees_through_load_variables() {
        // A universal lowered to load variables keys as the loads those
        // variables represent. A bound index inside a load variable keys by
        // binder ordinal, so renamed binders share a bucket with each other
        // and with the same universal written in load terms.
        let memory = intern_memory(SymbolicMemory::new().with_block("p", 12));
        let cell = |index: Variable| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                Address::new(
                    "p".into(),
                    AddressOffset::scaled_int32_node(OldMachineTerm::Variable(index), 4),
                ),
                crate::kernel::LoadKind::Int32,
            )
        };
        let universal = |index: Variable, term: OldMachineTerm| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                index,
                Sort::ProgramInt32,
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(term),
                        right: Box::new(OldMachineTerm::Variable(index)),
                    },
                    true,
                ),
            )
        };
        let named = |index: Variable| crate::kernel::canonical_term(&cell(index));
        assert!(matches!(
            named(Variable(3_000_000)),
            OldMachineTerm::MemoryLoad(..)
        ));
        let left = universal(Variable(3_000_000), named(Variable(3_000_000)));
        let renamed = universal(Variable(2_000_000), named(Variable(2_000_000)));
        let written = universal(Variable(3_000_001), cell(Variable(3_000_001)));
        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&renamed)
        );
        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&written)
        );
        assert!(quantified_binder_equivalent(&left, &renamed));
    }

    #[test]
    fn quantified_check_key_canonicalizes_range_fold_binders() {
        let universal = |index: Variable, accumulator: Variable, item: Variable| {
            let fold = OldMachineTerm::range_fold(
                OldMachineTerm::Variable(index),
                OldMachineTerm::add(OldMachineTerm::Variable(index), OldMachineTerm::constant(4)),
                OldMachineTerm::constant(0),
                accumulator,
                item,
                OldMachineTerm::add(
                    OldMachineTerm::Variable(accumulator),
                    OldMachineTerm::Variable(item),
                ),
            );
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                index,
                Sort::ProgramInt32,
                Proposition::condition_is(
                    OldConditionTerm::equal(fold, OldMachineTerm::constant(0)),
                    true,
                ),
            )
        };

        let left = universal(Variable(30_000), Variable(30_001), Variable(30_002));
        let renamed = universal(Variable(40_000), Variable(40_001), Variable(40_002));
        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&renamed),
            "range-fold binders should be alpha-equivalent in quantified fact keys"
        );

        let facts = PureFactStore::from_ordered(std::slice::from_ref(&left));
        assert_eq!(
            facts.matching_quantified_fact(&renamed),
            Some(left),
            "the alpha-equivalent range-fold fact should be found through its index"
        );
    }

    /// The perpetual-service `fold(service(owner))` near-miss: the body's
    /// separation fact is available from the unfold, but the fold state
    /// rewrites it through a memory that retains this path's store cells, so
    /// the two forms print identically yet compare structurally unequal.
    /// The bounded separation matcher must equate them from the recorded
    /// pointer-offset equality and separation facts, without the open-ended
    /// kernel search whose budget truncation used to be misreported as a
    /// missing fact.
    #[test]
    fn fold_body_separation_fact_matches_across_store_states() {
        let owner_base = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 4),
        );
        let owner_field = |bytes: i64| {
            Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::raw_add(owner_base.offset.clone(), AddressOffset::constant(bytes)),
            )
        };
        let phase_field = owner_field(4);
        let cell_field = owner_field(8);
        let load = |memory: &SymbolicMemory, pointer: &Address| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(intern_memory(memory.clone()))),
                pointer.clone(),
                crate::kernel::LoadKind::Int32,
            )
        };
        let empty = SymbolicMemory::new();
        // The form recorded when the resource body was unfolded: the cell
        // pointer read through the call-havoc state.
        let havoc = SymbolicMemory::new().with_block("havoc:1000000", 0);
        // The form carried by the recorded execution facts: the same
        // loads read through the branch-entry memory with its retained cells.
        let entry = empty
            .clone()
            .store(
                phase_field.clone(),
                ProgramValue::Int32(load(&empty, &phase_field)),
            )
            .store(
                owner_base.clone(),
                ProgramValue::Int32(load(&empty, &owner_base)),
            );
        let cell_element_offset = |memory: &SymbolicMemory| {
            AddressOffset::scaled_int32_node(load(memory, &cell_field), 4)
        };
        // The fold-state form reads the cell pointer through a memory
        // that still carries the `owner->cell[0] = owner->phase` store, whose
        // written address is itself written through a loaded pointer, so no
        // assumption-free normalization can drop the cell.
        let folded = havoc.clone().store(
            Address::new(AddressBase::ExternalArgument, cell_element_offset(&havoc)),
            ProgramValue::Int32(load(&havoc, &owner_base)),
        );
        let separation = |left_start: u32, left_end: u32, cell_memory: &SymbolicMemory| {
            Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new(
                    owner_base.clone(),
                    OldMachineTerm::constant(left_start),
                    OldMachineTerm::constant(left_end),
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new(
                    Address::new(
                        AddressBase::ExternalArgument,
                        cell_element_offset(cell_memory),
                    ),
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(1),
                ))),
            }
        };
        let required = separation(0, 4, &folded);
        let available = separation(0, 4, &havoc);

        // The two forms are different propositions, so plain exact matching
        // must miss even though source diagnostics render the same resource.
        assert_ne!(required, available);
        assert!(!exact_fact_is_available(
            &required,
            std::slice::from_ref(&available)
        ));

        // The recorded execution facts: the two forms of the cell pointer
        // denote one offset, and the loaded pointer's field is separate from
        // the written cell range.
        let offsets_equal = Proposition::condition_is(
            OldConditionTerm::AddressOffsetEqual(
                Box::new(cell_element_offset(&havoc)),
                Box::new(cell_element_offset(&entry)),
            ),
            true,
        );
        let fields_separate = separation(2, 4, &entry);
        let assumptions =
            assumptions_from_propositions(&[offsets_equal.clone(), fields_separate.clone()]);
        assert_eq!(
            directly_matching_separation_fact_under(
                &required,
                std::slice::from_ref(&available),
                &assumptions,
            ),
            Some(available.clone()),
            "the bounded separation matcher must transport the unfold form to the fold state"
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_reasoning/tests.rs");
        include!("../../scaling_tests/kernel/proof/fact_reasoning/float_comparison_spellings.rs");
    }
}

/// One side of an equality whose selected scalar reads can be related.
///
/// The bridging argument is identical for pointer-offset and int32
/// equalities — only the shape of a side and of the equality differ — so one
/// implementation serves both.
trait ScalarReadBridgeSide: Clone + PartialEq + Sized {
    /// The structural read this side represents, when it represents one.
    fn scalar_read(&self) -> Option<OldMachineTerm>;
    /// The two sides of an equality of this shape.
    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)>;
    /// An equality of this shape over the two sides.
    fn equality(left: Self, right: Self) -> Proposition;
}

impl ScalarReadBridgeSide for AddressOffset {
    fn scalar_read(&self) -> Option<OldMachineTerm> {
        let OffsetView::Int32Scaled { index: value, .. } = self.view() else {
            return None;
        };
        value.operand_view().read_source()?.scalar_read()
    }

    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)> {
        let Proposition::ConditionIs(condition, true) = proposition else {
            return None;
        };
        let (left, right) = condition.old_form().true_pointer_offset_sides()?;
        Some((left.clone(), right.clone()))
    }

    fn equality(left: Self, right: Self) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::AddressOffsetEqual(Box::new(left), Box::new(right)),
            true,
        )
    }
}

impl ScalarReadBridgeSide for OldMachineTerm {
    /// A side represents a load either with its load variable or with the
    /// load term itself; both forms denote one atom, so both answer here.
    fn scalar_read(&self) -> Option<OldMachineTerm> {
        crate::kernel::eval::viewed_as_memory_load(self)
    }

    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)> {
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = proposition.old_condition()
        else {
            return None;
        };
        Some((left.as_ref().clone(), right.as_ref().clone()))
    }

    fn equality(left: Self, right: Self) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            true,
        )
    }
}

/// Whether an equality premise follows from recorded equalities through
/// selected read endpoints. The existing bounded closure visits each side once;
/// it no longer needs to create a reserved name to recognize a read.
fn bridged_by_load_variable_edges<S: ScalarReadBridgeSide>(
    premise: &Proposition,
    facts: &[Proposition],
    exceeds_budget: fn(usize) -> bool,
) -> bool {
    if exceeds_budget(facts.len()) {
        return false;
    }
    let Some((start, goal)) = S::equality_sides(premise) else {
        return false;
    };
    let edges: Vec<(S, S)> = facts
        .iter()
        .filter_map(S::equality_sides)
        .filter(|(left, right)| left.scalar_read().is_some() || right.scalar_read().is_some())
        .collect();
    if edges.is_empty() {
        return false;
    }
    let mut frontier = vec![start];
    let mut visited: Vec<S> = Vec::new();
    while let Some(current) = frontier.pop() {
        if current == goal {
            return true;
        }
        if visited.contains(&current) {
            continue;
        }
        if exceeds_budget(edges.len() + visited.len()) {
            return false;
        }
        visited.push(current.clone());
        for (left, right) in &edges {
            if left == &current && !visited.contains(right) {
                frontier.push(right.clone());
            } else if right == &current && !visited.contains(left) {
                frontier.push(left.clone());
            }
        }
    }
    false
}

/// Decides, and remembers, whether two read descriptors stand for one cell
/// that framing shows unchanged between their origin states.
struct OriginsUnchanged<'a> {
    assumptions: &'a PureFactContext,
    decided: std::collections::HashMap<(OldMachineTerm, OldMachineTerm), bool>,
}

impl<'a> OriginsUnchanged<'a> {
    fn new(assumptions: &'a PureFactContext) -> Self {
        Self {
            assumptions,
            decided: std::collections::HashMap::new(),
        }
    }

    fn decide(&mut self, left: OldMachineTerm, right: OldMachineTerm) -> bool {
        let key = (left, right);
        if let Some(decided) = self.decided.get(&key) {
            return *decided;
        }
        let decided = self.compute(&key.0, &key.1);
        self.decided.insert(key, decided);
        decided
    }

    fn compute(&self, left: &OldMachineTerm, right: &OldMachineTerm) -> bool {
        let origin = |term: &OldMachineTerm| {
            let read = crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Old(term),
            )?;
            Some(crate::kernel::OldMachineTerm::read_named(
                read.origin?.for_legacy_read(),
                read.pointer,
                read.kind,
            ))
        };
        let (Some(left_load), Some(right_load)) = (origin(left), origin(right)) else {
            return false;
        };
        let (
            OldMachineTerm::MemoryLoad(_, left_pointer, left_kind),
            OldMachineTerm::MemoryLoad(_, right_pointer, right_kind),
        ) = (&left_load, &right_load)
        else {
            return false;
        };
        // Retain the selected, checked alias/state path when different
        // pointer spellings identify this cell. The read kind is preserved.
        left_kind == right_kind
            && ((left_pointer.base != right_pointer.base
                && crate::kernel::memory_history::checked_origin_load_equality(
                    left,
                    right,
                    self.assumptions,
                ))
                || left_pointer.address() == right_pointer.address()
                    && crate::kernel::explicit_atomic_equality_from_memory_derivations(
                        &left_load,
                        &right_load,
                        self.assumptions,
                    ))
    }
}

/// The forms of `side` that represent the same cell as one of `endpoints`.
fn origin_renamings<S: ScalarReadBridgeSide>(
    side: &S,
    endpoints: &[S],
    origins: &mut OriginsUnchanged<'_>,
    exceeds_budget: fn(usize) -> bool,
) -> Vec<S> {
    let Some(variable) = side.scalar_read() else {
        return vec![side.clone()];
    };
    let mut forms = vec![side.clone()];
    for endpoint in endpoints {
        if exceeds_budget(1) {
            break;
        }
        let candidate = endpoint.scalar_read().expect("filtered by the caller");
        if candidate != variable
            && origins.decide(variable.clone(), candidate)
            && !forms.contains(endpoint)
        {
            forms.push(endpoint.clone());
        }
    }
    forms
}

fn bridged_with_origins<S: ScalarReadBridgeSide>(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
    exceeds_budget: fn(usize) -> bool,
) -> bool {
    if exceeds_budget(facts.len()) {
        return false;
    }
    let Some((start, goal)) = S::equality_sides(premise) else {
        return false;
    };
    let mut origins = OriginsUnchanged::new(assumptions);
    // Two load variables for one unchanged cell need no fact edge at all:
    // when the premise equates them directly, the origins-unchanged proof is
    // the whole content.
    if let (Some(start_variable), Some(goal_variable)) = (start.scalar_read(), goal.scalar_read())
        && origins.decide(start_variable, goal_variable)
    {
        return true;
    }
    // One implicit hop only: restate the premise's load-variable endpoints as
    // fact endpoints naming the same cell, with `OriginsUnchanged` providing
    // the contextual evidence, then ask the plain fact-edge closure.
    let endpoints: Vec<S> = facts
        .iter()
        .filter_map(S::equality_sides)
        .flat_map(|(left, right)| [left, right])
        .filter(|side| side.scalar_read().is_some())
        .collect();
    let start_forms = origin_renamings(&start, &endpoints, &mut origins, exceeds_budget);
    let goal_forms = origin_renamings(&goal, &endpoints, &mut origins, exceeds_budget);
    for start_form in &start_forms {
        for goal_form in &goal_forms {
            if exceeds_budget(1) {
                return false;
            }
            if start_form == goal_form {
                return true;
            }
            let candidate = S::equality(start_form.clone(), goal_form.clone());
            if bridged_by_load_variable_edges::<S>(&candidate, facts, exceeds_budget) {
                return true;
            }
        }
    }
    false
}

/// A planner probe charges edge visits and origin comparisons to the active
/// search budget. Its answer has no checking authority.
pub(in crate::kernel) fn plan_load_variable_bridge(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    load_variable_bridge(
        premise,
        facts,
        assumptions,
        crate::instrumentation::deadline_exceeded_with_work,
    )
}

fn load_variable_bridge(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
    exceeds_budget: fn(usize) -> bool,
) -> bool {
    match premise {
        Proposition::ConditionIs(condition, true)
            if condition.old_form().pointer_offset_sides().is_some() =>
        {
            bridged_by_load_variable_edges::<AddressOffset>(premise, facts, exceeds_budget)
                || bridged_with_origins::<AddressOffset>(
                    premise,
                    facts,
                    assumptions,
                    exceeds_budget,
                )
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left: _,
                    right: _,
                },
                _,
            )) = condition_source_0.old_condition() =>
        {
            bridged_by_load_variable_edges::<OldMachineTerm>(premise, facts, exceeds_budget)
                || bridged_with_origins::<OldMachineTerm>(
                    premise,
                    facts,
                    assumptions,
                    exceeds_budget,
                )
        }
        _ => false,
    }
}

/// The condition branch of bridged availability. A load named at one
/// state and the same cell named at a later state are different load
/// variables whenever the edge between them is crossed only in context:
/// call-havoc and store edges carry no path assumptions (see
/// `MemoryDerivation`). A required condition is therefore available when an
/// already-selected candidate is the same condition with each pair of load
/// atoms proven equal under these assumptions.
/// Candidate selection remains the caller's state-blind bucket; nothing is
/// searched, and structurally different propositions never match.
pub(crate) fn condition_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    if matches!(required, Proposition::ResourceSeparate { .. }) || available.is_empty() {
        return false;
    }
    available.iter().any(|candidate| {
        propositions_equal_modulo_origin_unchanged(candidate, required, assumptions)
    })
}

/// [`condition_bridged_fact_is_available`] over an unindexed fact slice:
/// candidates are the facts sharing the required proposition's state-blind
/// key, selected by one pass over the slice, as the exact slice checks beside
/// it already do.
pub(crate) fn condition_bridged_fact_is_available_among(
    required: &Proposition,
    facts: &(impl super::PropositionSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    if matches!(required, Proposition::ResourceSeparate { .. }) {
        return false;
    }
    let key = super::fact_keys::memory_erased_proposition_key(required);
    let candidates: Vec<Proposition> = facts
        .propositions()
        .filter(|fact| {
            *fact != required && super::fact_keys::memory_erased_proposition_key(fact) == key
        })
        .cloned()
        .collect();
    condition_bridged_fact_is_available(required, &candidates, assumptions)
}

/// [`propositions_equal_modulo_proven_states`] for the condition bridge:
/// load atoms additionally match when the memory DAG proves the two loads
/// unchanged between their states under `assumptions`. Separations keep
/// their own branch.
fn propositions_equal_modulo_origin_unchanged(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && assumptions.conditions_equal_modulo_origin_unchanged(
                    left_condition.old_form(),
                    right_condition.old_form(),
                )
        }
        (Proposition::Implies(left_a, left_b), Proposition::Implies(right_a, right_b))
        | (Proposition::And(left_a, left_b), Proposition::And(right_a, right_b))
        | (Proposition::Or(left_a, left_b), Proposition::Or(right_a, right_b)) => {
            propositions_equal_modulo_origin_unchanged(left_a, right_a, assumptions)
                && propositions_equal_modulo_origin_unchanged(left_b, right_b, assumptions)
        }
        (Proposition::Not(left_body), Proposition::Not(right_body)) => {
            propositions_equal_modulo_origin_unchanged(left_body, right_body, assumptions)
        }
        _ => false,
    }
}

/// The separation branch of bridged availability. Keep its range and
/// proposition temporaries out of the shared fact-dispatch frame; the
/// expansion small-stack regression pins that boundary.
#[inline(never)]
fn separation_bridged_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
    framing: &(impl ExecutionFactSource + ?Sized),
) -> bool {
    let assumptions = framing
        .fact_iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact.proposition().clone())
        });
    available.iter().any(|candidate| {
        matches!(candidate, Proposition::ResourceSeparate { .. })
            && propositions_equal_modulo_proven_states(candidate, required, &assumptions)
    })
}

/// Whether two separations denote the same fact after canonicalization and
/// proven state comparison: each range's base offset and span terms
/// compare with load variables resolved shallowly and load atoms bridged
/// across proven states — the relation the condition arm uses, applied
/// to the terms a separation is made of. Separation is symmetric, so both pairings are
/// tried. Keep its range temporaries local rather than charging every caller;
/// the expansion small-stack regression pins that boundary.
#[inline(never)]
fn separations_equal_modulo_proven_states(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (Some((left_a, left_b)), Some((right_a, right_b))) =
        (left.memory_separation(), right.memory_separation())
    else {
        return false;
    };
    let ranges_equal = |left: &MemoryRange, right: &MemoryRange| {
        // The state transport below proves signed 32-bit equalities only.
        left == right
            || (left.int32_bounds().is_some()
                && right.int32_bounds().is_some()
                && left.element_width() == right.element_width()
                && left.base().base == right.base().base
                && assumptions.conditions_equal_modulo_proven_states(
                    &OldConditionTerm::AddressOffsetEqual(
                        Box::new(expand_offset_load_variables_shallow(&left.base().offset)),
                        Box::new(AddressOffset::constant(0)),
                    ),
                    &OldConditionTerm::AddressOffsetEqual(
                        Box::new(expand_offset_load_variables_shallow(&right.base().offset)),
                        Box::new(AddressOffset::constant(0)),
                    ),
                )
                && assumptions.conditions_equal_modulo_proven_states(
                    &OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(expand_load_variables_shallow(left.start())),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                    &OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(expand_load_variables_shallow(right.start())),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                )
                && assumptions.conditions_equal_modulo_proven_states(
                    &OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(expand_load_variables_shallow(left.end())),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                    &OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(expand_load_variables_shallow(right.end())),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                ))
    };
    ranges_equal(left_a, right_a) && ranges_equal(left_b, right_b)
        || ranges_equal(left_a, right_b) && ranges_equal(left_b, right_a)
}

#[cfg(test)]
mod integer_reflexivity_tests {
    use super::*;
    use crate::kernel::proof::PureFactStore;
    use crate::kernel::{
        Address, AddressOffset, IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType,
        OldMachineTerm, ProgramValue, SharedIntegerRangeEndpoint, SharedMachineIntegerTerm,
        SymbolicMemory, Variable,
    };

    #[test]
    fn integer_reflexivity_normalization_checks_polarity_and_exact_terms() {
        for term in [
            IntegerTerm::Variable(Variable(920)),
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                OldMachineTerm::Variable(Variable(920)),
            )
            .unwrap(),
        ] {
            let equal = OldConditionTerm::IntegerEqual(term.clone().into(), term.clone().into());
            let unequal =
                OldConditionTerm::IntegerNotEqual(term.clone().into(), term.clone().into());
            assert!(normalizes_context_free(&Proposition::condition_is(
                equal.clone(),
                true
            )));
            assert!(!normalizes_context_free(&Proposition::condition_is(
                equal, false
            )));
            assert!(normalizes_context_free(&Proposition::condition_is(
                unequal.clone(),
                false
            )));
            assert!(!normalizes_context_free(&Proposition::condition_is(
                unequal, true
            )));
            let successor = IntegerTerm::add(term.clone(), IntegerTerm::constant_i64(1));
            assert!(!normalizes_context_free(&Proposition::condition_is(
                OldConditionTerm::IntegerEqual(term.into(), successor.into()),
                true,
            )));
        }
    }

    fn integer_fold(
        index: IntegerRangeFoldIndex,
        accumulator: Variable,
        item: Variable,
        body: IntegerTerm,
    ) -> IntegerTerm {
        IntegerTerm::range_fold(index, IntegerTerm::constant_i64(0), accumulator, item, body)
    }

    fn integer_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(2).into(),
        }
    }

    fn int32_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
        }
    }

    #[test]
    fn integer_equality_normalization_accepts_alpha_equivalent_fold_carriers() {
        let left_accumulator = Variable(93_000);
        let left_item = Variable(93_001);
        let right_accumulator = Variable(94_000);
        let right_item = Variable(94_001);
        let left = integer_fold(
            integer_index(),
            left_accumulator,
            left_item,
            IntegerTerm::add(
                IntegerTerm::var(left_accumulator),
                IntegerTerm::var(left_item),
            ),
        );
        let right = integer_fold(
            integer_index(),
            right_accumulator,
            right_item,
            IntegerTerm::add(
                IntegerTerm::var(right_accumulator),
                IntegerTerm::var(right_item),
            ),
        );
        let equality = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &left.into(),
                &right.into(),
            ),
            Some(true)
        );
        assert!(normalizes_context_free(&equality));

        let left_accumulator = Variable(95_000);
        let left_item = Variable(95_001);
        let right_accumulator = Variable(96_000);
        let right_item = Variable(96_001);
        let left = integer_fold(
            int32_index(),
            left_accumulator,
            left_item,
            IntegerTerm::add(
                IntegerTerm::var(left_accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    OldMachineTerm::Variable(left_item),
                )),
            ),
        );
        let right = integer_fold(
            int32_index(),
            right_accumulator,
            right_item,
            IntegerTerm::add(
                IntegerTerm::var(right_accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    OldMachineTerm::Variable(right_item),
                )),
            ),
        );
        let equality = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &left.into(),
                &right.into(),
            ),
            Some(true)
        );
        assert!(normalizes_context_free(&equality));
    }

    fn listed_loaded_fold(memory: &SharedMemory, seed: u64, free: u64) -> Proposition {
        let fold = |seed| {
            let accumulator = Variable(seed);
            let item = Variable(seed + 1);
            let pointer = Address::new("listed-fold".into(), AddressOffset::constant(0))
                .offset_by_typed_elements(OldMachineTerm::Variable(item), 4, false, false);
            integer_fold(
                int32_index(),
                accumulator,
                item,
                IntegerTerm::add(
                    IntegerTerm::var(accumulator),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        crate::kernel::OldMachineTerm::read_named(
                            ProgramPoint::at(memory),
                            pointer,
                            LoadKind::Int32,
                        ),
                    )),
                ),
            )
        };
        Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                fold(seed).into(),
                IntegerTerm::add(fold(seed + 2), IntegerTerm::var(Variable(free))).into(),
            ),
            true,
        )
    }

    #[test]
    fn listed_loaded_fold_premises_allow_only_bound_renaming() {
        let _session = VerificationSession::enter();
        let before = intern_memory(SymbolicMemory::new().with_block("listed-fold", 16));
        let after = intern_memory(before.as_ref().clone().store(
            Address::new("listed-fold".into(), AddressOffset::constant(0)),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        ));
        let source = listed_loaded_fold(&before, 970_000, 979_000);
        let renamed = listed_loaded_fold(&before, 971_000, 979_000);
        assert!(
            super::super::fact_keys::integer_condition_alpha_key(&source)
                .unwrap()
                .checked_eq(
                    &super::super::fact_keys::integer_condition_alpha_key(&renamed).unwrap()
                )
                == Some(true)
        );
        assert!(listed_comparison_fact_is_available(
            &renamed,
            std::slice::from_ref(&source)
        ));
        assert!(!listed_comparison_fact_is_available(&renamed, &[]));
        for changed in [
            listed_loaded_fold(&after, 971_000, 979_000),
            listed_loaded_fold(&before, 971_000, 979_001),
        ] {
            assert!(!listed_comparison_fact_is_available(
                &changed,
                std::slice::from_ref(&source)
            ));
        }
        let Proposition::ConditionIs(condition, _) = renamed else {
            unreachable!()
        };
        assert!(!listed_comparison_fact_is_available(
            &Proposition::condition_is(condition, false),
            &[source]
        ));
    }

    fn normalization_pointer_equality(left: &Address, right: &Address) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::address_equal(left.clone(), right.clone()),
            true,
        )
    }

    #[test]
    fn normalize_using_shared_domain_reads_ordinary_bounds_without_exports() {
        use crate::kernel::machine_integer::{Operation, definedness::OverflowQueryView};
        use crate::kernel::{
            KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as Op,
            MachineOperandView as View,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable =
            |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
        let left = KernelTerm::machine_binary_shared(
            ty,
            Op::Multiply,
            [variable(975001), variable(975002)],
        );
        let right = variable(975003);
        let [upper, lower] = OverflowQueryView::from_operands(
            ty,
            Operation::Add,
            [View::Shared(&left), View::Shared(&right)],
        )
        .unwrap()
        .bounds();
        let domain = Proposition::And(Box::new(upper.clone()), Box::new(lower.clone()));
        let reversed = Proposition::And(Box::new(lower.clone()), Box::new(upper.clone()));
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&domain));
        let incomplete = PureFactStore::from_ordered(std::slice::from_ref(&upper));
        let exports = KernelTermExport::machine_export_count();
        for goal in [&upper, &lower] {
            assert!(
                normalize_using_conditions(goal, std::slice::from_ref(&domain), &facts).is_ok(),
                "{goal:?}"
            );
        }
        assert!(matches!(
            normalize_using_conditions(&lower, std::slice::from_ref(&domain), &incomplete),
            Err(ConditionalNormalizationError::UnavailablePremise(0))
        ));
        // The tactic still requires explicit logical construction of an And.
        for goal in [&domain, &reversed] {
            assert!(
                normalize_using_conditions(goal, std::slice::from_ref(&domain), &facts).is_err()
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn ordinary_domain_still_supplies_a_legacy_normalization_query() {
        let _session = crate::kernel::VerificationSession::enter();
        let condition = OldConditionTerm::signed_add_overflows(
            OldMachineTerm::add(
                OldMachineTerm::Variable(Variable(975011)),
                OldMachineTerm::Variable(Variable(975012)),
            ),
            OldMachineTerm::Variable(Variable(975013)),
        );
        let goal = Proposition::condition_is(condition, false);
        let bounds =
            crate::kernel::machine_integer::definedness::integer_bounds_of_definedness(&goal);
        let domain = Proposition::And(Box::new(bounds[0].clone()), Box::new(bounds[1].clone()));
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&domain));
        assert!(normalize_using_conditions(&goal, std::slice::from_ref(&domain), &facts).is_ok());
        assert!(normalize_using_conditions(&goal, &bounds[..1], &facts).is_err());
    }

    #[test]
    fn normalize_using_queries_ambient_graph_but_validates_cited_premises() {
        let a = Address::symbolic(Variable(96_100));
        let b = Address::symbolic(Variable(96_101));
        let c = Address::symbolic(Variable(96_102));
        let ab = normalization_pointer_equality(&a, &b);
        let bc = normalization_pointer_equality(&b, &c);
        let goal = normalization_pointer_equality(&a.offset_by_bytes(8), &c.offset_by_bytes(8));
        let parent = PureFactStore::from_ordered(std::slice::from_ref(&ab));
        let branch = parent.with_fact(bc.clone());
        assert!(normalize_using_conditions(&goal, &[], &branch).is_ok());
        assert!(normalize_using_conditions(&goal, &[ab], &branch).is_ok());
        assert!(matches!(
            normalize_using_conditions(&goal, &[], &parent),
            Err(ConditionalNormalizationError::DoesNotNormalize)
        ));
        let missing = Proposition::condition_is(OldConditionTerm::Variable(Variable(96_103)), true);
        assert!(matches!(
            normalize_using_conditions(&goal, &[missing], &branch),
            Err(ConditionalNormalizationError::UnavailablePremise(0))
        ));
        let compound = Proposition::And(Box::new(bc.clone()), Box::new(bc));
        let branch = branch.with_fact(compound.clone());
        assert!(matches!(
            normalize_using_conditions(&goal, &[compound], &branch),
            Err(ConditionalNormalizationError::UnsupportedPremise(0))
        ));
        assert!(
            normalize_using_conditions(&Proposition::Not(Box::new(goal)), &[], &branch).is_err()
        );
    }

    #[test]
    fn normalize_using_graph_keeps_load_states_and_binders_distinct() {
        let _session = crate::kernel::VerificationSession::enter();
        let a = Address::symbolic(Variable(96_110));
        let b = Address::symbolic(Variable(96_111));
        let before =
            crate::kernel::intern_memory(SymbolicMemory::new().with_block("normalize-graph", 8));
        let after = crate::kernel::intern_memory(
            before
                .memory()
                .clone()
                .store(a.clone(), ProgramValue::Int32(OldMachineTerm::constant(7))),
        );
        let load = |memory: &crate::kernel::SharedMemory, address: &Address| {
            Address::symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                address,
                crate::kernel::LoadKind::Int32,
                8,
                memory,
            ))
        };
        let left = load(&before, &a);
        let right = load(&before, &b);
        let changed = load(&after, &b);
        let facts = PureFactStore::from_ordered(&[normalization_pointer_equality(&a, &b)]);
        assert!(
            normalize_using_conditions(&normalization_pointer_equality(&left, &right), &[], &facts)
                .is_ok()
        );
        assert!(
            normalize_using_conditions(
                &normalization_pointer_equality(&left, &changed),
                &[],
                &facts
            )
            .is_err()
        );
        let quantified = crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(96_110),
            Sort::ProgramPointer(ProgramType::Int32Pointer),
            normalization_pointer_equality(&a, &b),
        );
        assert!(normalize_using_conditions(&quantified, &[], &facts).is_err());
    }

    #[test]
    fn normalize_using_accepts_reversed_alpha_renamed_integer_fold_equality() {
        let source = integer_fold(
            integer_index(),
            Variable(93_100),
            Variable(93_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(93_100)),
                IntegerTerm::var(Variable(93_101)),
            ),
        );
        let renamed = integer_fold(
            integer_index(),
            Variable(94_100),
            Variable(94_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(94_100)),
                IntegerTerm::var(Variable(94_101)),
            ),
        );
        let source: SharedIntegerTerm = source.into();
        let renamed: SharedIntegerTerm = renamed.into();
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(&source, &renamed),
            Some(true)
        );
        let premise = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(source.clone(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let goal = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(IntegerTerm::constant_i64(0).into(), renamed),
            true,
        );
        let facts =
            crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&premise));
        assert!(normalize_using_conditions(&goal, &[premise], &facts).is_ok());
    }

    #[test]
    fn normalize_using_alpha_reverse_keeps_state_identity_and_premise_scope() {
        let pointer = Address::new(
            "normalize-fold-retained_state".into(),
            AddressOffset::constant(0),
        );
        let before = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block("normalize-fold-retained_state", 8),
        );
        let after = crate::kernel::intern_memory(before.as_ref().clone().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        ));
        let load_fold = |memory: &crate::kernel::SharedMemory, accumulator, item| {
            integer_fold(
                int32_index(),
                accumulator,
                item,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    crate::kernel::OldMachineTerm::read_named(
                        ProgramPoint::at(memory),
                        pointer.clone(),
                        crate::kernel::LoadKind::Int32,
                    ),
                )),
            )
        };
        let source = load_fold(&before, Variable(94_200), Variable(94_201));
        let changed_memory_state = load_fold(&after, Variable(95_200), Variable(95_201));
        let premise = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(source.into(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let goal = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(0).into(),
                changed_memory_state.into(),
            ),
            true,
        );
        let facts =
            crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&premise));
        assert!(matches!(
            normalize_using_conditions(&goal, std::slice::from_ref(&premise), &facts),
            Err(ConditionalNormalizationError::DoesNotNormalize)
        ));

        // A cited premise must be available: the list is the whole evidence.
        let missing_facts = crate::kernel::proof::PureFactStore::from_ordered(&[]);
        assert!(matches!(
            normalize_using_conditions(&premise, std::slice::from_ref(&premise), &missing_facts),
            Err(ConditionalNormalizationError::UnavailablePremise(0))
        ));
        // A premise that holds without facts (`0 == 0`) needs none, as in
        // every other `using` list.
        let reflexive = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(0).into(),
                IntegerTerm::constant_i64(0).into(),
            ),
            true,
        );
        assert!(
            normalize_using_conditions(
                &reflexive,
                std::slice::from_ref(&reflexive),
                &missing_facts
            )
            .is_ok()
        );
    }

    #[test]
    fn normalize_using_reverses_scalar_integer_equalities_and_disequalities() {
        let left = IntegerTerm::var(Variable(95_300));
        let right = IntegerTerm::var(Variable(95_301));
        for (condition, reversed) in [
            (
                OldConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
                OldConditionTerm::IntegerEqual(right.clone().into(), left.clone().into()),
            ),
            (
                OldConditionTerm::IntegerNotEqual(left.clone().into(), right.clone().into()),
                OldConditionTerm::IntegerNotEqual(right.into(), left.into()),
            ),
        ] {
            let premise = Proposition::condition_is(condition, true);
            let goal = Proposition::condition_is(reversed, true);
            let facts =
                crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&premise));
            assert!(normalize_using_conditions(&goal, &[premise], &facts).is_ok());
        }
    }

    #[test]
    fn normalize_using_reverses_int32_equality_and_disequality() {
        let left = OldMachineTerm::Variable(Variable(95_302));
        let right = OldMachineTerm::Variable(Variable(95_303));
        for value in [true, false] {
            let premise = Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                value,
            );
            let goal = Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(right.clone()),
                    right: Box::new(left.clone()),
                },
                value,
            );
            let facts =
                crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&premise));
            assert!(normalize_using_conditions(&goal, &[premise], &facts).is_ok());
        }
    }

    #[test]
    fn integer_equality_normalization_rejects_free_and_cross_carrier_bindings() {
        let bound = integer_fold(
            integer_index(),
            Variable(97_000),
            Variable(97_001),
            IntegerTerm::var(Variable(97_000)),
        );
        let free = integer_fold(
            integer_index(),
            Variable(98_000),
            Variable(98_001),
            IntegerTerm::var(Variable(97_000)),
        );
        let equality = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(bound.clone().into(), free.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &bound.into(),
                &free.into(),
            ),
            Some(false)
        );
        assert!(!normalizes_context_free(&equality));

        let integer_item = Variable(99_000);
        let machine_item = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            OldMachineTerm::Variable(integer_item),
        ));
        let integer_bound = integer_fold(
            integer_index(),
            Variable(99_001),
            integer_item,
            IntegerTerm::var(integer_item),
        );
        let machine_bound =
            integer_fold(int32_index(), Variable(99_001), integer_item, machine_item);
        let equality = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                integer_bound.clone().into(),
                machine_bound.clone().into(),
            ),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &integer_bound.into(),
                &machine_bound.into(),
            ),
            Some(false)
        );
        assert!(!normalizes_context_free(&equality));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_reasoning/integer_reflexivity_tests.rs");
    }
}

#[cfg(test)]
mod uint64_loop_tests {
    use super::*;
    use crate::kernel::{OldConditionTerm, OldMachineTerm, Proposition, Variable};

    #[test]
    fn uint64_equality_certificate_requires_both_order_premises() {
        let a = OldMachineTerm::Variable(Variable(981001));
        let b = OldMachineTerm::Variable(Variable(981002));
        let goal =
            Proposition::condition_is(OldConditionTerm::int64_equal(a.clone(), b.clone()), true);
        let le = Proposition::condition_is(
            OldConditionTerm::uint64_less_equal(a.clone(), b.clone()),
            true,
        );
        let not_lt = Proposition::condition_is(OldConditionTerm::uint64_less_than(a, b), false);
        let premises = [le, not_lt];
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&premises);
        normalize_using_conditions(&goal, &premises, &facts).unwrap();
        for selection in [&premises[..1], &premises[1..], &premises[..0]] {
            assert!(normalize_using_conditions(&goal, selection, &facts).is_err());
        }
    }

    #[test]
    fn uint64_subtraction_upper_bound_requires_no_wrap_and_the_upper_bound() {
        let length = OldMachineTerm::Variable(Variable(981_011));
        let removed = OldMachineTerm::Variable(Variable(981_012));
        let upper = OldMachineTerm::Variable(Variable(981_013));
        let difference = OldMachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Subtract,
            left: Box::new(length.clone()),
            right: Box::new(removed.clone()),
        };
        let condition = OldConditionTerm::uint64_less_equal(difference, upper.clone());
        let goal = Proposition::condition_is(condition.clone(), true);
        let premises = [
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(removed, length.clone()),
                true,
            ),
            Proposition::condition_is(OldConditionTerm::uint64_less_equal(length, upper), true),
        ];
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&premises);
        normalize_using_conditions(&goal, &premises, &facts).unwrap();
        for selection in [&premises[..1], &premises[1..], &premises[..0]] {
            assert!(normalize_using_conditions(&goal, selection, &facts).is_err());
            let context = selection
                .iter()
                .cloned()
                .fold(crate::kernel::PureFactContext::new(), |context, fact| {
                    context.assume_proposition(fact)
                });
            assert_ne!(context.decide(&condition), Some(true));
        }
        let context = premises
            .iter()
            .cloned()
            .fold(crate::kernel::PureFactContext::new(), |context, fact| {
                context.assume_proposition(fact)
            });
        assert_eq!(context.decide(&condition), Some(true));
        // A full-width subtrahend must not be truncated into an apparent zero.
        let wrapped = OldMachineTerm::uint64_subtract(
            OldMachineTerm::uint64_constant(1),
            OldMachineTerm::uint64_constant(1u64 << 32),
        );
        assert_eq!(
            context.decide(&OldConditionTerm::uint64_less_equal(
                wrapped,
                OldMachineTerm::uint64_constant(1),
            )),
            Some(false)
        );
    }

    #[test]
    fn uint64_partial_restoration_requires_both_subtraction_and_addition_bounds() {
        let whole = OldMachineTerm::Variable(Variable(981_021));
        let removed = OldMachineTerm::Variable(Variable(981_022));
        let restored = OldMachineTerm::Variable(Variable(981_023));
        let upper = OldMachineTerm::Variable(Variable(981_024));
        let difference = OldMachineTerm::uint64_subtract(whole.clone(), removed.clone());
        let premises = [
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(removed.clone(), whole.clone()),
                true,
            ),
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(restored.clone(), removed),
                true,
            ),
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(whole, upper.clone()),
                true,
            ),
        ];
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&premises);
        for sum in [
            OldMachineTerm::uint64_add(difference.clone(), restored.clone()),
            OldMachineTerm::uint64_add(restored, difference),
        ] {
            let condition = OldConditionTerm::uint64_less_equal(sum, upper.clone());
            let goal = Proposition::condition_is(condition.clone(), true);
            normalize_using_conditions(&goal, &premises, &facts).unwrap();
            for omitted in 0..premises.len() {
                let selected: Vec<_> = premises
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != omitted)
                    .map(|(_, p)| p.clone())
                    .collect();
                assert!(normalize_using_conditions(&goal, &selected, &facts).is_err());
                let context = selected
                    .into_iter()
                    .fold(crate::kernel::PureFactContext::new(), |context, fact| {
                        context.assume_proposition(fact)
                    });
                assert_ne!(context.decide(&condition), Some(true));
            }
            let context = premises
                .iter()
                .cloned()
                .fold(crate::kernel::PureFactContext::new(), |context, fact| {
                    context.assume_proposition(fact)
                });
            assert_eq!(context.decide(&condition), Some(true));
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_reasoning/uint64_loop_tests.rs");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // SymbolicMemory state equality cannot reinterpret unequal native bounds as signed bits.
    #[test]
    fn wide_separations_compare_structurally_without_signed_state_transport() {
        let base = Address::symbolic(Variable(984_800));
        let wide = MemoryRange::new_wide(
            base.clone(),
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(1 << 33),
            4,
        );
        let other = MemoryRange::new_wide(
            base,
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(2 << 33),
            4,
        );
        let separation = |range| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range)),
            right: Box::new(Resource::Memory(wide.clone())),
        };
        let facts = PureFactContext::new();
        assert!(separations_equal_modulo_proven_states(
            &separation(wide.clone()),
            &separation(wide.clone()),
            &facts
        ));
        assert!(!separations_equal_modulo_proven_states(
            &separation(wide.clone()),
            &separation(other),
            &facts
        ));
    }
}

#[cfg(test)]
mod range_width_state_tests {
    use super::*;
    // One byte misses offset two, while one four-byte word overlaps it.
    #[test]
    fn separation_state_transport_keeps_element_widths() {
        let base = Address::symbolic(Variable(985_800));
        let range = |width| {
            MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 1u32.into(), width)
        };
        let right = MemoryRange::new_with_element_width(
            base.offset_by_bytes(2),
            0u32.into(),
            1u32.into(),
            1,
        );
        let separation = |width| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range(width))),
            right: Box::new(Resource::Memory(right.clone())),
        };
        assert!(!separations_equal_modulo_proven_states(
            &separation(1),
            &separation(4),
            &PureFactContext::new()
        ));
    }
}

#[cfg(test)]
mod annotated_address_condition_tests {
    use super::*;

    fn comparison(annotated: bool) -> OldConditionTerm {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let address = |id| {
            OldMachineTerm::object_pointer_address(
                Address::symbolic(Variable(id)),
                annotated.then_some(CAccessClass::Scalar(CScalarClass::Int)),
            )
        };
        OldConditionTerm::uint64_equal(address(981_020), address(981_021))
    }

    fn choice(condition: OldConditionTerm, value: bool) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::equal(
                OldMachineTerm::If {
                    condition: Box::new(condition),
                    then_term: Box::new(OldMachineTerm::constant(1)),
                    else_term: Box::new(OldMachineTerm::constant(0)),
                },
                OldMachineTerm::constant(u32::from(value)),
            ),
            true,
        )
    }

    #[test]
    fn annotated_address_truth_uses_the_shared_index_and_stays_scoped() {
        let _session = VerificationSession::enter();
        for annotated in [false, true] {
            for value in [false, true] {
                let source = Proposition::condition_is(comparison(annotated), value);
                let parent = PureFactContext::new();
                let branch = parent.clone().assume_proposition(source.clone());
                let queried = comparison(!annotated);
                assert_eq!(branch.decide(&queried), Some(value));
                assert_eq!(
                    branch
                        .selected_for_test()
                        .decide_selected_condition(&queried),
                    Some(value)
                );
                for context in [parent, branch.restricted_to_facts(&[], &[])] {
                    assert_eq!(context.decide(&queried), None);
                    assert_eq!(
                        context
                            .selected_for_test()
                            .decide_selected_condition(&queried),
                        None
                    );
                }
            }
        }
    }

    #[test]
    fn compound_address_facts_keep_the_same_candidate_and_checked_match() {
        let _session = VerificationSession::enter();
        let wrapped = |annotated, value| {
            Proposition::Implies(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Constant(true),
                    true,
                )),
                Box::new(Proposition::condition_is(comparison(annotated), value)),
            )
        };
        for annotated in [false, true] {
            for value in [false, true] {
                let source = wrapped(annotated, value);
                let target = wrapped(!annotated, value);
                let facts = crate::kernel::proof::PureFactStore::from_ordered(
                    std::slice::from_ref(&source),
                );
                assert_eq!(
                    super::super::fact_keys::memory_erased_proposition_key(&source),
                    super::super::fact_keys::memory_erased_proposition_key(&target),
                );
                assert!(condition_bridged_fact_is_available(
                    &target,
                    std::slice::from_ref(&source),
                    facts.assumptions(),
                ));
                assert!(facts.available_across_effects(&target, &ExecutionFacts::new()));
                assert!(!facts.available_across_effects(
                    &wrapped(!annotated, !value),
                    &ExecutionFacts::new()
                ));
                assert!(
                    !crate::kernel::proof::PureFactStore::default()
                        .available_across_effects(&target, &ExecutionFacts::new(),)
                );
            }
        }
    }

    #[test]
    fn annotated_address_candidates_do_not_erase_changed_index_reads() {
        let _session = VerificationSession::enter();
        let cell = Address::new("annotated-address-index".into(), AddressOffset::constant(0));
        let before = intern_memory(
            SymbolicMemory::new()
                .with_block("annotated-address-index", 4)
                .store(
                    cell.clone(),
                    ProgramValue::Int32(OldMachineTerm::constant(0)),
                ),
        );
        let after = intern_memory(before.memory().clone().store(
            cell.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        ));
        let fact = |memory: SharedMemory, annotated: bool| {
            use crate::kernel::effective_type::{CAccessClass, CScalarClass};
            let pointer = Address::new(
                "annotated-address-target".into(),
                AddressOffset::scale_int32(
                    crate::kernel::OldMachineTerm::read_named(
                        ProgramPoint::at(&memory),
                        cell.clone(),
                        LoadKind::Int32,
                    ),
                    1,
                ),
            );
            Proposition::Implies(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Constant(true),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::uint64_equal(
                        OldMachineTerm::object_pointer_address(
                            pointer,
                            annotated.then_some(CAccessClass::Scalar(CScalarClass::Int)),
                        ),
                        OldMachineTerm::integer_address(Address::new(
                            "annotated-address-target".into(),
                            AddressOffset::constant(0),
                        )),
                    ),
                    true,
                )),
            )
        };
        let source = fact(before, false);
        let target = fact(after, true);
        let key = super::super::fact_keys::memory_erased_proposition_key(&target);
        assert_eq!(
            key,
            super::super::fact_keys::memory_erased_proposition_key(&source)
        );
        assert!(key.requires_checked_match());
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&[source]);
        assert!(!facts.available_across_effects(&target, &ExecutionFacts::new()));
    }

    #[test]
    fn normalize_cites_either_address_spelling_without_importing_ambient_negations() {
        let _session = VerificationSession::enter();
        for annotated in [false, true] {
            for value in [false, true] {
                let source = Proposition::condition_is(comparison(annotated), value);
                let cited = Proposition::condition_is(comparison(!annotated), value);
                let facts = crate::kernel::proof::PureFactStore::from_ordered(&[source]);
                let goal = choice(comparison(annotated), value);
                normalize_using_conditions(&goal, std::slice::from_ref(&cited), &facts).unwrap();
                assert!(matches!(
                    normalize_using_conditions(
                        &goal,
                        &[cited],
                        &crate::kernel::proof::PureFactStore::from_ordered(&[])
                    ),
                    Err(ConditionalNormalizationError::UnavailablePremise(0))
                ));
                if !value {
                    assert!(
                        normalize_using_conditions(&goal, &[], &facts).is_err(),
                        "an uncited negative condition is not an equality"
                    );
                }
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/proof/fact_reasoning/annotated_address_condition_tests.rs"
        );
    }
}

#[cfg(test)]
mod index_sum_offset_tests {
    use super::*;
    use crate::kernel::proof::PureFactStore;

    pub(super) fn index(id: u64) -> OldMachineTerm {
        OldMachineTerm::Variable(Variable(id))
    }

    pub(super) fn scaled(id: u64, byte_width: i64) -> AddressOffset {
        AddressOffset::scaled_int64_node(index(id), byte_width, true)
    }

    pub(super) fn observed(id: u64) -> IntegerTerm {
        IntegerTerm::from_machine(MachineIntegerType::UInt64, index(id)).unwrap()
    }

    /// `base + shared... + prefix + suffix` against `base + shared... + total`.
    pub(super) fn address_goal(shared: u64, width: i64) -> Proposition {
        let mut common = AddressOffset::scaled_int32_node(index(990_000), 1);
        for addend in 0..shared {
            common = AddressOffset::raw_add(common, scaled(991_000 + addend, 1));
        }
        let pointer = |offset| Address::new(AddressBase::ExternalArgument, offset);
        let summed = AddressOffset::raw_add(
            AddressOffset::raw_add(common.clone(), scaled(1, width)),
            scaled(2, width),
        );
        let whole = AddressOffset::raw_add(common, scaled(3, width));
        Proposition::condition_is(
            OldConditionTerm::AddressEqual(Box::new(pointer(summed)), Box::new(pointer(whole))),
            true,
        )
    }

    pub(super) fn exact_sum() -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::integer_equal(
                observed(3),
                IntegerTerm::add(observed(1), observed(2)),
            ),
            true,
        )
    }

    #[test]
    fn an_exact_index_sum_equates_offsets_and_a_wrapping_one_does_not() {
        let cited = exact_sum();
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&cited));
        assert!(
            normalize_using_conditions(&address_goal(0, 4), std::slice::from_ref(&cited), &facts)
                .is_ok()
        );
        // Cited premises only: the same fact, held but not cited, decides nothing.
        assert!(normalize_using_conditions(&address_goal(0, 4), &[], &facts).is_err());
        let native = Proposition::condition_is(
            OldConditionTerm::uint64_equal(
                index(3),
                OldMachineTerm::uint64_add(index(1), index(2)),
            ),
            true,
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&native));
        assert!(
            normalize_using_conditions(&address_goal(0, 4), std::slice::from_ref(&native), &facts)
                .is_err()
        );
        // Indices at different element widths are different displacements.
        let mixed = Proposition::condition_is(
            OldConditionTerm::AddressEqual(
                Box::new(Address::new(
                    AddressBase::ExternalArgument,
                    AddressOffset::raw_add(scaled(1, 4), scaled(2, 8)),
                )),
                Box::new(Address::new(AddressBase::ExternalArgument, scaled(3, 4))),
            ),
            true,
        );
        let cited = exact_sum();
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&cited));
        assert!(normalize_using_conditions(&mixed, std::slice::from_ref(&cited), &facts).is_err());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_reasoning/index_sum_offset_tests.rs");
    }
}

/// Decide the supplied proposition without premise discovery.
pub(crate) fn holds_by_lookup_or_decision(
    context: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    if context.proves_exact(proposition) {
        return true;
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            context.decide(condition.old_form()) == Some(*value)
        }
        Proposition::Not(body) => matches!(
            body.as_ref(),
            Proposition::ConditionIs(condition, value)
                if context.decide(condition.old_form()) == Some(!*value)
        ),
        _ => false,
    }
}

#[cfg(test)]
#[path = "loaded_quantifier_tests.rs"]
mod loaded_quantifier_tests;
