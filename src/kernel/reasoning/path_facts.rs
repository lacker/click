use super::*;

pub(in crate::kernel) fn memory_range_still_available(
    range_memory: &CMemory,
    current_memory: &CMemory,
    base: &Pointer,
) -> bool {
    range_memory == current_memory
        || range_memory.has_block(&base.block) == current_memory.has_block(&base.block)
}

pub(in crate::kernel) fn forall_int32(var: Variable, body: Proposition) -> Proposition {
    Proposition::ForAll {
        var,
        sort: Sort::CInt32,
        body: Box::new(body),
    }
}

pub(in crate::kernel) fn wrap_proof_facts(
    proposition: Proposition,
    assumptions: &Assumptions,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    let proposition = facts
        .iter()
        .filter(|fact| fact.is_public())
        .rev()
        .fold(proposition, |body, fact| {
            Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
        });

    let proposition = assumptions
        .prop_facts
        .iter()
        .rev()
        .fold(proposition, |body, proposition| {
            Proposition::Implies(Box::new(proposition.clone()), Box::new(body))
        });

    assumptions
        .condition_facts
        .iter()
        .rev()
        .fold(proposition, |body, (condition, value)| {
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition.clone(), *value)),
                Box::new(body),
            )
        })
}

pub(in crate::kernel) fn wrap_path_context(
    proposition: Proposition,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    facts.iter().rev().fold(proposition, |body, fact| {
        Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
    })
}

pub(in crate::kernel) fn public_execution_pure_facts(
    facts: &[ExecutionPureFact],
) -> Vec<ExecutionPureFact> {
    facts
        .iter()
        .filter(|fact| fact.is_public())
        .cloned()
        .collect()
}

pub(in crate::kernel) fn memory_effect_execution_facts(
    facts: &[ExecutionPureFact],
) -> Vec<ExecutionPureFact> {
    facts
        .iter()
        .filter(|fact| {
            matches!(
                fact.proposition(),
                Proposition::CMemoryMutatesOnly { .. }
                    | Proposition::CMemoryEffectSummary { .. }
                    | Proposition::CHeapLifetimeRetired { .. }
            )
        })
        .cloned()
        .collect()
}

pub(in crate::kernel) fn solve_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => actual == expected,
        Proposition::And(left, right) => solve_builtin_prop(left) && solve_builtin_prop(right),
        Proposition::Or(left, right) => solve_builtin_prop(left) || solve_builtin_prop(right),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => {
                actual != expected
            }
            _ => false,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes)),
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => memory_ranges_disjoint_builtin(
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        ),
        Proposition::CResourceSeparate { .. } | Proposition::CResourceContains { .. } => false,
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => memory.access_in_bounds(pointer, *byte_width),
        _ => false,
    }
}

pub(in crate::kernel) fn memory_ranges_disjoint_builtin(
    left_base: &Pointer,
    left_start: &Bitvector32Term,
    left_end: &Bitvector32Term,
    right_base: &Pointer,
    right_start: &Bitvector32Term,
    right_end: &Bitvector32Term,
) -> bool {
    if left_base.blocks_proven_distinct(right_base) {
        return true;
    }

    let Some(left_base_index) = left_base.element_index_from_base(&Pointer {
        block: left_base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }) else {
        return false;
    };
    let Some(right_base_index) = right_base.element_index_from_base(&Pointer {
        block: right_base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }) else {
        return false;
    };
    let (Some(left_base_index), Some(left_start), Some(left_end)) = (
        signed_bitvector_constant(&left_base_index),
        signed_bitvector_constant(left_start),
        signed_bitvector_constant(left_end),
    ) else {
        return false;
    };
    let (Some(right_base_index), Some(right_start), Some(right_end)) = (
        signed_bitvector_constant(&right_base_index),
        signed_bitvector_constant(right_start),
        signed_bitvector_constant(right_end),
    ) else {
        return false;
    };

    let left_start = left_base_index + left_start;
    let left_end = left_base_index + left_end;
    let right_start = right_base_index + right_start;
    let right_end = right_base_index + right_end;
    left_end <= right_start || right_end <= left_start
}

pub(in crate::kernel) fn int32_element_index_from_offset(
    offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            int32_element_index_from_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            int32_element_index_from_offset(left)
        }
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            int32_element_index_from_offset(left)?,
            int32_element_index_from_offset(right)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width == 4 => {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Constant(offset) if offset % 4 == 0 => {
            let index = offset / 4;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn pointer_byte_offset_from_base(
    pointer: &Pointer,
    base: &Pointer,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }
    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }
    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            byte_offset_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            byte_offset_from_pointer_offset(left)
        }
        _ if base.offset == PointerOffsetTerm::Constant(0) => {
            byte_offset_from_pointer_offset(&pointer.offset)
        }
        _ => {
            let pointer_offset = byte_offset_from_pointer_offset(&pointer.offset)?;
            let base_offset = byte_offset_from_pointer_offset(&base.offset)?;
            Some(Bitvector32Term::subtract(pointer_offset, base_offset))
        }
    }
}

pub(in crate::kernel) fn byte_offset_from_pointer_offset(
    offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) => (i32::MIN as i64..=i32::MAX as i64)
            .contains(offset)
            .then_some(Bitvector32Term::Constant((*offset as i32) as u32)),
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            byte_offset_from_pointer_offset(left)?,
            byte_offset_from_pointer_offset(right)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let width = u32::try_from(*byte_width).ok()?;
            match width {
                0 => Some(Bitvector32Term::Constant(0)),
                1 => Some(value.as_ref().clone()),
                _ => Some(Bitvector32Term::Multiply(
                    Box::new(value.as_ref().clone()),
                    Box::new(Bitvector32Term::Constant(width)),
                )),
            }
        }
        PointerOffsetTerm::Variable(_) => None,
    }
}

pub(in crate::kernel) fn int32_element_count_from_bytes(
    bytes: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    match bytes {
        Bitvector32Term::Multiply(left, right)
            if right.as_ref() == &Bitvector32Term::Constant(4) =>
        {
            Some(left.as_ref().clone())
        }
        Bitvector32Term::Multiply(left, right)
            if left.as_ref() == &Bitvector32Term::Constant(4) =>
        {
            Some(right.as_ref().clone())
        }
        Bitvector32Term::Constant(bytes) if bytes % 4 == 0 => {
            Some(Bitvector32Term::Constant(bytes / 4))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn signed_const_add(
    term: &Bitvector32Term,
    addend: u32,
) -> Option<Bitvector32Term> {
    let addend = i32::try_from(addend).ok()?;
    let sum = (term.as_const()? as i32).checked_add(addend)?;
    Some(Bitvector32Term::Constant(sum as u32))
}

pub(in crate::kernel) fn add_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, true)
}

pub(in crate::kernel) fn add_path_fact_with_visibility(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
    public: bool,
) -> Option<()> {
    add_path_fact_with_visibility_after_effect(facts, assumptions, proposition, public, false)
}

fn add_path_fact_with_visibility_after_effect(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
    public: bool,
    certified_after_effect: bool,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_path_fact_with_visibility(
            facts,
            assumptions,
            condition,
            value,
            public,
            certified_after_effect,
        );
    }

    if assumptions.proves(&proposition) || facts.iter().any(|fact| fact.proposition == proposition)
    {
        return Some(());
    }

    facts.push(if public {
        ExecutionPureFact::new(proposition)
    } else {
        ExecutionPureFact::internal(proposition)
    });
    Some(())
}

pub(in crate::kernel) fn add_condition_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, true, false)
}

pub(in crate::kernel) fn add_internal_condition_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, false, false)
}

fn add_condition_path_fact_with_visibility(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
    public: bool,
    certified_after_effect: bool,
) -> Option<()> {
    if let Some(known) = assumptions.exact_condition_value(&condition) {
        if known == value {
            return Some(());
        }
        if !certified_after_effect {
            return None;
        }
    }
    if let Some(known) = Assumptions::decide_intrinsically(&condition) {
        return (known == value).then_some(());
    }
    if !assumptions.should_defer_non_exact_condition_reasoning()
        && let Some(known) = assumptions.decide(&condition)
    {
        if known == value {
            return Some(());
        }
        if !certified_after_effect {
            return None;
        }
    }

    if let Some(existing) = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    let proposition = Proposition::ConditionIs(condition, value);
    facts.push(if public {
        ExecutionPureFact::new(proposition)
    } else {
        ExecutionPureFact::internal(proposition)
    });
    Some(())
}

pub(in crate::kernel) fn add_pointer_offset_equality_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
        value,
    )?;

    if let (Some(left_index), Some(right_index)) = (
        int32_element_index_from_offset(&left),
        int32_element_index_from_offset(&right),
    ) {
        add_condition_path_fact(
            facts,
            assumptions,
            ConditionTerm::equal(left_index, right_index),
            value,
        )?;
    }

    Some(())
}

pub(in crate::kernel) fn add_proof_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_proof_obligation_with_context(obligations, assumptions, proposition, None)
}

pub(in crate::kernel) fn add_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
    context: Option<&str>,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_obligation(obligations, assumptions, condition, value, context);
    }

    let defer_contextual_proof = assumptions.should_defer_non_exact_loadability_obligations()
        && matches!(proposition, Proposition::CMemoryLoadable { .. });
    if assumptions.proves_exact(&proposition)
        || !defer_contextual_proof && assumptions.proves(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return Some(());
    }

    let obligation = ProofObligation::new(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
    Some(())
}

pub(in crate::kernel) fn add_required_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
    context: Option<&str>,
) {
    if assumptions.proves(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return;
    }

    let obligation = ProofObligation::verification_condition(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
}

pub(in crate::kernel) fn add_required_proof_obligation_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
    context: Option<&str>,
) {
    if assumptions.proves_exact(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return;
    }
    let obligation = ProofObligation::new(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
}

pub(in crate::kernel) fn append_required_proof_obligations(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_without_search(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_under_path_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    new_obligations: &[ProofObligation],
    facts: &[ExecutionPureFact],
    context_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context(
            obligations,
            assumptions,
            wrap_path_context(obligation.proposition().clone(), facts, context_obligations),
            obligation.context(),
        );
    }
}

pub(in crate::kernel) fn add_condition_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
    context: Option<&str>,
) -> Option<()> {
    if assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), value)) {
        return Some(());
    }
    if assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), !value)) {
        return None;
    }
    if let Some(known) = Assumptions::decide_intrinsically(&condition) {
        return (known == value).then_some(());
    }
    if !assumptions.should_defer_non_exact_condition_reasoning()
        && let Some(known) = assumptions.decide(&condition)
    {
        return (known == value).then_some(());
    }

    if let Some(existing) = obligations
        .iter()
        .filter_map(|obligation| match obligation.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    let obligation = ProofObligation::condition(condition, value);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
    Some(())
}

pub(in crate::kernel) fn merge_obligations(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    let mut obligations = left.to_vec();
    for obligation in right {
        if obligation.is_assumable() {
            // `right` was produced while executing under the complete left
            // path context. Preserve its path guard without asking the
            // general prover to reconsider it against an older memory
            // snapshot. Exact and intrinsic contradictions still reject the
            // merge; non-exact cross-snapshot reasoning cannot erase a path
            // that the executor just certified as possible.
            if assumptions.proves_exact(obligation.proposition())
                || obligations
                    .iter()
                    .any(|existing| existing.proposition() == obligation.proposition())
            {
                continue;
            }
            if let Proposition::ConditionIs(condition, value) = obligation.proposition()
                && (assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), !*value))
                    || Assumptions::decide_intrinsically(condition)
                        .is_some_and(|known| known != *value)
                    || obligations.iter().any(|existing| {
                        matches!(
                            existing.proposition(),
                            Proposition::ConditionIs(existing_condition, existing_value)
                                if existing_condition == condition && existing_value != value
                        )
                    }))
            {
                return None;
            }
            obligations.push(obligation.clone());
        } else {
            // A required obligation was already tested against the path
            // context that created it.  Merging path fragments must preserve
            // that verification condition, not rerun the general prover
            // against an older base context.  The latter cannot discharge a
            // new obligation and becomes catastrophically expensive as
            // verified-call chains accumulate implication facts.
            add_required_proof_obligation_without_search(
                &mut obligations,
                assumptions,
                obligation.proposition().clone(),
                obligation.context(),
            );
        }
    }
    Some(obligations)
}

pub(in crate::kernel) fn merge_facts(
    left: &[ExecutionPureFact],
    right: &[ExecutionPureFact],
    assumptions: &Assumptions,
) -> Option<Vec<ExecutionPureFact>> {
    let mut facts = left.to_vec();
    let mut saw_memory_effect = false;
    for fact in right {
        add_path_fact_with_visibility_after_effect(
            &mut facts,
            assumptions,
            fact.proposition().clone(),
            fact.is_public(),
            saw_memory_effect && fact.is_certified(),
        )?;
        if fact.is_certified()
            && let Some(existing) = facts
                .iter_mut()
                .find(|existing| existing.proposition() == fact.proposition())
        {
            *existing = fact.clone();
        }
        // A verified call emits its effect before its certified
        // postconditions. Entry-state condition facts cannot reject those
        // theorem-backed postconditions after memory has changed, although
        // agreeing entry facts can still make a postcondition redundant.
        if matches!(
            fact.proposition(),
            Proposition::CMemoryMutatesOnly { .. }
                | Proposition::CMemoryEffectSummary { .. }
                | Proposition::CHeapLifetimeRetired { .. }
        ) {
            saw_memory_effect = true;
        }
    }
    Some(facts)
}

pub(in crate::kernel) fn merge_execution_pure_facts_and_obligations(
    left_facts: &[ExecutionPureFact],
    left_obligations: &[ProofObligation],
    right_facts: &[ExecutionPureFact],
    right_obligations: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<(Vec<ExecutionPureFact>, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    // The right fragment was executed under the left fragment's path
    // context. Recheck its assumable obligations against that same context,
    // not against the older base assumptions. In particular, a verified call
    // can change a field that an entry-state branch constrained; replaying a
    // post-call load guard against only the entry snapshot can incorrectly
    // discard a valid successor path.
    let prefix_assumptions =
        assumptions_with_path_context(assumptions, left_facts, left_obligations);
    let obligations = merge_obligations(left_obligations, right_obligations, &prefix_assumptions)?;
    Some((facts, obligations))
}

pub(in crate::kernel) fn decide_with_facts(
    assumptions: &Assumptions,
    facts: &[ExecutionPureFact],
    condition: &ConditionTerm,
) -> Option<bool> {
    [true, false]
        .into_iter()
        .find(|value| {
            assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), *value))
        })
        .or_else(|| Assumptions::decide_intrinsically(condition))
        .or_else(|| {
            (!assumptions.should_defer_non_exact_condition_reasoning())
                .then(|| assumptions.decide(condition))
                .flatten()
        })
        .or_else(|| {
            facts.iter().find_map(|fact| match fact.proposition() {
                Proposition::ConditionIs(existing_condition, value)
                    if existing_condition == condition =>
                {
                    Some(*value)
                }
                _ => None,
            })
        })
        .or_else(|| {
            facts
                .iter()
                .fold(
                    if assumptions.should_defer_non_exact_condition_reasoning() {
                        Assumptions::new()
                    } else {
                        assumptions.clone()
                    },
                    |assumptions, fact| assumptions.assume_proposition(fact.proposition().clone()),
                )
                .decide(condition)
        })
}

pub(in crate::kernel) fn assumptions_with_path_context(
    assumptions: &Assumptions,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for fact in facts {
        assumptions = assumptions.assume_proposition(fact.proposition().clone());
    }
    for obligation in obligations {
        if obligation.is_assumable() {
            assumptions = assumptions.assume_proposition(obligation.proposition().clone());
        }
    }
    assumptions
}

pub(in crate::kernel) fn assumptions_with_propositions(
    assumptions: &Assumptions,
    propositions: &[Proposition],
) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for proposition in propositions {
        assumptions = assumptions.assume_proposition(proposition.clone());
    }
    assumptions
}
