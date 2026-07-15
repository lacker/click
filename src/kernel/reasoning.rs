use super::prelude::*;

pub(super) fn condition_contexts_for_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &Assumptions,
    desired_truthiness: bool,
) -> Vec<Assumptions> {
    let mut contexts = Vec::new();
    let Ok(condition_paths) = evaluate_c_expression_paths(
        state,
        condition,
        assumptions,
        &mut ExecutionBudget::default(),
    ) else {
        return contexts;
    };
    for condition_path in condition_paths {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let CExpressionOutcome::Value(value) = outcome else {
            continue;
        };

        for truthiness_path in
            c_truthiness_paths(value, facts.clone(), obligations.clone(), assumptions)
        {
            if truthiness_path.is_true == desired_truthiness {
                contexts.push(assumptions_with_path_context(
                    assumptions,
                    &truthiness_path.facts,
                    &truthiness_path.obligations,
                ));
            }
        }
    }
    contexts
}

pub(super) fn pointers_proven_distinct(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    left.blocks_proven_distinct(right)
        || left.block == right.block
            && assumptions.decide(&ConditionTerm::pointer_offset_equal(
                left.offset.clone(),
                right.offset.clone(),
            )) == Some(false)
        || assumptions.decide(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(false)
        || assumptions.pointers_proven_disjoint_by_range(left, right)
}

pub(super) fn pointers_proven_equal(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    left == right
        || left.block == right.block
            && assumptions.decide(&ConditionTerm::pointer_offset_equal(
                left.offset.clone(),
                right.offset.clone(),
            )) == Some(true)
        || assumptions.decide(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(true)
}

pub(super) fn memories_match_for_pointer_load(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
) -> bool {
    if left == right {
        return true;
    }
    if pointer.block.starts_with("local:") {
        return false;
    }

    left.blocks
        .iter()
        .filter(|(block, _)| !block.starts_with("local:"))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !block.starts_with("local:")))
        && left
            .cells
            .iter()
            .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block)
            .eq(right
                .cells
                .iter()
                .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block))
}

pub(super) fn memories_match_for_pointer_load_under_assumptions(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if pointer.block.starts_with("local:") {
        return false;
    }
    if !left
        .blocks
        .iter()
        .filter(|(block, _)| !block.starts_with("local:"))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !block.starts_with("local:")))
    {
        return false;
    }

    left.differing_cell_pointers(right)
        .into_iter()
        .filter(|cell_pointer| !cell_pointer.block.starts_with("local:"))
        .all(|cell_pointer| pointers_proven_distinct(&cell_pointer, pointer, assumptions))
}

pub(super) fn memory_matches_effect_summary_endpoint(
    expected: &CMemory,
    actual: &CMemory,
    pointer: &Pointer,
) -> bool {
    expected == actual || memories_match_for_pointer_load(expected, actual, pointer)
}

pub(super) fn condition_as_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        _ => None,
    }
}

pub(super) const FINITE_FORALL_INSTANTIATION_LIMIT: usize = 128;
pub(super) const FINITE_CONTEXT_SPLIT_LIMIT: usize = 8;
pub(super) const DISJUNCTION_CASE_LIMIT: usize = 8;

#[derive(Clone, Debug, Default)]
pub(super) struct FiniteForAllRange {
    pub(super) lower: i64,
    pub(super) upper: i64,
}

#[derive(Clone, Debug)]
pub(super) struct VariableOrderEdge {
    pub(super) lower: Variable,
    pub(super) upper: Variable,
    pub(super) strict: bool,
}

pub(super) fn collect_forall_chain<'a>(
    proposition: &'a Proposition,
    variables: &mut Vec<Variable>,
) -> &'a Proposition {
    match proposition {
        Proposition::ForAll {
            var,
            sort: Sort::CInt32,
            body,
        } => {
            variables.push(*var);
            collect_forall_chain(body, variables)
        }
        proposition => proposition,
    }
}

pub(super) fn collect_or_cases(proposition: &Proposition, cases: &mut Vec<Proposition>) {
    match proposition {
        Proposition::Or(left, right) => {
            collect_or_cases(left, cases);
            collect_or_cases(right, cases);
        }
        proposition => cases.push(proposition.clone()),
    }
}

pub(super) fn finite_forall_ranges(
    variables: &[Variable],
    body: &Proposition,
) -> Option<Vec<FiniteForAllRange>> {
    let variable_set = variables.iter().copied().collect::<BTreeSet<_>>();
    let mut ranges = variables
        .iter()
        .copied()
        .map(|variable| (variable, IntegerRangeFacts::default()))
        .collect::<BTreeMap<_, _>>();
    let mut edges = Vec::new();
    let mut order_facts = Vec::new();
    collect_implication_antecedent_order_facts(body, &mut order_facts);

    for (left, right, strict) in order_facts {
        match (bitvector_variable(&left), signed_bitvector_constant(&right)) {
            (Some(variable), Some(bound)) if variable_set.contains(&variable) => {
                let upper = if strict { bound.checked_sub(1)? } else { bound };
                tighten_upper_bound(&mut ranges, variable, upper);
                continue;
            }
            _ => {}
        }
        match (signed_bitvector_constant(&left), bitvector_variable(&right)) {
            (Some(bound), Some(variable)) if variable_set.contains(&variable) => {
                let lower = if strict { bound.checked_add(1)? } else { bound };
                tighten_lower_bound(&mut ranges, variable, lower);
                continue;
            }
            _ => {}
        }
        match (bitvector_variable(&left), bitvector_variable(&right)) {
            (Some(lower), Some(upper))
                if variable_set.contains(&lower) && variable_set.contains(&upper) =>
            {
                edges.push(VariableOrderEdge {
                    lower,
                    upper,
                    strict,
                });
            }
            _ => {}
        }
    }

    propagate_variable_order_bounds(&mut ranges, &edges)?;

    variables
        .iter()
        .map(|variable| {
            let range = ranges.get(variable)?;
            let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
                return None;
            };
            if lower > upper || upper - lower > 32 {
                return None;
            }
            Some(FiniteForAllRange { lower, upper })
        })
        .collect()
}

pub(super) fn collect_implication_antecedent_order_facts(
    proposition: &Proposition,
    facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
) {
    match proposition {
        Proposition::Implies(left, _) => collect_order_facts_from_assumed_proposition(left, facts),
        Proposition::And(left, right) | Proposition::Or(left, right) => {
            collect_implication_antecedent_order_facts(left, facts);
            collect_implication_antecedent_order_facts(right, facts);
        }
        Proposition::ForAll { body, .. } => collect_implication_antecedent_order_facts(body, facts),
        Proposition::Exists { .. } => {}
        Proposition::Not(_)
        | Proposition::ConditionIs(_, _)
        | Proposition::Equal(_, _)
        | Proposition::Predicate { .. }
        | Proposition::CExpressionEvaluates { .. }
        | Proposition::CConditionEvaluates { .. }
        | Proposition::CStatementExecutes { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CMemoryLoadable { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CMemoryDisjoint { .. }
        | Proposition::CResourceSeparate { .. }
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CWhileInvariantRule { .. } => {}
    }
}

pub(super) fn collect_order_facts_from_assumed_proposition(
    proposition: &Proposition,
    facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
) {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            if let Some(fact) = condition_as_order_fact(condition, *value) {
                facts.push(fact);
            }
        }
        Proposition::And(left, right) => {
            collect_order_facts_from_assumed_proposition(left, facts);
            collect_order_facts_from_assumed_proposition(right, facts);
        }
        _ => {}
    }
}

pub(super) fn tighten_lower_bound(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    variable: Variable,
    lower: i64,
) {
    if let Some(range) = ranges.get_mut(&variable) {
        range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
    }
}

pub(super) fn tighten_upper_bound(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    variable: Variable,
    upper: i64,
) {
    if let Some(range) = ranges.get_mut(&variable) {
        range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
    }
}

pub(super) fn propagate_variable_order_bounds(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    edges: &[VariableOrderEdge],
) -> Option<()> {
    let mut changed = true;
    while changed {
        changed = false;
        for edge in edges {
            let lower_range = ranges.get(&edge.lower)?;
            let upper_range = ranges.get(&edge.upper)?;
            let offset = if edge.strict { 1 } else { 0 };
            let inferred_lower_upper = upper_range
                .upper
                .and_then(|upper| upper.checked_sub(offset));
            let inferred_upper_lower = lower_range
                .lower
                .and_then(|lower| lower.checked_add(offset));

            if let Some(upper) = inferred_lower_upper {
                let range = ranges.get_mut(&edge.lower)?;
                let new_upper = range.upper.map_or(upper, |current| current.min(upper));
                if range.upper != Some(new_upper) {
                    range.upper = Some(new_upper);
                    changed = true;
                }
            }

            if let Some(lower) = inferred_upper_lower {
                let range = ranges.get_mut(&edge.upper)?;
                let new_lower = range.lower.map_or(lower, |current| current.max(lower));
                if range.lower != Some(new_lower) {
                    range.lower = Some(new_lower);
                    changed = true;
                }
            }
        }
    }
    Some(())
}

pub(super) fn signed_i64_bitvector_constant(value: i64) -> Bitvector32Term {
    debug_assert!((i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&value));
    Bitvector32Term::Constant(value as i32 as u32)
}

pub(super) fn instantiate_range_fold_step(
    body: &Bitvector32Term,
    accumulator: Variable,
    accumulator_value: &Bitvector32Term,
    item: Variable,
    item_value: &Bitvector32Term,
) -> Bitvector32Term {
    let body = substitute_bitvector_variable(body, accumulator, accumulator_value);
    substitute_bitvector_variable(&body, item, item_value)
}

#[derive(Clone, Debug, Default)]
pub(super) struct IntegerRangeFacts {
    pub(super) lower: Option<i64>,
    pub(super) upper: Option<i64>,
    pub(super) excluded: BTreeSet<i64>,
}

pub(super) fn finite_integer_range_exhausted(
    order_facts: &[(Bitvector32Term, Bitvector32Term, bool)],
    equal_facts: &[(Bitvector32Term, Bitvector32Term)],
    disequal_facts: &[(Bitvector32Term, Bitvector32Term)],
) -> bool {
    let mut ranges: BTreeMap<Variable, IntegerRangeFacts> = BTreeMap::new();

    for (left, right, strict) in order_facts {
        match (bitvector_variable(left), signed_bitvector_constant(right)) {
            (Some(variable), Some(bound)) => {
                let upper = if *strict { bound - 1 } else { bound };
                let range = ranges.entry(variable).or_default();
                range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
            }
            _ => {}
        }
        match (signed_bitvector_constant(left), bitvector_variable(right)) {
            (Some(bound), Some(variable)) => {
                let lower = if *strict { bound + 1 } else { bound };
                let range = ranges.entry(variable).or_default();
                range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
            }
            _ => {}
        }
    }

    for (left, right) in equal_facts {
        if let Some((variable, value)) = bitvector_variable_and_constant(left, right) {
            let range = ranges.entry(variable).or_default();
            range.lower = Some(range.lower.map_or(value, |current| current.max(value)));
            range.upper = Some(range.upper.map_or(value, |current| current.min(value)));
        }
    }

    for (left, right) in disequal_facts {
        if let Some((variable, value)) = bitvector_variable_and_constant(left, right) {
            ranges.entry(variable).or_default().excluded.insert(value);
        }
    }

    ranges.into_values().any(|range| {
        let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
            return false;
        };
        if lower > upper {
            return true;
        }
        upper - lower <= 256 && (lower..=upper).all(|value| range.excluded.contains(&value))
    })
}

pub(super) fn bitvector_variable(term: &Bitvector32Term) -> Option<Variable> {
    match term {
        Bitvector32Term::Variable(variable) => Some(*variable),
        _ => None,
    }
}

pub(super) fn signed_bitvector_constant(term: &Bitvector32Term) -> Option<i64> {
    term.as_const().map(|value| i64::from(value as i32))
}

pub(super) fn signed_u32_constant(value: u32) -> Option<i64> {
    i32::try_from(value).ok().map(i64::from)
}

pub(super) fn bitvector_variable_and_constant(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(Variable, i64)> {
    bitvector_variable(left)
        .zip(signed_bitvector_constant(right))
        .or_else(|| bitvector_variable(right).zip(signed_bitvector_constant(left)))
}

pub(super) fn bitvector_equality_after_additive_cancellation(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(Bitvector32Term, Bitvector32Term)> {
    match (left, right) {
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            Some((left_addend.as_ref().clone(), right_addend.as_ref().clone()))
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_addend => {
            Some((left_addend.as_ref().clone(), right_base.as_ref().clone()))
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_base => {
            Some((left_base.as_ref().clone(), right_addend.as_ref().clone()))
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_addend => {
            Some((left_base.as_ref().clone(), right_base.as_ref().clone()))
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_base.as_ref() == right => {
            Some((left_addend.as_ref().clone(), Bitvector32Term::Constant(0)))
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_addend.as_ref() == right => {
            Some((left_base.as_ref().clone(), Bitvector32Term::Constant(0)))
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if left == right_base.as_ref() => {
            Some((Bitvector32Term::Constant(0), right_addend.as_ref().clone()))
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if left == right_addend.as_ref() => {
            Some((Bitvector32Term::Constant(0), right_base.as_ref().clone()))
        }
        _ => None,
    }
}

#[derive(Clone, Debug)]
pub(super) struct CountFoldParts {
    pub(super) start: Bitvector32Term,
    pub(super) end: Bitvector32Term,
    pub(super) accumulator: Variable,
    pub(super) item: Variable,
    pub(super) contribution: Bitvector32Term,
}

pub(super) fn collect_bitvector_add_terms(
    term: &Bitvector32Term,
    terms: &mut Vec<Bitvector32Term>,
    constant: &mut u32,
) {
    match term {
        Bitvector32Term::Add(left, right) => {
            collect_bitvector_add_terms(left, terms, constant);
            collect_bitvector_add_terms(right, terms, constant);
        }
        Bitvector32Term::Constant(value) => {
            *constant = constant.wrapping_add(*value);
        }
        term => terms.push(term.clone()),
    }
}

pub(super) fn count_fold_parts(term: &Bitvector32Term) -> Option<CountFoldParts> {
    let Bitvector32Term::RangeFold {
        start,
        end,
        initial,
        accumulator,
        item,
        body,
    } = term
    else {
        return None;
    };

    if initial.as_ref() != &Bitvector32Term::Constant(0) {
        return None;
    }

    let contribution = match body.as_ref() {
        Bitvector32Term::Add(left, right)
            if left.as_ref() == &Bitvector32Term::Variable(*accumulator) =>
        {
            right.as_ref().clone()
        }
        Bitvector32Term::Add(left, right)
            if right.as_ref() == &Bitvector32Term::Variable(*accumulator) =>
        {
            left.as_ref().clone()
        }
        _ => return None,
    };

    Some(CountFoldParts {
        start: start.as_ref().clone(),
        end: end.as_ref().clone(),
        accumulator: *accumulator,
        item: *item,
        contribution,
    })
}

pub(super) fn count_fold_split_matches(
    whole: &Bitvector32Term,
    split: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let Some(whole) = count_fold_parts(whole) else {
        return false;
    };
    let Bitvector32Term::Add(left, right) = split else {
        return false;
    };

    count_fold_split_parts_match(&whole, left.as_ref(), right.as_ref(), assumptions)
        || count_fold_split_parts_match(&whole, right.as_ref(), left.as_ref(), assumptions)
}

pub(super) fn count_fold_split_parts_match(
    whole: &CountFoldParts,
    first: &Bitvector32Term,
    second: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let (Some(first), Some(second)) = (count_fold_parts(first), count_fold_parts(second)) else {
        return false;
    };

    whole.accumulator == first.accumulator
        && whole.accumulator == second.accumulator
        && whole.item == first.item
        && whole.item == second.item
        && assumptions.bitvector_terms_proven_equal(&whole.contribution, &first.contribution)
        && assumptions.bitvector_terms_proven_equal(&whole.contribution, &second.contribution)
        && assumptions.bitvector_terms_proven_equal(&whole.start, &first.start)
        && assumptions.bitvector_terms_proven_equal(&first.end, &second.start)
        && assumptions.bitvector_terms_proven_equal(&whole.end, &second.end)
        // The split identity fold(lo,hi) = fold(lo,mid) + fold(mid,hi) only
        // holds for lo <= mid <= hi. With half-open ranges a `mid` outside
        // [lo, hi] makes one side empty and the other over-count, so without
        // these bound checks the rule proves false equalities (e.g.
        // lo=0, mid=5, hi=2 gives 2 == 3).
        && assumptions.decide(&ConditionTerm::signed_less_equal(
            first.start.clone(),
            first.end.clone(),
        )) == Some(true)
        && assumptions.decide(&ConditionTerm::signed_less_equal(
            second.start.clone(),
            second.end.clone(),
        )) == Some(true)
}

pub(super) fn range_fold_terms_alpha_equivalent(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let (
        Bitvector32Term::RangeFold {
            start: left_start,
            end: left_end,
            initial: left_initial,
            accumulator: left_accumulator,
            item: left_item,
            body: left_body,
        },
        Bitvector32Term::RangeFold {
            start: right_start,
            end: right_end,
            initial: right_initial,
            accumulator: right_accumulator,
            item: right_item,
            body: right_body,
        },
    ) = (left, right)
    else {
        return false;
    };

    assumptions.bitvector_terms_proven_equal(left_start, right_start)
        && assumptions.bitvector_terms_proven_equal(left_end, right_end)
        && assumptions.bitvector_terms_proven_equal(left_initial, right_initial)
        && bitvector_terms_alpha_equivalent(
            left_body,
            right_body,
            &[
                (*left_accumulator, *right_accumulator),
                (*left_item, *right_item),
            ],
        )
}

fn bitvector_terms_alpha_equivalent(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    variable_pairs: &[(Variable, Variable)],
) -> bool {
    match (left, right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => left == right,
        (Bitvector32Term::Variable(left), Bitvector32Term::Variable(right)) => {
            variables_alpha_equivalent(*left, *right, variable_pairs)
        }
        (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
        | (
            Bitvector32Term::Subtract(left_a, left_b),
            Bitvector32Term::Subtract(right_a, right_b),
        )
        | (
            Bitvector32Term::Multiply(left_a, left_b),
            Bitvector32Term::Multiply(right_a, right_b),
        )
        | (Bitvector32Term::Divide(left_a, left_b), Bitvector32Term::Divide(right_a, right_b))
        | (
            Bitvector32Term::Remainder(left_a, left_b),
            Bitvector32Term::Remainder(right_a, right_b),
        )
        | (
            Bitvector32Term::ShiftLeft(left_a, left_b),
            Bitvector32Term::ShiftLeft(right_a, right_b),
        )
        | (
            Bitvector32Term::ArithmeticShiftRight(left_a, left_b),
            Bitvector32Term::ArithmeticShiftRight(right_a, right_b),
        )
        | (
            Bitvector32Term::BitwiseAnd(left_a, left_b),
            Bitvector32Term::BitwiseAnd(right_a, right_b),
        )
        | (
            Bitvector32Term::BitwiseOr(left_a, left_b),
            Bitvector32Term::BitwiseOr(right_a, right_b),
        )
        | (
            Bitvector32Term::BitwiseXor(left_a, left_b),
            Bitvector32Term::BitwiseXor(right_a, right_b),
        ) => {
            bitvector_terms_alpha_equivalent(left_a, right_a, variable_pairs)
                && bitvector_terms_alpha_equivalent(left_b, right_b, variable_pairs)
        }
        (Bitvector32Term::BitwiseNot(left), Bitvector32Term::BitwiseNot(right)) => {
            bitvector_terms_alpha_equivalent(left, right, variable_pairs)
        }
        (
            Bitvector32Term::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            Bitvector32Term::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) => {
            condition_terms_alpha_equivalent(left_condition, right_condition, variable_pairs)
                && bitvector_terms_alpha_equivalent(left_then, right_then, variable_pairs)
                && bitvector_terms_alpha_equivalent(left_else, right_else, variable_pairs)
        }
        (
            Bitvector32Term::RangeFold {
                start: left_start,
                end: left_end,
                initial: left_initial,
                accumulator: left_accumulator,
                item: left_item,
                body: left_body,
            },
            Bitvector32Term::RangeFold {
                start: right_start,
                end: right_end,
                initial: right_initial,
                accumulator: right_accumulator,
                item: right_item,
                body: right_body,
            },
        ) => {
            bitvector_terms_alpha_equivalent(left_start, right_start, variable_pairs)
                && bitvector_terms_alpha_equivalent(left_end, right_end, variable_pairs)
                && bitvector_terms_alpha_equivalent(left_initial, right_initial, variable_pairs)
                && {
                    let mut nested_pairs = variable_pairs.to_vec();
                    nested_pairs.push((*left_accumulator, *right_accumulator));
                    nested_pairs.push((*left_item, *right_item));
                    bitvector_terms_alpha_equivalent(left_body, right_body, &nested_pairs)
                }
        }
        (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) => {
            left_memory == right_memory
                && pointers_alpha_equivalent(left_pointer, right_pointer, variable_pairs)
        }
        _ => false,
    }
}

fn condition_terms_alpha_equivalent(
    left: &ConditionTerm,
    right: &ConditionTerm,
    variable_pairs: &[(Variable, Variable)],
) -> bool {
    match (left, right) {
        (ConditionTerm::Constant(left), ConditionTerm::Constant(right)) => left == right,
        (ConditionTerm::Variable(left), ConditionTerm::Variable(right)) => {
            variables_alpha_equivalent(*left, *right, variable_pairs)
        }
        (
            ConditionTerm::Bitvector32SignedLessThan(left_a, left_b),
            ConditionTerm::Bitvector32SignedLessThan(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedLessEqual(left_a, left_b),
            ConditionTerm::Bitvector32SignedLessEqual(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterThan(left_a, left_b),
            ConditionTerm::Bitvector32SignedGreaterThan(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterEqual(left_a, left_b),
            ConditionTerm::Bitvector32SignedGreaterEqual(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32Equal(left_a, left_b),
            ConditionTerm::Bitvector32Equal(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedAddOverflows(left_a, left_b),
            ConditionTerm::Bitvector32SignedAddOverflows(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedSubtractOverflows(left_a, left_b),
            ConditionTerm::Bitvector32SignedSubtractOverflows(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left_a, left_b),
            ConditionTerm::Bitvector32SignedMultiplyOverflows(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedDivideOverflows(left_a, left_b),
            ConditionTerm::Bitvector32SignedDivideOverflows(right_a, right_b),
        )
        | (
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left_a, left_b),
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(right_a, right_b),
        ) => {
            bitvector_terms_alpha_equivalent(left_a, right_a, variable_pairs)
                && bitvector_terms_alpha_equivalent(left_b, right_b, variable_pairs)
        }
        (
            ConditionTerm::PointerOffsetEqual(left_a, left_b),
            ConditionTerm::PointerOffsetEqual(right_a, right_b),
        ) => {
            pointer_offsets_alpha_equivalent(left_a, right_a, variable_pairs)
                && pointer_offsets_alpha_equivalent(left_b, right_b, variable_pairs)
        }
        (
            ConditionTerm::PointerEqual(left_a, left_b),
            ConditionTerm::PointerEqual(right_a, right_b),
        ) => {
            pointers_alpha_equivalent(left_a, right_a, variable_pairs)
                && pointers_alpha_equivalent(left_b, right_b, variable_pairs)
        }
        _ => false,
    }
}

fn pointers_alpha_equivalent(
    left: &Pointer,
    right: &Pointer,
    variable_pairs: &[(Variable, Variable)],
) -> bool {
    left.block == right.block
        && pointer_offsets_alpha_equivalent(&left.offset, &right.offset, variable_pairs)
}

fn pointer_offsets_alpha_equivalent(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    variable_pairs: &[(Variable, Variable)],
) -> bool {
    match (left, right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => left == right,
        (PointerOffsetTerm::Variable(left), PointerOffsetTerm::Variable(right)) => {
            variables_alpha_equivalent(*left, *right, variable_pairs)
        }
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_alpha_equivalent(left_a, right_a, variable_pairs)
                && pointer_offsets_alpha_equivalent(left_b, right_b, variable_pairs)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && bitvector_terms_alpha_equivalent(left_value, right_value, variable_pairs)
        }
        _ => false,
    }
}

fn variables_alpha_equivalent(
    left: Variable,
    right: Variable,
    variable_pairs: &[(Variable, Variable)],
) -> bool {
    left == right
        || variable_pairs
            .iter()
            .any(|(left_pair, right_pair)| left == *left_pair && right == *right_pair)
}

pub(super) fn bitvector_same_base_nonzero_const_offset(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    if let Some((left_base, left_addend)) = left.add_const_parts() {
        if &left_base == right {
            return left_addend != 0;
        }
        if let Some((right_base, right_addend)) = right.add_const_parts() {
            return left_base == right_base && left_addend != right_addend;
        }
    }

    if let Some((right_base, right_addend)) = right.add_const_parts() {
        return &right_base == left && right_addend != 0;
    }

    false
}

pub(super) fn collect_proposition_bitvector_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        Proposition::Equal(left, right) => {
            collect_term_bitvector_variables(left, variables);
            collect_term_bitvector_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_variables(condition, variables);
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bitvector_variables(argument, variables);
            }
        }
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(expression, variables);
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CConditionEvaluates {
            state, condition, ..
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(condition, variables);
        }
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_statement_bitvector_variables(statement, variables);
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionExecutes {
            state,
            arguments,
            function,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => {
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_specification_bitvector_variables(specification, variables);
        }
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CMemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(base, variables);
            collect_bitvector_variables(bytes, variables);
        }
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => {
            collect_pointer_bitvector_variables(left_base, variables);
            collect_bitvector_variables(left_start, variables);
            collect_bitvector_variables(left_end, variables);
            collect_pointer_bitvector_variables(right_base, variables);
            collect_bitvector_variables(right_start, variables);
            collect_bitvector_variables(right_end, variables);
        }
        Proposition::CResourceSeparate { left, right } => {
            collect_c_resource_bitvector_variables(left, variables);
            collect_c_resource_bitvector_variables(right, variables);
        }
        Proposition::CResourceContains { parent, child } => {
            collect_c_resource_bitvector_variables(parent, variables);
            collect_c_resource_bitvector_variables(child, variables);
        }
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for pointer in pointers {
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for range in mutable_ranges {
                collect_c_memory_range_bitvector_variables(range, variables);
            }
        }
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            collect_c_statement_bitvector_variables(body, variables);
            for proposition in preserved {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            collect_proposition_bitvector_variables(postcondition, variables);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_variables(left, variables);
            collect_proposition_bitvector_variables(right, variables);
        }
        Proposition::Not(body) => collect_proposition_bitvector_variables(body, variables),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            collect_proposition_bitvector_variables(body, variables);
            variables.remove(var);
        }
    }
}

pub(super) fn collect_term_bitvector_variables(term: &Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Term::Condition(condition) => collect_condition_bitvector_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_variables(bits, variables),
        Term::PointerOffset(offset) => {
            collect_pointer_offset_bitvector_variables(offset, variables)
        }
        Term::CValue(value) => collect_c_value_bitvector_variables(value, variables),
        Term::CExpressionOutcome(outcome) => {
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Term::CStatementOutcome(outcome) => {
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Term::CFunctionOutcome(outcome) => {
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Term::CMemory(memory) => collect_memory_bitvector_variables(memory, variables),
        Term::CState(state) => collect_c_state_bitvector_variables(state, variables),
    }
}

pub(super) fn collect_c_expression_bitvector_variables(
    expression: &CExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        CExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        CExpression::Variable(_) => {}
        CExpression::AddressOf(body) | CExpression::Not(body) | CExpression::Load(body) => {
            collect_c_expression_bitvector_variables(body, variables);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_c_expression_bitvector_variables(left, variables);
            collect_c_expression_bitvector_variables(right, variables);
        }
        CExpression::BitwiseNot(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
    }
}

pub(super) fn collect_c_statement_bitvector_variables(
    statement: &CStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        CStatement::Declare { .. } => {}
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        } => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        CStatement::CallAssign { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
        CStatement::Seq(first, second) => {
            collect_c_statement_bitvector_variables(first, variables);
            collect_c_statement_bitvector_variables(second, variables);
        }
        CStatement::Store { pointer, value } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::TypedStore { pointer, value, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            collect_c_statement_bitvector_variables(then_branch, variables);
            collect_c_statement_bitvector_variables(else_branch, variables);
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_spec_proposition_bitvector_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bitvector_variables(check.effect(), variables);
            }
            collect_c_statement_bitvector_variables(body, variables);
        }
    }
}

pub(super) fn collect_spec_memory_bitvector_variables(
    memory: &SpecMemory,
    variables: &mut BTreeSet<Variable>,
) {
    match memory {
        SpecMemory::Current | SpecMemory::FunctionEntry => {}
        SpecMemory::LoopEntry => {}
        SpecMemory::Fixed(memory) => collect_memory_bitvector_variables(memory, variables),
    }
}

pub(super) fn collect_spec_expression_bitvector_variables(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        SpecExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        SpecExpression::CExpression(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            collect_spec_expression_bitvector_variables(left, variables);
            collect_spec_expression_bitvector_variables(right, variables);
        }
        SpecExpression::BitwiseNot(expression) => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_spec_proposition_bitvector_variables(condition, variables);
            collect_spec_expression_bitvector_variables(then_branch, variables);
            collect_spec_expression_bitvector_variables(else_branch, variables);
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator: _,
            item: _,
            body,
        } => {
            collect_spec_expression_bitvector_variables(start, variables);
            collect_spec_expression_bitvector_variables(end, variables);
            collect_spec_expression_bitvector_variables(initial, variables);
            collect_spec_expression_bitvector_variables(body, variables);
        }
        SpecExpression::Let {
            name: _,
            value,
            body,
        } => {
            collect_spec_expression_bitvector_variables(value, variables);
            collect_spec_expression_bitvector_variables(body, variables);
        }
        SpecExpression::LoopEntrySnapshot(expression) => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width: _,
        } => {
            collect_spec_expression_bitvector_variables(pointer, variables);
            collect_spec_expression_bitvector_variables(elements, variables);
        }
        SpecExpression::MemoryLoad {
            memory, pointer, ..
        } => {
            collect_spec_memory_bitvector_variables(memory, variables);
            collect_spec_expression_bitvector_variables(pointer, variables);
        }
    }
}

pub(super) fn collect_spec_proposition_bitvector_variables(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        SpecProposition::Comparison { left, right, .. } => {
            collect_spec_expression_bitvector_variables(left, variables);
            collect_spec_expression_bitvector_variables(right, variables);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            collect_spec_proposition_bitvector_variables(left, variables);
            collect_spec_proposition_bitvector_variables(right, variables);
        }
        SpecProposition::Not(body) => {
            collect_spec_proposition_bitvector_variables(body, variables);
        }
        SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. } => {
            collect_spec_proposition_bitvector_variables(body, variables);
            variables.remove(variable);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_spec_expression_bitvector_variables(argument, variables);
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            collect_spec_resource_bitvector_variables(left, variables);
            collect_spec_resource_bitvector_variables(right, variables);
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            collect_spec_memory_bitvector_variables(memory, variables);
            collect_spec_expression_bitvector_variables(base, variables);
            collect_spec_expression_bitvector_variables(start, variables);
            collect_spec_expression_bitvector_variables(end, variables);
        }
    }
}

fn collect_spec_resource_bitvector_variables(
    resource: &SpecResource,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        SpecResource::Memory { base, start, end } => {
            collect_spec_expression_bitvector_variables(base, variables);
            collect_spec_expression_bitvector_variables(start, variables);
            collect_spec_expression_bitvector_variables(end, variables);
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                collect_spec_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(super) fn collect_loop_effect_bitvector_variables(
    effect: &CLoopEffect,
    variables: &mut BTreeSet<Variable>,
) {
    match effect {
        CLoopEffect::Immutable => {}
        CLoopEffect::Mutable(segments) => {
            for segment in segments {
                collect_c_expression_bitvector_variables(&segment.base, variables);
                collect_c_expression_bitvector_variables(&segment.start, variables);
                collect_c_expression_bitvector_variables(&segment.end, variables);
            }
        }
    }
}

pub(super) fn collect_c_expression_outcome_bitvector_variables(
    outcome: &CExpressionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    if let CExpressionOutcome::Value(value) = outcome {
        collect_c_value_bitvector_variables(value, variables);
    }
}

pub(super) fn collect_c_statement_outcome_bitvector_variables(
    outcome: &CStatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CStatementOutcome::Normal(state) => collect_c_state_bitvector_variables(state, variables),
        CStatementOutcome::Return { value, state } => {
            collect_c_value_bitvector_variables(value, variables);
            collect_c_state_bitvector_variables(state, variables);
        }
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => {}
    }
}

pub(super) fn collect_c_function_outcome_bitvector_variables(
    outcome: &CFunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CFunctionOutcome::Return { value, state } => {
            collect_c_value_bitvector_variables(value, variables);
            collect_c_state_bitvector_variables(state, variables);
        }
        CFunctionOutcome::UndefinedBehavior(_) | CFunctionOutcome::RuntimeError(_) => {}
    }
}

pub(super) fn collect_c_state_bitvector_variables(
    state: &CState,
    variables: &mut BTreeSet<Variable>,
) {
    for binding in state.locals.bindings.values() {
        match binding {
            CLocalBinding::Object { value, .. } => {
                collect_c_value_bitvector_variables(value, variables)
            }
            CLocalBinding::ArrayObject { .. } => {}
        }
    }
    collect_memory_bitvector_variables(&state.memory, variables);
    collect_resource_context_bitvector_variables(&state.resources, variables);
}

pub(super) fn collect_resource_context_bitvector_variables(
    resources: &ResourceContext,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in resources.facts() {
        collect_resource_bitvector_variables(resource, variables);
    }
}

pub(super) fn collect_resource_bitvector_variables(
    resource: &CResourceFact,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_resource_bitvector_variables(resource.resource(), variables);
}

pub(super) fn collect_c_resource_bitvector_variables(
    resource: &CResource,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResource::Memory(range) => collect_c_memory_range_bitvector_variables(range, variables),
        CResource::Composite { arguments, .. } | CResource::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_value_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(super) fn collect_c_function_bitvector_variables(
    function: &CFunction,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in function.resource_requires() {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for resource in function.resource_ensures() {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for proposition in function.contract_requires() {
        collect_spec_proposition_bitvector_variables(proposition, variables);
    }
    for proposition in function.contract_ensures() {
        collect_spec_proposition_bitvector_variables(proposition, variables);
    }
    for segment in function.contract_mutable() {
        collect_c_expression_bitvector_variables(&segment.base, variables);
        collect_c_expression_bitvector_variables(&segment.start, variables);
        collect_c_expression_bitvector_variables(&segment.end, variables);
    }
    collect_c_statement_bitvector_variables(function.body(), variables);
}

pub(super) fn collect_resource_spec_bitvector_variables(
    resource: &CResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResourceSpec::Read(segment) => {
            collect_c_expression_bitvector_variables(&segment.base, variables);
            collect_c_expression_bitvector_variables(&segment.start, variables);
            collect_c_expression_bitvector_variables(&segment.end, variables);
        }
        CResourceSpec::Write(segment) => {
            collect_c_expression_bitvector_variables(&segment.base, variables);
            collect_c_expression_bitvector_variables(&segment.start, variables);
            collect_c_expression_bitvector_variables(&segment.end, variables);
        }
        CResourceSpec::Composite { arguments, .. } | CResourceSpec::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(super) fn collect_c_function_specification_bitvector_variables(
    specification: &CFunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_state_bitvector_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_c_expression_bitvector_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bitvector_variables(requirement, variables);
    }
    collect_c_function_outcome_bitvector_variables(specification.outcome(), variables);
}

pub(super) fn collect_c_memory_range_bitvector_variables(
    range: &CMemoryRange,
    variables: &mut BTreeSet<Variable>,
) {
    collect_pointer_bitvector_variables(&range.base, variables);
    collect_bitvector_variables(&range.start, variables);
    collect_bitvector_variables(&range.end, variables);
}

pub(super) fn resource_context_has_read(
    resources: &ResourceContext,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    resources.permits_memory_read(pointer, byte_width, assumptions)
}

pub(super) fn resource_context_has_write(
    resources: &ResourceContext,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    resources.permits_memory_write(pointer, byte_width, assumptions)
}

pub(super) fn collect_condition_bitvector_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_bitvector_variables(&left.offset, variables);
            collect_pointer_offset_bitvector_variables(&right.offset, variables);
        }
    }
}

pub(super) fn collect_bitvector_variables(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
) {
    match term {
        Bitvector32Term::Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            variables.insert(*variable);
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        Bitvector32Term::BitwiseNot(value) => {
            collect_bitvector_variables(value, variables);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_variables(condition, variables);
            collect_bitvector_variables(then_term, variables);
            collect_bitvector_variables(else_term, variables);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_variables(start, variables);
            collect_bitvector_variables(end, variables);
            collect_bitvector_variables(initial, variables);
            collect_bitvector_variables(body, variables);
            variables.remove(accumulator);
            variables.remove(item);
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
    }
}

pub(super) fn collect_pointer_offset_bitvector_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            collect_bitvector_variables(value, variables);
        }
    }
}

pub(super) fn collect_pointer_bitvector_variables(
    pointer: &Pointer,
    variables: &mut BTreeSet<Variable>,
) {
    collect_pointer_offset_bitvector_variables(&pointer.offset, variables);
}

pub(super) fn collect_memory_bitvector_variables(
    memory: &CMemory,
    variables: &mut BTreeSet<Variable>,
) {
    for (pointer, value) in &memory.cells {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
}

pub(super) fn collect_c_value_bitvector_variables(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        CValue::Int32(bits) | CValue::UInt8(bits) => collect_bitvector_variables(bits, variables),
        CValue::Pointer(pointer) => collect_pointer_bitvector_variables(pointer, variables),
    }
}

pub(super) fn substitute_bitvector_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Bitvector32Term,
) -> Proposition {
    match proposition {
        Proposition::Equal(left, right) => Proposition::Equal(
            substitute_bitvector_variable_in_term(left, from, to),
            substitute_bitvector_variable_in_term(right, from, to),
        ),
        Proposition::ConditionIs(condition, value) => Proposition::ConditionIs(
            substitute_bitvector_variable_in_condition(condition, from, to),
            *value,
        ),
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_term(argument, from, to))
                .collect(),
        },
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::CExpressionEvaluates {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
            outcome: substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => Proposition::CStatementExecutes {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            statement: substitute_bitvector_variable_in_c_statement(statement, from, to),
            outcome: substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        },
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::CFunctionExecutes {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            outcome: substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        },
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionSatisfiesSpecification {
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            specification: substitute_bitvector_variable_in_c_function_specification(
                specification,
                from,
                to,
            ),
        },
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::CMemoryLoads {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
            outcome: substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::CMemoryCanStore {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
            byte_width: *byte_width,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryLoadable {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            base: substitute_bitvector_variable_in_pointer(base, from, to),
            bytes: substitute_bitvector_variable(bytes, from, to),
        },
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => Proposition::CMemoryDisjoint {
            left_base: substitute_bitvector_variable_in_pointer(left_base, from, to),
            left_start: substitute_bitvector_variable(left_start, from, to),
            left_end: substitute_bitvector_variable(left_end, from, to),
            right_base: substitute_bitvector_variable_in_pointer(right_base, from, to),
            right_start: substitute_bitvector_variable(right_start, from, to),
            right_end: substitute_bitvector_variable(right_end, from, to),
        },
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: substitute_bitvector_variable_in_c_resource(left, from, to),
            right: substitute_bitvector_variable_in_c_resource(right, from, to),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: substitute_bitvector_variable_in_c_resource(parent, from, to),
            child: substitute_bitvector_variable_in_c_resource(child, from, to),
        },
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => Proposition::CMemoryMutatesOnly {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            pointers: pointers
                .iter()
                .map(|pointer| substitute_bitvector_variable_in_pointer(pointer, from, to))
                .collect(),
        },
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::CMemoryEffectSummary {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            mutable_ranges: mutable_ranges
                .iter()
                .map(|range| substitute_bitvector_variable_in_c_memory_range(range, from, to))
                .collect(),
        },
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => Proposition::CWhileInvariantRule {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            body: substitute_bitvector_variable_in_c_statement(body, from, to),
            preserved: preserved
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            postcondition: Box::new(substitute_bitvector_variable_in_proposition(
                postcondition,
                from,
                to,
            )),
        },
        Proposition::And(left, right) => Proposition::And(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(
            substitute_bitvector_variable_in_proposition(body, from, to),
        )),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::ForAll { var, sort, body } if *var != from => Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(substitute_bitvector_variable_in_proposition(body, from, to)),
        },
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } if *var != from => Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(substitute_bitvector_variable_in_proposition(body, from, to)),
        },
        proposition => proposition.clone(),
    }
}

pub(super) fn substitute_bitvector_variable_in_term(
    term: &Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_bitvector_variable_in_condition(
            condition, from, to,
        )),
        Term::Bitvector32(bits) => Term::Bitvector32(substitute_bitvector_variable(bits, from, to)),
        Term::PointerOffset(offset) => Term::PointerOffset(
            substitute_bitvector_variable_in_pointer_offset(offset, from, to),
        ),
        Term::CValue(value) => {
            Term::CValue(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        Term::CExpressionOutcome(outcome) => Term::CExpressionOutcome(
            substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        ),
        Term::CStatementOutcome(outcome) => Term::CStatementOutcome(
            substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        ),
        Term::CFunctionOutcome(outcome) => Term::CFunctionOutcome(
            substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        ),
        Term::CMemory(memory) => {
            Term::CMemory(substitute_bitvector_variable_in_memory(memory, from, to))
        }
        Term::CState(state) => {
            Term::CState(substitute_bitvector_variable_in_c_state(state, from, to))
        }
    }
}

pub(super) fn substitute_bitvector_variable_in_c_expression(
    expression: &CExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpression {
    match expression {
        CExpression::Value(value) => {
            CExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpression::Variable(name) => CExpression::Variable(name.clone()),
        CExpression::AddressOf(body) => CExpression::AddressOf(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::Not(body) => CExpression::Not(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::Load(body) => CExpression::Load(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
        },
        CExpression::LessThan(left, right) => CExpression::LessThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::LessEqual(left, right) => CExpression::LessEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterThan(left, right) => CExpression::GreaterThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterEqual(left, right) => CExpression::GreaterEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Equal(left, right) => CExpression::Equal(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::NotEqual(left, right) => CExpression::NotEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::And(left, right) => CExpression::And(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Or(left, right) => CExpression::Or(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Add(left, right) => CExpression::Add(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Subtract(left, right) => CExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Multiply(left, right) => CExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Divide(left, right) => CExpression::Divide(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Remainder(left, right) => CExpression::Remainder(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::ShiftLeft(left, right) => CExpression::ShiftLeft(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::ShiftRight(left, right) => CExpression::ShiftRight(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseAnd(left, right) => CExpression::BitwiseAnd(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseOr(left, right) => CExpression::BitwiseOr(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseXor(left, right) => CExpression::BitwiseXor(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseNot(expression) => CExpression::BitwiseNot(Box::new(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        )),
        CExpression::Index(left, right) => CExpression::Index(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_statement(
    statement: &CStatement,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatement {
    match statement {
        CStatement::Declare { name, c_type } => CStatement::Declare {
            name: name.clone(),
            c_type: *c_type,
        },
        CStatement::Assign { name, expression } => CStatement::Assign {
            name: name.clone(),
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
        },
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => CStatement::CallAssign {
            target: target.clone(),
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        CStatement::Assert { condition, label } => CStatement::Assert {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            label: label.clone(),
        },
        CStatement::Seq(first, second) => CStatement::Seq(
            Box::new(substitute_bitvector_variable_in_c_statement(
                first, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_statement(
                second, from, to,
            )),
        ),
        CStatement::Return(expression) => CStatement::Return(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        ),
        CStatement::Store { pointer, value } => CStatement::Store {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
            value: substitute_bitvector_variable_in_c_expression(value, from, to),
        },
        CStatement::TypedStore {
            pointer,
            value,
            value_type,
        } => CStatement::TypedStore {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
            value: substitute_bitvector_variable_in_c_expression(value, from, to),
            value_type: *value_type,
        },
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => CStatement::If {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            then_branch: Box::new(substitute_bitvector_variable_in_c_statement(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_c_statement(
                else_branch,
                from,
                to,
            )),
        },
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } => CStatement::While {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            invariant_checks: invariant_checks
                .iter()
                .map(|check| CLoopInvariantCheck {
                    proposition: substitute_bitvector_variable_in_spec_proposition(
                        check.proposition(),
                        from,
                        to,
                    ),
                    entry_context: check.entry_context.clone(),
                    preservation_context: check.preservation_context.clone(),
                })
                .collect(),
            effect_checks: effect_checks
                .iter()
                .map(|check| CLoopEffectCheck {
                    effect: substitute_bitvector_variable_in_loop_effect(check.effect(), from, to),
                    span: check.span,
                    context: check.context.clone(),
                })
                .collect(),
            body: Box::new(substitute_bitvector_variable_in_c_statement(body, from, to)),
        },
    }
}

pub(super) fn substitute_bitvector_variable_in_spec_memory(
    memory: &SpecMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecMemory {
    match memory {
        SpecMemory::Current => SpecMemory::Current,
        SpecMemory::FunctionEntry => SpecMemory::FunctionEntry,
        SpecMemory::LoopEntry => SpecMemory::LoopEntry,
        SpecMemory::Fixed(memory) => {
            SpecMemory::Fixed(substitute_bitvector_variable_in_memory(memory, from, to))
        }
    }
}

pub(super) fn substitute_bitvector_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecExpression {
    match expression {
        SpecExpression::Value(value) => {
            SpecExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        SpecExpression::CExpression(expression) => SpecExpression::CExpression(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        ),
        SpecExpression::Add(left, right) => SpecExpression::Add(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Subtract(left, right) => SpecExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Multiply(left, right) => SpecExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Divide(left, right) => SpecExpression::Divide(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Remainder(left, right) => SpecExpression::Remainder(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::ShiftLeft(left, right) => SpecExpression::ShiftLeft(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::ShiftRight(left, right) => SpecExpression::ShiftRight(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseAnd(left, right) => SpecExpression::BitwiseAnd(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseOr(left, right) => SpecExpression::BitwiseOr(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseXor(left, right) => SpecExpression::BitwiseXor(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseNot(expression) => SpecExpression::BitwiseNot(Box::new(
            substitute_bitvector_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => SpecExpression::If {
            condition: Box::new(substitute_bitvector_variable_in_spec_proposition(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_bitvector_variable_in_spec_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_spec_expression(
                else_branch,
                from,
                to,
            )),
        },
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => SpecExpression::RangeFold {
            start: Box::new(substitute_bitvector_variable_in_spec_expression(
                start, from, to,
            )),
            end: Box::new(substitute_bitvector_variable_in_spec_expression(
                end, from, to,
            )),
            initial: Box::new(substitute_bitvector_variable_in_spec_expression(
                initial, from, to,
            )),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(substitute_bitvector_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::Let { name, value, body } => SpecExpression::Let {
            name: name.clone(),
            value: Box::new(substitute_bitvector_variable_in_spec_expression(
                value, from, to,
            )),
            body: Box::new(substitute_bitvector_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::LoopEntrySnapshot(expression) => {
            SpecExpression::LoopEntrySnapshot(Box::new(
                substitute_bitvector_variable_in_spec_expression(expression, from, to),
            ))
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => SpecExpression::PointerOffset {
            pointer: Box::new(substitute_bitvector_variable_in_spec_expression(
                pointer, from, to,
            )),
            elements: Box::new(substitute_bitvector_variable_in_spec_expression(
                elements, from, to,
            )),
            byte_width: *byte_width,
        },
        SpecExpression::MemoryLoad {
            memory,
            pointer,
            value_type,
        } => SpecExpression::MemoryLoad {
            memory: substitute_bitvector_variable_in_spec_memory(memory, from, to),
            pointer: Box::new(substitute_bitvector_variable_in_spec_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
        },
    }
}

pub(super) fn substitute_bitvector_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecProposition {
    match proposition {
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => SpecProposition::Comparison {
            left: substitute_bitvector_variable_in_spec_expression(left, from, to),
            operator: *operator,
            right: substitute_bitvector_variable_in_spec_expression(right, from, to),
        },
        SpecProposition::And(left, right) => SpecProposition::And(
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Or(left, right) => SpecProposition::Or(
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Not(body) => SpecProposition::Not(Box::new(
            substitute_bitvector_variable_in_spec_proposition(body, from, to),
        )),
        SpecProposition::Implies(left, right) => SpecProposition::Implies(
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } if *variable != from => SpecProposition::ForAllInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } if *variable != from => SpecProposition::ExistsInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::Predicate { name, arguments } => SpecProposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_spec_expression(argument, from, to)
                })
                .collect(),
        },
        SpecProposition::ResourceSeparate { left, right } => SpecProposition::ResourceSeparate {
            left: substitute_bitvector_variable_in_spec_resource(left, from, to),
            right: substitute_bitvector_variable_in_spec_resource(right, from, to),
        },
        SpecProposition::ResourceContains { parent, child } => SpecProposition::ResourceContains {
            parent: substitute_bitvector_variable_in_spec_resource(parent, from, to),
            child: substitute_bitvector_variable_in_spec_resource(child, from, to),
        },
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            element_width,
        } => SpecProposition::MemoryLoadable {
            memory: substitute_bitvector_variable_in_spec_memory(memory, from, to),
            base: substitute_bitvector_variable_in_spec_expression(base, from, to),
            start: substitute_bitvector_variable_in_spec_expression(start, from, to),
            end: substitute_bitvector_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        proposition => proposition.clone(),
    }
}

fn substitute_bitvector_variable_in_spec_resource(
    resource: &SpecResource,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecResource {
    match resource {
        SpecResource::Memory { base, start, end } => SpecResource::Memory {
            base: substitute_bitvector_variable_in_spec_expression(base, from, to),
            start: substitute_bitvector_variable_in_spec_expression(start, from, to),
            end: substitute_bitvector_variable_in_spec_expression(end, from, to),
        },
        SpecResource::Composite { name, arguments } => SpecResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_spec_expression(argument, from, to)
                })
                .collect(),
        },
        SpecResource::Token { name, arguments } => SpecResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_spec_expression(argument, from, to)
                })
                .collect(),
        },
    }
}

pub(super) fn substitute_bitvector_variable_in_loop_effect(
    effect: &CLoopEffect,
    from: Variable,
    to: &Bitvector32Term,
) -> CLoopEffect {
    match effect {
        CLoopEffect::Immutable => CLoopEffect::Immutable,
        CLoopEffect::Mutable(segments) => CLoopEffect::Mutable(
            segments
                .iter()
                .map(|segment| CMemorySegment {
                    base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
                    start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
                    end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
                })
                .collect(),
        ),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_expression_outcome(
    outcome: &CExpressionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpressionOutcome {
    match outcome {
        CExpressionOutcome::Value(value) => {
            CExpressionOutcome::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpressionOutcome::UndefinedBehavior(kind) => {
            CExpressionOutcome::UndefinedBehavior(kind.clone())
        }
        CExpressionOutcome::RuntimeError(kind) => CExpressionOutcome::RuntimeError(kind.clone()),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_statement_outcome(
    outcome: &CStatementOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatementOutcome {
    match outcome {
        CStatementOutcome::Normal(state) => {
            CStatementOutcome::Normal(substitute_bitvector_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Return { value, state } => CStatementOutcome::Return {
            value: substitute_bitvector_variable_in_c_value(value, from, to),
            state: substitute_bitvector_variable_in_c_state(state, from, to),
        },
        CStatementOutcome::UndefinedBehavior(kind) => {
            CStatementOutcome::UndefinedBehavior(kind.clone())
        }
        CStatementOutcome::RuntimeError(kind) => CStatementOutcome::RuntimeError(kind.clone()),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_function_outcome(
    outcome: &CFunctionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionOutcome {
    match outcome {
        CFunctionOutcome::Return { value, state } => CFunctionOutcome::Return {
            value: substitute_bitvector_variable_in_c_value(value, from, to),
            state: substitute_bitvector_variable_in_c_state(state, from, to),
        },
        CFunctionOutcome::UndefinedBehavior(kind) => {
            CFunctionOutcome::UndefinedBehavior(kind.clone())
        }
        CFunctionOutcome::RuntimeError(kind) => CFunctionOutcome::RuntimeError(kind.clone()),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_state(
    state: &CState,
    from: Variable,
    to: &Bitvector32Term,
) -> CState {
    let bindings = state
        .locals
        .bindings
        .iter()
        .map(|(name, binding)| {
            let binding = match binding {
                CLocalBinding::Object { value, c_type } => CLocalBinding::Object {
                    value: substitute_bitvector_variable_in_c_value(value, from, to),
                    c_type: *c_type,
                },
                CLocalBinding::ArrayObject {
                    element_type,
                    length,
                } => CLocalBinding::ArrayObject {
                    element_type: *element_type,
                    length: *length,
                },
            };
            (name.clone(), binding)
        })
        .collect();
    CState {
        locals: CLocalEnvironment { bindings },
        memory: substitute_bitvector_variable_in_memory(&state.memory, from, to),
        resources: substitute_bitvector_variable_in_resource_context(&state.resources, from, to),
    }
}

pub(super) fn substitute_bitvector_variable_in_resource_context(
    resources: &ResourceContext,
    from: Variable,
    to: &Bitvector32Term,
) -> ResourceContext {
    ResourceContext {
        facts: resources
            .facts()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource(resource, from, to))
            .collect(),
    }
}

pub(super) fn substitute_bitvector_variable_in_resource(
    resource: &CResourceFact,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceFact {
    match resource {
        CResourceFact::Own(resource) => CResourceFact::Own(
            substitute_bitvector_variable_in_c_resource(resource, from, to),
        ),
        CResourceFact::View(resource) => CResourceFact::View(
            substitute_bitvector_variable_in_c_resource(resource, from, to),
        ),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_resource(
    resource: &CResource,
    from: Variable,
    to: &Bitvector32Term,
) -> CResource {
    match resource {
        CResource::Memory(range) => CResource::Memory(
            substitute_bitvector_variable_in_c_memory_range(range, from, to),
        ),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_value(argument, from, to))
                .collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_value(argument, from, to))
                .collect(),
        },
    }
}

pub(super) fn substitute_bitvector_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunction {
    CFunction {
        return_type: function.return_type,
        name: function.name.clone(),
        parameters: function.parameters.clone(),
        body: substitute_bitvector_variable_in_c_statement(function.body(), from, to),
        source_body: substitute_bitvector_variable_in_c_statement(function.source_body(), from, to),
        resource_requires: function
            .resource_requires()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
            .collect(),
        resource_ensures: function
            .resource_ensures()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
            .collect(),
        contract_requires: function
            .contract_requires
            .iter()
            .map(|proposition| {
                substitute_bitvector_variable_in_spec_proposition(proposition, from, to)
            })
            .collect(),
        contract_ensures: function
            .contract_ensures
            .iter()
            .map(|proposition| {
                substitute_bitvector_variable_in_spec_proposition(proposition, from, to)
            })
            .collect(),
        contract_mutable: function
            .contract_mutable
            .iter()
            .map(|segment| CMemorySegment {
                base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
                start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
                end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
            })
            .collect(),
        contract_claims: function.contract_claims.clone(),
        opaque_contract_supported: function.opaque_contract_supported,
    }
}

pub(super) fn substitute_bitvector_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceSpec {
    match resource {
        CResourceSpec::Read(segment) => CResourceSpec::Read(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
        }),
        CResourceSpec::Write(segment) => CResourceSpec::Write(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
        }),
        CResourceSpec::Composite {
            access,
            name,
            arguments,
            parameter_types,
        } => CResourceSpec::Composite {
            access: *access,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
        CResourceSpec::Token {
            access,
            name,
            arguments,
            parameter_types,
        } => CResourceSpec::Token {
            access: *access,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
    }
}

pub(super) fn substitute_bitvector_variable_in_c_function_specification(
    specification: &CFunctionSpecification,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionSpecification {
    CFunctionSpecification {
        state: substitute_bitvector_variable_in_c_state(specification.state(), from, to),
        arguments: specification
            .arguments()
            .iter()
            .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
            .collect(),
        requires: specification
            .requires()
            .iter()
            .map(|requirement| substitute_bitvector_variable_in_proposition(requirement, from, to))
            .collect(),
        outcome: substitute_bitvector_variable_in_c_function_outcome(
            specification.outcome(),
            from,
            to,
        ),
    }
}

pub(super) fn substitute_bitvector_variable_in_c_memory_range(
    range: &CMemoryRange,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemoryRange {
    CMemoryRange {
        base: substitute_bitvector_variable_in_pointer(&range.base, from, to),
        start: substitute_bitvector_variable(&range.start, from, to),
        end: substitute_bitvector_variable(&range.end, from, to),
    }
}

pub(super) fn substitute_bitvector_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
        ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => ConditionTerm::signed_less_than(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => ConditionTerm::signed_less_equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::signed_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::signed_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            ConditionTerm::signed_add_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            ConditionTerm::signed_subtract_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            ConditionTerm::signed_multiply_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            ConditionTerm::signed_divide_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            ConditionTerm::signed_shift_left_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            substitute_bitvector_variable_in_pointer(left, from, to),
            substitute_bitvector_variable_in_pointer(right, from, to),
        ),
    }
}

pub(super) fn substitute_bitvector_variable(
    term: &Bitvector32Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
        Bitvector32Term::Variable(variable) if *variable == from => to.clone(),
        Bitvector32Term::Variable(variable) => Bitvector32Term::Variable(*variable),
        Bitvector32Term::Add(left, right) => Bitvector32Term::add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Divide(left, right) => Bitvector32Term::divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Remainder(left, right) => Bitvector32Term::remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::ShiftLeft(left, right) => Bitvector32Term::shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            Bitvector32Term::arithmetic_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseOr(left, right) => Bitvector32Term::bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseXor(left, right) => Bitvector32Term::bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseNot(value) => {
            Bitvector32Term::bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::if_then_else(
            substitute_bitvector_variable_in_condition(condition, from, to),
            substitute_bitvector_variable(then_term, from, to),
            substitute_bitvector_variable(else_term, from, to),
        ),
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let body = if *accumulator == from || *item == from {
                body.as_ref().clone()
            } else {
                substitute_bitvector_variable(body, from, to)
            };
            Bitvector32Term::range_fold(
                substitute_bitvector_variable(start, from, to),
                substitute_bitvector_variable(end, from, to),
                substitute_bitvector_variable(initial, from, to),
                *accumulator,
                *item,
                body,
            )
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => Bitvector32Term::MemoryLoad(
            Box::new(substitute_bitvector_variable_in_memory(memory, from, to)),
            Box::new(substitute_bitvector_variable_in_pointer(pointer, from, to)),
        ),
    }
}

pub(super) fn substitute_bitvector_variable_in_pointer_offset(
    offset: &PointerOffsetTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> PointerOffsetTerm {
    match offset {
        PointerOffsetTerm::Constant(value) => PointerOffsetTerm::Constant(*value),
        PointerOffsetTerm::Variable(variable) => PointerOffsetTerm::Variable(*variable),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            substitute_bitvector_variable(value, from, to),
            *byte_width,
        ),
    }
}

pub(super) fn substitute_bitvector_variable_in_pointer(
    pointer: &Pointer,
    from: Variable,
    to: &Bitvector32Term,
) -> Pointer {
    Pointer {
        block: pointer.block.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    }
}

pub(super) fn substitute_bitvector_variable_in_memory(
    memory: &CMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemory {
    let cells = memory
        .cells
        .iter()
        .map(|(pointer, value)| {
            (
                substitute_bitvector_variable_in_pointer(pointer, from, to),
                substitute_bitvector_variable_in_c_value(value, from, to),
            )
        })
        .collect();
    CMemory {
        blocks: memory.blocks.clone(),
        cells,
    }
}

pub(super) fn substitute_bitvector_variable_in_c_value(
    value: &CValue,
    from: Variable,
    to: &Bitvector32Term,
) -> CValue {
    match value {
        CValue::Int32(bits) => int32(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt8(bits) => uint8(substitute_bitvector_variable(bits, from, to)),
        CValue::Pointer(pointer) => {
            CValue::Pointer(substitute_bitvector_variable_in_pointer(pointer, from, to))
        }
    }
}

pub(super) fn memory_range_still_available(
    range_memory: &CMemory,
    current_memory: &CMemory,
    base: &Pointer,
) -> bool {
    range_memory == current_memory
        || range_memory.has_block(&base.block) == current_memory.has_block(&base.block)
}

pub(super) fn forall_int32(var: Variable, body: Proposition) -> Proposition {
    Proposition::ForAll {
        var,
        sort: Sort::CInt32,
        body: Box::new(body),
    }
}

pub(super) fn wrap_proof_facts(
    proposition: Proposition,
    assumptions: &Assumptions,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .filter(|obligation| obligation.is_assumable())
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

pub(super) fn wrap_path_context(
    proposition: Proposition,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .filter(|obligation| obligation.is_assumable())
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    facts.iter().rev().fold(proposition, |body, fact| {
        Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
    })
}

pub(super) fn public_execution_pure_facts(facts: &[ExecutionPureFact]) -> Vec<ExecutionPureFact> {
    facts
        .iter()
        .filter(|fact| fact.is_public())
        .cloned()
        .collect()
}

pub(super) fn solve_builtin_prop(proposition: &Proposition) -> bool {
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

pub(super) fn memory_ranges_disjoint_builtin(
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

pub(super) fn int32_element_index_from_offset(
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

pub(super) fn pointer_byte_offset_from_base(
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

pub(super) fn byte_offset_from_pointer_offset(
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

pub(super) fn int32_element_count_from_bytes(bytes: &Bitvector32Term) -> Option<Bitvector32Term> {
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

pub(super) fn signed_const_add(term: &Bitvector32Term, addend: u32) -> Option<Bitvector32Term> {
    let addend = i32::try_from(addend).ok()?;
    let sum = (term.as_const()? as i32).checked_add(addend)?;
    Some(Bitvector32Term::Constant(sum as u32))
}

pub(super) fn add_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, true)
}

pub(super) fn add_internal_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, false)
}

pub(super) fn add_path_fact_with_visibility(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
    public: bool,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_path_fact_with_visibility(
            facts,
            assumptions,
            condition,
            value,
            public,
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

pub(super) fn add_condition_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, true)
}

pub(super) fn add_internal_condition_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, false)
}

fn add_condition_path_fact_with_visibility(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
    public: bool,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
        return (known == value).then_some(());
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

pub(super) fn add_pointer_offset_equality_execution_pure_facts(
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

pub(super) fn add_proof_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_proof_obligation_with_context(obligations, assumptions, proposition, None)
}

pub(super) fn add_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
    context: Option<&str>,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_obligation(obligations, assumptions, condition, value, context);
    }

    if assumptions.proves(&proposition)
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

pub(super) fn add_required_proof_obligation_with_context(
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

pub(super) fn append_required_proof_obligations(
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

pub(super) fn append_required_proof_obligations_under_path_context(
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

pub(super) fn add_condition_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
    context: Option<&str>,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
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

pub(super) fn merge_obligations(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    let mut obligations = left.to_vec();
    for obligation in right {
        if obligation.is_assumable() {
            add_proof_obligation_with_context(
                &mut obligations,
                assumptions,
                obligation.proposition().clone(),
                obligation.context(),
            )?;
        } else {
            add_required_proof_obligation_with_context(
                &mut obligations,
                assumptions,
                obligation.proposition().clone(),
                obligation.context(),
            );
        }
    }
    Some(obligations)
}

pub(super) fn merge_facts(
    left: &[ExecutionPureFact],
    right: &[ExecutionPureFact],
    assumptions: &Assumptions,
) -> Option<Vec<ExecutionPureFact>> {
    let mut facts = left.to_vec();
    for fact in right {
        add_path_fact_with_visibility(
            &mut facts,
            assumptions,
            fact.proposition().clone(),
            fact.is_public(),
        )?;
    }
    Some(facts)
}

pub(super) fn merge_execution_pure_facts_and_obligations(
    left_facts: &[ExecutionPureFact],
    left_obligations: &[ProofObligation],
    right_facts: &[ExecutionPureFact],
    right_obligations: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<(Vec<ExecutionPureFact>, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    let obligations = merge_obligations(left_obligations, right_obligations, assumptions)?;
    Some((facts, obligations))
}

pub(super) fn decide_with_facts(
    assumptions: &Assumptions,
    facts: &[ExecutionPureFact],
    condition: &ConditionTerm,
) -> Option<bool> {
    assumptions
        .decide(condition)
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
                .fold(assumptions.clone(), |assumptions, fact| {
                    assumptions.assume_proposition(fact.proposition().clone())
                })
                .decide(condition)
        })
}

pub(super) fn assumptions_with_path_context(
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

pub(super) fn assumptions_with_propositions(
    assumptions: &Assumptions,
    propositions: &[Proposition],
) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for proposition in propositions {
        assumptions = assumptions.assume_proposition(proposition.clone());
    }
    assumptions
}
