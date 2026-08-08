use super::*;

pub(in crate::kernel) fn condition_as_order_fact(
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

pub(in crate::kernel) const FINITE_FORALL_INSTANTIATION_LIMIT: usize = 128;
pub(in crate::kernel) const FINITE_CONTEXT_SPLIT_LIMIT: usize = 8;
pub(in crate::kernel) const DISJUNCTION_CASE_LIMIT: usize = 8;

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct FiniteForAllRange {
    pub(in crate::kernel) lower: i64,
    pub(in crate::kernel) upper: i64,
}

#[derive(Clone, Debug)]
pub(in crate::kernel) struct VariableOrderEdge {
    pub(in crate::kernel) lower: Variable,
    pub(in crate::kernel) upper: Variable,
    pub(in crate::kernel) strict: bool,
}

pub(in crate::kernel) fn collect_forall_chain<'a>(
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

pub(in crate::kernel) fn collect_or_cases(proposition: &Proposition, cases: &mut Vec<Proposition>) {
    match proposition {
        Proposition::Or(left, right) => {
            collect_or_cases(left, cases);
            collect_or_cases(right, cases);
        }
        proposition => cases.push(proposition.clone()),
    }
}

pub(in crate::kernel) fn finite_forall_ranges(
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

pub(in crate::kernel) fn collect_implication_antecedent_order_facts(
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
        | Proposition::CStatementVerifies { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionVerifies { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CFunctionPartiallySatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CMemoryLoadable { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CMemoryDisjoint { .. }
        | Proposition::CResourceSeparate { .. }
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CHeapLifetimeRetired { .. }
        | Proposition::CWhileInvariantRule { .. } => {}
    }
}

pub(in crate::kernel) fn collect_order_facts_from_assumed_proposition(
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

pub(in crate::kernel) fn tighten_lower_bound(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    variable: Variable,
    lower: i64,
) {
    if let Some(range) = ranges.get_mut(&variable) {
        range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
    }
}

pub(in crate::kernel) fn tighten_upper_bound(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    variable: Variable,
    upper: i64,
) {
    if let Some(range) = ranges.get_mut(&variable) {
        range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
    }
}

pub(in crate::kernel) fn propagate_variable_order_bounds(
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

pub(in crate::kernel) fn signed_i64_bitvector_constant(value: i64) -> Bitvector32Term {
    debug_assert!((i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&value));
    Bitvector32Term::Constant(value as i32 as u32)
}

pub(in crate::kernel) fn instantiate_range_fold_step(
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
pub(in crate::kernel) struct IntegerRangeFacts {
    pub(in crate::kernel) lower: Option<i64>,
    pub(in crate::kernel) upper: Option<i64>,
    pub(in crate::kernel) excluded: BTreeSet<i64>,
}

pub(in crate::kernel) fn finite_integer_range_exhausted(
    order_facts: &[(Bitvector32Term, Bitvector32Term, bool)],
    equal_facts: &[(Bitvector32Term, Bitvector32Term)],
    disequal_facts: &[(Bitvector32Term, Bitvector32Term)],
) -> bool {
    let mut ranges: BTreeMap<Variable, IntegerRangeFacts> = BTreeMap::new();

    for (left, right, strict) in order_facts {
        if let (Some(variable), Some(bound)) =
            (bitvector_variable(left), signed_bitvector_constant(right))
        {
            let upper = if *strict { bound - 1 } else { bound };
            let range = ranges.entry(variable).or_default();
            range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
        }
        if let (Some(bound), Some(variable)) =
            (signed_bitvector_constant(left), bitvector_variable(right))
        {
            let lower = if *strict { bound + 1 } else { bound };
            let range = ranges.entry(variable).or_default();
            range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
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

pub(in crate::kernel) fn bitvector_variable(term: &Bitvector32Term) -> Option<Variable> {
    match term {
        Bitvector32Term::Variable(variable) => Some(*variable),
        _ => None,
    }
}

pub(in crate::kernel) fn signed_bitvector_constant(term: &Bitvector32Term) -> Option<i64> {
    term.as_const().map(|value| i64::from(value as i32))
}

pub(in crate::kernel) fn signed_u32_constant(value: u32) -> Option<i64> {
    i32::try_from(value).ok().map(i64::from)
}

pub(in crate::kernel) fn bitvector_variable_and_constant(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(Variable, i64)> {
    bitvector_variable(left)
        .zip(signed_bitvector_constant(right))
        .or_else(|| bitvector_variable(right).zip(signed_bitvector_constant(left)))
}

pub(in crate::kernel) fn bitvector_equality_after_additive_cancellation(
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
pub(in crate::kernel) struct CountFoldParts {
    pub(in crate::kernel) start: Bitvector32Term,
    pub(in crate::kernel) end: Bitvector32Term,
    pub(in crate::kernel) accumulator: Variable,
    pub(in crate::kernel) item: Variable,
    pub(in crate::kernel) contribution: Bitvector32Term,
}

pub(in crate::kernel) fn collect_bitvector_add_terms(
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

pub(in crate::kernel) fn count_fold_parts(term: &Bitvector32Term) -> Option<CountFoldParts> {
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

pub(in crate::kernel) fn count_fold_split_matches(
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

pub(in crate::kernel) fn count_fold_split_parts_match(
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

pub(in crate::kernel) fn range_fold_terms_alpha_equivalent(
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
