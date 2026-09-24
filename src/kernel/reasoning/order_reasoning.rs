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

/// The `int64` counterpart of [`condition_as_order_fact`]: a signed 64-bit
/// order fact as `(lower, upper, strict)`. The endpoints are 64-bit terms, so
/// callers must keep these bounds apart from int32 ones.
pub(in crate::kernel) fn condition_as_int64_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    let (left, right, lower_first, strict) = match condition {
        ConditionTerm::Bitvector64SignedLessThan(left, right) => (left, right, true, true),
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => (left, right, true, false),
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => (left, right, false, true),
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => (left, right, false, false),
        _ => return None,
    };
    let (lower, upper) = if lower_first {
        (left.as_ref().clone(), right.as_ref().clone())
    } else {
        (right.as_ref().clone(), left.as_ref().clone())
    };
    // A false order fact is the reversed order with the opposite strictness.
    Some(if value {
        (lower, upper, strict)
    } else {
        (upper, lower, !strict)
    })
}

#[derive(Clone, Debug, Default)]
pub(crate) struct FiniteForAllRange {
    pub(crate) lower: i64,
    pub(crate) upper: i64,
}

#[derive(Clone, Debug)]
pub(in crate::kernel) struct VariableOrderEdge {
    pub(in crate::kernel) lower: Variable,
    pub(in crate::kernel) upper: Variable,
    pub(in crate::kernel) strict: bool,
}

pub(crate) fn collect_forall_chain<'a>(
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

pub(crate) fn collect_or_cases(proposition: &Proposition, cases: &mut Vec<Proposition>) {
    match proposition {
        Proposition::Or(left, right) => {
            collect_or_cases(left, cases);
            collect_or_cases(right, cases);
        }
        proposition => cases.push(proposition.clone()),
    }
}

/// The constant box outside which `forall variables. body` is vacuously
/// true, when one can be established, so that checking `body` at every point
/// of the box proves the universal.
///
/// The body, below its `forall` chain, must be a tree of `And`, `Or`, and
/// nested `ForAll` nodes whose leaves are all implications. Every leaf's
/// antecedent alone must bound, to a constant range, each quantified
/// variable the leaf mentions; a leaf that mentions a quantified variable
/// without bounding it, or any other leaf shape, yields `None`. The result
/// is, per variable, the hull of the ranges of the leaves mentioning it:
/// outside that hull every such antecedent is false, so every leaf, and
/// therefore the whole tree, is true without inspection. A bare conjunct
/// such as `... and (k < 3)` is never vacuous and so never qualifies.
pub(crate) fn finite_forall_ranges(
    variables: &[Variable],
    body: &Proposition,
) -> Option<Vec<FiniteForAllRange>> {
    finite_forall_ranges_allowing_empty(variables, body, false)
}

/// [`finite_forall_ranges`], optionally admitting a guard that no integer
/// satisfies.
///
/// An empty hull is a range with zero members. Callers that ask a question
/// about the instances — `enumerate` checks each one — may take it, because
/// checking zero instances is exactly what the guard licenses. Callers that
/// harvest facts from instances gain nothing from it and keep rejecting it,
/// so this stays an opt-in.
pub(in crate::kernel) fn finite_forall_ranges_allowing_empty(
    variables: &[Variable],
    body: &Proposition,
    allow_empty: bool,
) -> Option<Vec<FiniteForAllRange>> {
    let variable_set = variables.iter().copied().collect::<BTreeSet<_>>();
    let mut leaves = Vec::new();
    if !collect_guarded_leaves(body, &mut leaves) || leaves.is_empty() {
        return None;
    }
    let mut hull = BTreeMap::<Variable, (i64, i64)>::new();
    for (antecedent, leaf) in leaves {
        let mut mentioned = BTreeSet::new();
        collect_proposition_bitvector_variables(leaf, &mut mentioned);
        let bounded = mentioned
            .iter()
            .filter(|variable| variable_set.contains(variable))
            .copied()
            .collect::<Vec<_>>();
        if bounded.is_empty() {
            continue;
        }
        let mut order_facts = Vec::new();
        collect_order_facts_from_assumed_proposition(antecedent, &mut order_facts);
        let ranges = antecedent_ranges(&variable_set, &order_facts)?;
        for variable in bounded {
            let range = ranges.get(&variable)?;
            let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
                return None;
            };
            hull.entry(variable)
                .and_modify(|(hull_lower, hull_upper)| {
                    *hull_lower = (*hull_lower).min(lower);
                    *hull_upper = (*hull_upper).max(upper);
                })
                .or_insert((lower, upper));
        }
    }

    variables
        .iter()
        .map(|variable| {
            let (lower, upper) = *hull.get(variable)?;
            if lower > upper && !allow_empty {
                return None;
            }
            Some(FiniteForAllRange { lower, upper })
        })
        .collect()
}

/// Collects `(antecedent, leaf)` for every implication leaf of the body's
/// `And`/`Or`/`ForAll` tree. `false` when some leaf is not an implication,
/// since such a leaf is not vacuous anywhere.
fn collect_guarded_leaves<'a>(
    proposition: &'a Proposition,
    leaves: &mut Vec<(&'a Proposition, &'a Proposition)>,
) -> bool {
    match proposition {
        Proposition::Implies(antecedent, _) => {
            leaves.push((antecedent, proposition));
            true
        }
        Proposition::And(left, right) | Proposition::Or(left, right) => {
            collect_guarded_leaves(left, leaves) && collect_guarded_leaves(right, leaves)
        }
        Proposition::ForAll { body, .. } => collect_guarded_leaves(body, leaves),
        _ => false,
    }
}

/// The constant ranges one antecedent's order facts impose on the quantified
/// variables, after propagating variable-to-variable order edges.
fn antecedent_ranges(
    variable_set: &BTreeSet<Variable>,
    order_facts: &[(Bitvector32Term, Bitvector32Term, bool)],
) -> Option<BTreeMap<Variable, IntegerRangeFacts>> {
    let mut ranges = variable_set
        .iter()
        .copied()
        .map(|variable| (variable, IntegerRangeFacts::default()))
        .collect::<BTreeMap<_, _>>();
    let mut edges = Vec::new();
    for (left, right, strict) in order_facts {
        match (bitvector_variable(left), signed_bitvector_constant(right)) {
            (Some(variable), Some(bound)) if variable_set.contains(&variable) => {
                let upper = if *strict {
                    bound.checked_sub(1)?
                } else {
                    bound
                };
                tighten_upper_bound(&mut ranges, variable, upper);
                continue;
            }
            _ => {}
        }
        match (signed_bitvector_constant(left), bitvector_variable(right)) {
            (Some(bound), Some(variable)) if variable_set.contains(&variable) => {
                let lower = if *strict {
                    bound.checked_add(1)?
                } else {
                    bound
                };
                tighten_lower_bound(&mut ranges, variable, lower);
                continue;
            }
            _ => {}
        }
        match (bitvector_variable(left), bitvector_variable(right)) {
            (Some(lower), Some(upper))
                if variable_set.contains(&lower) && variable_set.contains(&upper) =>
            {
                edges.push(VariableOrderEdge {
                    lower,
                    upper,
                    strict: *strict,
                });
            }
            _ => {}
        }
    }
    propagate_variable_order_bounds(&mut ranges, &edges)?;
    Some(ranges)
}

/// Whether a conjunction of signed order facts is unsatisfiable on its own:
/// its `<=`/`<` edges over syntactically identical terms form a cycle with at
/// least one strict edge. Identical terms denote one value, and the signed
/// int32 order is total, so `a <= ... < ... <= a` has no model. This reads
/// only the facts it is given, so `t <= k and k < t` is disproved without a
/// premise context. Constant-versus-constant comparisons are not evaluated
/// here; two distinct constants are two distinct nodes.
pub(in crate::kernel) fn order_facts_form_strict_cycle(
    facts: &[(Bitvector32Term, Bitvector32Term, bool)],
) -> bool {
    let mut nodes: BTreeMap<&Bitvector32Term, usize> = BTreeMap::new();
    let mut edges = Vec::with_capacity(facts.len());
    for (left, right, strict) in facts {
        let next = nodes.len();
        let from = *nodes.entry(left).or_insert(next);
        let next = nodes.len();
        let to = *nodes.entry(right).or_insert(next);
        edges.push((from, to, *strict));
    }
    let symbolic = {
        let mut flags = vec![false; nodes.len()];
        for (term, index) in &nodes {
            flags[*index] = !matches!(term, Bitvector32Term::Constant(_));
        }
        flags
    };
    // An edge between two non-constant terms is what makes the cycle a
    // symbolic one; a cycle of a variable against constants alone
    // (`0 <= k and k < 0`) is a finite range, decided elsewhere.
    let symbolic_edge = |from: usize, to: usize| symbolic[from] && symbolic[to];
    for &(from, to, strict) in &edges {
        if !strict {
            continue;
        }
        // A strict edge `from < to` closes a contradictory cycle when `to`
        // reaches `from`; the search state carries whether a symbolic edge
        // has been crossed, the strict edge itself included.
        let mut visited = vec![[false; 2]; nodes.len()];
        let mut stack = vec![(to, symbolic_edge(from, to))];
        while let Some((current, crossed)) = stack.pop() {
            if current == from {
                if crossed {
                    return true;
                }
                continue;
            }
            if std::mem::replace(&mut visited[current][usize::from(crossed)], true) {
                continue;
            }
            for &(edge_from, edge_to, _) in &edges {
                if edge_from == current {
                    let next = crossed || symbolic_edge(edge_from, edge_to);
                    if !visited[edge_to][usize::from(next)] {
                        stack.push((edge_to, next));
                    }
                }
            }
        }
    }
    false
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

pub(crate) fn signed_i64_bitvector_constant(value: i64) -> Bitvector32Term {
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

/// **The** reader for the signed value of a constant `int32` term.
///
/// `Bitvector32Term::as_const` answers `u32`, and every `int32` quantity the
/// kernel orders — an element index, a range endpoint, a block extent, an
/// owned quantity — is a signed number held in those bits. Reading one
/// through `as_const` and then comparing it makes `-1` the largest number
/// there is, which is how `e219bbc8`, `a98a05e4` and the commits beside them
/// each admitted a false theorem. A rule that wants a number rather than a
/// bit pattern asks here, or asks
/// [`exact_signed_constant`](crate::kernel::assumptions::exact_signed_constant)
/// where a recorded exact equality may name the value instead. See
/// "Index and offset arithmetic" in `docs/internals/kernel.md`.
///
/// `as_const` itself remains right for the questions that really are about
/// bits: equality, a hash or index key that carries no order, and the
/// width-scaling arithmetic that is modular by definition.
pub(in crate::kernel) fn signed_bitvector_constant(term: &Bitvector32Term) -> Option<i64> {
    term.as_const().map(|value| i64::from(value as i32))
}

/// The value of a 32-bit word read as `int32`, *when that value is
/// nonnegative*. This is not [`signed_bitvector_constant`] on a raw word: it
/// answers `None` rather than a negative number, so `is_none_or(|value|
/// value <= 0)` reads as "not a positive constant". Its callers are the
/// bound rules that want a positive constant addend and nothing else.
pub(in crate::kernel) fn nonnegative_int32_value(word: u32) -> Option<i64> {
    i32::try_from(word).ok().map(i64::from)
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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

/// Congruence for two int32-carrier range folds.
///
/// `(start..end).fold(initial, |acc, item| body)` is defined by recursion on
/// the half-open index range alone: it is `initial` when `end <= start`, and
/// otherwise `body[acc := fold(start..end - 1), item := end - 1]`. Its value
/// therefore depends on nothing but `(start, end, initial, body)`, so two
/// folds agreeing on all four denote the same value.
///
/// The three components outside the binders — `start`, `end`, and `initial` —
/// are compared semantically, by the context's own equality. The left fold is
/// then re-indexed at the right fold's copies of them, which cannot change its
/// value, and what remains is whether the two folds are the same term up to
/// their binders.
///
/// That last question is not answered here. A comparison that walks the two
/// bodies in step against a list of binder name pairs has to decide what a
/// variable occurrence means, and the obvious `left == right` clause — accept
/// any occurrence spelled the same on both sides — is wrong: it accepts an
/// occurrence that is *bound* on one side and *free* on the other. With fold
/// binder names hashed into a shared id space (`spec_fold_bound_variable`),
/// that is reachable from ordinary Click source: two sibling folds under one
/// `|acc, k|`, one of which rebinds `acc` while the other reads the enclosing
/// `acc` freely, then compare equal although one returns its initial value and
/// the other returns the enclosing accumulator.
///
/// So the binder question goes to the kernel's one checked answer,
/// [`crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent`],
/// which is what [`integer_range_fold_terms_alpha_equivalent`] already uses on
/// the Integer side. Its alpha key gives bound occurrences structural ordinals
/// and free occurrences their own identity, so the two can never match; it
/// restores an enclosing binding when a nested fold's body ends, so shadowing
/// is handled; and it carries a load's snapshot into the key, so two folds over
/// different snapshots of one array are never equated. Anything short of
/// `Some(true)`, including the `None` it returns on an unsupported node or an
/// exhausted work budget, is a refusal here.
///
/// Cost. Three component comparisons by the context's existing equality, then
/// one alpha key per fold, linear in the fold term under that key builder's
/// own work budget. Nothing scans the ambient facts.
pub(in crate::kernel) fn range_fold_terms_alpha_equivalent(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
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
            ..
        },
    ) = (left, right)
    else {
        return false;
    };

    if !assumptions.bitvector_terms_proven_equal(left_start, right_start)
        || !assumptions.bitvector_terms_proven_equal(left_end, right_end)
        || !assumptions.bitvector_terms_proven_equal(left_initial, right_initial)
    {
        return false;
    }

    let reindexed = Bitvector32Term::RangeFold {
        start: right_start.clone(),
        end: right_end.clone(),
        initial: right_initial.clone(),
        accumulator: *left_accumulator,
        item: *left_item,
        body: left_body.clone(),
    };
    crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent(&reindexed, right)
        == Some(true)
}

/// Endpoint congruence for an `Integer`-carrier range fold.
///
/// Two range folds denote the same Integer when they have the same initial
/// value, the same body, and equal endpoints. `range_fold_terms_alpha_equivalent`
/// is the same rule for the int32 carrier; the Integer carrier had no
/// counterpart, so `a == b` never bridged `fold(lo..a)` to `fold(lo..b)` and
/// no induction step could carry the append law's `end + 1` back to its goal.
///
/// Soundness. `(start..end).fold(initial, |acc, item| body)` is defined by
/// recursion on the half-open index range alone: it is `initial` when
/// `end <= start`, and otherwise `body[acc := fold(start..end - 1), item :=
/// end - 1]`. The value therefore depends on nothing but `(start, end,
/// initial, body)`, so equal components give equal values. A fold's endpoints
/// sit outside its two binders, so re-indexing the left fold at the right
/// fold's provably equal endpoints does not change its value. What is left is
/// whether the two re-indexed folds are the same term up to their binders,
/// and that question already has one checked answer in the kernel:
/// [`crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent`]. Its
/// snapshot-aware alpha key is what keeps a memory-reading body honest --- a
/// load carries its snapshot identity into the key, so two folds over
/// different snapshots of one array are never equated --- and it refuses an
/// opaque pure-function application or an algebraic match rather than
/// guessing at their binder occurrences. Anything short of `Some(true)`,
/// including the `None` it returns when its own work budget runs out, is a
/// refusal here.
///
/// Endpoint equality is decided by [`fold_endpoint_terms_proven_equal`] and
/// its Integer counterpart, which answer only from interner identity, an
/// exact recorded equality between exactly those two terms, or the affine
/// normal form of the two endpoints.
///
/// Cost. Two endpoint comparisons, each an interner-identity test, at most two
/// keyed lookups in `condition_facts`, and one affine flattening linear in the
/// two endpoint terms; then one alpha key per fold, under that key builder's
/// own work budget. Nothing scans the ambient facts and nothing recurses back
/// into `decide`.
pub(in crate::kernel) fn integer_range_fold_terms_alpha_equivalent(
    left: &SharedIntegerTerm,
    right: &SharedIntegerTerm,
    assumptions: &PureFactContext,
) -> bool {
    let (
        IntegerTerm::RangeFold {
            index: left_index,
            initial: left_initial,
            accumulator: left_accumulator,
            item: left_item,
            body: left_body,
        },
        IntegerTerm::RangeFold {
            index: right_index, ..
        },
    ) = (left.as_ref(), right.as_ref())
    else {
        return false;
    };

    if !integer_range_fold_indices_proven_equal(left_index, right_index, assumptions) {
        return false;
    }

    let reindexed = SharedIntegerTerm::intern(IntegerTerm::RangeFold {
        index: right_index.clone(),
        initial: left_initial.clone(),
        accumulator: *left_accumulator,
        item: *left_item,
        body: left_body.clone(),
    });
    crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(&reindexed, right) == Some(true)
}

fn integer_range_fold_indices_proven_equal(
    left: &IntegerRangeFoldIndex,
    right: &IntegerRangeFoldIndex,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (
            IntegerRangeFoldIndex::Int32 {
                start: left_start,
                end: left_end,
            },
            IntegerRangeFoldIndex::Int32 {
                start: right_start,
                end: right_end,
            },
        ) => {
            fold_endpoint_terms_proven_equal(left_start.value(), right_start.value(), assumptions)
                && fold_endpoint_terms_proven_equal(
                    left_end.value(),
                    right_end.value(),
                    assumptions,
                )
        }
        (
            IntegerRangeFoldIndex::Integer {
                start: left_start,
                end: left_end,
            },
            IntegerRangeFoldIndex::Integer {
                start: right_start,
                end: right_end,
            },
        ) => {
            integer_fold_endpoint_terms_proven_equal(left_start, right_start, assumptions)
                && integer_fold_endpoint_terms_proven_equal(left_end, right_end, assumptions)
        }
        // An int32 endpoint and an Integer endpoint index different fold
        // definitions; nothing here relates the two carriers.
        _ => false,
    }
}

/// Whether two int32 fold endpoints are the same value.
///
/// Three routes, none of them a search over the ambient facts:
///
/// 1. interner identity, which is the shared endpoint node's own equality;
/// 2. an equality between exactly these two terms already recorded as a fact,
///    found by a keyed lookup (`exact_condition_value` also tries the mirrored
///    orientation of an int32 equality);
/// 3. the two terms' affine normal forms, which is what makes `(hi - 1) + 1`
///    and `hi` the same endpoint.
///
/// Route 3 needs no definedness fact. `Bitvector32Term`'s `Add` and `Subtract`
/// denote wrapping 32-bit operations — a C signed overflow is a separate
/// definedness obligation, not a change of the term's value — so a term's
/// value is exactly its normal form's constant plus its signed atoms in
/// Z/2^32, and equal normal forms are equal values whether or not any
/// intermediate would overflow.
fn fold_endpoint_terms_proven_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || assumptions.exact_condition_value(&ConditionTerm::equal(left.clone(), right.clone()))
            == Some(true)
        || bitvector_affine_forms_equal(left, right)
}

/// The Integer-endpoint counterpart of [`fold_endpoint_terms_proven_equal`].
///
/// `exact_condition_value` has no mirrored orientation for an Integer
/// equality, so both orientations are looked up here. Integer `Add`,
/// `Subtract`, and `Negate` are exact unbounded arithmetic, so the affine
/// normal form is exact with no side condition at all.
fn integer_fold_endpoint_terms_proven_equal(
    left: &SharedIntegerTerm,
    right: &SharedIntegerTerm,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || assumptions
            .exact_condition_value(&ConditionTerm::IntegerEqual(left.clone(), right.clone()))
            == Some(true)
        || assumptions
            .exact_condition_value(&ConditionTerm::IntegerEqual(right.clone(), left.clone()))
            == Some(true)
        || integer_affine_forms_equal(left.as_ref(), right.as_ref())
}

/// Flatten `term` into signed atoms and a wrapping 32-bit constant.
///
/// Only `Add`, `Subtract`, and `Constant` are interpreted; every other node,
/// including the 64-bit constants and arithmetic that share this arena, is an
/// opaque atom. The walk visits each node of `term` once.
fn collect_bitvector_affine_atoms(
    term: &Bitvector32Term,
    positive: bool,
    atoms: &mut Vec<(bool, Bitvector32Term)>,
    constant: &mut u32,
) {
    match term {
        Bitvector32Term::Add(left, right) => {
            collect_bitvector_affine_atoms(left, positive, atoms, constant);
            collect_bitvector_affine_atoms(right, positive, atoms, constant);
        }
        Bitvector32Term::Subtract(left, right) => {
            collect_bitvector_affine_atoms(left, positive, atoms, constant);
            collect_bitvector_affine_atoms(right, !positive, atoms, constant);
        }
        Bitvector32Term::Constant(value) => {
            *constant = if positive {
                constant.wrapping_add(*value)
            } else {
                constant.wrapping_sub(*value)
            };
        }
        term => atoms.push((positive, term.clone())),
    }
}

fn bitvector_affine_forms_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    let mut left_atoms = Vec::new();
    let mut left_constant = 0u32;
    collect_bitvector_affine_atoms(left, true, &mut left_atoms, &mut left_constant);

    let mut right_atoms = Vec::new();
    let mut right_constant = 0u32;
    collect_bitvector_affine_atoms(right, true, &mut right_atoms, &mut right_constant);

    left_constant == right_constant && affine_atom_multisets_equal(left_atoms, right_atoms)
}

/// The Integer counterpart of [`collect_bitvector_affine_atoms`]; `Negate`
/// flips the sign of its whole operand and the constant is exact.
fn collect_integer_affine_atoms(
    term: &IntegerTerm,
    positive: bool,
    atoms: &mut Vec<(bool, IntegerTerm)>,
    constant: &mut num_bigint::BigInt,
) {
    match term {
        IntegerTerm::Add(left, right) => {
            collect_integer_affine_atoms(left.as_ref(), positive, atoms, constant);
            collect_integer_affine_atoms(right.as_ref(), positive, atoms, constant);
        }
        IntegerTerm::Subtract(left, right) => {
            collect_integer_affine_atoms(left.as_ref(), positive, atoms, constant);
            collect_integer_affine_atoms(right.as_ref(), !positive, atoms, constant);
        }
        IntegerTerm::Negate(value) => {
            collect_integer_affine_atoms(value.as_ref(), !positive, atoms, constant);
        }
        IntegerTerm::Constant(value) => {
            if positive {
                *constant += value;
            } else {
                *constant -= value;
            }
        }
        term => atoms.push((positive, term.clone())),
    }
}

fn integer_affine_forms_equal(left: &IntegerTerm, right: &IntegerTerm) -> bool {
    let mut left_atoms = Vec::new();
    let mut left_constant = num_bigint::BigInt::from(0);
    collect_integer_affine_atoms(left, true, &mut left_atoms, &mut left_constant);

    let mut right_atoms = Vec::new();
    let mut right_constant = num_bigint::BigInt::from(0);
    collect_integer_affine_atoms(right, true, &mut right_atoms, &mut right_constant);

    left_constant == right_constant && affine_atom_multisets_equal(left_atoms, right_atoms)
}

fn affine_atom_multisets_equal<T: PartialEq>(
    left: Vec<(bool, T)>,
    mut right: Vec<(bool, T)>,
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    for atom in left {
        let Some(index) = right.iter().position(|other| other == &atom) else {
            return false;
        };
        right.remove(index);
    }
    right.is_empty()
}
