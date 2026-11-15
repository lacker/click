use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey;
use crate::kernel::binary_term;
use crate::kernel::{bits32_constant, constant_u32};

pub(in crate::kernel) fn condition_as_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(MachineTerm, MachineTerm, bool)> {
    if let Some(view) =
        crate::kernel::machine_integer::comparison::native_comparison_view(condition, value)
    {
        if view.format != MachineIntegerType::Int32 {
            return None;
        }
        let strict = match view.relation {
            crate::kernel::machine_integer::Relation::Less => true,
            crate::kernel::machine_integer::Relation::LessEqual => false,
            _ => return None,
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view().retain(view.format).value().clone());
        return Some((left, right, strict));
    }
    match (condition, value) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            },
            true,
        ) => Some((left.as_ref().clone(), right.as_ref().clone(), true)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            },
            false,
        ) => Some((right.as_ref().clone(), left.as_ref().clone(), false)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            },
            true,
        ) => Some((left.as_ref().clone(), right.as_ref().clone(), false)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            },
            false,
        ) => Some((right.as_ref().clone(), left.as_ref().clone(), true)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            },
            true,
        ) => Some((right.as_ref().clone(), left.as_ref().clone(), true)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            },
            false,
        ) => Some((left.as_ref().clone(), right.as_ref().clone(), false)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            true,
        ) => Some((right.as_ref().clone(), left.as_ref().clone(), false)),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            false,
        ) => Some((left.as_ref().clone(), right.as_ref().clone(), true)),
        _ => None,
    }
}

/// The signed condition `lower < upper` (strict) or `lower <= upper`.
pub(in crate::kernel) fn order_condition(
    lower: MachineTerm,
    upper: MachineTerm,
    strict: bool,
) -> ConditionTerm {
    if strict {
        ConditionTerm::signed_less_than(lower, upper)
    } else {
        ConditionTerm::signed_less_equal(lower, upper)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct FiniteForAllRange {
    pub(crate) lower: i64,
    pub(crate) upper: i64,
    /// Whether the variable is an unsigned 64-bit one, bounded by 64-bit
    /// unsigned comparisons. Its values are then 64-bit constants.
    pub(crate) unsigned64: bool,
}

impl FiniteForAllRange {
    /// One value of the range as the constant its variable takes.
    pub(crate) fn constant(&self, value: i64) -> MachineTerm {
        if self.unsigned64 {
            MachineTerm::uint64_constant(value as u64)
        } else {
            signed_i64_bitvector_constant(value)
        }
    }
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
        // An unsigned 64-bit binder is ranged by its own 64-bit bounds
        // (`uint64_antecedent_ranges`); the finite tables read both.
        Proposition::ForAll {
            var,
            sort: Sort::ProgramInt32 | Sort::ProgramInteger(MachineIntegerType::UInt64),
            body,
            ..
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
    let mut unsigned64 = BTreeSet::new();
    // The quantified variables each leaf mentions. A leaf that mentions none
    // is the same proposition at every point of the domain, so it is not
    // vacuous anywhere and a zero-member table would never check it.
    let mut leaf_variables = Vec::new();
    for (antecedent, leaf) in leaves {
        // A guard that is the constant `false` is what an unsatisfiable
        // unsigned bound folds to: `k < 0u64` has no member. The leaf is
        // vacuous at every point, as under an empty range of every binder,
        // and a binder no other leaf ranges is given that empty range.
        if matches!(
            antecedent,
            Proposition::ConditionIs(ConditionTerm::Constant(false), true)
                | Proposition::ConditionIs(ConditionTerm::Constant(true), false)
        ) {
            for variable in variables {
                hull.entry(*variable).or_insert((0, -1));
            }
            leaf_variables.push(variables.to_vec());
            continue;
        }
        let mut mentioned = BTreeSet::new();
        collect_proposition_bitvector_variables(leaf, &mut mentioned);
        let bounded = mentioned
            .iter()
            .filter(|variable| variable_set.contains(variable))
            .copied()
            .collect::<Vec<_>>();
        if bounded.is_empty() {
            leaf_variables.push(bounded);
            continue;
        }
        leaf_variables.push(bounded.clone());
        let mut ranges = antecedent_ranges(&variable_set, antecedent)?;
        // A variable the antecedent bounds by unsigned 64-bit comparisons
        // with constants ranges over those values, from zero where it
        // states no lower bound.
        for (variable, (lower, upper)) in uint64_antecedent_ranges(&variable_set, antecedent) {
            let range = ranges.get_mut(&variable)?;
            if range.lower.is_some() || range.upper.is_some() {
                // One variable read at both widths has no single range.
                return None;
            }
            range.lower = Some(lower);
            range.upper = upper;
            unsigned64.insert(variable);
        }
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

    let empty = hull
        .iter()
        .filter(|(_, (lower, upper))| lower > upper)
        .map(|(variable, _)| *variable)
        .collect::<BTreeSet<_>>();
    if !empty.is_empty() {
        if !allow_empty {
            return None;
        }
        // A table with zero members checks no leaf, so it is evidence only
        // when every leaf is vacuous there: each must be guarded by a range
        // of some variable that no integer satisfies. A leaf mentioning no
        // such variable, including one mentioning no quantified variable at
        // all, still has to be checked, and this table cannot check it.
        if leaf_variables
            .iter()
            .any(|bounded| !bounded.iter().any(|variable| empty.contains(variable)))
        {
            return None;
        }
    }

    variables
        .iter()
        .map(|variable| {
            let (lower, upper) = *hull.get(variable)?;
            Some(FiniteForAllRange {
                lower,
                upper,
                unsigned64: unsigned64.contains(variable),
            })
        })
        .collect()
}

/// Visit only the comparisons explicitly written in a conjunctive guard.
/// The comparison view normalizes direction and truth while retaining shared
/// operands; consumers select variables and constants without exporting trees.
fn visit_antecedent_order(
    proposition: &Proposition,
    format: MachineIntegerType,
    visit: &mut impl FnMut(
        crate::kernel::MachineOperandView<'_>,
        crate::kernel::MachineOperandView<'_>,
        bool,
    ),
) {
    use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
    crate::instrumentation::record_deterministic_work(1);
    match proposition {
        Proposition::ConditionIs(condition, truth) => {
            let Some(view) = comparison_view(condition, *truth) else {
                return;
            };
            if view.format != format {
                return;
            }
            let strict = match view.relation {
                Relation::Less => true,
                Relation::LessEqual => false,
                _ => return,
            };
            visit(
                view.operands[0].operand_view(),
                view.operands[1].operand_view(),
                strict,
            );
        }
        Proposition::And(left, right) => {
            visit_antecedent_order(left, format, visit);
            visit_antecedent_order(right, format, visit);
        }
        _ => {}
    }
}

/// The ranges an antecedent's unsigned 64-bit comparisons with constants
/// impose on the quantified variables: `(lower, upper)`, with the lower
/// bound zero where none is stated and no upper bound where none is. Only
/// a conjunction's own comparisons are read, and only constants that fit
/// the signed 64-bit range table.
fn uint64_antecedent_ranges(
    variable_set: &BTreeSet<Variable>,
    antecedent: &Proposition,
) -> BTreeMap<Variable, (i64, Option<i64>)> {
    let mut ranges = BTreeMap::<Variable, (i64, Option<i64>)>::new();
    let constant = |term: crate::kernel::MachineOperandView<'_>| {
        term.uint64_constant()
            .and_then(|value| i64::try_from(value).ok())
    };
    visit_antecedent_order(
        antecedent,
        MachineIntegerType::UInt64,
        &mut |lower, upper, strict| {
            if let (Some(&variable), Some(bound)) = (lower.variable(), constant(upper))
                && variable_set.contains(&variable)
            {
                // `k < 0` has no member: its upper bound is below zero.
                let bound = if strict { bound - 1 } else { bound };
                let range = ranges.entry(variable).or_insert((0, None));
                range.1 = Some(range.1.map_or(bound, |current| current.min(bound)));
            } else if let (Some(bound), Some(&variable)) = (constant(lower), upper.variable())
                && variable_set.contains(&variable)
            {
                let Some(bound) = (if strict {
                    bound.checked_add(1)
                } else {
                    Some(bound)
                }) else {
                    return;
                };
                let range = ranges.entry(variable).or_insert((0, None));
                range.0 = range.0.max(bound);
            }
        },
    );
    ranges
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
    antecedent: &Proposition,
) -> Option<BTreeMap<Variable, IntegerRangeFacts>> {
    let mut ranges = variable_set
        .iter()
        .copied()
        .map(|variable| (variable, IntegerRangeFacts::default()))
        .collect::<BTreeMap<_, _>>();
    let mut edges = Vec::new();
    let constant = |term: crate::kernel::MachineOperandView<'_>| {
        term.word32_constant().map(|bits| i64::from(bits as i32))
    };
    visit_antecedent_order(
        antecedent,
        MachineIntegerType::Int32,
        &mut |left, right, strict| {
            if let (Some(&variable), Some(bound)) = (left.variable(), constant(right))
                && variable_set.contains(&variable)
            {
                // The endpoint is int32; shifting it by one fits this i64 table.
                tighten_upper_bound(&mut ranges, variable, bound - i64::from(strict));
                return;
            }
            if let (Some(bound), Some(&variable)) = (constant(left), right.variable())
                && variable_set.contains(&variable)
            {
                tighten_lower_bound(&mut ranges, variable, bound + i64::from(strict));
                return;
            }
            if let (Some(&lower), Some(&upper)) = (left.variable(), right.variable())
                && variable_set.contains(&lower)
                && variable_set.contains(&upper)
            {
                edges.push(VariableOrderEdge {
                    lower,
                    upper,
                    strict,
                });
            }
        },
    );
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
    facts: &[(ScalarOperandKey, ScalarOperandKey, bool)],
) -> bool {
    let mut nodes: BTreeMap<&ScalarOperandKey, usize> = BTreeMap::new();
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
            flags[*index] = term.operand_view().word32_constant().is_none();
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
    facts: &mut Vec<(ScalarOperandKey, ScalarOperandKey, bool)>,
) {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            let Some(view) =
                crate::kernel::machine_integer::comparison::comparison_view(condition, *value)
            else {
                return;
            };
            if view.format != MachineIntegerType::Int32 {
                return;
            }
            let strict = match view.relation {
                crate::kernel::machine_integer::Relation::Less => true,
                crate::kernel::machine_integer::Relation::LessEqual => false,
                _ => return,
            };
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| ScalarOperandKey::for_format(view.format, operand.operand_view()));
            facts.push((left, right, strict));
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

pub(crate) fn signed_i64_bitvector_constant(value: i64) -> MachineTerm {
    debug_assert!((i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&value));
    MachineTerm::constant(value as i32 as u32)
}

pub(in crate::kernel) fn instantiate_range_fold_step(
    body: &MachineTerm,
    accumulator: Variable,
    accumulator_value: &MachineTerm,
    item: Variable,
    item_value: &MachineTerm,
) -> MachineTerm {
    let body = substitute_bitvector_variable(body, accumulator, accumulator_value);
    substitute_bitvector_variable(&body, item, item_value)
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct IntegerRangeFacts {
    pub(in crate::kernel) lower: Option<i64>,
    pub(in crate::kernel) upper: Option<i64>,
    #[cfg(test)]
    pub(in crate::kernel) excluded: BTreeSet<i64>,
}

#[cfg(test)]
pub(in crate::kernel) fn finite_integer_range_exhausted(
    order_facts: &[(MachineTerm, MachineTerm, bool)],
    equal_facts: &[(MachineTerm, MachineTerm)],
    disequal_facts: &[(MachineTerm, MachineTerm)],
) -> bool {
    integer_range_facts(order_facts, equal_facts, disequal_facts)
        .values()
        .any(integer_range_exhausted)
}

#[cfg(test)]
/// Each variable's constant bounds and excluded values, as the order,
/// equality and disequality facts state them.
pub(in crate::kernel) fn integer_range_facts(
    order_facts: &[(MachineTerm, MachineTerm, bool)],
    equal_facts: &[(MachineTerm, MachineTerm)],
    disequal_facts: &[(MachineTerm, MachineTerm)],
) -> BTreeMap<Variable, IntegerRangeFacts> {
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
    ranges
}

#[cfg(test)]
/// Whether one variable's bounds admit no value: they cross, or a short
/// interval has every value excluded.
pub(in crate::kernel) fn integer_range_exhausted(range: &IntegerRangeFacts) -> bool {
    let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
        return false;
    };
    if lower > upper {
        return true;
    }
    upper - lower <= 256 && (lower..=upper).all(|value| range.excluded.contains(&value))
}

pub(in crate::kernel) fn bitvector_variable(term: &MachineTerm) -> Option<Variable> {
    match term {
        MachineTerm::Variable(variable) => Some(*variable),
        _ => None,
    }
}

/// **The** reader for the signed value of a constant `int32` term.
///
/// `MachineTerm::as_const` answers `u32`, and every `int32` quantity the
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
pub(in crate::kernel) fn signed_bitvector_constant(term: &MachineTerm) -> Option<i64> {
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
    left: &MachineTerm,
    right: &MachineTerm,
) -> Option<(Variable, i64)> {
    bitvector_variable(left)
        .zip(signed_bitvector_constant(right))
        .or_else(|| bitvector_variable(right).zip(signed_bitvector_constant(left)))
}

/// The existing cancellation rule with retained endpoints.
pub(in crate::kernel) fn shared_bitvector_equality_cancellation(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> Option<(
    crate::kernel::SharedMachineIntegerTerm,
    crate::kernel::SharedMachineIntegerTerm,
)> {
    use crate::kernel::machine_integer::{
        Relation,
        comparison::{ComparisonOperand, NativeComparisonView},
    };
    let ty = crate::kernel::MachineIntegerType::Int32;
    let view = NativeComparisonView {
        format: ty,
        relation: Relation::Equal,
        operands: [left, right].map(|v| match v {
            crate::kernel::MachineOperandView::Legacy(term) => ComparisonOperand::Written(term),
            crate::kernel::MachineOperandView::Shared(_) => {
                ComparisonOperand::Observation(v.retain(ty))
            }
        }),
    };
    let reduced = view.cancelled_equality()?;
    Some((
        reduced.operands[0].operand_view().retain(ty),
        reduced.operands[1].operand_view().retain(ty),
    ))
}

pub(in crate::kernel) fn bitvector_equality_after_additive_cancellation(
    left: &MachineTerm,
    right: &MachineTerm,
) -> Option<(MachineTerm, MachineTerm)> {
    // `a + b == a + c` exactly when `b == c` for sums of one 32-bit format,
    // and `a + b == a` exactly when `b == 0`. A sum of each format cancels
    // only against a sum, or an addend, of its own format.
    fn sum(
        term: &MachineTerm,
    ) -> Option<(
        crate::kernel::MachineIntegerType,
        &MachineTerm,
        &MachineTerm,
    )> {
        match term {
            binary_term!(Bits32 @ format, Add, base, addend) => {
                Some((*format, base.as_ref(), addend.as_ref()))
            }
            _ => None,
        }
    }
    let zero = |format| MachineTerm::constant_at32(format, 0);
    if let (
        Some((left_format, left_base, left_addend)),
        Some((right_format, right_base, right_addend)),
    ) = (sum(left), sum(right))
        && left_format == right_format
    {
        for ((left_kept, left_other), (right_kept, right_other)) in [
            ((left_base, left_addend), (right_base, right_addend)),
            ((left_base, left_addend), (right_addend, right_base)),
            ((left_addend, left_base), (right_base, right_addend)),
            ((left_addend, left_base), (right_addend, right_base)),
        ] {
            if left_kept == right_kept {
                return Some((left_other.clone(), right_other.clone()));
            }
        }
    }
    if let Some((format, base, addend)) = sum(left) {
        if base == right {
            return Some((addend.clone(), zero(format)));
        }
        if addend == right {
            return Some((base.clone(), zero(format)));
        }
    }
    if let Some((format, base, addend)) = sum(right) {
        if left == base {
            return Some((zero(format), addend.clone()));
        }
        if left == addend {
            return Some((zero(format), base.clone()));
        }
    }
    None
}

#[derive(Clone, Debug)]
pub(in crate::kernel) struct CountFoldParts {
    pub(in crate::kernel) start: MachineTerm,
    pub(in crate::kernel) end: MachineTerm,
    pub(in crate::kernel) accumulator: Variable,
    pub(in crate::kernel) item: Variable,
    pub(in crate::kernel) contribution: MachineTerm,
}

/// The addends of a sum of the 32-bit `format`, and the sum of its
/// constants; a sum of the other format is an addend of its own.
pub(in crate::kernel) fn collect_bitvector_add_terms(
    format: crate::kernel::MachineIntegerType,
    term: &MachineTerm,
    terms: &mut Vec<MachineTerm>,
    constant: &mut u32,
) {
    match term {
        binary_term!(Bits32 @ found, Add, left, right) if *found == format => {
            collect_bitvector_add_terms(format, left, terms, constant);
            collect_bitvector_add_terms(format, right, terms, constant);
        }
        bits32_constant!(value) => {
            *constant = constant.wrapping_add(constant_u32(*value));
        }
        term => terms.push(term.clone()),
    }
}

pub(in crate::kernel) fn count_fold_parts(term: &MachineTerm) -> Option<CountFoldParts> {
    let MachineTerm::RangeFold {
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

    if initial.as_ref() != &MachineTerm::constant(0) {
        return None;
    }

    let contribution = match body.as_ref() {
        binary_term!(Int32, Add, left, right)
            if left.as_ref() == &MachineTerm::Variable(*accumulator) =>
        {
            right.as_ref().clone()
        }
        binary_term!(Int32, Add, left, right)
            if right.as_ref() == &MachineTerm::Variable(*accumulator) =>
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
    whole: &MachineTerm,
    split: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let Some(whole) = count_fold_parts(whole) else {
        return false;
    };
    let binary_term!(Int32, Add, left, right) = split else {
        return false;
    };

    count_fold_split_parts_match(&whole, left.as_ref(), right.as_ref(), assumptions)
        || count_fold_split_parts_match(&whole, right.as_ref(), left.as_ref(), assumptions)
}

pub(in crate::kernel) fn count_fold_split_parts_match(
    whole: &CountFoldParts,
    first: &MachineTerm,
    second: &MachineTerm,
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
/// is handled; and it carries a load's state into the key, so two folds over
/// different states of one array are never equated. Anything short of
/// `Some(true)`, including the `None` it returns on an unsupported node or an
/// exhausted work budget, is a refusal here.
///
/// Cost. Three component comparisons by the context's existing equality, then
/// one alpha key per fold, linear in the fold term under that key builder's
/// own work budget. Nothing scans the ambient facts.
pub(in crate::kernel) fn range_fold_terms_alpha_equivalent(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let (
        MachineTerm::RangeFold {
            start: left_start,
            end: left_end,
            initial: left_initial,
            accumulator: left_accumulator,
            item: left_item,
            body: left_body,
        },
        MachineTerm::RangeFold {
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

    let reindexed = MachineTerm::RangeFold {
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
/// state-aware alpha key is what keeps a memory-reading body honest --- a
/// load carries its state identity into the key, so two folds over
/// different states of one array are never equated --- and it refuses an
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
            fold_endpoint_terms_proven_equal(
                left_start.machine_operand(),
                right_start.machine_operand(),
                assumptions,
            ) && fold_endpoint_terms_proven_equal(
                left_end.machine_operand(),
                right_end.machine_operand(),
                assumptions,
            )
        }
        // Unsigned 64-bit endpoints are equal by identity or by an exact
        // 64-bit equality fact; the 32-bit affine forms do not read them.
        (
            IntegerRangeFoldIndex::UInt64 {
                start: left_start,
                end: left_end,
            },
            IntegerRangeFoldIndex::UInt64 {
                start: right_start,
                end: right_end,
            },
        ) => {
            let equal = |left: &SharedIntegerRangeEndpoint, right: &SharedIntegerRangeEndpoint| {
                exact_fold_endpoint_equality(
                    MachineIntegerType::UInt64,
                    left.machine_operand().operand_view(),
                    right.machine_operand().operand_view(),
                    assumptions,
                )
            };
            equal(left_start, right_start) && equal(left_end, right_end)
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

fn exact_fold_endpoint_equality(
    format: MachineIntegerType,
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::machine_integer::{
        Relation,
        comparison::{ComparisonOperand, NativeComparisonView},
    };
    if ScalarOperandKey::for_format(format, left) == ScalarOperandKey::for_format(format, right) {
        return true;
    }
    let condition = |a: crate::kernel::MachineOperandView<'_>,
                     b: crate::kernel::MachineOperandView<'_>| {
        NativeComparisonView {
            format,
            relation: Relation::Equal,
            operands: [
                ComparisonOperand::Observation(a.retain(format)),
                ComparisonOperand::Observation(b.retain(format)),
            ],
        }
        .integer_condition()
    };
    let stated = |condition| {
        let Some(source) = assumptions.selected_comparison_source(&condition, true) else {
            return false;
        };
        crate::kernel::assumptions::record_implicit_reasoning_provenance(assumptions, source);
        true
    };
    stated(condition(left, right)) || stated(condition(right, left))
}

/// Whether two int32 fold endpoints are the same value.
///
/// Three routes, none of them a search over the ambient facts:
///
/// 1. interner identity, which is the shared endpoint node's own equality;
/// 2. an equality between exactly these two terms already recorded as a fact,
///    found by the selected comparison-source index in either orientation;
/// 3. the two terms' affine normal forms, which is what makes `(hi - 1) + 1`
///    and `hi` the same endpoint.
///
/// Route 3 needs no definedness fact. `MachineTerm`'s `Add` and `Subtract`
/// denote wrapping 32-bit operations — a C signed overflow is a separate
/// definedness obligation, not a change of the term's value — so a term's
/// value is exactly its normal form's constant plus its signed atoms in
/// Z/2^32, and equal normal forms are equal values whether or not any
/// intermediate would overflow.
fn fold_endpoint_terms_proven_equal(
    left: &SharedMachineIntegerTerm,
    right: &SharedMachineIntegerTerm,
    assumptions: &PureFactContext,
) -> bool {
    let (left, right) = (left.operand_view(), right.operand_view());
    exact_fold_endpoint_equality(MachineIntegerType::Int32, left, right, assumptions)
        || retained_fold_affine_equal(left, right)
}

thread_local! {
    // Syntax only: peeling a written constant offset reads no proof facts or
    // registered loads. Keep growing prefixes reusable across proof contexts.
    static FOLD_AFFINE_EQUALITIES: std::cell::RefCell<std::collections::HashMap<(u64, u64), bool>> = Default::default();
    static FOLD_AFFINE_BASES: std::cell::RefCell<std::collections::HashMap<u64, (Option<ScalarOperandKey>, u32)>> = Default::default();
}

pub(crate) fn clear_fold_affine_bases() {
    FOLD_AFFINE_BASES.with(|cache| cache.borrow_mut().clear());
    FOLD_AFFINE_EQUALITIES.with(|cache| cache.borrow_mut().clear());
}

/// Memoize only syntax-based equality. A new Add/Sub root can reuse the
/// preceding roots' affine equality across changing fact contexts. Exact
/// premise lookups never publish into this memo.
fn retained_fold_affine_equal(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> bool {
    use crate::kernel::{MachineBinaryOp as Op, MachineOperandView as V};
    let pair = |a: V<'_>, b: V<'_>| match (a, b) {
        (V::Shared(a), V::Shared(b)) => Some((a.id().min(b.id()), a.id().max(b.id()))),
        _ => None,
    };
    FOLD_AFFINE_EQUALITIES.with(|cache| {
        let mut cache = cache.borrow_mut();
        let key = pair(left, right);
        if let Some(result) = key.and_then(|key| cache.get(&key)) {
            return *result;
        }
        let known = |a: V<'_>, b: V<'_>| {
            pair(a, b).and_then(|key| cache.get(&key)).copied() == Some(true)
                || ScalarOperandKey::new(a) == ScalarOperandKey::new(b)
        };
        let congruent = match (left.binary(), right.binary()) {
            (
                Some((MachineIntegerType::Int32, a_op, [a, b])),
                Some((MachineIntegerType::Int32, b_op, [c, d])),
            ) if a_op == b_op && matches!(a_op, Op::Add | Op::Subtract) => {
                (known(a, c) && known(b, d)) || (a_op == Op::Add && known(a, d) && known(b, c))
            }
            _ => false,
        };
        let result = congruent
            || retained_fold_affine_base(left) == retained_fold_affine_base(right)
            || retained_fold_affine_form(left) == retained_fold_affine_form(right);
        if let Some(key) = key {
            cache.insert(key, result);
        }
        result
    })
}

/// The affine rule's common one-base case. Repeated `(prefix - 1) + 1`
/// queries should inspect their new constant spine, not the growing prefix.
fn retained_fold_affine_base(
    mut view: crate::kernel::MachineOperandView<'_>,
) -> (Option<ScalarOperandKey>, u32) {
    use crate::kernel::{MachineBinaryOp as Op, MachineOperandView as V};
    let literal = |v: V<'_>| v.literal().and_then(|term| term.as_const());
    FOLD_AFFINE_BASES.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut path = Vec::new();
        let mut result = loop {
            crate::instrumentation::record_deterministic_work(1);
            let id = match view {
                V::Shared(root) => Some(root.id()),
                V::Legacy(_) => None,
            };
            if let Some(known) = id.and_then(|id| cache.get(&id)) {
                break known.clone();
            }
            if let Some(value) = literal(view) {
                break (None, value);
            }
            if let Some((MachineIntegerType::Int32, operation, [left, right])) = view.binary() {
                let next = match operation {
                    Op::Add => literal(right)
                        .map(|c| (left, c))
                        .or_else(|| literal(left).map(|c| (right, c))),
                    Op::Subtract => literal(right).map(|c| (left, 0u32.wrapping_sub(c))),
                    _ => None,
                };
                if let Some((operand, offset)) = next {
                    path.push((id, offset));
                    view = operand;
                    continue;
                }
            }
            let result = (Some(ScalarOperandKey::new(view)), 0);
            if let Some(id) = id {
                cache.insert(id, result.clone());
            }
            break result;
        };
        for (id, offset) in path.into_iter().rev() {
            result.1 = result.1.wrapping_add(offset);
            if let Some(id) = id {
                cache.insert(id, result.clone());
            }
        }
        result
    })
}

/// Count signed occurrences in the explicit DAG rather than expanding one
/// occurrence per path. Positive/negative counts remain separate, preserving
/// the native rule's refusal to cancel opposite occurrences. Each count can
/// wrap modulo 2^32: every atom is multiplied in the endpoint's word ring.
/// Fixed-width counts also avoid quadratic big-integer work on a cold DAG
/// built by repeatedly doubling a shared child.
fn retained_fold_affine_form(
    root: crate::kernel::MachineOperandView<'_>,
) -> (BTreeMap<(bool, ScalarOperandKey), u32>, u32) {
    use crate::kernel::{MachineBinaryOp as Op, MachineOperandView as V};
    let identity = |view: V<'_>| match view {
        V::Shared(term) => (true, term.id()),
        V::Legacy(term) => (false, term as *const _ as usize as u64),
    };
    fn children(view: V<'_>) -> Option<(MachineIntegerType, Op, [V<'_>; 2])> {
        view.binary().filter(|(format, op, _)| {
            *format == MachineIntegerType::Int32 && matches!(op, Op::Add | Op::Subtract)
        })
    }
    let mut pending = vec![(root, false)];
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    while let Some((view, finish)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if finish {
            order.push(view);
            continue;
        }
        if !seen.insert(identity(view)) {
            continue;
        }
        pending.push((view, true));
        if let Some((_, _, [left, right])) = children(view) {
            pending.extend([(right, false), (left, false)]);
        }
    }
    let mut counts = std::collections::HashMap::from([(identity(root), [1u32, 0u32])]);
    let mut atoms = BTreeMap::new();
    let mut constant = 0u32;
    for view in order.into_iter().rev() {
        crate::instrumentation::record_deterministic_work(1);
        let [positive, negative] = counts
            .remove(&identity(view))
            .expect("reachable affine node");
        if let Some((_, op, [left, right])) = children(view) {
            let left = counts.entry(identity(left)).or_insert([0u32; 2]);
            left[0] = left[0].wrapping_add(positive);
            left[1] = left[1].wrapping_add(negative);
            let right = counts.entry(identity(right)).or_insert([0u32; 2]);
            if op == Op::Subtract {
                right[0] = right[0].wrapping_add(negative);
                right[1] = right[1].wrapping_add(positive);
            } else {
                right[0] = right[0].wrapping_add(positive);
                right[1] = right[1].wrapping_add(negative);
            }
        } else if let Some(value) = view.literal().and_then(|term| term.as_const()) {
            constant = constant
                .wrapping_add(value.wrapping_mul(positive))
                .wrapping_sub(value.wrapping_mul(negative));
        } else {
            let key = ScalarOperandKey::new(view);
            for (sign, count) in [(true, positive), (false, negative)] {
                if count != 0 {
                    let key = (sign, key.clone());
                    let total = atoms.get(&key).copied().unwrap_or(0u32).wrapping_add(count);
                    if total == 0 {
                        atoms.remove(&key);
                    } else {
                        atoms.insert(key, total);
                    }
                }
            }
        }
    }
    (atoms, constant)
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
#[cfg(test)]
fn collect_bitvector_affine_atoms(
    term: &MachineTerm,
    positive: bool,
    atoms: &mut Vec<(bool, MachineTerm)>,
    constant: &mut u32,
) {
    match term {
        binary_term!(Int32, Add, left, right) => {
            collect_bitvector_affine_atoms(left, positive, atoms, constant);
            collect_bitvector_affine_atoms(right, positive, atoms, constant);
        }
        binary_term!(Int32, Subtract, left, right) => {
            collect_bitvector_affine_atoms(left, positive, atoms, constant);
            collect_bitvector_affine_atoms(right, !positive, atoms, constant);
        }
        bits32_constant!(value) => {
            *constant = if positive {
                constant.wrapping_add(constant_u32(*value))
            } else {
                constant.wrapping_sub(constant_u32(*value))
            };
        }
        term => atoms.push((positive, term.clone())),
    }
}

#[cfg(test)]
fn bitvector_affine_forms_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
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

#[cfg(test)]
mod shared_antecedent_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
    };

    fn observed(format: MachineIntegerType, root: KernelTerm) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
    }

    fn bound(
        format: MachineIntegerType,
        root: KernelTerm,
        endpoint: i128,
        truth: bool,
    ) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(
                observed(format, root),
                IntegerTerm::constant(endpoint.into()),
            ),
            truth,
        )
    }

    #[test]
    fn shared_antecedents_preserve_polarity_width_and_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(997701);
        let variables = BTreeSet::from([variable]);
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let root = KernelTerm::variable(KernelType::Program(format.program_type()), variable);
            let arithmetic = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
            let exports = KernelTermExport::machine_export_count();
            let guard = Proposition::And(
                Box::new(bound(format, root.clone(), 2, false)),
                Box::new(Proposition::And(
                    Box::new(bound(format, root.clone(), 7, true)),
                    Box::new(bound(format, arithmetic, 1, true)),
                )),
            );
            if format == MachineIntegerType::Int32 {
                let ranges = antecedent_ranges(&variables, &guard).unwrap();
                assert_eq!(
                    (ranges[&variable].lower, ranges[&variable].upper),
                    (Some(3), Some(7))
                );
                assert!(uint64_antecedent_ranges(&variables, &guard).is_empty());
            } else {
                assert_eq!(
                    uint64_antecedent_ranges(&variables, &guard)[&variable],
                    (3, Some(7))
                );
                let ranges = antecedent_ranges(&variables, &guard).unwrap();
                assert_eq!(
                    (ranges[&variable].lower, ranges[&variable].upper),
                    (None, None)
                );
            }
            let disjunction = Proposition::Or(
                Box::new(bound(format, root.clone(), 2, false)),
                Box::new(bound(format, root, 7, true)),
            );
            assert!(uint64_antecedent_ranges(&variables, &disjunction).is_empty());
            let ranges = antecedent_ranges(&variables, &disjunction).unwrap();
            assert_eq!(
                (ranges[&variable].lower, ranges[&variable].upper),
                (None, None)
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/reasoning/order_reasoning/shared_antecedent_tests.rs");
    }
}

#[cfg(test)]
mod retained_cycle_tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm};

    fn observed(term: KernelTerm) -> IntegerTerm {
        IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, term).unwrap(),
        )
    }

    fn cycle(left: IntegerTerm, right: IntegerTerm, strict: bool, mirrored: bool) -> Proposition {
        let first = Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(left.clone(), right.clone()),
            true,
        );
        let second = if strict && mirrored {
            Proposition::ConditionIs(ConditionTerm::integer_less_equal(left, right), false)
        } else if strict {
            Proposition::ConditionIs(ConditionTerm::integer_less_than(right, left), true)
        } else {
            Proposition::ConditionIs(ConditionTerm::integer_less_equal(right, left), true)
        };
        Proposition::And(Box::new(first), Box::new(second))
    }

    #[test]
    fn shared_cycles_preserve_strictness_polarity_and_finite_range_boundary() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(995301));
        let root = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Multiply,
            [variable.clone(), variable],
        );
        let value = observed(root);
        let other = IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(995302))).unwrap();
        let exports = KernelTermExport::machine_export_count();
        for mirrored in [false, true] {
            assert!(
                super::super::path_facts::conjunction_order_facts_are_inconsistent(&cycle(
                    value.clone(),
                    other.clone(),
                    true,
                    mirrored
                ))
            );
        }
        assert!(
            !super::super::path_facts::conjunction_order_facts_are_inconsistent(&cycle(
                value,
                other.clone(),
                false,
                false
            ))
        );
        assert!(
            !super::super::path_facts::conjunction_order_facts_are_inconsistent(&cycle(
                IntegerTerm::constant_i64(0),
                other,
                true,
                false
            ))
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/reasoning/order_reasoning/retained_cycles.rs");
    }
}

#[cfg(test)]
mod retained_fold_endpoint_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineBinaryOp as Op,
        VerificationSession,
    };

    fn raw(op: Op, left: MachineTerm, right: MachineTerm) -> MachineTerm {
        MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    fn retained(format: MachineIntegerType, term: &MachineTerm) -> SharedMachineIntegerTerm {
        let root = KernelTermImport::default()
            .machine_arithmetic(format, term)
            .unwrap();
        let result = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
        assert!(!result.has_boxed_operand());
        result
    }

    #[test]
    fn shared_fold_affine_matching_preserves_the_native_multiset_rule() {
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(999001));
        let y = MachineTerm::Variable(Variable(999002));
        let one = MachineTerm::constant(1);
        let sum = raw(Op::Add, x.clone(), y.clone());
        let cases = [
            (
                raw(
                    Op::Add,
                    raw(Op::Subtract, x.clone(), one.clone()),
                    one.clone(),
                ),
                x.clone(),
            ),
            (sum.clone(), raw(Op::Add, y.clone(), x.clone())),
            (raw(Op::Subtract, sum.clone(), y.clone()), x.clone()),
            (raw(Op::Add, sum.clone(), one.clone()), sum.clone()),
            (
                raw(Op::Add, sum.clone(), sum.clone()),
                raw(Op::Add, sum.clone(), x.clone()),
            ),
        ];
        for (left, right) in cases {
            let a = retained(MachineIntegerType::Int32, &left);
            let b = retained(MachineIntegerType::Int32, &right);
            let exports = KernelTermExport::machine_export_count();
            let actual = retained_fold_affine_form(a.operand_view())
                == retained_fold_affine_form(b.operand_view());
            assert_eq!(actual, bitvector_affine_forms_equal(&left, &right));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn shared_fold_endpoint_equality_uses_exact_sources_at_the_index_width() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let _session = VerificationSession::enter();
            let left =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999101));
            let right =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999102));
            let left = SharedMachineIntegerTerm::from_shared(
                format,
                KernelTerm::machine_binary_shared(format, Op::Add, [left.clone(), left]),
            )
            .unwrap();
            let right = SharedMachineIntegerTerm::from_shared(
                format,
                KernelTerm::machine_binary_shared(format, Op::Add, [right.clone(), right]),
            )
            .unwrap();
            assert!(!left.has_boxed_operand() && !right.has_boxed_operand());
            let native = |variable| MachineTerm::Binary {
                format,
                op: Op::Add,
                left: Box::new(MachineTerm::Variable(variable)),
                right: Box::new(MachineTerm::Variable(variable)),
            };
            let source = ConditionTerm::machine_compare(
                format,
                CompareRelation::Equal,
                native(Variable(999102)),
                native(Variable(999101)),
            );
            let empty = PureFactContext::new();
            let cold_exports = KernelTermExport::machine_export_count();
            assert!(!exact_fold_endpoint_equality(
                format,
                left.operand_view(),
                right.operand_view(),
                &empty
            ));
            assert_eq!(KernelTermExport::machine_export_count(), cold_exports);
            let original = Proposition::ConditionIs(source.clone(), true);
            let known = empty.clone().assume_condition(source.clone(), true);
            let refuted = empty.clone().assume_condition(source, false);
            let exports = KernelTermExport::machine_export_count();
            let equal = |context: &PureFactContext| {
                exact_fold_endpoint_equality(
                    format,
                    left.operand_view(),
                    right.operand_view(),
                    context,
                )
            };
            assert!(!equal(&empty));
            let (proved, sources) =
                crate::kernel::assumptions::collect_reasoning_provenance(|| {
                    crate::kernel::assumptions::capture_implicit_reasoning_provenance(|| {
                        equal(&known)
                    })
                });
            assert!(proved, "{format:?}");
            assert_eq!(sources, vec![original.clone()]);
            assert!(!equal(&refuted));
            assert!(!equal(&empty));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    mod scaling_tests {
        use super::*;
        include!(
            "../../scaling_tests/kernel/reasoning/order_reasoning/retained_fold_endpoint_tests.rs"
        );
    }
}
