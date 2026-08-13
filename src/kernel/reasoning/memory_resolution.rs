use super::*;

pub(in crate::kernel) const MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT: usize = 64;

/// Budget for the expensive memory-resolution edges: recursive base matching
/// inside distinctness checks and stored-cell equality scans. The store
/// provenance these support only needs shallow reasoning, and an unbounded
/// budget makes the fact-scan leaves combinatorial.
pub(in crate::kernel) const MEMORY_RESOLUTION_EXPENSIVE_DEPTH_LIMIT: usize = 8;

/// Total node budget for one top-level memory-resolution query. The
/// resolution helpers are mutually recursive across reasoning.rs and
/// assumptions.rs, and several fact-scan edges re-enter through depth-0
/// wrappers, so a per-call depth limit alone cannot bound total work. The
/// fuel is armed at each public entry point and shared by every recursive
/// step underneath it, which keeps deep linear chains (repeated loads
/// through stores) affordable while cutting off exponential branching.
/// Results stay deterministic because the budget is per query, not global.
pub(in crate::kernel) const MEMORY_RESOLUTION_NODE_BUDGET: usize = 8_000;

thread_local! {
    static MEMORY_RESOLUTION_FUEL: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// One top-level memory-resolution equality query, keyed by fact-set content
/// identity plus the ambient DAG-bridging mode. Hot simple steps ask the
/// same handful of pointer/term equalities dozens of times while scanning
/// facts and resource contexts; the queries are pure functions of the fact
/// set, the memory DAG, and the bridging mode, so repeats are memoizable
/// with the same discipline as `decide`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ResolutionQueryKey {
    PointerEqual(u64, bool, Pointer, Pointer),
    PointerOffsetEqual(u64, bool, PointerOffsetTerm, PointerOffsetTerm),
    BitvectorEqual(u64, bool, Bitvector32Term, Bitvector32Term),
}

thread_local! {
    static RESOLUTION_QUERY_POSITIVE_MEMO: std::cell::RefCell<
        std::collections::HashSet<ResolutionQueryKey>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
    static RESOLUTION_QUERY_NEGATIVE_MEMO: std::cell::RefCell<
        std::collections::HashSet<(u64, ResolutionQueryKey)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

const RESOLUTION_QUERY_MEMO_LIMIT: usize = 200_000;

/// The memo identity for one top-level resolution query, or `None` when the
/// query must run unmemoized. Unmemoized cases are the ones whose answers
/// are ambient-state-dependent: a nested arm shares the caller's fuel, a
/// nested memory-DAG cell lookup sees the depth cutoff, and explicit
/// certificate replay crosses extra DAG edges. In-progress condition
/// decisions need no guard here: every decision cycle cut and in-decision
/// weakening records a search truncation, which already blocks negative
/// caching, and a positive answer is found evidence that remains valid
/// outside the weakened context.
fn resolution_query_memo_id(assumptions: &Assumptions) -> Option<(u64, bool)> {
    if crate::kernel::assumptions::decide_memo_disabled() {
        return None;
    }
    if MEMORY_RESOLUTION_FUEL.with(|fuel| fuel.get().is_some()) {
        return None;
    }
    if !crate::kernel::api::memory_dag_cell_lookup_depth_is_zero() {
        return None;
    }
    if crate::kernel::api::explicit_dag_replay_active() {
        return None;
    }
    // Ambient scope only: content-hashing the fact set on every top-level
    // query would cost more than many of the queries themselves. Outside any
    // scope the query runs unmemoized, as before.
    let id = crate::kernel::assumptions::ambient_assumptions_memo_id(assumptions)?;
    Some((id, crate::kernel::api::extended_dag_bridging_active()))
}

/// Runs one top-level resolution query through the memo. A `true` is found
/// evidence and stays valid however the search was pruned, so it is cached
/// unconditionally. A `false` is only the absence of a connection: it is
/// cached per memory-DAG derivation generation (new faithful edges can turn
/// it true) and never when the search was truncated by ambient fuel or depth
/// guards, exactly like the `decide` memo.
fn memoized_resolution_query(
    key: Option<ResolutionQueryKey>,
    run: impl FnOnce() -> bool,
) -> bool {
    let Some(key) = key else {
        return run();
    };
    if RESOLUTION_QUERY_POSITIVE_MEMO.with(|memo| memo.borrow().contains(&key)) {
        return true;
    }
    let generation = crate::kernel::primitives::c_memory_derivation_generation();
    if RESOLUTION_QUERY_NEGATIVE_MEMO
        .with(|memo| memo.borrow().contains(&(generation, key.clone())))
    {
        return false;
    }
    let truncations_before = crate::kernel::assumptions::search_truncations();
    let result = run();
    if result {
        RESOLUTION_QUERY_POSITIVE_MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            if memo.len() >= RESOLUTION_QUERY_MEMO_LIMIT {
                memo.clear();
            }
            memo.insert(key);
        });
    } else if crate::kernel::assumptions::search_truncations() == truncations_before {
        RESOLUTION_QUERY_NEGATIVE_MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            if memo.len() >= RESOLUTION_QUERY_MEMO_LIMIT {
                memo.clear();
            }
            memo.insert((generation, key));
        });
    }
    result
}

/// Runs `body` with the memory-resolution node budget armed. Nested calls
/// (a wrapper reached from inside another query) keep the outer budget.
pub(in crate::kernel) fn with_memory_resolution_fuel<T>(body: impl FnOnce() -> T) -> T {
    MEMORY_RESOLUTION_FUEL.with(|fuel| {
        if fuel.get().is_some() {
            return body();
        }
        fuel.set(Some(MEMORY_RESOLUTION_NODE_BUDGET));
        let result = body();
        fuel.set(None);
        result
    })
}

/// Runs `body` under its own capped budget, shielding whatever budget the
/// caller had armed: the outer query sees its fuel untouched no matter what
/// `body` spends. For advisory arms (memory-DAG hop checks) that run inside
/// arbitrary resolution queries — without the shield their spending would
/// perturb fuel-coupled answers elsewhere, and certified spellings must
/// replay byte-for-byte. Deterministic: the cap is a constant, so the answer
/// depends only on the inputs.
pub(in crate::kernel) fn with_isolated_memory_resolution_fuel<T>(
    budget: usize,
    body: impl FnOnce() -> T,
) -> T {
    MEMORY_RESOLUTION_FUEL.with(|fuel| {
        let saved = fuel.get();
        fuel.set(Some(budget));
        let result = body();
        fuel.set(saved);
        result
    })
}

/// Consumes one unit of the armed budget. Returns false when the budget is
/// exhausted; callers must fail their check (never claim a proof) then.
/// Outside any armed query this is a no-op that returns true.
pub(in crate::kernel) fn consume_memory_resolution_fuel() -> bool {
    if crate::instrumentation::deadline_exceeded() {
        crate::kernel::assumptions::note_search_truncation();
        return false;
    }
    MEMORY_RESOLUTION_FUEL.with(|fuel| match fuel.get() {
        None => true,
        Some(0) => {
            crate::kernel::assumptions::note_search_truncation();
            false
        }
        Some(remaining) => {
            fuel.set(Some(remaining - 1));
            true
        }
    })
}

/// Node budget for one top-level resource containment/separation query.
/// `proves_resource_separate` scans separation facts, each check running a
/// containment search that rescans the fact set per visited resource, with
/// order-graph decisions at the leaves — quartic-shaped work that needs a
/// hard per-query bound. Armed at the resource-prover entry points.
pub(in crate::kernel) const RESOURCE_PROVER_NODE_BUDGET: usize = 5_000;

thread_local! {
    static RESOURCE_PROVER_FUEL: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

pub(in crate::kernel) fn with_resource_prover_fuel<T>(body: impl FnOnce() -> T) -> T {
    RESOURCE_PROVER_FUEL.with(|fuel| {
        if fuel.get().is_some() {
            return body();
        }
        fuel.set(Some(RESOURCE_PROVER_NODE_BUDGET));
        let result = body();
        fuel.set(None);
        result
    })
}

pub(in crate::kernel) fn consume_resource_prover_fuel() -> bool {
    if crate::instrumentation::deadline_exceeded() {
        crate::kernel::assumptions::note_search_truncation();
        return false;
    }
    RESOURCE_PROVER_FUEL.with(|fuel| match fuel.get() {
        None => true,
        Some(0) => {
            crate::kernel::assumptions::note_search_truncation();
            false
        }
        Some(remaining) => {
            fuel.set(Some(remaining - 1));
            true
        }
    })
}

/// Test-only: the sole caller is the fenced `prove_c_while_invariant_rule`.
/// The production loop path forks the condition through
/// `assume_condition_truthiness`, which threads facts and obligations rather
/// than collapsing them into bare `Assumptions`.
#[cfg(test)]
pub(in crate::kernel) fn condition_contexts_for_truthiness(
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

pub(in crate::kernel) fn pointers_proven_distinct(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return false;
    }
    left.blocks_proven_distinct(right)
        || assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution(left, right)
        || pointer_offsets_with_common_base_proven_distinct(left, right, assumptions)
        || left.block == right.block
            && assumptions.decide(&ConditionTerm::pointer_offset_equal(
                left.offset.clone(),
                right.offset.clone(),
            )) == Some(false)
        || assumptions.decide(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(false)
        || assumptions.pointers_proven_disjoint_by_range(left, right)
}

/// Alias check used while resolving a symbolic memory load. This deliberately
/// avoids general equality transport because that transport may itself resolve
/// memory loads.
pub(in crate::kernel) fn pointers_proven_distinct_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    with_memory_resolution_fuel(|| {
        pointers_proven_distinct_for_memory_resolution_with_depth(left, right, assumptions, 0)
    })
}

fn pointers_proven_distinct_for_memory_resolution_with_depth(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if left == right
        || depth > MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT
        || !consume_memory_resolution_fuel()
    {
        return false;
    }
    left.blocks_proven_distinct(right)
        || pointer_offsets_with_common_base_proven_distinct_for_memory_resolution(
            left,
            right,
            assumptions,
            depth + 1,
        )
        || left.block == right.block
            && pointer_offsets_equal_for_memory_resolution(
                &left.offset,
                &right.offset,
                assumptions,
                depth + 1,
            ) == Some(false)
        || assumptions
            .exact_condition_value(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(false)
        || assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution_with_depth(
            left,
            right,
            depth + 1,
        )
}

fn pointer_offsets_with_common_base_proven_distinct_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if depth > MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT || left.block != right.block {
        return false;
    }
    let zero = PointerOffsetTerm::Constant(0);
    let offsets_equal = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
        left == right
            || depth <= MEMORY_RESOLUTION_EXPENSIVE_DEPTH_LIMIT
                && pointer_offsets_equal_for_memory_resolution(left, right, assumptions, depth + 1)
                    == Some(true)
    };
    let index_pair = match (&left.offset, &right.offset) {
        (
            PointerOffsetTerm::Add(left_base, left_index),
            PointerOffsetTerm::Add(right_base, right_index),
        ) => {
            if offsets_equal(left_base, right_base) {
                Some((left_index.as_ref(), right_index.as_ref()))
            } else if offsets_equal(left_base, right_index) {
                Some((left_index.as_ref(), right_base.as_ref()))
            } else if offsets_equal(left_index, right_base) {
                Some((left_base.as_ref(), right_index.as_ref()))
            } else if offsets_equal(left_index, right_index) {
                Some((left_base.as_ref(), right_base.as_ref()))
            } else {
                None
            }
        }
        (PointerOffsetTerm::Add(base, index), right) if offsets_equal(base, right) => {
            Some((index.as_ref(), &zero))
        }
        (PointerOffsetTerm::Add(index, base), right) if offsets_equal(base, right) => {
            Some((index.as_ref(), &zero))
        }
        (left, PointerOffsetTerm::Add(base, index)) if offsets_equal(left, base) => {
            Some((&zero, index.as_ref()))
        }
        (left, PointerOffsetTerm::Add(index, base)) if offsets_equal(left, base) => {
            Some((&zero, index.as_ref()))
        }
        _ => None,
    };
    let Some((left_index, right_index)) = index_pair else {
        return false;
    };
    let (Some(left_index), Some(right_index)) = (
        int32_element_index_from_offset(left_index),
        int32_element_index_from_offset(right_index),
    ) else {
        return false;
    };

    assumptions.decide_bitvector_equality_shallow(&left_index, &right_index) == Some(false)
        || assumptions.proves_order_condition_for_memory_resolution(
            &ConditionTerm::signed_less_than(left_index.clone(), right_index.clone()),
            true,
        )
        || assumptions.proves_order_condition_for_memory_resolution(
            &ConditionTerm::signed_less_than(right_index, left_index),
            true,
        )
}

pub(in crate::kernel) fn pointers_proven_equal_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::PointerEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        with_memory_resolution_fuel(|| {
            pointers_proven_equal_for_memory_resolution_with_depth(left, right, assumptions, 0)
        })
    })
}

pub(in crate::kernel) fn pointer_offsets_proven_equal_for_memory_resolution(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::PointerOffsetEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        with_memory_resolution_fuel(|| {
            pointer_offsets_equal_for_memory_resolution(left, right, assumptions, 0) == Some(true)
        })
    })
}

pub(in crate::kernel) fn pointers_proven_equal_for_memory_resolution_with_depth(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if depth > MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT || !consume_memory_resolution_fuel() {
        return false;
    }
    if left == right {
        return true;
    }
    let candidate = left.block == right.block
        && pointer_offsets_equal_for_memory_resolution(
            &left.offset,
            &right.offset,
            assumptions,
            depth + 1,
        ) == Some(true)
        || assumptions
            .exact_condition_value(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(true);
    candidate
        && !assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution_with_depth(
            left,
            right,
            depth + 1,
        )
}

pub(in crate::kernel) fn pointer_offsets_equal_for_memory_resolution(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
    depth: usize,
) -> Option<bool> {
    if depth > MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT || !consume_memory_resolution_fuel() {
        return None;
    }
    if left == right {
        return Some(true);
    }
    if let Some(value) = assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
        left.clone(),
        right.clone(),
    )) {
        return Some(value);
    }
    if let (Some(left), Some(right)) = (
        int32_element_index_from_offset(left),
        int32_element_index_from_offset(right),
    ) {
        if bitvector_terms_equal_for_memory_resolution(&left, &right, assumptions, depth + 1) {
            return Some(true);
        }
        return assumptions.decide_bitvector_equality_shallow(&left, &right);
    }
    match (left.as_const(), right.as_const()) {
        (Some(left), Some(right)) => Some(left == right),
        _ => None,
    }
}

fn bitvector_terms_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if left == right {
        return true;
    }
    if !consume_memory_resolution_fuel() {
        return false;
    }
    // Ask the memory DAG before canonicalizing anything. Two loads of one
    // cell whose derivations resolve to the same source are equal after a
    // bounded walk over named edges, with no snapshot comparison at all;
    // canonicalization below is the fallback for everything the walk cannot
    // reach (see `loads_equal_along_memory_derivations`).
    if crate::kernel::api::atomic_loads_equal_along_memory_derivations(left, right, assumptions) {
        return true;
    }
    // Deep canonicalization covers every term variant, including folds and
    // conditionals the structural arms below do not descend into; two
    // spellings of one value differing only representationally compare
    // equal here. Both calls are memoized. Pathologically deep terms skip
    // this arm: canonicalization and memo hashing recurse structurally.
    const CANONICAL_COMPARE_DEPTH_LIMIT: usize = 64;
    if !crate::kernel::api::bitvector_term_deeper_than(left, CANONICAL_COMPARE_DEPTH_LIMIT)
        && !crate::kernel::api::bitvector_term_deeper_than(right, CANONICAL_COMPARE_DEPTH_LIMIT)
        && crate::kernel::api::canonicalize_atomic_loads(left)
            == crate::kernel::api::canonicalize_atomic_loads(right)
    {
        return true;
    }
    if assumptions.bitvector_terms_equal_from_facts(left, right) {
        return true;
    }
    if [1, 4].into_iter().any(|byte_width| {
        assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(left.clone(), byte_width),
            PointerOffsetTerm::scale_int32(right.clone(), byte_width),
        )) == Some(true)
    }) {
        return true;
    }
    if depth > MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT {
        return false;
    }
    if let Bitvector32Term::MemoryLoad(memory, pointer) = left
        && let Some(CValue::Int32(value)) = memory.known_value(pointer)
        && &value != left
        && bitvector_terms_equal_for_memory_resolution(&value, right, assumptions, depth + 1)
    {
        return true;
    }
    if depth <= MEMORY_RESOLUTION_EXPENSIVE_DEPTH_LIMIT
        && let Bitvector32Term::MemoryLoad(memory, pointer) = left
        && let Some((_, CValue::Int32(value))) = memory.cells.iter().find(|(stored_pointer, _)| {
            stored_pointer.block == pointer.block
                && pointers_proven_equal_for_memory_resolution_with_depth(
                    pointer,
                    stored_pointer,
                    assumptions,
                    depth + 1,
                )
        })
        && value != left
        && bitvector_terms_equal_for_memory_resolution(value, right, assumptions, depth + 1)
    {
        return true;
    }
    if let Bitvector32Term::MemoryLoad(memory, pointer) = right
        && let Some(CValue::Int32(value)) = memory.known_value(pointer)
        && &value != right
        && bitvector_terms_equal_for_memory_resolution(left, &value, assumptions, depth + 1)
    {
        return true;
    }
    if depth <= MEMORY_RESOLUTION_EXPENSIVE_DEPTH_LIMIT
        && let Bitvector32Term::MemoryLoad(memory, pointer) = right
        && let Some((_, CValue::Int32(value))) = memory.cells.iter().find(|(stored_pointer, _)| {
            stored_pointer.block == pointer.block
                && pointers_proven_equal_for_memory_resolution_with_depth(
                    pointer,
                    stored_pointer,
                    assumptions,
                    depth + 1,
                )
        })
        && value != right
        && bitvector_terms_equal_for_memory_resolution(left, value, assumptions, depth + 1)
    {
        return true;
    }
    if let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right) {
        return bitvector_terms_equal_for_memory_resolution(&left, &right, assumptions, depth + 1);
    }
    let zero = Bitvector32Term::Constant(0);
    if let Bitvector32Term::Add(base, addend) = left
        && ((bitvector_terms_equal_for_memory_resolution(base, right, assumptions, depth + 1)
            && bitvector_terms_equal_for_memory_resolution(addend, &zero, assumptions, depth + 1))
            || (bitvector_terms_equal_for_memory_resolution(addend, right, assumptions, depth + 1)
                && bitvector_terms_equal_for_memory_resolution(
                    base,
                    &zero,
                    assumptions,
                    depth + 1,
                )))
    {
        return true;
    }
    if let Bitvector32Term::Add(base, addend) = right
        && ((bitvector_terms_equal_for_memory_resolution(left, base, assumptions, depth + 1)
            && bitvector_terms_equal_for_memory_resolution(addend, &zero, assumptions, depth + 1))
            || (bitvector_terms_equal_for_memory_resolution(left, addend, assumptions, depth + 1)
                && bitvector_terms_equal_for_memory_resolution(
                    base,
                    &zero,
                    assumptions,
                    depth + 1,
                )))
    {
        return true;
    }

    match (left, right) {
        (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
        | (
            Bitvector32Term::Subtract(left_a, left_b),
            Bitvector32Term::Subtract(right_a, right_b),
        )
        | (
            Bitvector32Term::Multiply(left_a, left_b),
            Bitvector32Term::Multiply(right_a, right_b),
        ) => {
            bitvector_terms_equal_for_memory_resolution(left_a, right_a, assumptions, depth + 1)
                && bitvector_terms_equal_for_memory_resolution(
                    left_b,
                    right_b,
                    assumptions,
                    depth + 1,
                )
        }
        (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) => {
            pointers_proven_equal_for_memory_resolution_with_depth(
                left_pointer,
                right_pointer,
                assumptions,
                depth + 1,
            ) && memory_snapshots_match_for_resolution(
                left_memory,
                right_memory,
                left_pointer,
                assumptions,
                depth + 1,
            )
        }
        _ => false,
    }
}

pub(in crate::kernel) fn bitvector_terms_proven_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::BitvectorEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        with_memory_resolution_fuel(|| {
            bitvector_terms_equal_for_memory_resolution(left, right, assumptions, 0)
        })
    })
}

pub(in crate::kernel) fn c_values_proven_equal_for_memory_resolution(
    left: &CValue,
    right: &CValue,
    assumptions: &Assumptions,
) -> bool {
    match (left, right) {
        (CValue::Void, CValue::Void) => true,
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        _ => false,
    }
}

pub(in crate::kernel) fn memories_proven_equal_for_memory_resolution(
    left: &CMemory,
    right: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
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
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| !pointer.block.starts_with("local:"))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .all(|pointer| {
            let left_value = left.known_value(pointer);
            let right_value = right.known_value(pointer);
            match (&left_value, &right_value) {
                (Some(left), Some(right)) => {
                    c_values_proven_equal_for_memory_resolution(left, right, assumptions)
                }
                (None, None) => true,
                _ => {
                    memory_has_materialized_load_from(left, right, pointer, assumptions, 0)
                        || memory_has_materialized_load_from(right, left, pointer, assumptions, 0)
                }
            }
        })
}

pub(in crate::kernel) fn memory_load_terms_equal_for_fact_transport(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer),
    ) = (left, right)
    else {
        return false;
    };
    (pointers_proven_equal_for_memory_resolution(left_pointer, right_pointer, assumptions)
        || left_pointer.block == right_pointer.block
            && assumptions
                .has_pointer_offset_snapshot_fact(&left_pointer.offset, &right_pointer.offset))
        && memory_snapshots_match_for_resolution(
            left_memory,
            right_memory,
            left_pointer,
            assumptions,
            0,
        )
}

fn memory_snapshots_match_for_resolution(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if canonical_memory_for_pointer_load(left, pointer)
        == canonical_memory_for_pointer_load(right, pointer)
    {
        return true;
    }
    if assumptions
        .memory_snapshots_directly_proven_equal_for_memory_resolution(left, right, pointer)
    {
        return true;
    }
    if depth > MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT || pointer.block.starts_with("local:") {
        return false;
    }
    if memory_has_materialized_load_from(left, right, pointer, assumptions, depth + 1)
        || memory_has_materialized_load_from(right, left, pointer, assumptions, depth + 1)
    {
        return true;
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
        .all(|cell_pointer| {
            pointers_proven_distinct_for_memory_resolution_with_depth(
                &cell_pointer,
                pointer,
                assumptions,
                depth + 1,
            )
        })
}

pub(in crate::kernel) fn memory_snapshots_proven_equal_at_pointer(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    memory_snapshots_match_for_resolution(left, right, pointer, assumptions, 0)
}

fn memory_has_materialized_load_from(
    source: &CMemory,
    materialized: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    let Some(CValue::Int32(Bitvector32Term::MemoryLoad(snapshot, load_pointer))) =
        materialized.known_value(pointer)
    else {
        return false;
    };
    pointers_proven_equal_for_memory_resolution_with_depth(
        &load_pointer,
        pointer,
        assumptions,
        depth + 1,
    ) && memory_snapshots_match_for_resolution(source, &snapshot, pointer, assumptions, depth + 1)
}

pub(in crate::kernel) fn pointer_offsets_with_common_base_proven_distinct(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if left.block != right.block {
        return false;
    }
    let (
        PointerOffsetTerm::Add(left_base, left_index),
        PointerOffsetTerm::Add(right_base, right_index),
    ) = (&left.offset, &right.offset)
    else {
        return false;
    };
    // Cancel a structurally identical additive base before comparing indices.
    // This also avoids expanding memory-derived bases during alias checks.
    let index_pair = if left_base == right_base {
        Some((left_index.as_ref(), right_index.as_ref()))
    } else if left_base == right_index {
        Some((left_index.as_ref(), right_base.as_ref()))
    } else if left_index == right_base {
        Some((left_base.as_ref(), right_index.as_ref()))
    } else if left_index == right_index {
        Some((left_base.as_ref(), right_base.as_ref()))
    } else {
        None
    };
    let Some((left_index, right_index)) = index_pair else {
        return false;
    };
    let (Some(left_index), Some(right_index)) = (
        int32_element_index_from_offset(left_index),
        int32_element_index_from_offset(right_index),
    ) else {
        return false;
    };
    assumptions.decide(&ConditionTerm::equal(left_index, right_index)) == Some(false)
}

pub(in crate::kernel) fn pointers_proven_equal(
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

pub(in crate::kernel) fn memories_match_for_pointer_load(
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

    memory_havoc_markers(left).eq(memory_havoc_markers(right))
        && left.blocks.get(&pointer.block) == right.blocks.get(&pointer.block)
        && left
            .cells
            .iter()
            .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block)
            .eq(right
                .cells
                .iter()
                .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block))
}

fn memory_havoc_markers(memory: &CMemory) -> impl Iterator<Item = (&PointerBlock, &CBlock)> {
    memory
        .blocks
        .iter()
        .filter(|(block, _)| block.starts_with("havoc:") || block.starts_with("call-havoc:"))
}

/// Returns a canonical representation of the portion of memory observable by
/// one atomic load. Unrelated blocks cannot affect the load. A block made only
/// of cached loads from one common source is observationally that source, so
/// collapse it before discarding unrelated blocks. Loop and call havoc markers
/// are global snapshot identities, so they remain observable at every
/// non-local pointer until an explicit effect fact frames that pointer.
pub(in crate::kernel) fn canonical_memory_for_pointer_load(
    memory: &CMemory,
    pointer: &Pointer,
) -> CMemory {
    thread_local! {
        static CACHE: std::cell::RefCell<
            std::collections::HashMap<(super::SharedCMemory, Pointer), CMemory>,
        > = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    // Canonicalization is assumption-free and deterministic, so memoize by
    // interned snapshot identity; the intern also dedups the key storage.
    let key = (super::intern_c_memory_ref(memory), pointer.clone());
    if let Some(hit) = CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = canonical_memory_for_pointer_load_with_depth(memory, pointer, 0);
    CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

/// Canonicalization keyed by an already-interned snapshot: the cache lookup
/// hashes and compares by interned identity, with no re-interning, no
/// structural hash, and no clone on the hit path.
pub(in crate::kernel) fn canonical_memory_for_shared_pointer_load(
    memory: &super::SharedCMemory,
    pointer: &Pointer,
) -> CMemory {
    thread_local! {
        static CACHE: std::cell::RefCell<
            std::collections::HashMap<(super::SharedCMemory, Pointer), CMemory>,
        > = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    let key = (memory.clone(), pointer.clone());
    if let Some(hit) = CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = canonical_memory_for_pointer_load_with_depth(memory, pointer, 0);
    CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

fn canonical_memory_for_pointer_load_with_depth(
    memory: &CMemory,
    pointer: &Pointer,
    depth: usize,
) -> CMemory {
    if depth >= MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT {
        return memory.clone();
    }
    let relevant_cells = memory
        .cells
        .iter()
        .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block)
        .collect::<Vec<_>>();
    let materialization_sources = relevant_cells
        .iter()
        .map(|(cell_pointer, value)| {
            let source = materialized_cell_source(cell_pointer, value)?;
            Some(canonical_memory_for_pointer_load_with_depth(
                source,
                cell_pointer,
                depth + 1,
            ))
        })
        .collect::<Option<Vec<_>>>();
    let common_materialization_source = materialization_sources.as_ref().and_then(|sources| {
        let first = sources.first()?;
        sources
            .iter()
            .all(|source| source == first)
            .then(|| first.clone())
    });
    let mut canonical = common_materialization_source.unwrap_or_else(|| memory.clone());
    std::sync::Arc::make_mut(&mut canonical.blocks).retain(|block, _| {
        block == &pointer.block || block.starts_with("havoc:") || block.starts_with("call-havoc:")
    });
    std::sync::Arc::make_mut(&mut canonical.cells).retain(|cell_pointer, value| {
        cell_pointer.block == pointer.block
            && !cell_disjoint_from_load_by_constant_offset(cell_pointer, value, pointer)
    });
    canonical
}

/// The widest scalar load the kernel performs; assuming it when the true
/// width is unknown only ever shrinks the provable-disjoint set.
const MAX_SCALAR_LOAD_BYTES: i64 = 4;

/// Splits a pointer offset into its non-constant atoms and total constant
/// byte shift, folding constants nested inside scaled indices.
pub(in crate::kernel) fn offset_atoms_and_constant(
    offset: &PointerOffsetTerm,
) -> (Vec<PointerOffsetTerm>, i64) {
    fn collect(offset: &PointerOffsetTerm, atoms: &mut Vec<PointerOffsetTerm>, shift: &mut i64) {
        match offset {
            PointerOffsetTerm::Constant(value) => *shift += *value,
            PointerOffsetTerm::Add(left, right) => {
                collect(left, atoms, shift);
                collect(right, atoms, shift);
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                if let Some((base, constant)) = value.add_const_parts() {
                    *shift += (constant as i32 as i64) * *byte_width;
                    atoms.push(PointerOffsetTerm::Int32Scaled {
                        value: Box::new(base),
                        byte_width: *byte_width,
                    });
                } else if let Some((base, constant)) = value.subtract_const_parts() {
                    *shift -= (constant as i32 as i64) * *byte_width;
                    atoms.push(PointerOffsetTerm::Int32Scaled {
                        value: Box::new(base),
                        byte_width: *byte_width,
                    });
                } else {
                    atoms.push(offset.clone());
                }
            }
            other => atoms.push(other.clone()),
        }
    }
    let mut atoms = Vec::new();
    let mut shift = 0;
    collect(offset, &mut atoms, &mut shift);
    atoms.sort();
    (atoms, shift)
}

/// True when a cached cell provably cannot alias the loaded pointer because
/// both offsets share the same non-constant atoms and their constant byte
/// intervals are disjoint. This needs no assumptions, so canonicalization
/// may drop the cell for any load width up to [`MAX_SCALAR_LOAD_BYTES`].
fn cell_disjoint_from_load_by_constant_offset(
    cell_pointer: &Pointer,
    value: &CValue,
    load_pointer: &Pointer,
) -> bool {
    let (cell_atoms, cell_shift) = offset_atoms_and_constant(&cell_pointer.offset);
    let (load_atoms, load_shift) = offset_atoms_and_constant(&load_pointer.offset);
    if cell_atoms != load_atoms {
        return false;
    }
    let cell_width = match value {
        CValue::Void => return false,
        CValue::Int32(_) => 4,
        CValue::UInt8(_) => 1,
        CValue::Pointer(_) => return false,
    };
    cell_shift + cell_width <= load_shift || load_shift + MAX_SCALAR_LOAD_BYTES <= cell_shift
}

fn materialized_cell_source<'a>(cell_pointer: &Pointer, value: &'a CValue) -> Option<&'a CMemory> {
    match value {
        CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer))
            if source_pointer.as_ref() == cell_pointer =>
        {
            Some(source)
        }
        CValue::Void | CValue::Int32(_) | CValue::UInt8(_) | CValue::Pointer(_) => None,
    }
}

pub(in crate::kernel) fn memories_match_for_pointer_load_under_assumptions(
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
        .all(|cell_pointer| {
            // Inside a condition decision only the bounded resolution check
            // is safe: the general distinctness check consults `decide`,
            // whose order-fact matching resolves memory loads and re-enters
            // this function, forming an unbounded cycle. Suppressing the
            // general check weakens the search, so record a truncation: a
            // negative answer from this weaker context must not be memoized
            // and replayed where the full check would have run.
            pointers_proven_distinct_for_memory_resolution(&cell_pointer, pointer, assumptions)
                || if crate::kernel::assumptions::inside_condition_decision() {
                    crate::kernel::assumptions::note_search_truncation();
                    false
                } else {
                    pointers_proven_distinct(&cell_pointer, pointer, assumptions)
                }
        })
}

pub(in crate::kernel) fn memory_matches_effect_summary_endpoint(
    expected: &CMemory,
    actual: &CMemory,
    pointer: &Pointer,
) -> bool {
    expected == actual || memories_match_for_pointer_load(expected, actual, pointer)
}

pub(in crate::kernel) fn collect_memory_effect_write_pointers(
    facts: &[ExecutionPureFact],
) -> BTreeSet<Pointer> {
    // Concrete stores certify exact pointers. Abstract calls and loops certify
    // ranges separately through CMemoryEffectSummary; comparing endpoint
    // memories would mistake join abstraction and call havoc for writes.
    let mut writes = BTreeSet::new();
    for fact in facts {
        if let Proposition::CMemoryMutatesOnly { pointers, .. } = fact.proposition() {
            writes.extend(pointers.iter().cloned());
        }
    }

    writes
}
