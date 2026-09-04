use super::*;

/// A memory-resolution query in progress on this thread. The resolvers are
/// mutually recursive over pointers, offsets, index terms, loads, stored
/// cells, and range facts. A query met again while it is in progress is a
/// cycle through the facts and proves nothing on that path; distinct
/// queries nest freely, bounded by the terms and facts the query connects,
/// and each is answered once per fact set by the memo below.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::kernel) enum ResolutionQuery {
    PointerDistinct(Pointer, Pointer),
    CommonBaseDistinct(Pointer, Pointer),
    PointerEqual(Pointer, Pointer),
    OffsetEqual(PointerOffsetTerm, PointerOffsetTerm),
    BitvectorEqual(Bitvector32Term, Bitvector32Term),
    SnapshotsMatch(SharedCMemory, SharedCMemory, Pointer),
    CanonicalMemory(SharedCMemory, Pointer),
    RangeDisjoint(Pointer, Pointer),
    RangesSeparate(CMemoryRange, CMemoryRange),
    RangeContained(CMemoryRange, CMemoryRange),
    PointerInRange(Pointer, Pointer, Bitvector32Term, Bitvector32Term, u32),
}

thread_local! {
    static RESOLUTION_QUERIES_IN_PROGRESS: std::cell::RefCell<BTreeSet<ResolutionQuery>> =
        const { std::cell::RefCell::new(BTreeSet::new()) };
}

/// Registers a resolution query for as long as it runs. `enter` refuses a
/// query already in progress, noting the cycle as a truncation so the memo
/// does not cache an answer the cycle weakened.
pub(in crate::kernel) struct ResolutionQueryGuard {
    query: ResolutionQuery,
}

impl ResolutionQueryGuard {
    pub(in crate::kernel) fn enter(query: ResolutionQuery) -> Option<Self> {
        let entered = RESOLUTION_QUERIES_IN_PROGRESS
            .with(|queries| queries.borrow_mut().insert(query.clone()));
        if !entered {
            crate::kernel::assumptions::note_search_truncation();
        }
        // `then`, not `then_some`: a guard built eagerly and discarded on
        // the cycle path would run `drop` and unregister the outer query.
        entered.then(|| Self { query })
    }
}

impl Drop for ResolutionQueryGuard {
    fn drop(&mut self) {
        RESOLUTION_QUERIES_IN_PROGRESS.with(|queries| {
            queries.borrow_mut().remove(&self.query);
        });
    }
}

/// A query already in progress refuses re-entry without unregistering the
/// outer query, and distinct queries nest.
#[cfg(test)]
#[test]
fn resolution_query_guard_refuses_reentry_and_keeps_the_outer_query() {
    let pointer = |index: u64| Pointer {
        block: "cell".into(),
        offset: PointerOffsetTerm::Constant(index as i64),
    };
    let first = ResolutionQuery::PointerEqual(pointer(0), pointer(1));
    let second = ResolutionQuery::PointerDistinct(pointer(0), pointer(1));
    let outer = ResolutionQueryGuard::enter(first.clone()).expect("the first query registers");
    assert!(
        ResolutionQueryGuard::enter(first.clone()).is_none(),
        "re-entering the query is a cycle"
    );
    let nested = ResolutionQueryGuard::enter(second);
    assert!(nested.is_some(), "a distinct query nests");
    drop(nested);
    assert!(
        ResolutionQueryGuard::enter(first.clone()).is_none(),
        "the refused re-entry left the outer query registered"
    );
    drop(outer);
    assert!(ResolutionQueryGuard::enter(first).is_some());
}

/// Whether the verification deadline has passed, noted as a truncation so
/// the memo does not cache the answer the deadline cut short.
pub(in crate::kernel) fn resolution_interrupted() -> bool {
    if crate::instrumentation::deadline_exceeded() {
        crate::kernel::assumptions::note_search_truncation();
        return true;
    }
    false
}

/// One top-level memory-resolution equality query, keyed by fact-set content
/// identity plus the ambient DAG-bridging mode. Hot simple steps ask the
/// same handful of pointer/term equalities dozens of times while scanning
/// facts and resource contexts; the queries are pure functions of the fact
/// set, the memory DAG, and the bridging mode, so repeats are memoizable
/// with the same discipline as `decide`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ResolutionQueryKey {
    PointerDistinct(u64, bool, Pointer, Pointer),
    PointerRangeDisjoint(u64, bool, Pointer, Pointer),
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

thread_local! {
    static CANONICAL_MEMORY_CACHE: std::cell::RefCell<
        std::collections::HashMap<(super::SharedCMemory, Pointer), CMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

pub(crate) fn clear_memory_resolution_memos() {
    RESOLUTION_QUERY_POSITIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    RESOLUTION_QUERY_NEGATIVE_MEMO.with(|memo| memo.borrow_mut().clear());
}

pub(crate) fn clear_canonical_memory_cache() {
    CANONICAL_MEMORY_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// The memo identity for one top-level resolution query, or `None` when the
/// query must run unmemoized. Unmemoized cases are the ones whose answers
/// are ambient-state-dependent: a nested arm shares the caller's fuel, a
/// nested memory-DAG cell lookup sees the depth cutoff, and explicit
/// certificate validation crosses extra DAG edges. In-progress condition
/// decisions need no guard here: every decision cycle cut and in-decision
/// weakening records a search truncation, which already blocks negative
/// caching, and a positive answer is found evidence that remains valid
/// outside the weakened context.
fn resolution_query_memo_id(assumptions: &PureFactContext) -> Option<(u64, bool)> {
    if !crate::kernel::api::memory_dag_cell_lookup_depth_is_zero() {
        return None;
    }
    if crate::kernel::api::explicit_dag_check_active() {
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
fn memoized_resolution_query(key: Option<ResolutionQueryKey>, run: impl FnOnce() -> bool) -> bool {
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

/// Memoized entry for the range-membership disjointness prover: the DAG
/// walk re-asks it per store edge per caller, and the underlying candidate
/// scan is expensive. Positive answers are found evidence; negatives cache
/// per derivation generation exactly like the other resolution queries.
/// Symmetric, so the key orders the pair.
pub(crate) fn pointers_disjoint_by_range_memoized(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let (first, second) = if left <= right {
        (left, right)
    } else {
        (right, left)
    };
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::PointerRangeDisjoint(id, bridging, first.clone(), second.clone())
    });
    memoized_resolution_query(key, || {
        assumptions.pointers_directly_disjoint_by_range(left, right)
    })
}

thread_local! {
    static BOUNDED_SNAPSHOT_COMPARISON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `body` with the whole-snapshot general-alias comparison suppressed:
/// per-cell distinctness stays on the bounded resolution check, and each
/// suppression records a search truncation so the weaker context's negative
/// answers are never memoized where the full check would have run. For
/// callers like load-variable origin bridging, whose answers must come
/// from recorded derivations and effect facts, never from whole-snapshot
/// alias search.
pub(crate) fn with_bounded_snapshot_comparison<T>(body: impl FnOnce() -> T) -> T {
    BOUNDED_SNAPSHOT_COMPARISON.with(|flag| {
        let previous = flag.get();
        flag.set(true);
        let result = body();
        flag.set(previous);
        result
    })
}

pub(crate) fn bounded_snapshot_comparison_active() -> bool {
    BOUNDED_SNAPSHOT_COMPARISON.with(std::cell::Cell::get)
}

/// Test-only: the sole caller is the fenced `prove_c_while_invariant_rule`.
/// The production loop path forks the condition through
/// `assume_condition_truthiness`, which threads facts and obligations rather
/// than collapsing them into bare `PureFactContext`.
#[cfg(test)]
pub(in crate::kernel) fn condition_contexts_for_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    desired_truthiness: bool,
) -> Vec<PureFactContext> {
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

/// Alias check used while resolving a symbolic memory load. This deliberately
/// avoids general equality transport because that transport may itself resolve
/// memory loads.
pub(in crate::kernel) fn pointers_proven_distinct_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        let (left, right) = if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        ResolutionQueryKey::PointerDistinct(id, bridging, left, right)
    });
    memoized_resolution_query(key, || {
        pointers_proven_distinct_for_memory_resolution_unmemoized(left, right, assumptions)
    })
}

fn pointers_proven_distinct_for_memory_resolution_unmemoized(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left == right || resolution_interrupted() {
        return false;
    }
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::PointerDistinct(
        left.clone(),
        right.clone(),
    )) else {
        return false;
    };
    left.blocks_proven_distinct(right)
        || crate::instrumentation::measure_operation(
            "kernel",
            "general pointer distinctness",
            "general distinctness: offset cancellation",
            || {
                pointer_offsets_with_common_base_proven_distinct_for_memory_resolution(
                    left,
                    right,
                    assumptions,
                )
            },
        )
        || crate::instrumentation::measure_operation(
            "kernel",
            "general pointer distinctness",
            "general distinctness: offset disequality",
            || {
                left.block == right.block
                    && pointer_offsets_equal_for_memory_resolution(
                        &left.offset,
                        &right.offset,
                        assumptions,
                    ) == Some(false)
            },
        )
        || assumptions
            .exact_condition_value(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(false)
        || crate::instrumentation::measure_operation(
            "kernel",
            "general pointer distinctness",
            "general distinctness: explicit range",
            || {
                assumptions
                    .pointers_proven_disjoint_by_explicit_range_for_memory_resolution(left, right)
            },
        )
}

fn pointer_offsets_with_common_base_proven_distinct_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left.block != right.block {
        return false;
    }
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::CommonBaseDistinct(
        left.clone(),
        right.clone(),
    )) else {
        return false;
    };
    let zero = PointerOffsetTerm::Constant(0);
    let offsets_equal = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
        left == right
            || pointer_offsets_proven_equal_for_memory_resolution(left, right, assumptions)
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
    if let (Some(left), Some(right)) = (left_index.as_const(), right_index.as_const()) {
        return left != right;
    }
    let Some(element_width) = common_pointer_offset_element_width(left_index, right_index) else {
        return false;
    };
    let (Some(left_index), Some(right_index)) = (
        element_index_from_offset(left_index, element_width),
        element_index_from_offset(right_index, element_width),
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
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::PointerEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        pointers_proven_equal_for_memory_resolution_unmemoized(left, right, assumptions)
    })
}

pub(in crate::kernel) fn pointer_offsets_proven_equal_for_memory_resolution(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::PointerOffsetEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        pointer_offsets_equal_for_memory_resolution(left, right, assumptions) == Some(true)
    })
}

fn pointers_proven_equal_for_memory_resolution_unmemoized(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if resolution_interrupted() {
        return false;
    }
    let Some(_query) =
        ResolutionQueryGuard::enter(ResolutionQuery::PointerEqual(left.clone(), right.clone()))
    else {
        return false;
    };
    let candidate = left.block == right.block
        && pointer_offsets_proven_equal_for_memory_resolution(
            &left.offset,
            &right.offset,
            assumptions,
        )
        || assumptions
            .exact_condition_value(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(true)
        // A loop invariant may establish an equality for a pointer local at
        // the loop head. After the loop, both the local and the argument
        // pointer can have advanced by the same proven displacement. Reuse
        // the bounded pointer congruence relation here so memory-load
        // equality sees the same certified address fact as ordinary pointer
        // simplification.
        || assumptions.has_pointer_equality_path(left, right);
    candidate
        && !assumptions
            .pointers_proven_disjoint_by_explicit_range_for_memory_resolution(left, right)
}

pub(in crate::kernel) fn pointer_offsets_equal_for_memory_resolution(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<bool> {
    if left == right {
        return Some(true);
    }
    if resolution_interrupted() {
        return None;
    }
    let Some(_query) =
        ResolutionQueryGuard::enter(ResolutionQuery::OffsetEqual(left.clone(), right.clone()))
    else {
        return None;
    };
    if let Some(value) = assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
        left.clone(),
        right.clone(),
    )) {
        return Some(value);
    }
    if let Some(element_width) = common_pointer_offset_element_width(left, right)
        && let (Some(left), Some(right)) = (
            element_index_from_offset(left, element_width),
            element_index_from_offset(right, element_width),
        )
    {
        if let (Some(left), Some(right)) = (
            crate::kernel::assumptions::exact_signed_constant(&left, assumptions),
            crate::kernel::assumptions::exact_signed_constant(&right, assumptions),
        ) {
            return Some(left == right);
        }
        if bitvector_terms_proven_equal_for_memory_resolution(&left, &right, assumptions) {
            return Some(true);
        }
        return assumptions.decide_bitvector_equality_shallow(&left, &right);
    }
    match (left.as_const(), right.as_const()) {
        (Some(left), Some(right)) => Some(left == right),
        _ => None,
    }
}

/// The value stored at `pointer` or at a pointer proven equal to it: the
/// exact cell, then one lookup per member of the element index's recorded
/// equality class, then the block's cells through the memoized pointer
/// equality query, so a pair is resolved once per fact set.
fn stored_value_at_equal_pointer(
    memory: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    if let Some(value) = memory.known_value(pointer) {
        return Some(value);
    }
    if let PointerOffsetTerm::Int32Scaled {
        value: index,
        byte_width,
    } = &pointer.offset
        && let Some(value) = assumptions
            .recorded_equality_class(index)
            .into_iter()
            .find_map(|member| {
                memory.known_value(&Pointer {
                    block: pointer.block.clone(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(member),
                        byte_width: *byte_width,
                    },
                })
            })
    {
        return Some(value);
    }
    memory
        .cells
        .iter()
        .find(|(stored, _)| {
            stored.block == pointer.block
                && pointers_proven_equal_for_memory_resolution(pointer, stored, assumptions)
        })
        .map(|(_, value)| value.clone())
}

fn bitvector_terms_equal_for_memory_resolution_unmemoized(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if let (Some(left), Some(right)) = (
        crate::kernel::assumptions::exact_signed_constant(left, assumptions),
        crate::kernel::assumptions::exact_signed_constant(right, assumptions),
    ) {
        return left == right;
    }
    if resolution_interrupted() {
        return false;
    }
    let Some(_query) =
        ResolutionQueryGuard::enter(ResolutionQuery::BitvectorEqual(left.clone(), right.clone()))
    else {
        return false;
    };
    // A load variable is its load for equality reasoning: view it
    // through the registry so snapshot provenance fires exactly as it would
    // for the load term, then fall through to the variable-form
    // paths if the load view does not decide.
    let canonical_view = |term: &Bitvector32Term| {
        if let Bitvector32Term::Variable(variable) = term {
            if let Some((memory, pointer)) =
                crate::kernel::eval::registered_load_origin_for_variable(variable)
            {
                return Some(Bitvector32Term::MemoryLoad(memory, Box::new(pointer)));
            }
        }
        None
    };
    let left_view = canonical_view(left);
    let right_view = canonical_view(right);
    if (left_view.is_some() || right_view.is_some())
        && bitvector_terms_proven_equal_for_memory_resolution(
            left_view.as_ref().unwrap_or(left),
            right_view.as_ref().unwrap_or(right),
            assumptions,
        )
    {
        return true;
    }
    // Equality facts first: the indexed, memoized walk over the context's
    // equality graph decides nearly every query any layer here decides.
    if assumptions.bitvector_terms_equal_from_facts(left, right) {
        return true;
    }
    // Two loads of one cell whose derivations resolve to the same source
    // are equal after a bounded walk over named edges, with no snapshot
    // comparison at all (see `loads_equal_along_memory_derivations`). The
    // walk applies only to two load terms of one pointer.
    if crate::kernel::api::atomic_loads_equal_along_memory_derivations(left, right, assumptions) {
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
    if let Bitvector32Term::MemoryLoad(memory, pointer) = left
        && let Some(CValue::Int32(value)) =
            stored_value_at_equal_pointer(memory, pointer, assumptions)
        && &value != left
        && bitvector_terms_proven_equal_for_memory_resolution(&value, right, assumptions)
    {
        return true;
    }
    if let Bitvector32Term::MemoryLoad(memory, pointer) = right
        && let Some(CValue::Int32(value)) =
            stored_value_at_equal_pointer(memory, pointer, assumptions)
        && &value != right
        && bitvector_terms_proven_equal_for_memory_resolution(left, &value, assumptions)
    {
        return true;
    }
    if let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right) {
        return bitvector_terms_proven_equal_for_memory_resolution(&left, &right, assumptions);
    }
    let zero = Bitvector32Term::Constant(0);
    if let Bitvector32Term::Add(base, addend) = left
        && ((bitvector_terms_proven_equal_for_memory_resolution(base, right, assumptions)
            && bitvector_terms_proven_equal_for_memory_resolution(addend, &zero, assumptions))
            || (bitvector_terms_proven_equal_for_memory_resolution(addend, right, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(base, &zero, assumptions)))
    {
        return true;
    }
    if let Bitvector32Term::Add(base, addend) = right
        && ((bitvector_terms_proven_equal_for_memory_resolution(left, base, assumptions)
            && bitvector_terms_proven_equal_for_memory_resolution(addend, &zero, assumptions))
            || (bitvector_terms_proven_equal_for_memory_resolution(left, addend, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(base, &zero, assumptions)))
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
            bitvector_terms_proven_equal_for_memory_resolution(left_a, right_a, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(left_b, right_b, assumptions)
        }
        (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) => {
            pointers_proven_equal_for_memory_resolution(left_pointer, right_pointer, assumptions)
                && memory_snapshots_match_for_resolution(
                    left_memory,
                    right_memory,
                    left_pointer,
                    assumptions,
                )
        }
        _ => false,
    }
}

pub(in crate::kernel) fn bitvector_terms_proven_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::BitvectorEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        bitvector_terms_equal_for_memory_resolution_unmemoized(left, right, assumptions)
    })
}

pub(in crate::kernel) fn c_values_proven_equal_for_memory_resolution(
    left: &CValue,
    right: &CValue,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (CValue::Void, CValue::Void) => true,
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            pointers_proven_equal_for_memory_resolution(
                left.pointer(),
                right.pointer(),
                assumptions,
            )
        }
        _ => false,
    }
}

pub(in crate::kernel) fn memories_proven_equal_for_memory_resolution(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
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
                    memory_has_materialized_load_from(left, right, pointer, assumptions)
                        || memory_has_materialized_load_from(right, left, pointer, assumptions)
                }
            }
        })
}

pub(in crate::kernel) fn memory_load_terms_equal_for_fact_transport(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let (Some(left_load), Some(right_load)) = (
        crate::kernel::eval::viewed_as_memory_load(left),
        crate::kernel::eval::viewed_as_memory_load(right),
    ) else {
        return false;
    };
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer),
    ) = (&left_load, &right_load)
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
        )
}

fn memory_snapshots_match_for_resolution(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
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
    if pointer.block.starts_with("local:") {
        return false;
    }
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::SnapshotsMatch(
        super::intern_c_memory_ref(left),
        super::intern_c_memory_ref(right),
        pointer.clone(),
    )) else {
        return false;
    };
    if memory_has_materialized_load_from(left, right, pointer, assumptions)
        || memory_has_materialized_load_from(right, left, pointer, assumptions)
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

    let differing = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "snapshot comparison: differing cells",
        || left.differing_cell_pointers(right),
    );
    differing
        .into_iter()
        .filter(|cell_pointer| !cell_pointer.block.starts_with("local:"))
        .all(|cell_pointer| {
            pointers_proven_distinct_for_memory_resolution(&cell_pointer, pointer, assumptions)
        })
}

pub(in crate::kernel) fn memory_snapshots_proven_equal_at_pointer(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    memory_snapshots_match_for_resolution(left, right, pointer, assumptions)
}

fn memory_has_materialized_load_from(
    source: &CMemory,
    materialized: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(CValue::Int32(Bitvector32Term::MemoryLoad(snapshot, load_pointer))) =
        materialized.known_value(pointer)
    else {
        return false;
    };
    pointers_proven_equal_for_memory_resolution(&load_pointer, pointer, assumptions)
        && memory_snapshots_match_for_resolution(source, &snapshot, pointer, assumptions)
}

pub(in crate::kernel) fn pointer_offsets_with_common_base_proven_distinct(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(condition) = pointer_offsets_with_common_base_distinctness_condition(left, right)
    else {
        return false;
    };
    match condition {
        ConditionTerm::Constant(value) => !value,
        condition => assumptions.decide(&condition) == Some(false),
    }
}

/// The exact scalar equality whose falsity proves two same-block pointers
/// with one structurally shared additive base are distinct.
///
/// Keeping this cancellation witness separate lets a proof-producing caller
/// retain the selected local obligation instead of repeating the alias
/// search when it later validates a memory-DAG edge.
pub(in crate::kernel) fn pointer_offsets_with_common_base_distinctness_condition(
    left: &Pointer,
    right: &Pointer,
) -> Option<ConditionTerm> {
    if left.block != right.block {
        return None;
    }
    let zero = PointerOffsetTerm::Constant(0);
    // Cancel a structurally identical additive base before comparing indices.
    // This also avoids expanding memory-derived bases during alias checks.
    let index_pair = match (&left.offset, &right.offset) {
        (
            PointerOffsetTerm::Add(left_base, left_index),
            PointerOffsetTerm::Add(right_base, right_index),
        ) if left_base == right_base => Some((left_index.as_ref(), right_index.as_ref())),
        (
            PointerOffsetTerm::Add(left_base, left_index),
            PointerOffsetTerm::Add(right_base, right_index),
        ) if left_base == right_index => Some((left_index.as_ref(), right_base.as_ref())),
        (
            PointerOffsetTerm::Add(left_base, left_index),
            PointerOffsetTerm::Add(right_base, right_index),
        ) if left_index == right_base => Some((left_base.as_ref(), right_index.as_ref())),
        (
            PointerOffsetTerm::Add(left_base, left_index),
            PointerOffsetTerm::Add(right_base, right_index),
        ) if left_index == right_index => Some((left_base.as_ref(), right_base.as_ref())),
        (PointerOffsetTerm::Add(base, index), right) if base.as_ref() == right => {
            Some((index.as_ref(), &zero))
        }
        (PointerOffsetTerm::Add(index, base), right) if base.as_ref() == right => {
            Some((index.as_ref(), &zero))
        }
        (left, PointerOffsetTerm::Add(base, index)) if left == base.as_ref() => {
            Some((&zero, index.as_ref()))
        }
        (left, PointerOffsetTerm::Add(index, base)) if left == base.as_ref() => {
            Some((&zero, index.as_ref()))
        }
        _ => None,
    };
    let Some((left_index, right_index)) = index_pair else {
        return None;
    };
    if let (Some(left), Some(right)) = (left_index.as_const(), right_index.as_const()) {
        return Some(ConditionTerm::Constant(left == right));
    }
    let Some(element_width) = common_pointer_offset_element_width(left_index, right_index) else {
        return None;
    };
    let (Some(left_index), Some(right_index)) = (
        element_index_from_offset(left_index, element_width),
        element_index_from_offset(right_index, element_width),
    ) else {
        return None;
    };
    Some(ConditionTerm::equal(left_index, right_index))
}

pub(in crate::kernel) fn pointers_proven_equal(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
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
    // Canonicalization is assumption-free and deterministic, so memoize by
    // interned snapshot identity; the intern also dedups the key storage.
    let key = (super::intern_c_memory_ref(memory), pointer.clone());
    if let Some(hit) = CANONICAL_MEMORY_CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "canonical memory for load: miss",
        || canonical_memory_for_pointer_load_uncached(memory, pointer),
    );
    CANONICAL_MEMORY_CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

fn canonical_memory_for_pointer_load_uncached(memory: &CMemory, pointer: &Pointer) -> CMemory {
    // A snapshot met again while its own canonical form is being computed
    // is a cycle through the materialized cells and stands for itself.
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::CanonicalMemory(
        super::intern_c_memory_ref(memory),
        pointer.clone(),
    )) else {
        return memory.clone();
    };
    let relevant_cells = memory
        .cells
        .iter()
        .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block)
        .collect::<Vec<_>>();
    let materialization_sources = relevant_cells
        .iter()
        .map(|(cell_pointer, value)| {
            let source = materialized_cell_source(cell_pointer, value)?;
            Some(canonical_memory_for_pointer_load(&source, cell_pointer))
        })
        .collect::<Option<Vec<_>>>();
    let common_materialization_source = materialization_sources.as_ref().and_then(|sources| {
        let first = sources.first()?;
        sources
            .iter()
            .all(|source| source == first)
            .then(|| first.clone())
    });
    let jumped = common_materialization_source.is_some();
    let mut canonical = common_materialization_source.unwrap_or_else(|| memory.clone());
    if jumped {
        // The jump rebases the load onto the cells' common source, which
        // witnesses only that the surviving cells are unchanged since that
        // source. The original memory's havoc markers must survive the
        // jump: a havoc may have written the loaded pointer itself, and
        // erasing the marker would let the canonical-equality shortcut
        // treat the load as unchanged with no frame evidence (pinned by
        // `sibling_materialization_cells_must_not_launder_a_havoc`).
        let markers = memory
            .blocks
            .iter()
            .filter(|(block, _)| block.starts_with("havoc:") || block.starts_with("call-havoc:"))
            .map(|(block, size)| (block.clone(), size.clone()))
            .collect::<Vec<_>>();
        let blocks = std::sync::Arc::make_mut(&mut canonical.blocks);
        for (block, size) in markers {
            blocks.entry(block).or_insert(size);
        }
    }
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
        CValue::Int16(_) | CValue::UInt16(_) => 2,
        CValue::Int32(_) => 4,
        CValue::UInt8(_) => 1,
        CValue::UInt32(_) => 4,
        CValue::Int64(_) | CValue::UInt64(_) => 8,
        CValue::Pointer(_) => return false,
    };
    cell_shift + cell_width <= load_shift || load_shift + MAX_SCALAR_LOAD_BYTES <= cell_shift
}

/// The source snapshot a materialization cell stands for: a cell at `p`
/// whose value is `load(source, p)`, or — with terms canonical at creation —
/// the load variable registered for a load of `p`, whose source the registry
/// records. Materialization changes which cells are concrete, not what the
/// load means.
fn materialized_cell_source(cell_pointer: &Pointer, value: &CValue) -> Option<SharedCMemory> {
    match value {
        CValue::Int16(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt16(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Int64(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt64(Bitvector32Term::MemoryLoad(source, source_pointer))
            if source_pointer.as_ref() == cell_pointer =>
        {
            Some(source.clone())
        }
        CValue::Int16(Bitvector32Term::Variable(variable))
        | CValue::UInt16(Bitvector32Term::Variable(variable))
        | CValue::Int32(Bitvector32Term::Variable(variable))
        | CValue::UInt8(Bitvector32Term::Variable(variable))
        | CValue::Int64(Bitvector32Term::Variable(variable))
        | CValue::UInt64(Bitvector32Term::Variable(variable))
            if crate::kernel::eval::is_load_variable(variable) =>
        {
            let (source, source_pointer) =
                crate::kernel::eval::registered_load_for_variable(variable)?;
            (&source_pointer == cell_pointer).then_some(source)
        }
        CValue::Void
        | CValue::Int16(_)
        | CValue::Int32(_)
        | CValue::UInt8(_)
        | CValue::UInt16(_)
        | CValue::UInt32(_)
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_) => None,
    }
}

/// The bounded-alias-only form of
/// [`memories_match_for_pointer_load_under_assumptions`]: every differing
/// cell must be provably distinct from the load through the memoized
/// resolution check alone. Used as a pre-pass before the derivation-DAG
/// walk, where paying the general composition-backed alias search per cell
/// would dominate a simple step's budget; a miss here is not a negative
/// answer, because the full comparison still runs later in the same query.
pub(in crate::kernel) fn memories_match_for_pointer_load_bounded_alias(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
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
            let value = left
                .cells
                .get(&cell_pointer)
                .or_else(|| right.cells.get(&cell_pointer));
            // A cell present on one side only, at the loaded pointer itself,
            // whose value is that side's own materialization of the load
            // (`load(source, p)` with `source` matching the other side at
            // `p`) denotes the same loaded value: materialization changes
            // which cells are concrete, not what the load means.
            if cell_pointer == *pointer {
                return value
                    .and_then(|value| materialized_cell_source(&cell_pointer, value))
                    .is_some_and(|source| {
                        memories_match_for_pointer_load(&source, left, pointer)
                            || memories_match_for_pointer_load(&source, right, pointer)
                            || crate::kernel::api::c_memories_canonically_equal(&source, left)
                            || crate::kernel::api::c_memories_canonically_equal(&source, right)
                    });
            }
            value.is_some_and(|value| {
                cell_disjoint_from_load_by_constant_offset(&cell_pointer, value, pointer)
            }) || pointers_proven_distinct_for_memory_resolution(
                &cell_pointer,
                pointer,
                assumptions,
            )
        })
}

pub(in crate::kernel) fn memories_match_for_pointer_load_under_assumptions(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
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
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "snapshot comparison: bounded alias",
                || {
                    pointers_proven_distinct_for_memory_resolution(
                        &cell_pointer,
                        pointer,
                        assumptions,
                    )
                },
            )
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
