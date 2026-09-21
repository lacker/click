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
            crate::kernel::assumptions::note_incomplete_reasoning();
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
    crate::kernel::assumptions::reasoning_interrupted()
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
    /// The producer-known source of one canonical load projection. The
    /// projected snapshot is intentionally not given an ordinary memory-DAG
    /// derivation: one interned projection can be shared by several sources.
    /// This pointer-specific preferred edge preserves the oldest known sound
    /// source for checked load equality without pretending the projection has
    /// a unique memory parent.
    static CANONICAL_LOAD_PROJECTION_SOURCES: std::cell::RefCell<
        std::collections::HashMap<(super::SharedCMemory, Pointer), super::SharedCMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Every exact producer-known projection triple. Evidence checks this
    /// durable set rather than requiring its selected source to remain the
    /// preferred source if an older equivalent producer is registered later.
    static CANONICAL_LOAD_PROJECTIONS: std::cell::RefCell<
        std::collections::HashSet<(super::SharedCMemory, super::SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

pub(crate) fn clear_memory_resolution_memos() {
    RESOLUTION_QUERY_POSITIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    RESOLUTION_QUERY_NEGATIVE_MEMO.with(|memo| memo.borrow_mut().clear());
}

pub(crate) fn clear_canonical_memory_cache() {
    CANONICAL_MEMORY_CACHE.with(|cache| cache.borrow_mut().clear());
    CANONICAL_LOAD_PROJECTION_SOURCES.with(|sources| sources.borrow_mut().clear());
    CANONICAL_LOAD_PROJECTIONS.with(|projections| projections.borrow_mut().clear());
}

/// Records the exact source used when load canonicalization constructs a
/// pointer-observable projection. This is provenance, not a cache: checked
/// evidence later names this exact edge and validates it by identity, without
/// rescanning either snapshot. A canonical projection can be interned from
/// multiple equivalent sources, so all exact triples remain valid while the
/// oldest arena node is kept as the constant-time lookup preference.
pub(in crate::kernel) fn record_canonical_load_projection(
    source: &super::SharedCMemory,
    projected: &super::SharedCMemory,
    pointer: &Pointer,
) {
    if source == projected {
        return;
    }
    CANONICAL_LOAD_PROJECTIONS.with(|projections| {
        projections
            .borrow_mut()
            .insert((source.clone(), projected.clone(), pointer.clone()));
    });
    CANONICAL_LOAD_PROJECTION_SOURCES.with(|sources| {
        let mut sources = sources.borrow_mut();
        let preferred = sources
            .entry((projected.clone(), pointer.clone()))
            .or_insert_with(|| source.clone());
        if source.arena_id() < preferred.arena_id() {
            *preferred = source.clone();
        }
    });
}

/// Returns the retained source for an exact canonical projection endpoint.
/// The lookup is constant-time in the number of projections and never
/// reconstructs the canonical form.
pub(in crate::kernel) fn canonical_load_projection_source(
    projected: &super::SharedCMemory,
    pointer: &Pointer,
) -> Option<super::SharedCMemory> {
    CANONICAL_LOAD_PROJECTION_SOURCES.with(|sources| {
        sources
            .borrow()
            .get(&(projected.clone(), pointer.clone()))
            .cloned()
    })
}

pub(in crate::kernel) fn canonical_load_projection_recorded(
    source: &super::SharedCMemory,
    projected: &super::SharedCMemory,
    pointer: &Pointer,
) -> bool {
    CANONICAL_LOAD_PROJECTIONS.with(|projections| {
        projections
            .borrow()
            .contains(&(source.clone(), projected.clone(), pointer.clone()))
    })
}

/// The memo identity for one top-level resolution query, or `None` when the
/// query must run unmemoized. Unmemoized cases are the ones whose answers
/// are ambient-state-dependent: a nested memory-DAG cell lookup sees an
/// active lookup, and explicit proof validation crosses extra DAG edges.
/// In-progress condition decisions need no guard here: every decision cycle
/// cut records incomplete reasoning, which already blocks negative
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
/// it true) and never after an exact cycle cut or an observed verification
/// limit, exactly like the `decide` memo.
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
    let epoch_before = crate::kernel::assumptions::incomplete_reasoning_epoch();
    let result = run();
    if result {
        RESOLUTION_QUERY_POSITIVE_MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            if memo.len() >= RESOLUTION_QUERY_MEMO_LIMIT {
                memo.clear();
            }
            memo.insert(key);
        });
    } else if crate::kernel::assumptions::incomplete_reasoning_epoch() == epoch_before {
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

#[cfg(test)]
#[test]
fn expired_nested_reasoning_does_not_poison_resolution_memo() {
    // Surface planning; only this test reaches it from inside the kernel.
    use crate::surface::planning::proposition_search::PropositionSearch;
    clear_memory_resolution_memos();
    let key = ResolutionQueryKey::BitvectorEqual(
        7_490_001,
        false,
        Bitvector32Term::Variable(Variable(7_490_002)),
        Bitvector32Term::Constant(1),
    );
    // Expiry occurs inside the memo boundary, including at a helper which
    // formerly called the raw deadline checkpoint without recording a cut.
    assert!(!memoized_resolution_query(Some(key.clone()), || {
        crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            let assumptions = PureFactContext::new();
            assumptions.proves(&Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            ))
        })
    }));
    assert!(memoized_resolution_query(Some(key.clone()), || true));
    assert!(memoized_resolution_query(Some(key), || panic!(
        "positive result should be cached"
    )));
    clear_memory_resolution_memos();
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
        || crate::instrumentation::measure_operation(
            "kernel",
            "general pointer distinctness",
            "general distinctness: exact alias hop",
            || pointers_distinct_through_one_exact_alias(left, right, assumptions),
        )
        || crate::instrumentation::measure_operation(
            "kernel",
            "general pointer distinctness",
            "general distinctness: never-address-taken local",
            || never_address_taken_local_versus_pointer_value(left, right, assumptions),
        )
}

/// Whether one side is an automatic object whose address the program never
/// takes, and the other is a pointer value the verifier has not resolved.
///
/// This is what frames the commonest read of all. `p = f(); … p[0]` stores the
/// returned pointer into the caller's own `p`, and that store is itself a step
/// the read has to be told apart from; no contract can say anything about it,
/// because `p` belongs to the caller of the function whose contract is being
/// written. Structure says nothing either: a `Symbolic` block is proven
/// distinct from nothing.
///
/// The claim is about *addressability*, and it is made once for the whole
/// session by the registry behind
/// [`crate::kernel::primitives::block_is_never_address_taken_local`], whose
/// soundness argument is on that function: an object whose name is never
/// declared with an aggregate type and never appears under `&` in any function
/// body has no address any C value in this program can hold, so no pointer
/// value designates it. That is why `local_versus_argument` in
/// `PointerBlock::proven_distinct` can stay the narrower structural rule and
/// this one lives here, where the assumptions are in scope.
///
/// Deferring to what the context states is the other half of the rule, and it
/// is not an optimization. An equality the context *assumes* between the
/// pointer and this very object would be refuted by the paragraph above, and a
/// refuted assumption is an inconsistent context, from which everything
/// follows. So when any exact equality places the pointer in this object's
/// block, this rule declines and leaves the answer to
/// [`pointers_distinct_through_one_exact_alias`], which substitutes the
/// equality instead of contradicting it. Today such an equality can only be
/// established, never assumed — every surface form that introduces one proves
/// it first — so the guard is a second lock on a door that is already shut.
///
/// Boundedness: one registry lookup on a name of bounded length, plus the one
/// keyed alias lookup the guard needs. No fact-set scan, no walk.
fn never_address_taken_local_versus_pointer_value(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let separated = |local: &Pointer, value: &Pointer| {
        if !matches!(value.block, PointerBlock::Symbolic(_))
            || !crate::kernel::primitives::block_is_never_address_taken_local(&local.block)
        {
            return false;
        }
        crate::instrumentation::record_deterministic_work(1);
        // Defer to a stated equality that puts the pointer in this object.
        !assumptions
            .exact_pointer_aliases(value)
            .any(|alias| alias.block == local.block)
    };
    separated(left, right) || separated(right, left)
}

/// Whether one exact pointer equality resolves an unresolved pointer to an
/// address the program names, and *that* address is proven distinct from the
/// other one.
///
/// A `Symbolic` block is a pointer value, not an object the function can name:
/// [`PointerBlock::proven_distinct`] separates it from nothing at all, so a
/// load through a pointer a call returned is framed only by evidence. The most
/// direct evidence a contract can state is where the pointer points --
/// `ensures result == &g[0]`, `ensures result == p` -- and this is the rule
/// that spends it. Without it, the honest `observable_by_load` keeps every
/// cell in the question and the stated equality never gets a say.
///
/// Soundness. `exact_pointer_aliases` reads the index of *assumed*
/// `PointerEqual` facts: never a derived, heuristic or disjunctive conclusion,
/// and never a `!=`. Two pointers such a fact relates are one address, so a
/// pointer proven distinct from one is proven distinct from the other; that is
/// substitution of equals, not a new separation claim.
/// `ConditionTerm::pointer_equal` folds an equality between two offsets of one
/// block to a `PointerOffsetEqual`, which is not a `PointerEqual` at all, so an
/// entry can only ever exchange two spellings of *one* address and never shifts
/// an offset. The resolved spelling must itself be non-symbolic, so the hop
/// always moves towards a block the structural rule can decide, and the answer
/// is `false` whenever no such equality is stated.
///
/// Boundedness. One keyed lookup per side, over the equalities stated about
/// that one pointer, with no transitive closure and no fact-set scan: an alias
/// of an alias is not reported. The re-ask is the ordinary query, but on a
/// pointer that is *not* unresolved, so this rule is a no-op inside it and one
/// hop cannot become a walk; `ResolutionQueryGuard` closes the remaining cycle.
/// This is the same bound `arm_binding_program_spelling` accepts for the same
/// index.
fn pointers_distinct_through_one_exact_alias(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let unresolved = |pointer: &Pointer| {
        matches!(
            pointer.block,
            PointerBlock::Symbolic(_) | PointerBlock::FunctionSymbolic(_)
        )
    };
    let resolved_side_is_distinct = |pointer: &Pointer, other: &Pointer| {
        if !unresolved(pointer) {
            return false;
        }
        crate::instrumentation::record_deterministic_work(1);
        assumptions.exact_pointer_aliases(pointer).any(|alias| {
            !unresolved(alias)
                && pointers_proven_distinct_for_memory_resolution(alias, other, assumptions)
        })
    };
    resolved_side_is_distinct(left, right) || resolved_side_is_distinct(right, left)
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
        element_index_from_offset_with_facts(left_index, element_width, assumptions),
        element_index_from_offset_with_facts(right_index, element_width, assumptions),
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
    // Blocks the system proves distinct (distinct heap identities, distinct
    // concrete names, string literals with different bytes, locals versus
    // arguments) can never denote one address. No assumption may override
    // that structural fact: consulting assumptions here would let a
    // contradictory `Constant(false)` fact, or any bogus equality, merge
    // distinct allocations during resource normalization.
    if left.blocks_proven_distinct(right) {
        return false;
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
    let _query =
        ResolutionQueryGuard::enter(ResolutionQuery::OffsetEqual(left.clone(), right.clone()))?;
    if let Some(value) = assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
        left.clone(),
        right.clone(),
    )) {
        return Some(value);
    }
    if let Some(element_width) = common_pointer_offset_element_width(left, right)
        && let (Some(left), Some(right)) = (
            element_index_from_offset_with_facts(left, element_width, assumptions),
            element_index_from_offset_with_facts(right, element_width, assumptions),
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
/// equality class, then the observable cells through the memoized pointer
/// equality query, so a pair is resolved once per fact set.
///
/// The last search is filtered by `observable_by_load`, the one filter the
/// load-framing routes share, and not by block name. A cell in another block
/// can be the cell this pointer reads whenever the two are not proven distinct:
/// `ensures result == &g[0]` makes the store to `g[0]` the store this load
/// reads, and a name filter here would answer "no stored value" for it. The
/// pointer equality is still what decides; the filter only says which cells are
/// worth asking about. Keeping a cell that is proven distinct would be wasted
/// work, never a wrong answer, and dropping one that may alias is what used to
/// lose the read.
fn stored_value_at_equal_pointer(
    memory: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    if let Some(value) = memory.known_value(pointer) {
        return Some(value);
    }
    if let Some(value) = memory.known_union_value(pointer, CType::Int32) {
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
                memory
                    .known_value(&Pointer {
                        block: pointer.block.clone(),
                        offset: PointerOffsetTerm::Int32Scaled {
                            value: Box::new(member.clone()),
                            byte_width: *byte_width,
                        },
                    })
                    .or_else(|| {
                        memory.known_union_value(
                            &Pointer {
                                block: pointer.block.clone(),
                                offset: PointerOffsetTerm::Int32Scaled {
                                    value: Box::new(member),
                                    byte_width: *byte_width,
                                },
                            },
                            CType::Int32,
                        )
                    })
            })
    {
        return Some(value);
    }
    memory
        .cells
        .iter()
        .find(|(stored, _)| {
            stored.block.observable_by_load(&pointer.block)
                && pointers_proven_equal_for_memory_resolution(pointer, stored, assumptions)
        })
        .map(|(_, value)| value.clone())
        .or_else(|| {
            memory
                .union_cells
                .iter()
                .find(|((stored, value_type), _)| {
                    *value_type == CType::Int32
                        && stored.block.observable_by_load(&pointer.block)
                        && pointers_proven_equal_for_memory_resolution(pointer, stored, assumptions)
                })
                .map(|(_, value)| value.clone())
        })
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
        if let Bitvector32Term::Variable(variable) = term
            && let Some((memory, pointer)) =
                crate::kernel::eval::registered_load_origin_for_variable(variable)
        {
            return Some(Bitvector32Term::MemoryLoad(memory, Box::new(pointer)));
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
                && !loads_separated_by_recorded_history(
                    left_memory,
                    right_memory,
                    left_pointer,
                    assumptions,
                )
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
        (CValue::Int16(left), CValue::Int16(right))
        | (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right))
        | (CValue::UInt16(left), CValue::UInt16(right))
        | (CValue::UInt32(left), CValue::UInt32(right))
        | (CValue::Int64(left), CValue::Int64(right))
        | (CValue::UInt64(left), CValue::UInt64(right))
        | (CValue::Float32(left), CValue::Float32(right))
        | (CValue::Float64(left), CValue::Float64(right)) => {
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

/// The only `local:` block a snapshot comparison with **no load pointer** may
/// drop before comparing.
///
/// [`memories_proven_equal_for_memory_resolution`] and its certification twin
/// `c_memories_definitionally_equal` are whole-snapshot equalities. They are
/// handed no pointer, so they cannot ask
/// [`PointerBlock::observable_by_load`] which cells a particular read could
/// see, and both used to drop every cell and block spelled `local:` instead.
/// That is the withdrawn `Symbolic` exception of `observable_by_load` with the
/// sides swapped: instead of claiming an unresolved load reads only its own
/// block, it claims no automatic object is memory such a load reads.
/// `int32* echo(int32* p) { return p; } … q = echo(&x); x = 1;` refutes it —
/// `q` *is* `&x`, so two snapshots differing only in `local:x` are two
/// different states for a read through `q`
/// (`mdtests/an_unresolved_pointer_sees_the_store_to_a_local.md` is the false
/// theorem the pointer-aware spelling of the same shortcut admitted).
///
/// What survives is the half of the claim that needs no pointer. An automatic
/// object whose address no function in this session's sources ever forms is
/// not memory any pointer value in the program designates, so *no* load
/// anywhere can tell two snapshots apart by it. That is
/// [`crate::kernel::primitives::block_is_never_address_taken_local`], whose
/// soundness argument lives on that function; it is a property of the whole
/// program's source rather than of one proof path, which is exactly why a
/// comparison may spend it with neither a pointer nor a fact context — the
/// same reason the two naming walks may.
///
/// The object read under **its own name** is a different question, and not
/// this filter's to answer. A scalar local's program-visible value lives in
/// the `CLocalEnvironment` binding, which the callers of these two
/// comparisons either compare exactly as part of `CState` equality or do not
/// ask about at all (an effect chain's two endpoints). A caller that needs the
/// slot cell itself compares `CState::local_cell_values` beside the memory,
/// as `function_entry_representation_states_match` does.
///
/// Cost: one registry lookup on a name of bounded length.
pub(in crate::kernel) fn local_block_no_pointer_can_reach(block: &PointerBlock) -> bool {
    crate::kernel::primitives::block_is_never_address_taken_local(block)
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
        .filter(|(block, _)| !local_block_no_pointer_can_reach(block))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !local_block_no_pointer_can_reach(block)))
    {
        return false;
    }
    if left.forgotten.ended_local_blocks != right.forgotten.ended_local_blocks {
        return false;
    }
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| !local_block_no_pointer_can_reach(&pointer.block))
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
        && left
            .union_cells
            .keys()
            .chain(right.union_cells.keys())
            .filter(|(pointer, _)| !local_block_no_pointer_can_reach(&pointer.block))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .all(|(pointer, value_type)| {
                match (
                    left.union_cells.get(&(pointer.clone(), *value_type)),
                    right.union_cells.get(&(pointer.clone(), *value_type)),
                ) {
                    (Some(left), Some(right)) => {
                        c_values_proven_equal_for_memory_resolution(left, right, assumptions)
                    }
                    (None, None) => true,
                    _ => false,
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

/// Whether the recorded history puts a step that writes this load's bytes
/// between the two snapshots.
///
/// This is the one veto the snapshot comparisons answer to, and it is read
/// off walks they have already paid for: the equality question reaches
/// `recorded_load_history` first, so the refutation is a memo lookup on the
/// same key. A stated or assumed equality never reaches here — the fact
/// graph is consulted before the load arms are — so the veto withdraws only
/// the structural routes.
///
/// The snapshots a framing comparison holds are often naming projections:
/// built rather than derived, carrying no recorded step of their own, so a
/// walk from one stops immediately. The projection registry leads each back
/// to the snapshot its materialized cells were loaded from, which is where
/// the history is, and the pair is asked again from there.
pub(in crate::kernel) fn loads_separated_by_recorded_history(
    left: &SharedCMemory,
    right: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let separated = |left: &SharedCMemory, right: &SharedCMemory| {
        // Asked with every recorded edge readable, in every scope. Crossing a
        // block declaration or a cell-forgetting step is not an inference the
        // loadable prover licenses — those steps write nothing, and a walk
        // that stops at one has read the history only as far as the first
        // bookkeeping edge. The pre-arc scope keeps its own equality answers
        // (see `recorded_load_history`); what it must not keep is a *weaker*
        // view of which stores happened, because then one route would frame a
        // load across a store another route refuses.
        crate::kernel::api::with_extended_dag_bridging(|| {
            crate::kernel::api::recorded_load_history(left, right, pointer, assumptions)
        }) == crate::kernel::api::LoadHistory::DifferentVersions
    };
    separated(left, right) || {
        let left_source = canonical_load_projection_source(left, pointer);
        let right_source = canonical_load_projection_source(right, pointer);
        (left_source.is_some() || right_source.is_some())
            && separated(
                left_source.as_ref().unwrap_or(left),
                right_source.as_ref().unwrap_or(right),
            )
    }
}

/// The term-level form of [`loads_separated_by_recorded_history`], for the
/// routes that compare two whole terms rather than two snapshots.
///
/// Three structural routes can call two loads of one cell equal: the history
/// walk itself, the snapshot comparison, and the deep canonical-form
/// comparison. The first asks the history by construction; this is what the
/// other two answer to, so that one store cannot be seen by one route and
/// missed by another. A load variable is viewed through the load registry,
/// exactly as those routes view it.
///
/// Routes that derive the equality from stated or assumed facts are not
/// vetoed and never reach here: a premise about the two values outranks what
/// the history says about the cell, and the fact graph is consulted first
/// everywhere this is used.
pub(in crate::kernel) fn load_equality_refuted_by_history(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let load = |term: &Bitvector32Term| match term {
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            Some((memory.clone(), pointer.as_ref().clone()))
        }
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_for_variable(variable)
        }
        _ => None,
    };
    let (Some((left_memory, left_pointer)), Some((right_memory, right_pointer))) =
        (load(left), load(right))
    else {
        return false;
    };
    left_pointer == right_pointer
        && loads_separated_by_recorded_history(
            &left_memory,
            &right_memory,
            &left_pointer,
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
    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    differing
        .into_iter()
        .filter(|cell_pointer| cell_is_observable_by_load(cell_pointer, pointer))
        .all(|cell_pointer| {
            differing_cell_bytes_miss_the_load(
                left,
                right,
                &cell_pointer,
                pointer,
                load_bytes,
                assumptions,
            ) && pointers_proven_distinct_for_memory_resolution(&cell_pointer, pointer, assumptions)
        })
}

/// How many bytes a cell holding this value occupies.
///
/// A cell that is only a union view, or one holding `Void`, has no value width
/// to read and stands in the widest scalar: over-stating a width can only
/// shrink the separated set.
pub(in crate::kernel) fn cell_access_byte_width(value: &CValue) -> u32 {
    match value.byte_width() {
        0 => crate::kernel::resource_tracker::widest_scalar_access_bytes(),
        bytes => bytes,
    }
}

/// How wide the cell the two snapshots differ on is, in bytes.
///
/// The width comes from the value the cell holds, on whichever side holds
/// one, and from the wider of the two where both do and disagree: the entry
/// has to cover every byte either snapshot keeps there. A cell that is only a
/// union view, or one holding `Void`, has no value width to read here and
/// stands in the widest scalar — over-stating a width can only shrink the
/// separated set.
fn differing_cell_byte_width(left: &CMemory, right: &CMemory, cell_pointer: &Pointer) -> u32 {
    let stored_width = |memory: &CMemory| {
        memory
            .cells
            .get(cell_pointer)
            .map(CValue::byte_width)
            .filter(|bytes| *bytes > 0)
    };
    stored_width(left)
        .into_iter()
        .chain(stored_width(right))
        .max()
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// Whether the address ladder may answer for this differing cell at all.
///
/// The ladder below it decides whether the cell's *address* is a different
/// address from the load's. That is not the question these comparisons are
/// asking: they are deciding whether the two snapshots hold the same value
/// for this load, and a cell at `p + 1` holding one byte is a different
/// address from `p` while being the second byte a four-byte read there
/// returns. Only where the bytes are shown separate may the ladder stand in
/// for them; provable overlap and an unknown gap both mean the snapshots are
/// not shown to agree.
pub(in crate::kernel) fn differing_cell_bytes_miss_the_load(
    left: &CMemory,
    right: &CMemory,
    cell_pointer: &Pointer,
    load_pointer: &Pointer,
    load_bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    access_byte_overlap(
        cell_pointer,
        differing_cell_byte_width(left, right, cell_pointer),
        load_pointer,
        load_bytes,
        assumptions,
    ) == AccessByteOverlap::Separate
}

/// The filter the three "do these snapshots agree about this load" comparisons
/// — [`memory_snapshots_match_for_resolution`],
/// [`memories_match_for_pointer_load_bounded_alias`] and
/// [`memories_match_for_pointer_load_under_assumptions`] — apply to the cells
/// the two snapshots differ on, before asking whether each one is separate
/// from the load.
///
/// It is [`PointerBlock::observable_by_load`] — the same filter the rest of
/// the load-framing routes use — and this note exists because it used to be
/// `!cell.block.starts_with("local:")`, a block-name shortcut that dropped
/// every differing `local:` cell from the comparison without asking anything.
///
/// The shortcut's implicit claim was that a load the caller cannot resolve to
/// a named object never reads one of this function's own automatic objects.
/// That is the same claim the `Symbolic` exception in `observable_by_load`
/// used to make, and it is false in the same way: `&x` may be passed to a
/// callee and come back as the callee's result, so a `Symbolic` pointer can
/// designate exactly the local a later statement stores to. With the shortcut
/// in place, two snapshots that differed only in `local:x` were declared to
/// agree about a load through such a pointer, and `q[0] == 5` survived
/// `x = 1` with `q == &x`
/// (`mdtests/an_unresolved_pointer_sees_the_store_to_a_local.md`, and
/// `mdtests/returned_pointer_to_a_caller_local_may_alias_it.md` for the same
/// C with the equality stated). A store to a *global* was never skipped,
/// which is the difference that made the local case the surviving one.
///
/// Nothing is lost where the shortcut was sound. A load pointer in a `local:`
/// block is refused by each of the three before they reach here; for every
/// other spelling the program can write a store through —
/// `ExternalArgument`, `ExternalObject`, another `Concrete` block, `Heap`,
/// `Temporary` — `PointerBlock::proven_distinct` separates it from a `local:`
/// block, so those cells are answered `true` on the first rung of the
/// distinctness ladder instead of being skipped. What the filter keeps is
/// exactly the set of cells whose block the kernel cannot tell apart from the
/// load's, which is the set the comparison exists to decide.
fn cell_is_observable_by_load(cell_pointer: &Pointer, load: &Pointer) -> bool {
    cell_pointer.block.observable_by_load(&load.block)
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
    let (left_index, right_index) = common_base_index_offsets(left, right)?;
    if let (Some(left), Some(right)) = (left_index.as_const(), right_index.as_const()) {
        return Some(ConditionTerm::Constant(left == right));
    }
    let (left_index, right_index, _) = element_indices_of(&left_index, &right_index)?;
    Some(ConditionTerm::equal(left_index, right_index))
}

/// The element indices the common-base ladder compares, counted in the
/// element width they share.
///
/// A caller that needs more than "are these two addresses different" — how
/// many bytes apart they are, or which of them is the lower — needs the
/// indices themselves, not just the equality built from them. The byte
/// question a store hop actually asks is one of those callers: an address
/// ladder proving the indices differ guarantees a gap of one element, and
/// whether one element is enough depends on how wide the two accesses are.
pub(in crate::kernel) fn common_base_element_indices(
    left: &Pointer,
    right: &Pointer,
) -> Option<(Bitvector32Term, Bitvector32Term, u32)> {
    let (left_index, right_index) = common_base_index_offsets(left, right)?;
    element_indices_of(&left_index, &right_index)
}

/// Convert a cancelled index pair into element indices of their common
/// width. A constant that is not a whole number of elements has no element
/// index, which is how an address sitting part-way into an element declines
/// the ladder rather than rounding itself onto an element boundary.
fn element_indices_of(
    left_index: &PointerOffsetTerm,
    right_index: &PointerOffsetTerm,
) -> Option<(Bitvector32Term, Bitvector32Term, u32)> {
    let element_width = common_pointer_offset_element_width(left_index, right_index)?;
    let left = element_index_from_offset(left_index, element_width)?;
    let right = element_index_from_offset(right_index, element_width)?;
    Some((left, right, element_width))
}

/// Cancel a structurally identical additive base from two same-block offsets
/// and return what remains on each side.
fn common_base_index_offsets(
    left: &Pointer,
    right: &Pointer,
) -> Option<(PointerOffsetTerm, PointerOffsetTerm)> {
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
    let (left_index, right_index) = index_pair?;
    Some((left_index.clone(), right_index.clone()))
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

    // Cells outside the loaded pointer's own block are compared too whenever
    // their block is not proven distinct from it: an `ExternalArgument`
    // pointer and a `global:` block are spelled differently and may still be
    // one object, so dropping the global's cells here would frame the
    // argument's load across a write the caller can aim at it.
    memory_havoc_markers(left).eq(memory_havoc_markers(right))
        && left.blocks.get(&pointer.block) == right.blocks.get(&pointer.block)
        && left
            .cells
            .iter()
            .filter(|(cell_pointer, _)| cell_pointer.block.observable_by_load(&pointer.block))
            .eq(right
                .cells
                .iter()
                .filter(|(cell_pointer, _)| cell_pointer.block.observable_by_load(&pointer.block)))
        && left
            .union_cells
            .iter()
            .filter(|((cell_pointer, _), _)| cell_pointer.block.observable_by_load(&pointer.block))
            .eq(right.union_cells.iter().filter(|((cell_pointer, _), _)| {
                cell_pointer.block.observable_by_load(&pointer.block)
            }))
}

fn memory_havoc_markers(memory: &CMemory) -> impl Iterator<Item = (&PointerBlock, &CBlock)> {
    memory
        .blocks
        .iter()
        .filter(|(block, _)| block.starts_with("havoc:") || block.starts_with("call-havoc:"))
}

/// Returns a canonical representation of the portion of memory observable by
/// one atomic load. Only a block proven distinct from the load's block cannot
/// affect it; a block that is merely named differently, such as a `global:`
/// block beside an `ExternalArgument` pointer, stays. A block made only
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
        .filter(|(cell_pointer, _)| cell_pointer.block.observable_by_load(&pointer.block))
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
        // A forget mark survives the jump for the same reason a havoc marker
        // does, and it is the source's mark that must not be inherited: the
        // cells' common source may be a state this one has since forgotten
        // things from, and wearing that state's identity is exactly what
        // names a changed load `old(...)`.
        std::sync::Arc::make_mut(&mut canonical.forgotten).forgotten_from =
            memory.forgotten.forgotten_from;
    }
    // Only the cells below decide what a load reads. Declaring a block writes
    // nothing, so the block list stays the load's own block plus the havoc
    // markers even where a cell of another block is kept.
    std::sync::Arc::make_mut(&mut canonical.blocks).retain(|block, _| {
        block == &pointer.block || block.starts_with("havoc:") || block.starts_with("call-havoc:")
    });
    std::sync::Arc::make_mut(&mut canonical.cells).retain(|cell_pointer, value| {
        cell_pointer.block.observable_by_load(&pointer.block)
            && !cell_disjoint_from_load_by_constant_offset(cell_pointer, value, pointer)
    });
    std::sync::Arc::make_mut(&mut canonical.union_cells).retain(|(cell_pointer, _), value| {
        cell_pointer.block.observable_by_load(&pointer.block)
            && !cell_disjoint_from_load_by_constant_offset(cell_pointer, value, pointer)
    });
    canonical
}

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
/// intervals are disjoint. This needs no assumptions, so canonicalization may
/// drop the cell.
///
/// The cell contributes the real width of the value stored in it, taken from
/// [`CValue::byte_width`] rather than from a second width table here: an
/// `int64`, a `uint64`, a `double` and an LP64 pointer are eight bytes, and a
/// cell whose width this function guessed too small would be dropped while
/// the load still reads part of it.
///
/// A `MemoryLoad` term records no width, so the load contributes
/// [`MAX_SCALAR_ACCESS_BYTES`]. That is the only sound reading of an unknown
/// width here: dropping a cell makes two snapshots compare equal at this
/// load, so every byte the load might read has to be considered. An
/// eight-byte load at the loaded pointer covers the four bytes above it, and
/// a fixed four here reported a cell exactly four bytes above the load as
/// disjoint from it.
fn cell_disjoint_from_load_by_constant_offset(
    cell_pointer: &Pointer,
    value: &CValue,
    load_pointer: &Pointer,
) -> bool {
    // Offsets are only comparable inside one block. Two blocks that may be
    // the same object still carry unrelated bases — a parameter may point at
    // `g[1]` — so a constant byte shift proves nothing between them.
    if cell_pointer.block != load_pointer.block {
        return false;
    }
    let (cell_atoms, cell_shift) = offset_atoms_and_constant(&cell_pointer.offset);
    let (load_atoms, load_shift) = offset_atoms_and_constant(&load_pointer.offset);
    if cell_atoms != load_atoms {
        return false;
    }
    // A `Void` cell holds no bytes, so it spans no interval to compare.
    let cell_width = i64::from(value.byte_width());
    if cell_width == 0 {
        return false;
    }
    crate::kernel::byte_intervals_disjoint(
        cell_shift,
        cell_width,
        load_shift,
        crate::kernel::MAX_SCALAR_ACCESS_BYTES,
    )
}

/// What one access's bytes do to another's, where an address ladder is about
/// to be used to answer the byte question.
///
/// Separation is a question about bytes, and every address ladder in the
/// kernel answers a different one: whether two *addresses* denote different
/// locations. `p + 1` is a different address from `p` under every test there
/// is, and a one-byte write there still overwrites the second byte of a
/// four-byte read at `p`. So a ladder may only stand in for the byte question
/// where the gap it establishes clears both accesses, and this is the one
/// place that decides whether it does.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum AccessByteOverlap {
    /// The two accesses provably share a byte. No address ladder may speak:
    /// they touch the same storage whatever their addresses are called.
    Overlaps,
    /// The two accesses provably share no byte, or the gap a ladder
    /// establishes is wide enough that neither can reach the other.
    Separate,
    /// Neither is shown. A ladder proving the addresses differ still says
    /// nothing about the bytes, so it may not stand in for this.
    Unknown,
}

/// Whether the `left_bytes` bytes at `left` reach the `right_bytes` bytes at
/// `right`.
///
/// Two accesses in blocks proven distinct never share a byte, whatever their
/// widths. Within one block it comes down to the gap the offsets guarantee:
///
/// - Both offsets constant: the exact interval test decides it, in both
///   directions. This is taken first, because provable overlap is the answer
///   however clean the addresses look — `+4` inside an eight-byte element is
///   a sub-element shift that the element-width rule below reports as a clean
///   element width.
/// - Offsets that differ by a whole element of a common width: an address
///   ladder proving the element indices differ guarantees a gap of at least
///   that element width. Which access has to fit inside that gap depends on
///   what the ladder knows. A bare disequality leaves the direction open, so
///   both accesses must fit: an eight-byte load at element `i` of a
///   four-byte-scaled pointer reaches into element `i + 1`, and `i != j`
///   does not rule out `j == i + 1`. A strict order fixes the direction, and
///   then only the *lower* access has to fit — the upper one extends away
///   from the gap, so its width cannot close it.
/// - Anything else: the gap is unknown, and an unknown gap separates nothing.
///
/// An address sitting part-way into an element has no element index at all,
/// so it declines the ladder rather than rounding onto an element boundary:
/// a store at `a[j] + 4` lands inside `a[i]` when `j == i`, though a ladder
/// proving `i != j` would separate the indices happily enough.
pub(in crate::kernel) fn access_byte_overlap(
    left: &Pointer,
    left_bytes: u32,
    right: &Pointer,
    right_bytes: u32,
    assumptions: &PureFactContext,
) -> AccessByteOverlap {
    if let Some(shift) = constant_byte_shift_between(left, right) {
        return if crate::kernel::byte_intervals_disjoint(
            shift,
            i64::from(left_bytes),
            0,
            i64::from(right_bytes),
        ) {
            AccessByteOverlap::Separate
        } else {
            AccessByteOverlap::Overlaps
        };
    }
    if one_element_gap_separates_bytes(left, left_bytes, right, right_bytes, assumptions) {
        AccessByteOverlap::Separate
    } else {
        AccessByteOverlap::Unknown
    }
}

/// The element-width half of [`access_byte_overlap`]: whether the gap an
/// address ladder can establish between two same-block offsets is wide enough
/// to clear both accesses. See that function's note for which access has to
/// fit and why the direction matters.
fn one_element_gap_separates_bytes(
    left: &Pointer,
    left_bytes: u32,
    right: &Pointer,
    right_bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    if left.block != right.block {
        // Two addresses in different blocks are separated by the block
        // ladder, which needs no width: distinct objects share no byte.
        return true;
    }
    let Some((left_index, right_index, element_width)) = common_base_element_indices(left, right)
    else {
        return false;
    };
    let element_width = i64::from(element_width);
    // The direction-free answer first: when both accesses fit in an element,
    // no direction can make them overlap, and no order query is needed.
    if i64::from(left_bytes.max(right_bytes)) <= element_width {
        return true;
    }
    // Only a known direction can separate them now. Ask for it in the order
    // that puts the narrower requirement first.
    let strictly_below = |low: &Bitvector32Term, high: &Bitvector32Term| {
        assumptions.decide(&ConditionTerm::signed_less_than(low.clone(), high.clone()))
            == Some(true)
    };
    let lower_access_bytes = if strictly_below(&left_index, &right_index) {
        left_bytes
    } else if strictly_below(&right_index, &left_index) {
        right_bytes
    } else {
        return false;
    };
    i64::from(lower_access_bytes) <= element_width
}

/// The constant byte distance from `base` to `pointer`, when the two
/// addresses differ by a constant.
fn constant_byte_shift_between(pointer: &Pointer, base: &Pointer) -> Option<i64> {
    pointer_byte_offset_from_base(pointer, base)
        .as_ref()
        .and_then(signed_bitvector_constant)
}

/// The bytes a store covers, as non-constant offset atoms plus a constant
/// byte interval, for the cells of the same block to be compared against.
/// `None` where the write has no constant extent to compare.
pub(in crate::kernel) struct StoreByteInterval {
    atoms: Vec<PointerOffsetTerm>,
    shift: i64,
    bytes: i64,
}

impl StoreByteInterval {
    pub(in crate::kernel) fn of(write_pointer: &Pointer, write_bytes: u32) -> Option<Self> {
        (write_bytes > 0).then(|| {
            let (atoms, shift) = offset_atoms_and_constant(&write_pointer.offset);
            Self {
                atoms,
                shift,
                bytes: i64::from(write_bytes),
            }
        })
    }

    /// Whether this store provably overwrites bytes the cell occupies.
    ///
    /// Both widths are exact: the store's comes from the value it writes and
    /// the cell's from the value it holds, so this decides bytes rather than
    /// bounding them by the widest scalar. It is deliberately a different
    /// question from the address-separation checks it is used beside, which
    /// answer whether two *addresses* denote different locations: `p` and
    /// `p + 4` are different addresses, and a one-byte write at `p + 4`
    /// still overwrites part of an `int64` cell at `p`.
    pub(in crate::kernel) fn overwrites(
        &self,
        cell_pointer: &Pointer,
        cell_value: &CValue,
    ) -> bool {
        let cell_width = i64::from(cell_value.byte_width());
        self.overwrites_bytes(cell_pointer, cell_width)
    }

    pub(in crate::kernel) fn overwrites_typed(
        &self,
        cell_pointer: &Pointer,
        cell_type: CType,
    ) -> bool {
        self.overwrites_bytes(cell_pointer, i64::from(cell_type.byte_width()))
    }

    /// Whether this store writes *every* byte the cell occupies.
    ///
    /// This is the difference between a cell that is stale and a cell that is
    /// forgotten. A store that covers the cell completely replaces exactly
    /// what dropping the cell lost, so the snapshot it produces still says
    /// everything about the state it describes. A store that covers only some
    /// of the cell's bytes leaves the rest at values nothing records any more:
    /// the byte written into the middle of an `int64` is in the result, and
    /// the other seven bytes are knowledge the result no longer has. Calling
    /// that partial case stale let the produced snapshot claim to be the state
    /// before the store.
    pub(in crate::kernel) fn overwrites_completely(
        &self,
        cell_pointer: &Pointer,
        cell_value: &CValue,
    ) -> bool {
        self.covers_bytes(cell_pointer, i64::from(cell_value.byte_width()))
    }

    pub(in crate::kernel) fn overwrites_typed_completely(
        &self,
        cell_pointer: &Pointer,
        cell_type: CType,
    ) -> bool {
        self.covers_bytes(cell_pointer, i64::from(cell_type.byte_width()))
    }

    fn covers_bytes(&self, cell_pointer: &Pointer, cell_width: i64) -> bool {
        if cell_width == 0 {
            return false;
        }
        let (cell_atoms, cell_shift) = offset_atoms_and_constant(&cell_pointer.offset);
        if cell_atoms != self.atoms {
            return false;
        }
        self.shift <= cell_shift
            && cell_shift
                .checked_add(cell_width)
                .is_some_and(|cell_end| self.shift.checked_add(self.bytes) >= Some(cell_end))
    }

    fn overwrites_bytes(&self, cell_pointer: &Pointer, cell_width: i64) -> bool {
        if cell_width == 0 {
            return false;
        }
        let (cell_atoms, cell_shift) = offset_atoms_and_constant(&cell_pointer.offset);
        if cell_atoms != self.atoms {
            return false;
        }
        !crate::kernel::byte_intervals_disjoint(cell_shift, cell_width, self.shift, self.bytes)
    }
}

/// The source snapshot a materialization cell stands for: a cell at `p`
/// whose value is `load(source, p)`, or — with terms canonical at creation —
/// the load variable registered for a load of `p`, whose source the registry
/// records. Materialization changes which cells are concrete, not what the
/// load means.
fn materialized_cell_source(cell_pointer: &Pointer, value: &CValue) -> Option<SharedCMemory> {
    match value {
        CValue::Bool(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Int16(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt16(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Int64(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::UInt64(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Float32(Bitvector32Term::MemoryLoad(source, source_pointer))
        | CValue::Float64(Bitvector32Term::MemoryLoad(source, source_pointer))
            if source_pointer.as_ref() == cell_pointer =>
        {
            Some(source.clone())
        }
        CValue::Bool(Bitvector32Term::Variable(variable))
        | CValue::Int16(Bitvector32Term::Variable(variable))
        | CValue::UInt16(Bitvector32Term::Variable(variable))
        | CValue::Int32(Bitvector32Term::Variable(variable))
        | CValue::UInt8(Bitvector32Term::Variable(variable))
        | CValue::Int64(Bitvector32Term::Variable(variable))
        | CValue::UInt64(Bitvector32Term::Variable(variable))
        | CValue::Float32(Bitvector32Term::Variable(variable))
        | CValue::Float64(Bitvector32Term::Variable(variable))
            if crate::kernel::eval::is_load_variable(variable) =>
        {
            let (source, source_pointer) =
                crate::kernel::eval::registered_load_for_variable(variable)?;
            (&source_pointer == cell_pointer).then_some(source)
        }
        CValue::Void
        | CValue::Bool(_)
        | CValue::Int16(_)
        | CValue::Int32(_)
        | CValue::UInt8(_)
        | CValue::UInt16(_)
        | CValue::UInt32(_)
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
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
    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    left.differing_cell_pointers(right)
        .into_iter()
        .filter(|cell_pointer| cell_is_observable_by_load(cell_pointer, pointer))
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
            }) || differing_cell_bytes_miss_the_load(
                left,
                right,
                &cell_pointer,
                pointer,
                load_bytes,
                assumptions,
            ) && pointers_proven_distinct_for_memory_resolution(
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

    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    left.differing_cell_pointers(right)
        .into_iter()
        .filter(|cell_pointer| cell_is_observable_by_load(cell_pointer, pointer))
        .all(|cell_pointer| {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "snapshot comparison: bounded alias",
                || {
                    differing_cell_bytes_miss_the_load(
                        left,
                        right,
                        &cell_pointer,
                        pointer,
                        load_bytes,
                        assumptions,
                    ) && pointers_proven_distinct_for_memory_resolution(
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
