use super::*;
use crate::kernel::binary_term;

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

#[cfg(test)]
#[test]
fn structural_slot_distinctness_does_not_depend_on_recursive_query_availability() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Pointer {
        block: PointerBlock::Symbolic(Variable(1000001)),
        offset: PointerOffsetTerm::Constant(16),
    };
    let read = Pointer {
        offset: PointerOffsetTerm::Constant(12),
        ..slot.clone()
    };
    let _outer =
        ResolutionQueryGuard::enter(ResolutionQuery::PointerDistinct(slot.clone(), read.clone()))
            .unwrap();
    assert!(pointers_proven_distinct_for_memory_resolution(
        &slot,
        &read,
        &PureFactContext::new()
    ));
    assert!(!pointers_proven_distinct_for_memory_resolution(
        &slot,
        &slot,
        &PureFactContext::new()
    ));
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
    /// [`source_holds_cells_observable_by`], by interned snapshot and block.
    static SOURCE_OBSERVABLE_BY_BLOCK: std::cell::RefCell<
        std::collections::HashMap<(super::SharedCMemory, crate::kernel::primitives::PointerBlock), bool>,
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
    /// The latest producer observation of a named value read. Every stored
    /// edge is structural and valid only for its recorded access width.
    static VALUE_LOAD_ORIGINS: std::cell::RefCell<
        std::collections::HashMap<(super::SharedCMemory, Pointer, u32), super::SharedCMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Reverse definitions select a name from the exact observation. Keeping
    /// this direction preserves earlier observations when a name is reused.
    static VALUE_LOAD_NAMES: std::cell::RefCell<
        std::collections::HashMap<(super::SharedCMemory, Pointer, u32), super::SharedCMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static LOAD_DEFINITION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
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
    SOURCE_OBSERVABLE_BY_BLOCK.with(|memo| memo.borrow_mut().clear());
    CANONICAL_LOAD_PROJECTION_SOURCES.with(|sources| sources.borrow_mut().clear());
    CANONICAL_LOAD_PROJECTIONS.with(|projections| projections.borrow_mut().clear());
    VALUE_LOAD_ORIGINS.with(|origins| origins.borrow_mut().clear());
    VALUE_LOAD_NAMES.with(|names| names.borrow_mut().clear());
    advance_load_definition_generation();
}

fn advance_load_definition_generation() {
    LOAD_DEFINITION_GENERATION.with(|generation| {
        generation.set(crate::kernel::equality_graph::next_read_definition_generation());
    });
}

pub(in crate::kernel) fn load_definition_generation() -> u64 {
    LOAD_DEFINITION_GENERATION.with(std::cell::Cell::get)
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
    let changed = CANONICAL_LOAD_PROJECTION_SOURCES.with(|sources| {
        let mut sources = sources.borrow_mut();
        let key = (projected.clone(), pointer.clone());
        if sources
            .get(&key)
            .is_none_or(|preferred| source.arena_id() < preferred.arena_id())
        {
            sources.insert(key, source.clone());
            true
        } else {
            false
        }
    });
    if changed {
        advance_load_definition_generation();
    }
}

/// Retain the selected-width equation already established by structural
/// value-load naming. Unlike a projection edge, this may cross writes outside
/// that width, so it must never be used for a wider observation.
pub(in crate::kernel) fn record_value_load_origin(
    origin: &super::SharedCMemory,
    named: &super::SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
) {
    if origin != named {
        let changed_origin = VALUE_LOAD_ORIGINS.with(|origins| {
            origins
                .borrow_mut()
                .insert((named.clone(), pointer.clone(), bytes), origin.clone())
                .as_ref()
                != Some(origin)
        });
        let changed_name = VALUE_LOAD_NAMES.with(|names| {
            names
                .borrow_mut()
                .insert((origin.clone(), pointer.clone(), bytes), named.clone())
                .as_ref()
                != Some(named)
        });
        if changed_origin || changed_name {
            advance_load_definition_generation();
        }
    }
}

pub(in crate::kernel) fn value_load_origin(
    named: &super::SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
) -> Option<super::SharedCMemory> {
    VALUE_LOAD_ORIGINS.with(|origins| {
        origins
            .borrow()
            .get(&(named.clone(), pointer.clone(), bytes))
            .cloned()
    })
}

/// The structurally chosen name for this exact observation and width.
pub(in crate::kernel) fn value_load_name(
    origin: &super::SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
) -> Option<super::SharedCMemory> {
    VALUE_LOAD_NAMES.with(|names| {
        names
            .borrow()
            .get(&(origin.clone(), pointer.clone(), bytes))
            .cloned()
    })
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

/// A pointer-distinctness query that failed inside one smart closure, keyed
/// by the unsalted content id of its fact set, the memory-DAG generation, and
/// the scope modes its answer depends on. See [`with_closure_failure_memo`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ClosureDistinctnessFailure {
    assumptions: u64,
    lookups: u64,
    generation: u64,
    bridging: bool,
    explicit: bool,
    left: Pointer,
    right: Pointer,
}

/// Which checked fact-transport question a [`ClosureFactCheckFailure`]
/// remembers.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ClosureFactCheck {
    /// Whether a bare condition target holds in the selected live context.
    ConditionTarget,
    /// Whether a load-variable chain through the listed facts bridges the
    /// target.
    LoadVariableBridge,
    /// Whether the certified reachability walk carries the source to the
    /// target.
    Reachability,
    /// Whether the quantified frame carries the source to the target.
    QuantifiedFrame,
}

/// A fact-transport check that failed inside one smart closure: its exact
/// inputs, and the scope state its answer depends on. See
/// [`closure_memoized_fact_check`].
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ClosureFactCheckFailure {
    check: ClosureFactCheck,
    propositions: Vec<Proposition>,
    after: Option<(u32, u32)>,
    assumptions: u64,
    lookups: u64,
    transitions: crate::kernel::ExecutionFacts,
    generation: u64,
    bridging: bool,
    explicit: bool,
}

thread_local! {
    static CLOSURE_DISTINCTNESS_FAILURES: std::cell::RefCell<
        Option<std::collections::HashSet<ClosureDistinctnessFailure>>,
    > = const { std::cell::RefCell::new(None) };
    static CLOSURE_TRANSPORT_FAILURES: std::cell::RefCell<
        Option<BTreeSet<ClosureFactCheckFailure>>,
    > = const { std::cell::RefCell::new(None) };
}

/// Runs one checked fact-transport question through the closure failure memo
/// ([`with_closure_failure_memo`]): outside a closure it just runs; inside
/// one, a question whose exact inputs already failed in this closure fails
/// again without being recomputed.
///
/// The snapshot transport closure lowers one goal at every recorded snapshot;
/// every snapshot that holds the goal's cells unchanged lowers it to the same
/// source, so the same failing questions -- the goal's frame across the step
/// the proof could not see past -- ran once per such snapshot, and again for
/// each of solve's strategies that reaches the closure. The key is the
/// question's whole input: its propositions (source, target, and any listed
/// facts, in order), the memory it lands in, the content id of its fact set,
/// its transition facts, the memory-DAG generation, the DAG scope modes, and
/// the cell lookups in progress. A failure that observed a cycle cut or a
/// limit is not remembered. Work is the key's size per question.
pub(crate) fn closure_memoized_fact_check(
    check: ClosureFactCheck,
    propositions: &[&Proposition],
    after: Option<&CMemory>,
    assumptions: &PureFactContext,
    transitions: &(impl ExecutionFactSource + ?Sized),
    run: impl FnOnce() -> bool,
) -> bool {
    let active = CLOSURE_TRANSPORT_FAILURES.with(|failures| failures.borrow().is_some());
    if !active {
        return run();
    }
    crate::instrumentation::record_deterministic_work(propositions.len() + transitions.len());
    let failure = ClosureFactCheckFailure {
        check,
        propositions: propositions
            .iter()
            .map(|proposition| (*proposition).clone())
            .collect(),
        after: after.map(|after| crate::kernel::intern_c_memory_ref(after).arena_id()),
        assumptions: crate::kernel::assumptions::unsalted_assumptions_memo_id(assumptions),
        lookups: crate::kernel::resource_tracker::cell_source::memory_dag_cell_lookups_fingerprint(
        ),
        transitions: transitions.persistent_facts(),
        generation: crate::kernel::primitives::c_memory_derivation_generation(),
        bridging: crate::kernel::api::extended_dag_bridging_active(),
        explicit: crate::kernel::api::explicit_dag_check_active(),
    };
    let known = CLOSURE_TRANSPORT_FAILURES.with(|failures| {
        failures
            .borrow()
            .as_ref()
            .is_some_and(|failures| failures.contains(&failure))
    });
    if known {
        return false;
    }
    let epoch_before = crate::kernel::assumptions::incomplete_reasoning_epoch();
    let result = run();
    if !result && crate::kernel::assumptions::incomplete_reasoning_epoch() == epoch_before {
        CLOSURE_TRANSPORT_FAILURES.with(|failures| {
            if let Some(failures) = failures.borrow_mut().as_mut() {
                failures.insert(failure);
            }
        });
    }
    result
}

/// Clears the closure failure memo when the outermost scope ends, including
/// on unwind.
struct ClosureFailureMemoScope {
    outermost: bool,
}

impl Drop for ClosureFailureMemoScope {
    fn drop(&mut self) {
        if self.outermost {
            CLOSURE_DISTINCTNESS_FAILURES.with(|failures| *failures.borrow_mut() = None);
            CLOSURE_TRANSPORT_FAILURES.with(|failures| *failures.borrow_mut() = None);
        }
    }
}

/// Runs one smart closure or explicit transport check with its failed
/// pointer-distinctness queries and fact-transport checks remembered for the
/// enclosing attempt's duration.
///
/// A closure that tries one goal against many candidates -- the snapshot
/// transport closure lowers the goal at every recorded snapshot -- asks the
/// same failing distinctness question about the goal's own loads once per
/// candidate, in contexts of equal content, where the ambient resolution memo
/// is not active: the transport check builds its own contexts. Each query may
/// cost thousands of units through the explicit-range arm, so a goal whose
/// frame cannot be proved burned the whole smart budget repeating one
/// failure instead of failing promptly.
///
/// Only failures are remembered, keyed by the cell lookups in progress (a
/// nested answer may have met an in-progress cell), and never one whose
/// computation observed a cycle cut or a limit, so a remembered answer is
/// exactly what recomputing it would return: the memo changes the closure's
/// cost, never its outcome. The key is the fact set's content id, not a
/// salted attempt id, so candidates tried as separate search attempts share
/// it; nothing outlives the closure. [`closure_memoized_fact_check`] uses the
/// same scope for whole fact-transport questions.
pub(crate) fn with_closure_failure_memo<T>(body: impl FnOnce() -> T) -> T {
    let outermost = CLOSURE_DISTINCTNESS_FAILURES.with(|failures| {
        let mut failures = failures.borrow_mut();
        if failures.is_some() {
            return false;
        }
        *failures = Some(std::collections::HashSet::new());
        true
    });
    if outermost {
        CLOSURE_TRANSPORT_FAILURES.with(|failures| *failures.borrow_mut() = Some(BTreeSet::new()));
    }
    let _scope = ClosureFailureMemoScope { outermost };
    body()
}

fn closure_distinctness_failure_key(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> Option<ClosureDistinctnessFailure> {
    let active = CLOSURE_DISTINCTNESS_FAILURES.with(|failures| failures.borrow().is_some());
    if !active {
        return None;
    }
    let (left, right) = if left <= right {
        (left.clone(), right.clone())
    } else {
        (right.clone(), left.clone())
    };
    Some(ClosureDistinctnessFailure {
        assumptions: crate::kernel::assumptions::unsalted_assumptions_memo_id(assumptions),
        lookups: crate::kernel::resource_tracker::cell_source::memory_dag_cell_lookups_fingerprint(
        ),
        generation: crate::kernel::primitives::c_memory_derivation_generation(),
        bridging: crate::kernel::api::extended_dag_bridging_active(),
        explicit: crate::kernel::api::explicit_dag_check_active(),
        left,
        right,
    })
}

/// Inside a closure a failed fact check is answered again without running;
/// a success is never remembered, nothing is remembered outside a closure,
/// and the memo ends with the outermost closure.
#[cfg(test)]
#[test]
fn closure_failure_memo_answers_a_repeated_failure_once() {
    let assumptions = PureFactContext::new();
    let source = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let target = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let runs = std::cell::Cell::new(0);
    let check = |answer: bool| {
        closure_memoized_fact_check(
            ClosureFactCheck::Reachability,
            &[&source, &target],
            None,
            &assumptions,
            &[],
            || {
                runs.set(runs.get() + 1);
                answer
            },
        )
    };
    assert!(!check(false));
    assert!(!check(false));
    assert_eq!(runs.get(), 2, "outside a closure every check runs");
    with_closure_failure_memo(|| {
        assert!(!check(false));
        assert!(!check(false));
        with_closure_failure_memo(|| assert!(!check(false)));
    });
    assert_eq!(runs.get(), 3, "one closure runs a failed check once");
    with_closure_failure_memo(|| {
        assert!(check(true));
        assert!(check(true));
    });
    assert_eq!(runs.get(), 5, "a success is never remembered");
    with_closure_failure_memo(|| assert!(!check(false)));
    assert_eq!(runs.get(), 6, "nothing outlives the closure");
}

/// Direct evidence for store cache preservation. A miss forgets the value;
/// it must not invoke memory resolution, range selection or alias enumeration.
/// The caller separately checks that distinct addresses separate whole accesses.
pub(in crate::kernel) fn pointers_directly_distinct_for_store(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return false;
    }
    if left.blocks_proven_distinct(right)
        || constant_byte_shift(left, right).is_some_and(|shift| shift != 0)
        || assumptions
            .exact_condition_value(&ConditionTerm::pointer_equal(left.clone(), right.clone()))
            == Some(false)
    {
        return true;
    }
    if let Some((left, right, _)) = common_base_element_indices(left, right) {
        if assumptions.exact_condition_value(&ConditionTerm::equal(left.clone(), right.clone()))
            == Some(false)
            || assumptions.exact_condition_value(&ConditionTerm::signed_less_than(
                left.clone(),
                right.clone(),
            )) == Some(true)
            || assumptions.exact_condition_value(&ConditionTerm::signed_less_than(
                right.clone(),
                left.clone(),
            )) == Some(true)
        {
            return true;
        }
    }
    let private_local = |local: &Pointer, value: &Pointer| {
        matches!(value.block, PointerBlock::Symbolic(_))
            && crate::kernel::primitives::block_is_never_address_taken_local(&local.block)
            && assumptions.pointer_in_block(value, &local.block).is_none()
    };
    private_local(left, right) || private_local(right, left)
}

/// Alias check used while resolving a symbolic memory load. This deliberately
/// avoids general equality transport because that transport may itself resolve
/// memory loads.
pub(in crate::kernel) fn pointers_proven_distinct_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    // Structural separation needs no recursive premise query. In particular,
    // a compact run's slot check may ask this while the same query is active.
    if left.blocks_proven_distinct(right)
        || (left.block == right.block
            && matches!((&left.offset, &right.offset),
                (PointerOffsetTerm::Constant(a), PointerOffsetTerm::Constant(b)) if a != b))
    {
        return true;
    }
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        let (left, right) = if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        ResolutionQueryKey::PointerDistinct(id, bridging, left, right)
    });
    if key.is_none()
        && let Some(failure) = closure_distinctness_failure_key(left, right, assumptions)
    {
        let known = CLOSURE_DISTINCTNESS_FAILURES.with(|failures| {
            failures
                .borrow()
                .as_ref()
                .is_some_and(|failures| failures.contains(&failure))
        });
        if known {
            return false;
        }
        let epoch_before = crate::kernel::assumptions::incomplete_reasoning_epoch();
        let result =
            pointers_proven_distinct_for_memory_resolution_unmemoized(left, right, assumptions);
        if !result && crate::kernel::assumptions::incomplete_reasoning_epoch() == epoch_before {
            CLOSURE_DISTINCTNESS_FAILURES.with(|failures| {
                if let Some(failures) = failures.borrow_mut().as_mut() {
                    failures.insert(failure);
                }
            });
        }
        return result;
    }
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
/// The comparison retains both complete addresses, including their offsets,
/// so an entry exchanges two spellings of *one* address without extending
/// the premise to other offsets. The resolved spelling must itself be non-symbolic, so the hop
/// always moves towards a block the structural rule can decide, and the answer
/// is `false` whenever no such equality is stated.
///
/// Interior pointers may additionally use an exact zero-offset base alias,
/// but only to establish structural separation of whole objects. This route
/// never infers byte-span separation from unequal translated addresses.
///
/// Boundedness. At most two keyed lookups per side, over equalities stated
/// about that pointer or its zero-offset base, with no fact-set scan: an alias
/// of an alias is not reported. The re-ask is the ordinary query, but on a
/// pointer that is *not* unresolved, so this rule is a no-op inside it and one
/// hop cannot become a walk; `ResolutionQueryGuard` closes the remaining cycle.
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
        if assumptions.exact_pointer_aliases(pointer).any(|alias| {
            !unresolved(alias)
                && pointers_proven_distinct_for_memory_resolution(alias, other, assumptions)
        }) {
            return true;
        }
        if pointer.offset == PointerOffsetTerm::Constant(0) {
            return false;
        }
        // An exact base alias also identifies the object of q + d. Use
        // whole-object separation only: unequal translated starting addresses
        // would not establish that multi-byte accesses cannot overlap.
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        assumptions
            .exact_pointer_aliases(&base)
            .any(|alias| !unresolved(alias) && alias.blocks_proven_distinct(other))
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
    if let Some(distinct) =
        wide_element_offsets_proven_distinct(left_index, right_index, assumptions)
    {
        return distinct;
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

/// Whether two offsets formed from unsigned 64-bit element indices of one
/// width are proven different, or `None` when either is another form.
///
/// An `Int64Scaled` offset denotes the exact product `index * width`: it is
/// folded to a constant only when that product fits `i64`, and is otherwise
/// kept as the term. Exact products of different indices differ, whatever
/// their size, so indices decided unequal, by an order or by a disequality,
/// are different offsets. This is the rule a signed 32-bit index has, where
/// distinct words are distinct exact offsets. Whether an offset lies inside
/// an object is a separate question, which the membership rule answers
/// with the object-size limit. No 32-bit reading of either index takes part.
fn wide_element_offsets_proven_distinct(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<bool> {
    // A constant offset of whole elements beside a scaled index is the
    // constant index: `base[0]` against `base[k]`.
    let (left, right, width) = match (left, right) {
        (
            PointerOffsetTerm::Int64Scaled {
                value: left,
                byte_width: left_width,
                unsigned: true,
            },
            PointerOffsetTerm::Int64Scaled {
                value: right,
                byte_width: right_width,
                unsigned: true,
            },
        ) => {
            if left_width != right_width || *left_width < 1 {
                return Some(false);
            }
            (left.as_ref().clone(), right.as_ref().clone(), *left_width)
        }
        (
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
            PointerOffsetTerm::Constant(bytes),
        )
        | (
            PointerOffsetTerm::Constant(bytes),
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
        ) if *byte_width >= 1 && *bytes >= 0 && bytes % byte_width == 0 => (
            value.as_ref().clone(),
            Bitvector32Term::UInt64Constant((bytes / byte_width) as u64),
            *byte_width,
        ),
        _ => return None,
    };
    let (left, right, _) = (&left, &right, width);
    let decided = |condition: ConditionTerm| assumptions.decide(&condition);
    let below = |smaller: &Bitvector32Term, larger: &Bitvector32Term| {
        decided(ConditionTerm::uint64_less_than(
            smaller.clone(),
            larger.clone(),
        )) == Some(true)
    };
    let unequal = |first: &Bitvector32Term, second: &Bitvector32Term| {
        decided(ConditionTerm::uint64_equal(first.clone(), second.clone())) == Some(false)
    };
    Some(below(left, right) || below(right, left) || unequal(left, right) || unequal(right, left))
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
    // The shared graph answers known equality first. Offset reasoning below
    // is a stronger, separately guarded judgment, not another alias walk.
    let candidate = assumptions.pointers_known_equal(left, right)
        || pointer_in_block_for_memory_resolution(right, &left.block, assumptions).is_some_and(
            |right| {
                pointer_offsets_proven_equal_for_memory_resolution(
                    &left.offset,
                    &right.offset,
                    assumptions,
                )
            },
        );
    candidate
        && !assumptions
            .pointers_proven_disjoint_by_explicit_range_for_memory_resolution(left, right)
}

/// `pointer` spelled as an address in `block`, when the two name one
/// coordinate: the same block, an affine equality class the graph maintains,
/// or two reads of one cell whose snapshots agree on its bytes. This answers
/// where an address is; it grants no access, which the caller's designation
/// check still decides.
pub(in crate::kernel) fn pointer_in_block_for_memory_resolution(
    pointer: &Pointer,
    block: &PointerBlock,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    if pointer.block == *block {
        return Some(pointer.clone());
    }
    if let Some(aligned) = assumptions.equality_graph.pointer_in_block(pointer, block) {
        return Some(aligned);
    }
    // A cell holds a whole pointer, so two reads of it that see the same
    // bytes produce one value; the read in `block` is then this pointer
    // before its displacement.
    let read = pointer.as_loaded_value()?;
    let target = Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }
    .as_loaded_value()?;
    // As for a retained read's stored value (`pointer_read_stored_value`),
    // the comparison may cross cache-forgetting edges: they discard
    // knowledge but write no program bytes. A projected read is compared
    // from its source snapshot, as its designation is.
    (pointers_proven_equal_for_memory_resolution(
        &read.defining_address,
        &target.defining_address,
        assumptions,
    ) && (crate::kernel::api::with_extended_dag_bridging(|| {
        memory_snapshots_match_for_resolution(
            read.defining_memory.memory(),
            target.defining_memory.memory(),
            &read.defining_address,
            assumptions,
        )
    }) || crate::kernel::memory_provenance::pointer_reads_see_one_cell_source(
        &read,
        &target,
        assumptions,
    )))
    .then(|| Pointer {
        block: block.clone(),
        offset: read.displacement,
    })
}

/// Equal exact observations of a native unsigned index and a signed index
/// denote the same displacement at the same element width. A truncated bit
/// pattern alone is insufficient: only the explicitly established Integer
/// equality participates, so high bits and the signed interpretation survive.
fn mixed_index_offsets_equal(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<bool> {
    use crate::kernel::{IntegerTerm, MachineIntegerType};
    let (wide, narrow, wide_width, narrow_width) = match (left, right) {
        (
            PointerOffsetTerm::Int64Scaled {
                value: wide,
                byte_width: wide_width,
                unsigned: true,
            },
            PointerOffsetTerm::Int32Scaled {
                value: narrow,
                byte_width: narrow_width,
            },
        )
        | (
            PointerOffsetTerm::Int32Scaled {
                value: narrow,
                byte_width: narrow_width,
            },
            PointerOffsetTerm::Int64Scaled {
                value: wide,
                byte_width: wide_width,
                unsigned: true,
            },
        ) => (wide, narrow, wide_width, narrow_width),
        _ => return None,
    };
    if wide_width != narrow_width || *wide_width < 1 {
        return None;
    }
    let wide = IntegerTerm::from_machine(MachineIntegerType::UInt64, wide.as_ref().clone())?;
    let narrow = IntegerTerm::from_machine(MachineIntegerType::Int32, narrow.as_ref().clone())?;
    for (left, right) in [(wide.clone(), narrow.clone()), (narrow, wide)] {
        crate::instrumentation::record_deterministic_work(1);
        if assumptions
            .exact_condition_value(&ConditionTerm::IntegerEqual(left.into(), right.into()))
            == Some(true)
        {
            return Some(true);
        }
    }
    None
}

/// The number of addends a pointer offset sums.
fn addend_count(offset: &PointerOffsetTerm) -> usize {
    match offset {
        PointerOffsetTerm::Add(left, right) => addend_count(left) + addend_count(right),
        _ => 1,
    }
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
    if let Some(equal) = mixed_index_offsets_equal(left, right, assumptions) {
        return Some(equal);
    }
    // Two unsigned 64-bit indices at one element width. The offset is the
    // exact product `index * width`, so equal indices are one offset and
    // unequal ones are different offsets.
    if let (
        PointerOffsetTerm::Int64Scaled {
            value: left_index,
            byte_width: left_width,
            unsigned: true,
        },
        PointerOffsetTerm::Int64Scaled {
            value: right_index,
            byte_width: right_width,
            unsigned: true,
        },
    ) = (left, right)
        && left_width == right_width
        && *left_width > 0
    {
        let equal = assumptions.decide(&ConditionTerm::uint64_equal(
            left_index.as_ref().clone(),
            right_index.as_ref().clone(),
        ));
        match equal {
            Some(true) => return Some(true),
            Some(false) => return Some(false),
            None => {}
        }
    }
    // An unsigned 64-bit index against a constant offset of whole
    // elements: `base[x]` is `base[2]` exactly when `x == 2`, since the
    // scaled offset is the exact product.
    for (scaled, constant) in [(left, right), (right, left)] {
        if let (
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
            PointerOffsetTerm::Constant(bytes),
        ) = (scaled, constant)
            && *byte_width >= 1
        {
            if *bytes < 0 || bytes % byte_width != 0 {
                return Some(false);
            }
            // A value the equalities pin to a constant is that constant.
            if let Some(pinned) = assumptions.wide_constant_from_equalities(value) {
                return Some(pinned == (bytes / byte_width) as u64);
            }
            let index = Bitvector32Term::UInt64Constant((bytes / byte_width) as u64);
            let stated = [
                ConditionTerm::uint64_equal(value.as_ref().clone(), index.clone()),
                ConditionTerm::uint64_equal(index, value.as_ref().clone()),
            ];
            if let Some(equal) = stated.iter().find_map(|equality| {
                assumptions
                    .exact_condition_value(equality)
                    .or_else(|| assumptions.decide(equality))
            }) {
                return Some(equal);
            }
        }
    }
    // An unsigned 64-bit index advanced by whole elements: `i * w + k * w`
    // is `(i + k) * w` when `i + k` does not wrap, which is how a cursor
    // stepped by one element and the element after index `i` spell one
    // address. The stepped index is compared as a 64-bit value and the
    // sum is shown to stay in range; no 32-bit reading takes part.
    for (stepped, whole) in [(left, right), (right, left)] {
        let PointerOffsetTerm::Add(first, second) = stepped else {
            continue;
        };
        let (index, bytes) = match (first.as_ref(), second.as_ref()) {
            (index @ PointerOffsetTerm::Int64Scaled { .. }, PointerOffsetTerm::Constant(bytes))
            | (PointerOffsetTerm::Constant(bytes), index @ PointerOffsetTerm::Int64Scaled { .. }) => {
                (index, *bytes)
            }
            _ => continue,
        };
        let (
            PointerOffsetTerm::Int64Scaled {
                value: index,
                byte_width,
                unsigned: true,
            },
            PointerOffsetTerm::Int64Scaled {
                value: whole_index,
                byte_width: whole_width,
                unsigned: true,
            },
        ) = (index, whole)
        else {
            continue;
        };
        if byte_width != whole_width || *byte_width < 1 || bytes < 1 || bytes % *byte_width != 0 {
            continue;
        }
        let elements = (bytes / *byte_width) as u64;
        let advanced = Bitvector32Term::uint64_add(
            index.as_ref().clone(),
            Bitvector32Term::UInt64Constant(elements),
        );
        let same = advanced == **whole_index
            || assumptions.decide(&ConditionTerm::uint64_equal(
                advanced,
                whole_index.as_ref().clone(),
            )) == Some(true);
        if same
            && assumptions.decide(&ConditionTerm::uint64_less_equal(
                index.as_ref().clone(),
                Bitvector32Term::UInt64Constant(u64::MAX - elements),
            )) == Some(true)
        {
            return Some(true);
        }
    }
    // Addends both offsets share cancel exactly, and constants regroup:
    // `s + 5` is `(s + 4) + 1`, which is how a field's element and a run's
    // base spell one address. Only sums are split, so a pair of leaves pays
    // nothing.
    if matches!(left, PointerOffsetTerm::Add(..)) || matches!(right, PointerOffsetTerm::Add(..)) {
        let (rest_left, rest_right) =
            crate::kernel::assumptions::cancel_common_offset_addends(left, right);
        if let (Some(left), Some(right)) = (rest_left.as_const(), rest_right.as_const()) {
            return Some(left == right);
        }
        // `x + a == x + b` exactly when `a == b`, so once a shared addend
        // cancels, the remainder is the whole question. Decide it there:
        // the rebuilds and decisions below would otherwise read every
        // shared term again on both sides.
        if (rest_left != *left || rest_right != *right)
            && addend_count(&rest_left) + addend_count(&rest_right)
                < addend_count(left) + addend_count(right)
        {
            return pointer_offsets_equal_for_memory_resolution(
                &rest_left,
                &rest_right,
                assumptions,
            );
        }
        if let Some(equal) = mixed_index_offsets_equal(&rest_left, &rest_right, assumptions) {
            return Some(equal);
        }
        // What is left after cancelling may be an unsigned 64-bit index
        // against a constant, `base + x` against `base`: the rule above
        // reads that pair, and the question is strictly smaller.
        if matches!(
            (&rest_left, &rest_right),
            (
                PointerOffsetTerm::Int64Scaled { unsigned: true, .. },
                PointerOffsetTerm::Constant(_)
            ) | (
                PointerOffsetTerm::Constant(_),
                PointerOffsetTerm::Int64Scaled { unsigned: true, .. }
            )
        ) && let Some(equal) =
            pointer_offsets_equal_for_memory_resolution(&rest_left, &rest_right, assumptions)
        {
            return Some(equal);
        }
    }
    let _query =
        ResolutionQueryGuard::enter(ResolutionQuery::OffsetEqual(left.clone(), right.clone()))?;
    if let Some(value) = assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
        left.clone(),
        right.clone(),
    )) {
        return Some(value);
    }
    // These classes denote exact byte offsets, unlike the wrapping scalar
    // index equalities consulted by the guarded rebuild below.
    if assumptions.equality_graph.has_term_equivalences()
        && assumptions.equality_graph.are_offsets_equal(left, right)
    {
        return Some(true);
    }
    // A field displacement plus one signed index is an exact byte offset,
    // not a modular sum of element indices. Move the constant displacement
    // to the concrete side before consulting the existing equality facts.
    // This lets `4 + 4*i == 8` use `i == 1` without general arithmetic search.
    if let Some(width) = common_pointer_offset_element_width(left, right) {
        for (indexed, concrete) in [(left, right), (right, left)] {
            let Some(concrete) = concrete.as_const() else {
                continue;
            };
            if concrete % i64::from(width) != 0 {
                continue;
            }
            let Some(delta) = exact_element_delta_from_offset(indexed, width) else {
                continue;
            };
            let Some(expected) = (concrete / i64::from(width)).checked_sub(delta.constant) else {
                continue;
            };
            let Ok(expected) = i32::try_from(expected) else {
                return Some(false);
            };
            let expected = Bitvector32Term::Constant(expected as u32);
            if delta.index == expected {
                return Some(true);
            }
            if let Some(value) = assumptions
                .exact_condition_value(&ConditionTerm::equal(delta.index.clone(), expected.clone()))
            {
                return Some(value);
            }
            if assumptions.int32_values_known_equal(&delta.index, &expected) {
                return Some(true);
            }
        }
    }
    if let Some(element_width) = common_pointer_offset_element_width(left, right)
        && let (Some(left_index), Some(right_index)) = (
            element_index_from_offset_with_facts(left, element_width, assumptions),
            element_index_from_offset_with_facts(right, element_width, assumptions),
        )
    {
        // The rebuilt indices are residues modulo 2^32. Unequal residues
        // refute exact offset equality, but equal residues affirm it only
        // when both rebuilds are proved not to wrap. Keep this check at the
        // offset boundary so every scalar equality source obeys it.
        let exact = std::cell::OnceCell::new();
        let exact = || {
            *exact.get_or_init(|| {
                assumptions.element_index_rebuild_is_exact_for_width(left, element_width)
                    && assumptions.element_index_rebuild_is_exact_for_width(right, element_width)
            })
        };
        if let (Some(left), Some(right)) = (
            crate::kernel::assumptions::exact_signed_constant(&left_index, assumptions),
            crate::kernel::assumptions::exact_signed_constant(&right_index, assumptions),
        ) {
            if left != right {
                return Some(false);
            }
            if exact() {
                return Some(true);
            }
        }
        if bitvector_terms_proven_equal_for_memory_resolution(
            &left_index,
            &right_index,
            assumptions,
        ) && exact()
        {
            return Some(true);
        }
        if let Some(equal) =
            assumptions.decide_bitvector_equality_shallow(&left_index, &right_index)
            && (!equal || exact())
        {
            return Some(equal);
        }
        // An element index whose recorded constant bounds exclude a constant
        // index is a different word, so the two offsets differ: `1 <= u`
        // places `loc[u]` off `loc[0]` exactly as `u != 0` would. Only the
        // disequality follows: distinct words are distinct residues, and so
        // distinct exact offsets, whatever the rebuilt indices wrapped. The
        // bounds are the ones filed under the index itself, one keyed lookup
        // (`indexed_constant_interval`): this comparison runs for every pair
        // of cells a store or load is placed against, so it may not search.
        let excluded = |symbolic: &Bitvector32Term, constant: &Bitvector32Term| {
            let Some(constant) = signed_bitvector_constant(constant) else {
                return false;
            };
            assumptions
                .indexed_constant_interval(symbolic)
                .is_some_and(|(low, high)| constant < low || high < constant)
        };
        if excluded(&left_index, &right_index) || excluded(&right_index, &left_index) {
            return Some(false);
        }
    }
    // Addition of equal exact byte offsets preserves equality even when
    // folding the whole sum into an int32 index would wrap. Reach this only
    // after cheaper scalar comparisons have failed to decide the question.
    if let (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) =
        (left, right)
        && pointer_offsets_proven_equal_for_memory_resolution(left_a, right_a, assumptions)
        && pointer_offsets_proven_equal_for_memory_resolution(left_b, right_b, assumptions)
    {
        return Some(true);
    }
    match (left.as_const(), right.as_const()) {
        (Some(left), Some(right)) => Some(left == right),
        _ => None,
    }
}

#[cfg(test)]
#[test]
fn indexed_field_offsets_use_exact_displacements() {
    let index = Bitvector32Term::Variable(Variable(849));
    let offset = PointerOffsetTerm::add(
        PointerOffsetTerm::Constant(4),
        PointerOffsetTerm::scale_int32(index.clone(), 4),
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    let concrete = PointerOffsetTerm::Constant(8);
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&offset, &concrete, &assumptions),
        Some(true)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&concrete, &offset, &assumptions),
        Some(true)
    );
    let boundary = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index, Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    // Adding the field offset happens after sign extension: it must not
    // wrap i32::MAX + 1 to i32::MIN before comparing byte addresses.
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &offset,
            &PointerOffsetTerm::Constant(i64::from(i32::MIN) * 4),
            &boundary
        ),
        Some(false)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &offset,
            &PointerOffsetTerm::Constant((i64::from(i32::MAX) + 1) * 4),
            &boundary
        ),
        Some(true)
    );
}

#[cfg(test)]
#[test]
fn a_constant_index_outside_the_recorded_bounds_is_a_different_offset() {
    let index = Bitvector32Term::Variable(Variable(851));
    let scaled = PointerOffsetTerm::scale_int32(index.clone(), 4);
    let at_least_one = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), index.clone()),
        true,
    );
    for constant in [0, -4] {
        let concrete = PointerOffsetTerm::Constant(constant);
        assert_eq!(
            pointer_offsets_equal_for_memory_resolution(&scaled, &concrete, &at_least_one),
            Some(false)
        );
        assert_eq!(
            pointer_offsets_equal_for_memory_resolution(&concrete, &scaled, &at_least_one),
            Some(false)
        );
    }
    // `1 <= u` leaves `u == 1` open: nothing is decided about `a[1]`.
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &scaled,
            &PointerOffsetTerm::Constant(4),
            &at_least_one
        ),
        None
    );
    let unbounded = PureFactContext::new();
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &scaled,
            &PointerOffsetTerm::Constant(0),
            &unbounded
        ),
        None
    );
}

#[cfg(test)]
#[test]
fn memory_resolution_uses_graph_offset_congruence_in_branch_scope() {
    let scalar = |id: u64| Bitvector32Term::Variable(Variable(91_000 + id));
    let offset = |id| {
        PointerOffsetTerm::add(
            PointerOffsetTerm::Constant(4),
            PointerOffsetTerm::scale_int32(scalar(id), 4),
        )
    };
    let named = PointerOffsetTerm::Variable(Variable(91_100));
    let named_fact = ConditionTerm::pointer_offset_equal(offset(2), named.clone());
    let scalar_fact = ConditionTerm::equal(scalar(1), scalar(2));
    let parent = PureFactContext::new().assume_condition(named_fact.clone(), true);
    let branch = parent.clone().assume_condition(scalar_fact.clone(), true);
    let pointer = |offset| Pointer {
        block: PointerBlock::ExternalArgument,
        offset,
    };

    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &parent),
        None
    );
    assert!(!pointers_proven_equal_for_memory_resolution(
        &pointer(offset(1)),
        &pointer(named.clone()),
        &parent,
    ));
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &branch),
        Some(true)
    );
    assert!(pointers_proven_equal_for_memory_resolution(
        &pointer(offset(1)),
        &pointer(named.clone()),
        &branch,
    ));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);

    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(scalar_fact, true));
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &withdrawn),
        Some(true)
    );
    let restricted = branch.restricted_to_facts(&[], &[]);
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &restricted),
        Some(true)
    );
    let retained = branch.without_exact_fact(&Proposition::ConditionIs(named_fact, true));
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &retained),
        Some(true)
    );
}

#[cfg(test)]
#[test]
fn memory_resolution_uses_pointer_classes_across_blocks() {
    let pointer = |block: u64, offset| Pointer {
        block: PointerBlock::Symbolic(Variable(91_200 + block)),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let first = ConditionTerm::pointer_equal(pointer(0, 0), pointer(1, 4));
    let second = ConditionTerm::pointer_equal(pointer(1, 4), pointer(2, 8));
    let parent = PureFactContext::new().assume_condition(first, true);
    let branch = parent.clone().assume_condition(second.clone(), true);
    assert!(!pointers_proven_equal_for_memory_resolution(
        &pointer(0, 12),
        &pointer(2, 20),
        &parent,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &pointer(0, 12),
        &pointer(2, 20),
        &branch,
    ));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(second, true));
    assert!(!pointers_proven_equal_for_memory_resolution(
        &pointer(0, 12),
        &pointer(2, 20),
        &withdrawn,
    ));
}

#[cfg(test)]
#[test]
fn memory_resolution_graph_offsets_keep_load_snapshots_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = crate::kernel::intern_c_memory(CMemory::new().with_block("offset-load", 16));
    let scalar = |id: u64| Bitvector32Term::Variable(Variable(95_000 + id));
    let address = |index| Pointer {
        block: "offset-load".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let loaded = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
            memory,
            &address(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let after = crate::kernel::intern_c_memory(before.memory().clone().store(
        address(scalar(1)),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let left = PointerOffsetTerm::scale_int32(loaded(&before, scalar(1)), 4);
    let right = PointerOffsetTerm::scale_int32(loaded(&before, scalar(2)), 4);
    let changed = PointerOffsetTerm::scale_int32(loaded(&after, scalar(2)), 4);
    let context =
        PureFactContext::new().assume_condition(ConditionTerm::equal(scalar(1), scalar(2)), true);
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&left, &right, &context),
        Some(true)
    );
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&left, &changed, &context),
        Some(true)
    );
}

/// Substitute only stated scalar constants in an address, then use the
/// cell map's exact index. Work is proportional to this address expression.
fn pointer_with_exact_index_constants(pointer: &Pointer, assumptions: &PureFactContext) -> Pointer {
    enum Task<'a> {
        Visit(&'a PointerOffsetTerm),
        Add,
    }
    let mut work = vec![Task::Visit(&pointer.offset)];
    let mut values = Vec::new();
    while let Some(task) = work.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match task {
            Task::Visit(PointerOffsetTerm::Add(left, right)) => {
                work.push(Task::Add);
                work.push(Task::Visit(right));
                work.push(Task::Visit(left));
            }
            Task::Visit(offset @ PointerOffsetTerm::Int32Scaled { value, byte_width }) => {
                values.push(
                    crate::kernel::assumptions::exact_signed_constant(value, assumptions)
                        .and_then(|index| i32::try_from(index).ok())
                        .and_then(|index| i64::from(index).checked_mul(*byte_width))
                        .map(PointerOffsetTerm::Constant)
                        .unwrap_or_else(|| offset.clone()),
                );
            }
            Task::Visit(offset @ PointerOffsetTerm::Int64Scaled { .. }) => {
                values.push(
                    crate::kernel::assumptions::exact_wide_scaled_offset_constant(
                        offset,
                        assumptions,
                    )
                    .map(PointerOffsetTerm::Constant)
                    .unwrap_or_else(|| offset.clone()),
                );
            }
            Task::Visit(offset) => values.push(offset.clone()),
            Task::Add => {
                let right = values.pop().expect("right offset");
                let left = values.pop().expect("left offset");
                if let (Some(left), Some(right)) = (left.as_const(), right.as_const())
                    && left.checked_add(right).is_none()
                {
                    return pointer.clone();
                }
                values.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    Pointer {
        block: pointer.block.clone(),
        offset: values.pop().expect("pointer offset"),
    }
}

/// Resolve this address through exact cells, recorded scalar/pointer aliases,
/// and the indexed interval of cells with the same base address.
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
    let normalized = pointer_with_exact_index_constants(pointer, assumptions);
    if normalized != *pointer
        && let Some(value) = memory
            .known_value(&normalized)
            .or_else(|| memory.known_union_value(&normalized, CType::Int32))
    {
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
    // A load equality asks about this address and its stated aliases, not
    // every stored cell. Recursively trying every cell here makes a failed
    // equality query branch again at each nested load in a pointer.
    assumptions
        .exact_pointer_aliases(pointer)
        .cloned()
        .chain(assumptions.exact_pointer_offset_aliases(pointer))
        .find_map(|alias| {
            crate::instrumentation::record_deterministic_work(1);
            memory
                .known_value(&alias)
                .or_else(|| memory.known_union_value(&alias, CType::Int32))
        })
        .or_else(|| {
            // Add(root, displacement) occupies one contiguous map interval.
            // Query that interval instead of visiting unrelated objects in
            // the shared ExternalArgument block.
            let mut root = &pointer.offset;
            while let PointerOffsetTerm::Add(left, _) = root { root = left; }
            if matches!(root, PointerOffsetTerm::Constant(_)) { return None; }
            let first = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Add(Box::new(root.clone()), Box::new(PointerOffsetTerm::Constant(i64::MIN))),
            };
            memory.cells.concrete().range(first..)
                .take_while(|(stored, _)| stored.block == pointer.block
                    && matches!(&stored.offset, PointerOffsetTerm::Add(left, _) if left.as_ref() == root))
                .find_map(|(stored, value)| {
                    crate::instrumentation::record_deterministic_work(1);
                    pointers_proven_equal_for_memory_resolution(pointer, stored, assumptions)
                        .then(|| value.clone())
                })
                .or_else(|| {
                    memory
                        .cells
                        .runs_based_at(&pointer.block, root)
                        .find_map(|run| {
                            run_value_at_equal_displaced_pointer(run, pointer, root, assumptions)
                        })
                })
        })
}

/// [`stored_value_at_equal_pointer`]'s interval scan over one run: the value
/// of a live slot spelled `root + shift` that `pointer` is proven equal to.
///
/// Only a run based exactly at `root` has such slots (every slot past the
/// first is spelled `root + shift`). Every slot is `root` plus its own
/// constant, so a pointer at `root` plus a constant can be proven at only the
/// slot at that constant; one at `root` plus a scaled index can be proven at
/// a slot only when the facts pin the index to one value, and then only at
/// the slot that value names. An index the facts do not pin names no slot.
/// Any other displacement is asked slot by slot, as the concrete cells are.
fn run_value_at_equal_displaced_pointer(
    run: &crate::kernel::primitives::CellRun,
    pointer: &Pointer,
    root: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    crate::instrumentation::record_deterministic_work(1);
    if run.base().block != pointer.block || run.base().offset != *root || run.live_count() == 0 {
        return None;
    }
    let displacement = match run_access(run, pointer) {
        RunAccess::DistinctBlock => return None,
        RunAccess::Shift(shift) => Some(shift),
        RunAccess::Scaled {
            index,
            scale,
            shift,
        } => {
            let pinned = crate::kernel::assumptions::exact_signed_constant(&index, assumptions)
                .or_else(|| {
                    assumptions
                        .signed_interval(&index)
                        .filter(|(low, high)| low == high)
                        .map(|(low, _)| low)
                });
            let pinned = pinned?;
            pinned
                .checked_mul(scale)
                .and_then(|bytes| bytes.checked_add(shift))
        }
        // The same for an unsigned 64-bit index, whose product is exact.
        RunAccess::ScaledWide {
            index,
            scale,
            shift,
        } => {
            let pinned = crate::kernel::assumptions::exact_sixty_four_bit_constant(
                &index,
                true,
                assumptions,
            )?;
            pinned
                .checked_mul(scale)
                .and_then(|bytes| bytes.checked_add(shift))
        }
        RunAccess::Other => None,
    };
    if let Some(displacement) = displacement {
        let width = i64::from(run.element_width());
        if displacement <= 0 || displacement % width != 0 {
            return None;
        }
        let index = u32::try_from(displacement / width).ok()?;
        return (index < run.count() && !run.holes().contains(index)).then(|| run.value(index));
    }
    run.live_indexes()
        .filter(|index| *index > 0)
        .find_map(|index| {
            crate::instrumentation::record_deterministic_work(1);
            let stored = run.slot_pointer(index);
            pointers_proven_equal_for_memory_resolution(pointer, &stored, assumptions)
                .then(|| run.value(index))
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
        if let Bitvector32Term::Variable(variable) = term {
            return crate::kernel::eval::registered_load_origin_term_for_variable(variable);
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
    // Maintained int32 equality first; no fact-component walk is needed.
    if assumptions.int32_values_known_equal(left, right) {
        return true;
    }
    // Two loads of one cell whose derivations resolve to the same source
    // are equal after a bounded walk over named edges, with no snapshot
    // comparison at all (see `atomic_loads_equal_along_memory_derivations`). The
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
    if let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Int32) = left
        && let Some(CValue::Int32(value)) =
            stored_value_at_equal_pointer(memory, pointer, assumptions)
        && &value != left
        && bitvector_terms_proven_equal_for_memory_resolution(&value, right, assumptions)
    {
        return true;
    }
    if let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Int32) = right
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
    if let binary_term!(Int32, Add, base, addend) = left
        && ((bitvector_terms_proven_equal_for_memory_resolution(base, right, assumptions)
            && bitvector_terms_proven_equal_for_memory_resolution(addend, &zero, assumptions))
            || (bitvector_terms_proven_equal_for_memory_resolution(addend, right, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(base, &zero, assumptions)))
    {
        return true;
    }
    if let binary_term!(Int32, Add, base, addend) = right
        && ((bitvector_terms_proven_equal_for_memory_resolution(left, base, assumptions)
            && bitvector_terms_proven_equal_for_memory_resolution(addend, &zero, assumptions))
            || (bitvector_terms_proven_equal_for_memory_resolution(left, addend, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(base, &zero, assumptions)))
    {
        return true;
    }

    match (left, right) {
        (binary_term!(Int32, Add, left_a, left_b), binary_term!(Int32, Add, right_a, right_b))
        | (
            binary_term!(Int32, Subtract, left_a, left_b),
            binary_term!(Int32, Subtract, right_a, right_b),
        )
        | (
            binary_term!(Int32, Multiply, left_a, left_b),
            binary_term!(Int32, Multiply, right_a, right_b),
        ) => {
            bitvector_terms_proven_equal_for_memory_resolution(left_a, right_a, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(left_b, right_b, assumptions)
        }
        (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
        ) => {
            // Equal addresses are not enough: two reads there are one value
            // only when they are one kind of read.
            left_kind == right_kind
                && pointers_proven_equal_for_memory_resolution(
                    left_pointer,
                    right_pointer,
                    assumptions,
                )
                && !loads_separated_by_recorded_history(
                    left_memory,
                    right_memory,
                    left_pointer,
                    *left_kind,
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

/// Compare int32 *values* through the trusted graph before broader memory
/// resolution. Callers proving exact byte-offset equality must use the
/// separate offset judgment rather than this wrapping value equality.
pub(in crate::kernel) fn int32_values_proven_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    assumptions.int32_values_known_equal(left, right)
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

pub(in crate::kernel) fn c_values_proven_equal_for_memory_resolution(
    left: &CValue,
    right: &CValue,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (CValue::Void, CValue::Void) => true,
        (CValue::Int8(left), CValue::Int8(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Int32(left), CValue::Int32(right)) => {
            int32_values_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Int64(left), CValue::Int64(right))
        | (CValue::UInt64(left), CValue::UInt64(right)) => {
            assumptions.uint64_values_known_equal(left, right)
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Int16(left), CValue::Int16(right))
        | (CValue::UInt8(left), CValue::UInt8(right))
        | (CValue::UInt16(left), CValue::UInt16(right))
        | (CValue::UInt32(left), CValue::UInt32(right))
        | (CValue::Float32(left), CValue::Float32(right))
        | (CValue::Float64(left), CValue::Float64(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            assumptions.pointer_designations_match(left, right)
                && pointers_proven_equal_for_memory_resolution(
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
    // The cell comparison below reads an entry neither side holds as
    // agreement, which holds only between maps over one underlying state
    // (see `snapshot_objects_agree`).
    if left.forgotten.forgotten_from != right.forgotten.forgotten_from
        || left.forgotten.join_inputs != right.forgotten.join_inputs
    {
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
        Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (&left_load, &right_load)
    else {
        return false;
    };
    left_kind == right_kind
        && (pointers_proven_equal_for_memory_resolution(left_pointer, right_pointer, assumptions)
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
    kind: LoadKind,
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
            crate::kernel::api::recorded_load_history(left, right, pointer, kind, assumptions)
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
        Bitvector32Term::MemoryLoad(_, _, _) => Some(term.clone()),
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        _ => None,
    };
    let (
        Some(Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind)),
        Some(Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind)),
    ) = (load(left), load(right))
    else {
        return false;
    };
    // Two reads of one address that differ in kind are two values whatever
    // the history says, so no structural route may call them equal.
    left_pointer == right_pointer
        && (left_kind != right_kind
            || loads_separated_by_recorded_history(
                &left_memory,
                &right_memory,
                &left_pointer,
                left_kind,
                assumptions,
            ))
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
    if pointer.block.is_local_block() {
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
    if !snapshot_objects_agree(left, right, pointer) {
        return false;
    }

    // Slots of a run at a constant gap from the load that clears its bytes
    // are other addresses by arithmetic, as for
    // `memories_match_for_pointer_load_under_assumptions`; spelling each of
    // them out would cost the run's whole extent.
    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    let differing = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "snapshot comparison: differing cells",
        || left.differing_cell_pointers_meeting_load(right, pointer, load_bytes),
    );
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
pub(in crate::kernel) fn differing_cell_byte_width(
    left: &CMemory,
    right: &CMemory,
    cell_pointer: &Pointer,
) -> u32 {
    let stored_width = |memory: &CMemory| {
        memory
            .cells
            .get(cell_pointer)
            .map(|value| value.byte_width())
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
/// `!cell.block.is_local_block()`, a block-name shortcut that dropped
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

/// Whether the three assumption-carrying comparisons agree about the
/// *objects* the two snapshots hold, as against the values in their cells:
/// each block's extent, and which automatic blocks have had their lifetimes
/// ended.
///
/// The cell filter beside this one was corrected to
/// [`cell_is_observable_by_load`]; this one was left as the same block-name
/// shortcut, `!block.is_local_block()`, and it makes the same claim about
/// a different map. A block's extent is what says the object is there and how
/// big it is, so two snapshots that disagree about a local's extent or
/// liveness disagree about the object a load through a pointer that may
/// designate it reads — and `&a` may be handed to a callee and come back as
/// its result, so "the load's pointer is not spelled `local:`" does not mean
/// the load misses every local.
///
/// The filter is now [`local_block_no_pointer_can_reach`], the one
/// [`memories_proven_equal_for_memory_resolution`] spends in the same place: a
/// local whose address is never taken anywhere in the program is not memory
/// any pointer value designates, so no load can tell two snapshots apart by
/// it. That is a property of the whole program's source, which is why it may
/// be spent with neither a pointer nor a fact context. Every other local stays
/// in the comparison.
fn snapshot_objects_agree(left: &CMemory, right: &CMemory, pointer: &Pointer) -> bool {
    let reachable = |block: &PointerBlock| !local_block_no_pointer_can_reach(block);
    // Every caller goes on to compare the two cell maps and treats an entry
    // neither side holds as agreement. That reading is only valid between
    // maps layered over one underlying state: a cell map is knowledge about
    // the state its forget mark names, and a store whose cell was later
    // forgotten leaves no entry on either side for a difference to show.
    // `memories_match_for_pointer_load` asks the same question first for the
    // same reason; two snapshots with different marks are related by the
    // recorded history or not at all.
    left.forgotten.forgotten_from == right.forgotten.forgotten_from
        && left.forgotten.join_inputs == right.forgotten.join_inputs
        && left
            .blocks
            .iter()
            .filter(|(block, _)| reachable(block))
            .eq(right.blocks.iter().filter(|(block, _)| reachable(block)))
        && retirements_agree_for_load(left, right, pointer)
}

/// Whether the two snapshots agree about which automatic objects the load may
/// reach have had their lifetimes ended.
///
/// None of the four "do these snapshots agree about this load" comparisons
/// looked at this map. Once a retired block's cells are gone the tombstone is
/// the only record that its lifetime ended, and a load through a stale alias
/// is exactly the load these comparisons are asked about;
/// `memories_proven_equal_for_memory_resolution`, `CMemory`'s own `eq` and
/// `read_region_identity` all compare it.
///
/// Two exclusions, both sound, and each catches what the other does not: this
/// load's block is proven distinct from that object, or *no* pointer value in
/// the program designates it.
fn retirements_agree_for_load(left: &CMemory, right: &CMemory, pointer: &Pointer) -> bool {
    left.forgotten
        .ended_local_blocks
        .symmetric_difference(&right.forgotten.ended_local_blocks)
        .into_iter()
        .all(|block| {
            !block.observable_by_load(&pointer.block) || local_block_no_pointer_can_reach(block)
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
    let Some(CValue::Int32(Bitvector32Term::MemoryLoad(snapshot, load_pointer, LoadKind::Int32))) =
        materialized.known_value(pointer)
    else {
        return false;
    };
    // The cell holds four bytes of the source; it answers for the read at
    // this address only when the read is no wider.
    crate::kernel::load_access_width_at_address_or_widest(pointer) <= 4
        && pointers_proven_equal_for_memory_resolution(&load_pointer, pointer, assumptions)
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
pub(in crate::kernel) fn common_base_index_offsets(
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
        // Neither address adds anything to its block: the common base is
        // the block itself, and the whole offsets are the indices. This is
        // `p[i]` against `p[j]` for a pointer that is its own block, such as
        // one loaded from memory.
        (left, right)
            if !matches!(left, PointerOffsetTerm::Add(..))
                && !matches!(right, PointerOffsetTerm::Add(..)) =>
        {
            Some((left, right))
        }
        _ => None,
    };
    let (left_index, right_index) = index_pair?;
    Some((left_index.clone(), right_index.clone()))
}

/// Broader pointer proof search, including arithmetic and conditional facts.
/// Use `PureFactContext::pointers_known_equal` when only maintained equality
/// is wanted; memory resolution separately enforces its resource guards.
pub(in crate::kernel) fn pointers_proven_equal_by_reasoning(
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
    if pointer.block.is_local_block() {
        return false;
    }

    // A cell map is knowledge layered over the state named by its forget
    // mark. Equal maps over different marks are not equal states: each may
    // have forgotten a different value at this very pointer. There is no
    // recorded history between the snapshots handled by this matcher that
    // could recover that distinction later.
    //
    // Every comparison below is of the entries observable by the load, and
    // an entry in a block proven distinct from the load's is not observable,
    // so each side walks its candidate ranges (`AliasCandidates`) alone, in
    // the same order on both sides.
    let candidates = AliasCandidates::of_block(&pointer.block);
    left.forgotten.forgotten_from == right.forgotten.forgotten_from
        && left.forgotten.join_inputs == right.forgotten.join_inputs
        && observable_blocks_match_for_load(left, right, pointer, &candidates)
        && retirements_agree_for_load(left, right, pointer)
        && observable_heap_metadata_matches_for_load(left, right, pointer, &candidates)
        && observable_cells_match(&candidates, left, right, pointer)
        && observable_entries_match(
            &candidates,
            &left.union_cells,
            &right.union_cells,
            |(cell_pointer, _)| cell_pointer.block.observable_by_load(&pointer.block),
        )
}

/// [`observable_entries_match`] over the cells of two memories: their runs
/// compared whole ([`CellStore::observable_runs_match`]) and then their
/// concrete cells, or their logical maps where the runs do not pair up.
///
/// [`CellStore::observable_runs_match`]: crate::kernel::primitives::CellStore::observable_runs_match
fn observable_cells_match(
    candidates: &AliasCandidates,
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
) -> bool {
    let observable = |cell_pointer: &Pointer| cell_pointer.block.observable_by_load(&pointer.block);
    let runs_match = left.cells.observable_runs_match(&right.cells, |run| {
        candidates.admits_block(&run.base().block) && observable(run.base())
    });
    let answer = match runs_match {
        Some(false) => false,
        Some(true) => observable_entries_match(
            candidates,
            left.cells.concrete(),
            right.cells.concrete(),
            observable,
        ),
        None => {
            // The runs do not pair up: walk both stores' candidate cells in
            // order, as the logical maps would, spelling a run's slots only
            // as the walk reaches them, so a difference early in the walk
            // stops it there.
            let visited = std::cell::Cell::new(0usize);
            let equal = left
                .cells
                .candidate_logical_entries(candidates)
                .inspect(|_| visited.set(visited.get() + 1))
                .filter(|(key, _)| observable(key))
                .eq(right
                    .cells
                    .candidate_logical_entries(candidates)
                    .inspect(|_| visited.set(visited.get() + 1))
                    .filter(|(key, _)| observable(key)));
            crate::instrumentation::record_deterministic_work(visited.get());
            equal
        }
    };
    #[cfg(debug_assertions)]
    if left
        .cells
        .runs()
        .chain(right.cells.runs())
        .all(|run| run.count() <= crate::kernel::primitives::CHECKED_RUN_SLOTS)
    {
        crate::instrumentation::uncharged_debug_check(|| {
            assert_eq!(
                answer,
                observable_entries_match(
                    candidates,
                    left.cells.logical(),
                    right.cells.logical(),
                    observable,
                ),
                "comparing two memories' runs whole disagrees with comparing their cells for a load at {pointer:?}"
            );
        });
    }
    answer
}

/// Whether the candidate entries `observable` accepts are the same in both
/// maps. Charges one work unit per candidate entry visited.
fn observable_entries_match<K: BlockKeyed, V: PartialEq>(
    candidates: &AliasCandidates,
    left: &SnapshotMap<K, V>,
    right: &SnapshotMap<K, V>,
    observable: impl Fn(&K) -> bool,
) -> bool {
    if left.ptr_eq(right) {
        return true;
    }
    let visited = std::cell::Cell::new(0usize);
    let equal = candidates
        .entries(left)
        .inspect(|_| visited.set(visited.get() + 1))
        .filter(|(key, _)| observable(key))
        .eq(candidates
            .entries(right)
            .inspect(|_| visited.set(visited.get() + 1))
            .filter(|(key, _)| observable(key)));
    crate::instrumentation::record_deterministic_work(visited.get());
    equal
}

/// [`observable_entries_match`] for a set.
fn observable_elements_match<K: BlockKeyed>(
    candidates: &AliasCandidates,
    left: &SnapshotSet<K>,
    right: &SnapshotSet<K>,
    observable: impl Fn(&K) -> bool,
) -> bool {
    let visited = std::cell::Cell::new(0usize);
    let equal = candidates
        .elements(left)
        .inspect(|_| visited.set(visited.get() + 1))
        .filter(|key| observable(key))
        .eq(candidates
            .elements(right)
            .inspect(|_| visited.set(visited.get() + 1))
            .filter(|key| observable(key)));
    crate::instrumentation::record_deterministic_work(visited.get());
    equal
}

/// Whether the two snapshots agree about every object this load may name.
///
/// Havoc markers are global snapshot identities and therefore remain even
/// though their synthetic concrete block names are distinct from ordinary
/// pointers. Every other block is selected with the same may-alias predicate
/// as cells. A never-address-taken local is the one safe omission: no pointer
/// value in the program can designate it.
fn observable_blocks_match_for_load(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    candidates: &AliasCandidates,
) -> bool {
    // The havoc markers by their name ranges, then the candidate blocks the
    // load may name. A marker that is also a candidate is compared twice,
    // on both sides alike.
    havoc_marker_blocks(&left.blocks).eq(havoc_marker_blocks(&right.blocks))
        && observable_entries_match(candidates, &left.blocks, &right.blocks, |block| {
            !local_block_no_pointer_can_reach(block) && block.observable_by_load(&pointer.block)
        })
}

/// Whether heap facts that can change this load agree in two unrelated
/// snapshots.
///
/// Heap metadata is part of load evaluation even when no concrete cell is
/// cached: the load reads deallocation, uninitialized-cell, retained
/// initialization and calloc-zero facts directly. Pending allocation and
/// reallocation bookkeeping is deliberately absent; it changes future path
/// refinement, not what an existing load reads. A fresh heap block is
/// structurally distinct from every other block, so filter each map by the
/// same observable-block question instead of requiring unrelated heap
/// allocations to match.
fn observable_heap_metadata_matches_for_load(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    candidates: &AliasCandidates,
) -> bool {
    let observable = |candidate: &Pointer| candidate.block.observable_by_load(&pointer.block);
    observable_entries_match(
        candidates,
        &left.heap.deallocated_allocations,
        &right.heap.deallocated_allocations,
        observable,
    ) && observable_elements_match(
        candidates,
        &left.heap.uninitialized_allocations,
        &right.heap.uninitialized_allocations,
        observable,
    ) && observable_entries_match(
        candidates,
        &left.heap.uninitialized_objects,
        &right.heap.uninitialized_objects,
        |candidate| candidate.block.observable_by_load(&pointer.block),
    ) && observable_entries_match(
        candidates,
        left.heap.initialized.as_map(),
        right.heap.initialized.as_map(),
        observable,
    ) && observable_elements_match(
        candidates,
        &left.heap.zeroed_allocations,
        &right.heap.zeroed_allocations,
        observable,
    ) && observable_entries_match(
        candidates,
        &left.heap.zeroed_prefix_allocations,
        &right.heap.zeroed_prefix_allocations,
        observable,
    )
}

#[cfg(test)]
#[test]
fn unrelated_forgotten_snapshots_do_not_prove_their_loads_equal() {
    let pointer = Pointer {
        block: "unrelated-forgotten".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let shell = CMemory::new().with_block("unrelated-forgotten", 4);
    let left_source = crate::kernel::intern_c_memory_ref(
        &shell
            .clone()
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1))),
    );
    let right_source = crate::kernel::intern_c_memory_ref(
        &shell
            .clone()
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(2))),
    );
    let mut left = shell.clone();
    left.mark_forgotten_from(&left_source);
    let mut right = shell;
    right.mark_forgotten_from(&right_source);

    assert_eq!(
        left.cells, right.cells,
        "the attack has identical cell maps"
    );
    assert_ne!(
        left.forgotten.forgotten_from, right.forgotten.forgotten_from,
        "the maps describe different underlying states"
    );
    assert!(
        !memories_match_for_pointer_load(&left, &right, &pointer),
        "a cell-map match must not erase the identity of forgotten knowledge"
    );

    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    assert!(
        !PureFactContext::new().memory_loads_proven_equal(&load(&left), &load(&right)),
        "unconnected snapshots over different forgotten sources are not one load"
    );
}

#[cfg(test)]
#[test]
fn unrelated_snapshots_do_not_erase_object_or_heap_state_visible_to_the_load() {
    let loads_proven_equal = |left: &CMemory, right: &CMemory, pointer: &Pointer| {
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        PureFactContext::new().memory_loads_proven_equal(&load(left), &load(right))
    };
    let symbolic = Pointer {
        block: PointerBlock::Symbolic(Variable(7_620_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let bare = CMemory::new();
    let with_global = bare
        .clone()
        .with_block_without_derivation("global:unrelated-snapshot", 4);
    assert!(
        !memories_match_for_pointer_load(&bare, &with_global, &symbolic),
        "a symbolic load can designate the object present on only one side"
    );
    assert!(
        !loads_proven_equal(&bare, &with_global, &symbolic),
        "object disagreement in unrelated snapshots cannot prove load equality"
    );

    let heap_pointer = Pointer {
        block: PointerBlock::Heap(7_620_002),
        offset: PointerOffsetTerm::Constant(0),
    };
    let heap_shell = CMemory::new().with_block_without_derivation(heap_pointer.block.clone(), 4);
    let mut uninitialized = heap_shell.clone();
    std::sync::Arc::make_mut(&mut uninitialized.heap)
        .live_allocations
        .insert(heap_pointer.clone(), Bitvector32Term::Constant(4));
    std::sync::Arc::make_mut(&mut uninitialized.heap)
        .uninitialized_allocations
        .insert(heap_pointer.clone());
    let mut zeroed = heap_shell;
    std::sync::Arc::make_mut(&mut zeroed.heap)
        .live_allocations
        .insert(heap_pointer.clone(), Bitvector32Term::Constant(4));
    std::sync::Arc::make_mut(&mut zeroed.heap)
        .zeroed_allocations
        .insert(heap_pointer.clone());
    assert!(
        !memories_match_for_pointer_load(&uninitialized, &zeroed, &heap_pointer),
        "an uninitialized load and calloc's implicit zero are not one value"
    );
    assert!(
        !loads_proven_equal(&uninitialized, &zeroed, &heap_pointer),
        "heap-read metadata disagreement cannot prove load equality"
    );

    let concrete = Pointer {
        block: "unrelated-concrete".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let concrete_memory = CMemory::new().with_block("unrelated-concrete", 4);
    let mut with_unrelated_heap = concrete_memory.clone();
    std::sync::Arc::make_mut(&mut with_unrelated_heap.blocks)
        .insert(PointerBlock::Heap(7_620_003), CBlock::new(4));
    std::sync::Arc::make_mut(&mut with_unrelated_heap.heap)
        .live_allocations
        .insert(
            Pointer {
                block: PointerBlock::Heap(7_620_003),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(4),
        );
    assert!(
        memories_match_for_pointer_load(&concrete_memory, &with_unrelated_heap, &concrete),
        "a fresh allocation cannot affect a load through another concrete block"
    );
    assert!(
        loads_proven_equal(&concrete_memory, &with_unrelated_heap, &concrete),
        "the matcher still ignores heap metadata this pointer cannot observe"
    );

    let pending_base = Pointer {
        block: PointerBlock::Symbolic(Variable(7_620_004)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let with_pending = concrete_memory.clone().with_pending_heap_allocation(
        pending_base,
        Bitvector32Term::Constant(4),
        false,
    );
    assert!(
        memories_match_for_pointer_load(&concrete_memory, &with_pending, &concrete),
        "an unresolved future allocation changes no existing load"
    );
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

/// The elements that answer for every live slot of `run` in a per-slot
/// question about how its slots' loads are named, or `None` when each slot
/// has to be asked itself.
///
/// A slot's value is the canonical load of its own element in the run's
/// source. When that source holds nothing a load of the run's block could
/// observe — no cell, no typed view and no live run slot in any block such a
/// load may alias — every element's load projects the source to the same
/// memory: the projection depends on the pointer only through the cells and
/// views it keeps, of which there are none, and through the pointer's block,
/// which every element shares. A projection with no recorded derivation is
/// then the point every element's load is named at. What is left to differ
/// between two elements is the pointer's spelling: element 0 is spelled as
/// the base itself, the element whose shift cancels a constant the base ends
/// in (if any) as the base's bare stem, and every other element as that stem
/// plus its own constant ([`CellRun::slot_pointer`]), so the first live
/// element of each of those shapes answers for its shape.
///
/// [`CellRun::slot_pointer`]: crate::kernel::primitives::CellRun::slot_pointer
pub(in crate::kernel) fn run_shape_representatives(
    run: &crate::kernel::primitives::CellRun,
) -> Option<Vec<u32>> {
    if let crate::kernel::primitives::RunValueMode::Copy { source_base } = run.value_mode() {
        let source_run = crate::kernel::primitives::CellRun::new(
            source_base.clone(),
            run.element_width(),
            run.element_type(),
            run.count(),
            run.source().clone(),
            run.holes().clone(),
        );
        if copied_source_has_observable_slots(&source_run) {
            return None;
        }
        let source_stem = run_stem_slot(&source_run);
        let destination_stem = run_stem_slot(run);
        let mut representatives = Vec::new();
        for index in [Some(0), source_stem, destination_stem]
            .into_iter()
            .flatten()
        {
            if index < run.count()
                && !run.holes().contains(index)
                && !representatives.contains(&index)
            {
                representatives.push(index);
            }
        }
        if let Some(index) = run.live_indexes().find(|index| {
            *index != 0 && Some(*index) != source_stem && Some(*index) != destination_stem
        }) {
            representatives.push(index);
        }
        if let Some(first) = run.live_indexes().next()
            && !representatives.contains(&first)
        {
            representatives.push(first);
        }
        for index in &representatives {
            let pointer = source_run.slot_pointer(*index);
            let value = source_run.value(*index);
            if materialized_cell_source(&pointer, &value)
                .is_some_and(|source| source.derivation().is_some())
            {
                return None;
            }
        }
        return Some(representatives);
    }
    let first = run.live_indexes().next()?;
    if source_holds_cells_observable_by(run.source(), &run.base().block) {
        return None;
    }
    let stem = run_stem_slot(run).filter(|index| !run.holes().contains(*index));
    let first_later = run
        .live_indexes()
        .find(|later| *later > 0 && Some(*later) != stem);
    let mut representatives = vec![first];
    for representative in first_later.into_iter().chain(stem) {
        if !representatives.contains(&representative) {
            representatives.push(representative);
        }
    }
    for representative in &representatives {
        let cell_pointer = run.slot_pointer(*representative);
        let value = run.value(*representative);
        if materialized_cell_source(&cell_pointer, &value)
            .is_some_and(|named_at| named_at.derivation().is_some())
        {
            return None;
        }
    }
    Some(representatives)
}

// A copied run can skip represented source lanes: those were captured as
// independent cells/runs and are holes here. Only a live slot that could fold
// to a stored value invalidates the uniform spelling argument. Walk source
// representations, never the logical array length.
fn copied_source_has_observable_slots(run: &crate::kernel::primitives::CellRun) -> bool {
    if !source_holds_cells_observable_by(run.source(), &run.base().block) {
        return false;
    }
    let source = run.source().memory();
    let candidates = AliasCandidates::of_block(&run.base().block);
    let width = i64::from(run.element_width());
    let intersects = |shift: i64, bytes: u64| {
        let low = shift.div_euclid(width).max(0).min(i64::from(run.count())) as u32;
        let Some(end) = shift.checked_add(i64::try_from(bytes).unwrap_or(i64::MAX)) else {
            return true;
        };
        let high = (end.saturating_add(width - 1).div_euclid(width))
            .max(0)
            .min(i64::from(run.count())) as u32;
        !run.holes().covers_range(low, high)
    };
    for (pointer, value) in candidates.entries(source.cells.concrete()) {
        crate::instrumentation::record_deterministic_work(1);
        if !pointer.block.observable_by_load(&run.base().block) {
            continue;
        }
        let RunAccess::Shift(shift) = run_access(run, pointer) else {
            return true;
        };
        if intersects(shift, u64::from(value.byte_width())) {
            return true;
        }
    }
    if candidates.any_entry(&source.union_cells, |(pointer, _), _| {
        pointer.block.observable_by_load(&run.base().block)
    }) {
        return true;
    }
    for held in source.cells.candidate_runs(&candidates) {
        crate::instrumentation::record_deterministic_work(1);
        if !held.base().block.observable_by_load(&run.base().block) {
            continue;
        }
        let RunAccess::Shift(shift) = run_access(run, held.base()) else {
            return true;
        };
        for (low, high) in held.live_intervals().intervals() {
            if intersects(
                shift.saturating_add(i64::from(low) * i64::from(held.element_width())),
                u64::from(high - low) * u64::from(held.element_width()),
            ) {
                return true;
            }
        }
    }
    false
}

/// The later element of `run` spelled as its base's bare stem: the one whose
/// shift cancels a negative constant the base ends in.
fn run_stem_slot(run: &crate::kernel::primitives::CellRun) -> Option<u32> {
    let (stem, constant) = crate::kernel::primitives::offset_stem_and_constant(&run.base().offset);
    stem?;
    let width = i64::from(run.element_width());
    if constant >= 0 || width <= 0 || constant % width != 0 {
        return None;
    }
    u32::try_from(-constant / width)
        .ok()
        .filter(|index| *index < run.count())
}

/// Whether `source` holds a cell, a typed view or a live run slot that a
/// load in `block` could observe. A function of the snapshot and the block
/// alone, asked of a run's source by every walk that visits the run, so it
/// is memoized by interned snapshot identity; a miss visits the source's
/// candidate entries up to the first observable one.
fn source_holds_cells_observable_by(
    source: &crate::kernel::primitives::SharedCMemory,
    block: &crate::kernel::primitives::PointerBlock,
) -> bool {
    let key = (source.clone(), block.clone());
    if let Some(known) = SOURCE_OBSERVABLE_BY_BLOCK.with(|memo| memo.borrow().get(&key).copied()) {
        return known;
    }
    let memory = source.memory();
    let candidates = AliasCandidates::of_block(block);
    // An unresolved block's candidates are every block, slots no pointer
    // value reaches included; the store's maintained reachable map leaves
    // those out, so the first observable cell is found without visiting
    // every such slot ahead of it.
    let observable_cell = if matches!(
        block,
        crate::kernel::primitives::PointerBlock::Symbolic(_)
            | crate::kernel::primitives::PointerBlock::LoadedPointer(_)
    ) {
        let mut visited = 0usize;
        let found = memory
            .cells
            .caught_up_pointer_reachable()
            .iter()
            .inspect(|_| visited += 1)
            .any(|(cell, _)| cell.block.observable_by_load(block));
        crate::instrumentation::record_deterministic_work(visited);
        found
    } else {
        candidates.any_entry(memory.cells.concrete(), |cell, _| {
            cell.block.observable_by_load(block)
        })
    };
    let observable = observable_cell
        || candidates.any_entry(&memory.union_cells, |(cell, _), _| {
            cell.block.observable_by_load(block)
        })
        || memory
            .cells
            .candidate_runs(&candidates)
            .any(|other| other.base().block.observable_by_load(block));
    SOURCE_OBSERVABLE_BY_BLOCK.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len() >= RESOLUTION_QUERY_MEMO_LIMIT {
            memo.clear();
        }
        memo.insert(key, observable);
    });
    observable
}

/// The representative of element `index` among `representatives`
/// ([`run_shape_representatives`]): element 0 and the bare-stem element
/// answer for themselves, and the first other later representative for
/// every other later element.
#[cfg(debug_assertions)]
pub(in crate::kernel) fn run_shape_representative(
    run: &crate::kernel::primitives::CellRun,
    representatives: &[u32],
    index: u32,
) -> u32 {
    let stem = run_stem_slot(run);
    if index == 0 || Some(index) == stem {
        return index;
    }
    *representatives
        .iter()
        .find(|representative| **representative > 0 && Some(**representative) != stem)
        .unwrap_or(&representatives[0])
}

/// The load-canonical source of each live slot of `run`, as
/// [`canonical_memory_for_pointer_load_uncached`] asks it of a cell: one
/// answer per spelling shape where [`run_shape_representatives`] finds the
/// slots uniform, and one per slot otherwise.
fn run_materialization_sources(run: &crate::kernel::primitives::CellRun) -> Vec<Option<CMemory>> {
    let slot_source = |index: u32| {
        let cell_pointer = run.slot_pointer(index);
        let value = run.value(index);
        let source = materialized_cell_source(&cell_pointer, &value)?;
        Some(canonical_memory_for_pointer_load(&source, &cell_pointer))
    };
    let Some(representatives) = run_shape_representatives(run) else {
        return run.live_indexes().map(slot_source).collect();
    };
    let answers = representatives
        .iter()
        .map(|index| slot_source(*index))
        .collect::<Vec<_>>();
    #[cfg(debug_assertions)]
    if run.count() <= crate::kernel::primitives::CHECKED_RUN_SLOTS {
        crate::instrumentation::uncharged_debug_check(|| {
            for index in run.live_indexes() {
                let representative = run_shape_representative(run, &representatives, index);
                let position = representatives
                    .iter()
                    .position(|candidate| *candidate == representative)
                    .expect("a listed representative");
                assert_eq!(
                    slot_source(index),
                    answers[position],
                    "a run's load-canonical source for its spelling shape disagrees with element {index}'s own in {run:?}"
                );
            }
        });
    }
    answers
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
    // A cell in a block proven distinct from the load's is not observable
    // by it, so every scan below visits the candidates alone.
    let candidates = AliasCandidates::of_block(&pointer.block);
    let unresolved = matches!(
        pointer.block,
        PointerBlock::Symbolic(_)
            | PointerBlock::LoadedPointer(_)
            | PointerBlock::ExternalArgument
            | PointerBlock::ExternalObject(_)
    );
    // A load through an unresolved pointer observes only pointer-reachable
    // cells; reading them from the store's maintained reachable map skips
    // the slots no pointer value can reach without visiting each one.
    let reachable = unresolved.then(|| {
        if matches!(
            pointer.block,
            PointerBlock::ExternalArgument | PointerBlock::ExternalObject(_)
        ) {
            memory.cells.caught_up_external_reachable()
        } else {
            memory.cells.caught_up_pointer_reachable()
        }
    });
    let mut visited = 0usize;
    // Lazily: the collection below stops at the first cell that is not a
    // cached load, so an ordinary store costs one visit, not every cell.
    let observable: Box<dyn Iterator<Item = (&Pointer, &CValue)>> = match &reachable {
        Some(reachable) => Box::new(reachable.iter()),
        None => Box::new(candidates.entries(memory.cells.concrete())),
    };
    let materialization_sources = observable
        .inspect(|_| visited += 1)
        .filter(|(cell_pointer, _)| cell_pointer.block.observable_by_load(&pointer.block))
        .map(|(cell_pointer, value)| {
            let source = materialized_cell_source(cell_pointer, value)?;
            Some(canonical_memory_for_pointer_load(&source, cell_pointer))
        })
        .chain(
            memory
                .cells
                .candidate_runs(&candidates)
                .filter(|run| run.base().block.observable_by_load(&pointer.block))
                .flat_map(run_materialization_sources),
        )
        .collect::<Option<Vec<_>>>();
    crate::instrumentation::record_deterministic_work(visited);
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
        let markers = havoc_marker_blocks(&memory.blocks)
            .map(|(block, size)| (block.clone(), size.clone()))
            .collect::<Vec<_>>();
        let blocks = std::sync::Arc::make_mut(&mut canonical.blocks);
        for (block, size) in markers {
            blocks.get_or_insert(block, size);
        }
        // A forget mark survives the jump for the same reason a havoc marker
        // does, and it is the source's mark that must not be inherited: the
        // cells' common source may be a state this one has since forgotten
        // things from, and wearing that state's identity is exactly what
        // names a changed load `old(...)`.
        std::sync::Arc::make_mut(&mut canonical.forgotten).forgotten_from =
            memory.forgotten.forgotten_from;
        std::sync::Arc::make_mut(&mut canonical.forgotten).join_inputs =
            memory.forgotten.join_inputs.clone();
    }
    // Only the cells below decide what a load reads. Declaring a block writes
    // nothing, so the block list stays the load's own block plus the havoc
    // markers even where a cell of another block is kept.
    //
    // Each map is rebuilt from the entries it keeps, found by key range, so
    // the unrelated blocks and cells are never visited.
    let blocks = canonical
        .blocks
        .get(&pointer.block)
        .map(|size| (pointer.block.clone(), size.clone()))
        .into_iter()
        .chain(
            havoc_marker_blocks(&canonical.blocks)
                .map(|(block, size)| (block.clone(), size.clone())),
        )
        .collect::<SnapshotMap<_, _>>();
    //
    // A jump keeps only the source cells this memory still holds: the
    // surviving cells are materializations of the source, but a source cell
    // this memory lacks was erased since (a havoc wrote it), and carrying it
    // over would make the snapshot the load names record a value the cell no
    // longer holds (pinned by
    // `a_load_projection_jump_does_not_restore_a_havocked_cell`).
    let mut cells = (*canonical.cells).clone();
    let keep = |cell_pointer: &Pointer, value: &CValue| {
        cell_pointer.block.observable_by_load(&pointer.block)
            && !cell_disjoint_from_load_by_constant_offset(cell_pointer, value, pointer)
            && (!jumped || memory.cells.get(cell_pointer).is_some())
    };
    // A load through an unresolved pointer observes every pointer-reachable
    // cell outside a few key ranges; projecting from the store's maintained
    // reachable map keeps the cells of other objects without visiting them,
    // so the cost does not grow with every object the memory holds
    // (`roadmap/scaling.md` cause 6).
    let mut visited = match unresolved
        .then(|| cells.retain_for_unresolved_load(pointer, keep))
        .flatten()
    {
        Some(visited) => visited,
        None => cells.retain_only_candidates_by(&candidates, keep, |run| {
            // Dropping a run this memory does not hold forgets knowledge,
            // which a projection may always do.
            if jumped && !memory.cells.holds_run(run) {
                return (SlotSet::Nothing, RuleAnswer::Sound);
            }
            run_slots_kept_by_load_projection(run, pointer)
        }),
    };
    let union_cells = candidates
        .entries(&canonical.union_cells)
        .inspect(|_| visited += 1)
        .filter(|((cell_pointer, _), value)| {
            cell_pointer.block.observable_by_load(&pointer.block)
                && !cell_disjoint_from_load_by_constant_offset(cell_pointer, value, pointer)
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect::<SnapshotMap<_, _>>();
    crate::instrumentation::record_deterministic_work(visited);
    canonical.blocks = std::sync::Arc::new(blocks);
    canonical.cells = std::sync::Arc::new(cells);
    canonical.union_cells = std::sync::Arc::new(union_cells);
    canonical.record_diagnostic_transform(
        "project memory for pointer read",
        vec![memory.clone()],
        vec![CValue::pointer(pointer.clone())],
    );
    canonical
}

/// The loop- and call-havoc marker blocks of a block map, found as the two
/// key ranges their name prefixes occupy (concrete block names order as
/// strings, so the names sharing a prefix are contiguous).
pub(in crate::kernel) fn havoc_marker_blocks(
    blocks: &SnapshotMap<PointerBlock, CBlock>,
) -> impl Iterator<Item = (&PointerBlock, &CBlock)> {
    ["call-havoc:", "havoc:"]
        .into_iter()
        .flat_map(move |prefix| {
            blocks
                .range::<_, PointerBlock>(PointerBlock::Concrete(prefix.to_string())..)
                .take_while(move |(block, _)| block.starts_with(prefix))
        })
}

/// Splits a pointer offset into its non-constant atoms and total constant
/// byte shift.
///
/// The offset is an exact sum, so its summands are what may be separated:
/// every `Constant` summand joins the shift, and so does an `int32` scaled
/// index whose value is a constant, at its signed value times the width.
/// A scaled index that is not a constant is one atom, *whole*. Its value is
/// a 32-bit word, and `Int32Scaled { i + c }` is `sext(i + c) * w`, which is
/// `sext(i) * w + c * w` only when `i + c` does not wrap. A signed C index
/// cannot wrap there, but an index converted from an unsigned sum
/// (`(int32)(u + 2147483648u)`) wraps by definition, and reading its
/// constant into the shift placed the access `2^32` elements from where it
/// is: a store the facts kept inside a run was judged to miss every slot.
/// This split has no facts to prove the sum does not wrap, so it never
/// takes the sum apart; pairs such as `i` and `i + 1` are decided by the
/// fact-reading ladders instead, which compare the words themselves.
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
                match signed_bitvector_constant(value)
                    .and_then(|value| value.checked_mul(*byte_width))
                {
                    Some(bytes) => *shift += bytes,
                    None => atoms.push(offset.clone()),
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

/// Where an access lies relative to the elements of a [`CellRun`], decided for
/// the whole run: the element slots all share the run base's non-constant
/// atoms and differ only in their constant byte shift, so every per-cell rule
/// below that compares an access with a slot by its atoms and constant shift
/// answers the same way for a whole interval of elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::kernel) enum RunAccess {
    /// The access is in a block proven distinct from the run's.
    DistinctBlock,
    /// The access has the run base's atoms and this constant byte shift from
    /// element 0.
    Shift(i64),
    /// The access has the run base's atoms plus one scaled index, and this
    /// constant byte shift from element 0.
    Scaled {
        index: Bitvector32Term,
        scale: i64,
        shift: i64,
    },
    /// The same with an unsigned 64-bit index, which is not read as a
    /// signed word.
    ScaledWide {
        index: Bitvector32Term,
        scale: i64,
        shift: i64,
    },
    /// Anything else: another base, a block that may be the run's, or a
    /// shape with more than one extra atom.
    Other,
}

/// [`RunAccess`] for `pointer`, read structurally.
pub(in crate::kernel) fn run_access(run: &CellRun, pointer: &Pointer) -> RunAccess {
    if run.base().blocks_proven_distinct(pointer) {
        return RunAccess::DistinctBlock;
    }
    if run.base().block != pointer.block {
        return RunAccess::Other;
    }
    let (base_atoms, base_shift) = offset_atoms_and_constant(&run.base().offset);
    let (atoms, shift) = offset_atoms_and_constant(&pointer.offset);
    if atoms == base_atoms {
        return RunAccess::Shift(shift - base_shift);
    }
    // One extra atom beyond the base's: remove the base's atoms one by one.
    let mut rest = atoms;
    for atom in &base_atoms {
        let Some(position) = rest.iter().position(|candidate| candidate == atom) else {
            return RunAccess::Other;
        };
        rest.remove(position);
    }
    match rest.as_slice() {
        [PointerOffsetTerm::Int32Scaled { value, byte_width }] if *byte_width > 0 => {
            RunAccess::Scaled {
                index: value.as_ref().clone(),
                scale: *byte_width,
                shift: shift - base_shift,
            }
        }
        [
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
        ] if *byte_width > 0 => RunAccess::ScaledWide {
            index: value.as_ref().clone(),
            scale: *byte_width,
            shift: shift - base_shift,
        },
        _ => RunAccess::Other,
    }
}

/// [`PureFactContext::resolve_memory_load_value`]'s cell scan over one run:
/// the live slot whose pointer a load at `pointer` is at, and whether some
/// other live slot is neither proven at it nor proven elsewhere. `None`
/// sends the caller to assumption-aware compact slot selection.
///
/// That scan compares start addresses. A pointer in a block proven distinct
/// from the run's is elsewhere than every slot. One with the base's atoms and
/// a constant shift is at the slot starting at that shift, if there is one,
/// and at a different constant distance from every other slot, which the
/// facts need not be consulted to tell apart.
///
/// [`PureFactContext::resolve_memory_load_value`]: crate::kernel::PureFactContext::resolve_memory_load_value
pub(in crate::kernel) fn run_slots_resolving_load(
    run: &CellRun,
    pointer: &Pointer,
) -> Option<(Option<u32>, bool)> {
    // One step of the caller's scan, which charges the visit.
    match run_access(run, pointer) {
        RunAccess::DistinctBlock => Some((None, false)),
        RunAccess::Shift(shift) => {
            let width = i64::from(run.element_width());
            let index = (width > 0 && shift >= 0 && shift % width == 0)
                .then(|| u32::try_from(shift / width).ok())
                .flatten()
                .filter(|index| *index < run.count() && !run.holes().contains(*index));
            Some((index, false))
        }
        RunAccess::Scaled { .. } | RunAccess::ScaledWide { .. } | RunAccess::Other => None,
    }
}

/// The elements of `run` whose bytes `[k * width, k * width + value_width)`
/// meet the access bytes `[shift, shift + bytes)`, as `low..high`.
pub(in crate::kernel) fn run_elements_meeting(run: &CellRun, shift: i64, bytes: i64) -> (u32, u32) {
    let width = i64::from(run.element_width()).max(1);
    let value_width = i64::from(run.value_width()).max(1);
    // k * width < shift + bytes  and  shift < k * width + value_width
    let high = (shift + bytes - 1).div_euclid(width) + 1;
    let low = (shift - value_width).div_euclid(width) + 1;
    let clamp = |value: i64| value.clamp(0, i64::from(run.count())) as u32;
    let (low, high) = (clamp(low), clamp(high));
    (low, high.max(low))
}

/// Which of `run`'s live slots the distinct-cell reduction of a load of
/// `bytes` bytes at `pointer` keeps: every slot not both proven distinct from
/// the load and proven to share none of its bytes.
///
/// `normalized` holds the pointer with its exactly known index constants
/// substituted, computed on the first run a query asks about and shared by
/// the rest.
pub(in crate::kernel) fn run_slots_kept_by_load_reduction(
    run: &CellRun,
    pointer: &Pointer,
    normalized: &std::cell::OnceCell<Pointer>,
    bytes: u32,
    assumptions: &PureFactContext,
) -> (SlotSet, RuleAnswer) {
    let normalized =
        normalized.get_or_init(|| pointer_with_exact_index_constants(pointer, assumptions));
    (
        run_slots_kept_by_load_reduction_set(run, normalized, bytes),
        RuleAnswer::Sound,
    )
}

/// The slots of [`run_slots_kept_by_load_reduction`]. Dropping a cell only
/// renames the load at a snapshot that does not record it, so the answer
/// has two obligations, not one: it may drop a slot only when the slot's
/// bytes provably miss the load's, which the constant byte arithmetic of a
/// `Shift` decides for every slot at once, and it may keep any slot, which is
/// what it does for a symbolic index (the ladder may still drop an element a
/// fact bounds away; keeping it names the load at a snapshot that records
/// one more cell, which the load does not read).
fn run_slots_kept_by_load_reduction_set(
    run: &CellRun,
    normalized: &Pointer,
    bytes: u32,
) -> SlotSet {
    match run_access(run, normalized) {
        RunAccess::DistinctBlock => SlotSet::Nothing,
        // Common atoms and unequal constants are distinct addresses, and the
        // constant gap decides the bytes exactly: a slot survives only where
        // its bytes meet the load's.
        RunAccess::Shift(shift) => {
            let (low, high) = run_elements_meeting(run, shift, i64::from(bytes));
            SlotSet::Elements(low, high)
        }
        // A scaled index is distinct from an element only where the facts
        // bound it away from that element. When the index's known range
        // reaches past both ends of the run, no element is bounded away and
        // every slot stays; anything narrower is asked slot by slot.
        RunAccess::Scaled { .. } => SlotSet::All,
        // Another base in a block the run's may be: no constant gap relates
        // the two, so no slot is shown to miss the load's bytes.
        RunAccess::ScaledWide { .. } | RunAccess::Other => SlotSet::All,
    }
}

/// Whole-run separation through the bounded ownership selector or one stated
/// fact at the two address anchors. Two fact candidates already mean ambiguity:
/// never walk a member, composition, or separation bucket.
fn run_has_direct_store_separation(
    run: &CellRun,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::resource_tracker::cell_source::AccessInRangeEvidence;
    let Some((run_pointer, run_bytes)) = run.live_byte_footprint() else {
        return false;
    };
    let footprint = assumptions.owned_store_footprint(pointer, bytes);
    if assumptions.access_owned_apart_from_store(&footprint, pointer, &run_pointer, run_bytes) {
        return true;
    }
    let mut candidates = assumptions.anchored_memory_separation_candidates(&run_pointer, pointer);
    crate::instrumentation::record_deterministic_work(1);
    let Some(fact) = candidates.next() else {
        return false;
    };
    if candidates.next().is_some() {
        return false;
    }
    let Some((left, right)) = fact.memory_separation() else {
        return false;
    };
    if assumptions.memory_ranges_overlap_after_base_equality(left, right)
        || assumptions.numeric_access_byte_overlap(&run_pointer, run_bytes, pointer, bytes)
            == Some(AccessByteOverlap::Overlaps)
    {
        return false;
    }
    let fits = |range, access| {
        AccessInRangeEvidence::for_access(&run_pointer, run_bytes, range, assumptions).is_some()
            && AccessInRangeEvidence::for_access(pointer, bytes, access, assumptions).is_some()
    };
    if fits(left, right) || fits(right, left) {
        crate::kernel::record_implicit_reasoning_provenance(assumptions, fact);
        true
    } else {
        false
    }
}

/// Which of `run`'s live slots a store of `bytes` bytes at `pointer` leaves
/// in place, and whether dropping the others forgot anything the store does
/// not itself replace ([`CMemory::without_possible_aliasing_cells`]).
///
/// At a constant shift from the run's base the store's bytes decide it: a
/// slot they meet is dropped, and forgotten unless the store covers all of
/// it, and every other slot keeps its value, being a different address whose
/// bytes the gap clears. A store the facts place outside the run's whole
/// extent leaves every slot. A bounded symbolic store forgets its possible
/// window at once; an unplaced store forgets the whole run, regardless of its
/// value mode. One stated separation at the exact anchors may keep the whole
/// run. No range-fact search or per-slot query participates. Explicit
/// transport can recover required source loads from the recorded history.
/// Keeping a slot needs a proof its bytes are missed; dropping one only forgets.
pub(in crate::kernel) fn run_slots_kept_by_store(
    run: &CellRun,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> (SlotSet, bool) {
    match run_access(run, pointer) {
        RunAccess::DistinctBlock => (SlotSet::All, false),
        RunAccess::Shift(shift) => {
            let (low, high) = run_elements_meeting(run, shift, i64::from(bytes));
            if low >= high {
                return (SlotSet::All, false);
            }
            let width = i64::from(run.element_width());
            let value_width = i64::from(run.value_width());
            let covered = |index: u32| {
                let start = i64::from(index) * width;
                shift <= start && start + value_width <= shift + i64::from(bytes)
            };
            // Coverage is an interval, so its endpoints decide each live
            // interval. Walking logical slots here also made a known whole-
            // array store cost the array's extent despite its compact form.
            let forgot = run.holes().gap_intervals(run.count()).any(|(start, end)| {
                crate::instrumentation::record_deterministic_work(1);
                let first = start.max(low);
                let end = end.min(high);
                first < end && (!covered(first) || !covered(end - 1))
            });
            (SlotSet::Except(low, high), forgot)
        }
        RunAccess::Scaled { .. } | RunAccess::ScaledWide { .. } | RunAccess::Other => {
            if run_has_direct_store_separation(run, pointer, bytes, assumptions) {
                return (SlotSet::All, false);
            }

            // The facts bound a scaled index: the store's bytes lie within
            // what the index's extremes reach, and every slot outside those
            // keeps its value. Forget the possible window as one interval,
            // including any slots a more precise per-cell search might keep.
            // The caller records their initialized bytes in compact form.
            if let RunAccess::Scaled {
                index,
                scale,
                shift,
            } = run_access(run, pointer)
                && let Some((low, high)) = assumptions.signed_interval(&index)
                && let (Some(first), Some(extent)) = (
                    low.checked_mul(scale)
                        .and_then(|bytes| bytes.checked_add(shift)),
                    high.checked_sub(low)
                        .and_then(|span| span.checked_mul(scale))
                        .and_then(|span| span.checked_add(i64::from(bytes))),
                )
            {
                let (low, high) = run_elements_meeting(run, first, extent);
                if low >= high {
                    return (SlotSet::All, false);
                }
                return (
                    SlotSet::Except(low, high),
                    !run.holes().covers_range(low, high),
                );
            }
            // Unknown values are no reason to enumerate a compact run.
            // Forget its cached contents together; initialization and the
            // recorded store history remain available to explicit proofs.
            (SlotSet::Nothing, !run.holes().covers_range(0, run.count()))
        }
    }
}

/// Which of `run`'s live slots the equal-cell scan of a load at `pointer`
/// can match: the one element the pointer names, when it names one.
///
/// `normalized` is shared by a query's runs as for
/// [`run_slots_kept_by_load_reduction`].
pub(in crate::kernel) fn run_slots_equal_to_load(
    run: &CellRun,
    pointer: &Pointer,
    normalized: &std::cell::OnceCell<Pointer>,
    assumptions: &PureFactContext,
) -> (SlotSet, RuleAnswer) {
    let normalized =
        normalized.get_or_init(|| pointer_with_exact_index_constants(pointer, assumptions));
    let set = match run_access(run, normalized) {
        RunAccess::DistinctBlock => SlotSet::Nothing,
        RunAccess::Shift(shift) => {
            let width = i64::from(run.element_width()).max(1);
            if shift.rem_euclid(width) != 0 {
                return (SlotSet::Nothing, RuleAnswer::Sound);
            }
            let index = shift.div_euclid(width);
            match u32::try_from(index) {
                Ok(index) if index < run.count() => SlotSet::Elements(index, index + 1),
                _ => SlotSet::Nothing,
            }
        }
        // A symbolic index names an element only where a fact fixes it, which
        // the exact-constant rewrite above already applied; another spelling
        // names one only through a stated alias. One hop of each is what the
        // per-cell ladder's first rungs read, and only those are asked.
        RunAccess::Scaled { .. } | RunAccess::ScaledWide { .. } | RunAccess::Other => assumptions
            .exact_pointer_aliases(normalized)
            .cloned()
            .chain(assumptions.exact_pointer_offset_aliases(normalized))
            .find_map(|alias| {
                crate::instrumentation::record_deterministic_work(1);
                let alias = pointer_with_exact_index_constants(&alias, assumptions);
                let RunAccess::Shift(shift) = run_access(run, &alias) else {
                    return None;
                };
                let width = i64::from(run.element_width()).max(1);
                if shift.rem_euclid(width) != 0 {
                    return None;
                }
                u32::try_from(shift.div_euclid(width))
                    .ok()
                    .filter(|index| *index < run.count())
                    .map(|index| SlotSet::Elements(index, index + 1))
            })
            // A stated alias is filed under the exact pointer it names, so
            // `id` reaches the run's base `p` but `id + 8` reaches nothing,
            // although the graph already holds `id + 8 == p + 8`: the
            // per-cell ladder answers that pair by `pointers_known_equal`,
            // and a run must name the same slot its cells would. Re-express
            // the load in the run's own block through the trusted affine
            // class relation, one keyed query that enumerates no class
            // member, and read the slot from the byte shift as above.
            .or_else(|| {
                if normalized.block == run.base().block {
                    return None;
                }
                crate::instrumentation::record_deterministic_work(1);
                let aligned = assumptions
                    .equality_graph
                    .pointer_in_block(normalized, &run.base().block)?;
                let RunAccess::Shift(shift) = run_access(run, &aligned) else {
                    return None;
                };
                let width = i64::from(run.element_width()).max(1);
                if shift.rem_euclid(width) != 0 {
                    return None;
                }
                u32::try_from(shift.div_euclid(width))
                    .ok()
                    .filter(|index| *index < run.count())
                    .map(|index| SlotSet::Elements(index, index + 1))
            })
            .unwrap_or(SlotSet::Nothing),
    };
    // A `Shift` names one address exactly, by the byte arithmetic every slot
    // shares; the per-cell ladder may miss a regrouped spelling of it. A
    // symbolic index no fact fixes is equal to no single element, so no slot
    // is the load's value; the load stays symbolic, which is its value too.
    (set, RuleAnswer::Sound)
}

/// Which of `run`'s live slots the load-canonical projection keeps: slots an
/// access at `pointer` can observe and that no constant gap keeps apart from
/// it (see [`cell_disjoint_from_load_by_constant_offset`]).
pub(in crate::kernel) fn run_slots_kept_by_load_projection(
    run: &CellRun,
    pointer: &Pointer,
) -> (SlotSet, RuleAnswer) {
    (
        run_slots_kept_by_load_projection_set(run, pointer),
        RuleAnswer::Exact,
    )
}

fn run_slots_kept_by_load_projection_set(run: &CellRun, pointer: &Pointer) -> SlotSet {
    if !run.base().block.observable_by_load(&pointer.block) {
        return SlotSet::Nothing;
    }
    if run.base().block != pointer.block {
        return SlotSet::All;
    }
    match run_access(run, pointer) {
        RunAccess::Shift(shift) => {
            let (low, high) =
                run_elements_meeting(run, shift, crate::kernel::MAX_SCALAR_ACCESS_BYTES);
            SlotSet::Elements(low, high)
        }
        RunAccess::DistinctBlock
        | RunAccess::Scaled { .. }
        | RunAccess::ScaledWide { .. }
        | RunAccess::Other => SlotSet::All,
    }
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
/// The load is named here by its address alone, so it contributes
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
    if let Some(overlap) = assumptions
        .numeric_access_byte_overlap(left, left_bytes, right, right_bytes)
        .or_else(|| exact_access_byte_overlap(left, left_bytes, right, right_bytes))
    {
        return overlap;
    }
    if one_element_gap_separates_bytes(left, left_bytes, right, right_bytes, assumptions) {
        AccessByteOverlap::Separate
    } else {
        AccessByteOverlap::Unknown
    }
}

/// Exact byte geometry only: no fact search, address-inequality ladder, or
/// memory history. Suitable for admitting one select-over-store graph edge.
pub(in crate::kernel) fn exact_access_byte_overlap(
    left: &Pointer,
    left_bytes: u32,
    right: &Pointer,
    right_bytes: u32,
) -> Option<AccessByteOverlap> {
    if left.blocks_proven_distinct(right) {
        return Some(AccessByteOverlap::Separate);
    }
    let shift = constant_byte_shift(left, right)?;
    Some(
        if crate::kernel::byte_intervals_disjoint(
            shift,
            i64::from(left_bytes),
            0,
            i64::from(right_bytes),
        ) {
            AccessByteOverlap::Separate
        } else {
            AccessByteOverlap::Overlaps
        },
    )
}

/// The constant byte distance from `base` to `pointer`, when exact byte
/// geometry knows one: the shift [`exact_access_byte_overlap`] decides from.
pub(in crate::kernel) fn constant_byte_shift(pointer: &Pointer, base: &Pointer) -> Option<i64> {
    exact_constant_byte_shift(pointer, base).or_else(|| constant_byte_shift_between(pointer, base))
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
    // Two offsets whose difference is a multiple of some stride at least as
    // wide as both accesses are separated by the inequality alone: a
    // nonzero multiple of the stride is at least the stride away. This is
    // what clears the `int32` field at `s + 8x + 4` from the one at `s + 4`,
    // and declines a byte at `p + 5` against the `int32` at `p + 4k`, whose
    // difference `4k - 5` has no stride but one.
    if offset_difference_stride(&left.offset, &right.offset)
        .is_some_and(|stride| i64::from(left_bytes.max(right_bytes)) <= stride)
    {
        return true;
    }
    // Cancelling a shared additive base is what lets two indexed addresses be
    // compared, and a pair with no base to cancel — `a + 4` against `a[i]`,
    // where one side is a bare constant and the other a bare scaled index —
    // had nothing to cancel and so was declined. Their own offsets are the
    // indices in that case, and reading them is sound for the same reason
    // the cancelled pair's are: `element_index_from_offset` answers only
    // where every leaf contributes a whole multiple of the element width, so
    // two offsets it answers for are both multiples of that width, and two
    // different multiples of `w` are at least `w` apart. That is the gap this
    // rule measures, and it needs no index arithmetic to establish.
    let Some((left_index, right_index, element_width)) = common_base_element_indices(left, right)
        .or_else(|| element_indices_of(&left.offset, &right.offset))
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
        let condition = ConditionTerm::signed_less_than(low.clone(), high.clone());
        // This preliminary byte-gap check runs inside memory-history walks.
        // Even a recorded-order graph walk grows with ambient facts. Read
        // one stated order only; a proof can establish that order explicitly
        // before requesting preservation across a store.
        assumptions.exact_condition_value(&condition) == Some(true)
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

/// The stride every value of `left - right` is a multiple of, when the two
/// offsets have one and are not provably equal: the greatest common divisor
/// of the element widths of their symbolic scaled summands and of their
/// constant difference, after cancelling summands both sides share.
///
/// A `PointerOffsetTerm` is an exact `i64` sum, and a scaled summand is its
/// index sign- or zero-extended times its width, so each symbolic summand
/// contributes a multiple of its width whatever the index is. An opaque
/// offset variable that does not cancel has no stride, and so has the pair.
/// A difference that is a constant is left to exact geometry (`None`), as is
/// a difference with no summand at all, which is the equal pair.
fn offset_difference_stride(left: &PointerOffsetTerm, right: &PointerOffsetTerm) -> Option<i64> {
    fn summands<'a>(offset: &'a PointerOffsetTerm, into: &mut Vec<&'a PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                summands(left, into);
                summands(right, into);
            }
            other => into.push(other),
        }
    }
    fn gcd(a: i64, b: i64) -> i64 {
        let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
        while b != 0 {
            (a, b) = (b, a % b);
        }
        i64::try_from(a).unwrap_or(i64::MAX)
    }
    let mut left_summands = Vec::new();
    summands(left, &mut left_summands);
    let mut right_summands = Vec::new();
    summands(right, &mut right_summands);
    // Cancel summands both sides share, one occurrence for one.
    left_summands.retain(|summand| {
        if let Some(position) = right_summands.iter().position(|other| other == summand) {
            right_summands.swap_remove(position);
            false
        } else {
            true
        }
    });
    let mut constant = 0i64;
    let mut stride = 0i64;
    let mut symbolic = false;
    for (summand, sign) in left_summands
        .iter()
        .map(|summand| (*summand, 1i64))
        .chain(right_summands.iter().map(|summand| (*summand, -1i64)))
    {
        match summand {
            PointerOffsetTerm::Constant(value) => {
                constant = constant.checked_add(sign.checked_mul(*value)?)?;
            }
            PointerOffsetTerm::Variable(_) => return None,
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                match signed_bitvector_constant(value) {
                    Some(index) => {
                        constant = constant
                            .checked_add(sign.checked_mul(index.checked_mul(*byte_width)?)?)?;
                    }
                    None => {
                        symbolic = true;
                        stride = gcd(stride, *byte_width);
                    }
                }
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let index = if *unsigned {
                    value
                        .uint64_as_const()
                        .and_then(|index| i64::try_from(index).ok())
                } else {
                    value.int64_as_const()
                };
                match index {
                    Some(index) => {
                        constant = constant
                            .checked_add(sign.checked_mul(index.checked_mul(*byte_width)?)?)?;
                    }
                    None => {
                        symbolic = true;
                        stride = gcd(stride, *byte_width);
                    }
                }
            }
            PointerOffsetTerm::Add(..) => unreachable!("summands are not sums"),
        }
    }
    if !symbolic {
        return None;
    }
    let stride = gcd(stride, constant);
    (stride > 0).then_some(stride)
}

/// The exact byte distance from `base` to `pointer`, when their offsets are
/// the same non-constant summands plus different constants.
///
/// A pointer offset is a mathematical `i64` sum, so two offsets with the same
/// multiset of non-constant summands differ by exactly the difference of their
/// constant parts, whatever those summands are: an `int64` scaled index, an
/// opaque offset variable, or an `int32` scaled index alike. Each summand is
/// kept whole. In particular an `int32` index `i + 1` is not split into
/// `i` plus one element: `sext(i + 1)` is `sext(i) + 1` only when the int32
/// addition does not wrap, which nothing here knows. A constant sum that
/// leaves `i64` has no answer.
fn exact_constant_byte_shift(pointer: &Pointer, base: &Pointer) -> Option<i64> {
    fn summands(
        offset: &PointerOffsetTerm,
        atoms: &mut Vec<PointerOffsetTerm>,
        shift: &mut Option<i64>,
    ) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                summands(left, atoms, shift);
                summands(right, atoms, shift);
            }
            PointerOffsetTerm::Constant(value) => {
                *shift = shift.and_then(|shift| shift.checked_add(*value));
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                match signed_bitvector_constant(value) {
                    Some(value) => {
                        *shift = shift
                            .zip(value.checked_mul(*byte_width))
                            .and_then(|(shift, bytes)| shift.checked_add(bytes));
                    }
                    None => atoms.push(offset.clone()),
                }
            }
            other => atoms.push(other.clone()),
        }
    }
    if pointer.block != base.block {
        return None;
    }
    let mut pointer_atoms = Vec::new();
    let mut pointer_shift = Some(0);
    summands(&pointer.offset, &mut pointer_atoms, &mut pointer_shift);
    let mut base_atoms = Vec::new();
    let mut base_shift = Some(0);
    summands(&base.offset, &mut base_atoms, &mut base_shift);
    pointer_atoms.sort();
    base_atoms.sort();
    (pointer_atoms == base_atoms)
        .then(|| pointer_shift?.checked_sub(base_shift?))
        .flatten()
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
    let bits = match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int8(bits)
        | CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Int128(bits)
        | CValue::UInt128(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => bits,
        // A pointer cell is a materialization when it holds the pointer a
        // typed load of this same cell produces (`symbolic_pointer_load`):
        // that read's own name, which records the complete value and
        // provenance of reading the cell's bytes in its defining memory. A
        // pointer given a symbolic identity, or one loaded from another cell,
        // is a write and never qualifies.
        CValue::Pointer(value) => {
            let read = value.pointer().as_loaded_value()?;
            return (read.displacement == PointerOffsetTerm::Constant(0)
                && read.defining_address == *cell_pointer)
                .then_some(read.defining_memory);
        }
        CValue::Parameter(_) => return None,
        CValue::Void | CValue::UInt32(_) => return None,
    };
    let load = match bits {
        Bitvector32Term::MemoryLoad(_, _, _) => bits.clone(),
        Bitvector32Term::Variable(variable) if crate::kernel::eval::is_load_variable(variable) => {
            crate::kernel::eval::registered_load_term_for_variable(variable)?
        }
        _ => return None,
    };
    let Bitvector32Term::MemoryLoad(source, source_pointer, kind) = load else {
        return None;
    };
    // The cell is the load only when it holds the load of its own kind: a
    // narrower or differently signed read stored in it is another value
    // than a read of the cell returns.
    (source_pointer.as_ref() == cell_pointer && kind.reads_value(value)).then_some(source)
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
    if pointer.block.is_local_block() {
        return false;
    }
    if !snapshot_objects_agree(left, right, pointer) {
        return false;
    }
    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    left.differing_cell_pointers_meeting_load(right, pointer, load_bytes)
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
                    .and_then(|value| materialized_cell_source(&cell_pointer, &value))
                    .is_some_and(|source| {
                        memories_match_for_pointer_load(&source, left, pointer)
                            || memories_match_for_pointer_load(&source, right, pointer)
                            || crate::kernel::api::c_memories_canonically_equal(&source, left)
                            || crate::kernel::api::c_memories_canonically_equal(&source, right)
                    });
            }
            value.is_some_and(|value| {
                cell_disjoint_from_load_by_constant_offset(&cell_pointer, &value, pointer)
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
    if pointer.block.is_local_block() {
        return false;
    }
    if !snapshot_objects_agree(left, right, pointer) {
        return false;
    }

    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    left.differing_cell_pointers_meeting_load(right, pointer, load_bytes)
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

pub(in crate::kernel) fn collect_memory_effect_write_accesses(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> BTreeSet<(Pointer, u32)> {
    // Concrete stores certify exact pointer-width pairs. Abstract calls and
    // loops certify ranges separately through CMemoryEffectSummary; comparing
    // endpoint memories would mistake join abstraction and call havoc for
    // writes.
    let mut writes = BTreeSet::new();
    for fact in facts.fact_iter() {
        if let Proposition::CMemoryMutatesOnly {
            writes: accesses, ..
        } = fact.proposition()
        {
            writes.extend(accesses.iter().cloned());
        }
    }

    writes
}

pub(in crate::kernel) fn collect_memory_effect_write_pointers(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> BTreeSet<Pointer> {
    collect_memory_effect_write_accesses(facts)
        .into_iter()
        .map(|(pointer, _)| pointer)
        .collect()
}

#[cfg(test)]
#[test]
fn offset_resolution_does_not_promote_wrapped_index_equality() {
    let i = Bitvector32Term::Variable(Variable(90_001));
    let j = Bitvector32Term::Variable(Variable(90_002));
    let k = Bitvector32Term::Variable(Variable(90_003));
    let scaled = |index: Bitvector32Term| PointerOffsetTerm::scale_int32(index, 4);
    let sum = PointerOffsetTerm::Add(Box::new(scaled(i.clone())), Box::new(scaled(j.clone())));
    let other = scaled(k.clone());
    let index_sum = Bitvector32Term::add(i.clone(), j.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(index_sum.clone(), k.clone()), true)
        .assume_condition(
            ConditionTerm::equal(i.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(i32::MIN as u32)),
            true,
        );
    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(index_sum, k)),
        Some(true)
    );
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&sum, &other, &assumptions),
        Some(true)
    );
    assert_ne!(
        assumptions.decide(&ConditionTerm::pointer_offset_equal(sum, other)),
        Some(true)
    );
}

#[cfg(test)]
#[test]
fn offset_resolution_accepts_exact_index_equalities_at_each_width() {
    let i = Bitvector32Term::Variable(Variable(90_011));
    let j = Bitvector32Term::Variable(Variable(90_012));
    let k = Bitvector32Term::Variable(Variable(90_013));
    let index_sum = Bitvector32Term::add(i.clone(), j.clone());
    let fact = ConditionTerm::equal(index_sum, k.clone());
    let symbolic = PureFactContext::new().assume_condition(fact.clone(), true);
    let exact = symbolic
        .clone()
        .assume_condition(
            ConditionTerm::equal(i.clone(), Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(3)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(5)),
            true,
        );
    for width in [1, 4, 8] {
        let scaled = |index: Bitvector32Term| PointerOffsetTerm::scale_int32(index, width);
        let sum = PointerOffsetTerm::Add(Box::new(scaled(i.clone())), Box::new(scaled(j.clone())));
        let other = scaled(k.clone());
        assert_ne!(
            pointer_offsets_equal_for_memory_resolution(&sum, &other, &symbolic),
            Some(true),
            "an index equality alone cannot prove the exact offset at width {width}"
        );
        assert_eq!(
            pointer_offsets_equal_for_memory_resolution(&sum, &other, &exact),
            Some(true),
            "a proven nonwrapping sum should retain offset equality at width {width}"
        );
    }
}

#[cfg(test)]
#[test]
fn mixed_index_offsets_require_exact_observations_and_matching_strides() {
    use crate::kernel::{IntegerTerm, MachineIntegerType};
    let wide = Bitvector32Term::Variable(Variable(81001));
    let narrow = Bitvector32Term::Variable(Variable(81002));
    let observed_wide =
        IntegerTerm::from_machine(MachineIntegerType::UInt64, wide.clone()).unwrap();
    let observed_narrow =
        IntegerTerm::from_machine(MachineIntegerType::Int32, narrow.clone()).unwrap();
    let fact =
        ConditionTerm::IntegerEqual(observed_wide.clone().into(), observed_narrow.clone().into());
    let native = |width| PointerOffsetTerm::scale_int64(wide.clone(), width, true);
    let signed = |width| PointerOffsetTerm::scale_int32(narrow.clone(), width);
    let empty = PureFactContext::new();
    let checked = empty.clone().assume_condition(fact.clone(), true);
    for width in [1, 2, 4, 8, 16] {
        for (left, right) in [
            (native(width), signed(width)),
            (signed(width), native(width)),
        ] {
            assert_eq!(
                pointer_offsets_equal_for_memory_resolution(&left, &right, &empty),
                None
            );
            assert_eq!(
                pointer_offsets_equal_for_memory_resolution(&left, &right, &checked),
                Some(true)
            );
            let common =
                PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(81003)), 4);
            assert_eq!(
                pointer_offsets_equal_for_memory_resolution(
                    &PointerOffsetTerm::add(common.clone(), left),
                    &PointerOffsetTerm::add(common, right),
                    &checked
                ),
                Some(true)
            );
        }
    }
    let reversed = empty.clone().assume_condition(
        ConditionTerm::IntegerEqual(observed_narrow.into(), observed_wide.into()),
        true,
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(1), &reversed),
        Some(true)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(4), &checked),
        None
    );
    let withdrawn = checked.without_exact_fact(&Proposition::ConditionIs(fact.clone(), true));
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(1), &withdrawn),
        None
    );
    let denied = empty.clone().assume_condition(fact, false);
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(1), &denied),
        None
    );
    let truncated = empty.assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::uint32_from_64(wide.clone()),
            narrow.clone(),
        ),
        true,
    );
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(1), &truncated),
        Some(true)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &PointerOffsetTerm::Constant(4294967296),
            &PointerOffsetTerm::Constant(0),
            &truncated
        ),
        Some(false)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &PointerOffsetTerm::Constant(4294967295),
            &PointerOffsetTerm::Constant(-1),
            &truncated
        ),
        Some(false)
    );
}

#[test]
fn external_load_projection_retains_aliases_across_cell_updates() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointers = [
        PointerBlock::Symbolic(Variable(998_900)),
        PointerBlock::ExternalArgument,
        PointerBlock::ExternalObject(Variable(998_901)),
        PointerBlock::Concrete("global:projection".into()),
        PointerBlock::Concrete("local:projection".into()),
        PointerBlock::Heap(998_902),
        PointerBlock::Temporary(998_903),
    ]
    .map(|block| Pointer {
        block,
        offset: PointerOffsetTerm::Constant(0),
    });
    let mut memory = CMemory::new();
    for pointer in &pointers {
        memory = memory.store(pointer.clone(), CValue::Int32(7u32.into()));
    }
    for load in [&pointers[1], &pointers[2]] {
        let projected = canonical_memory_for_pointer_load(&memory, load);
        for pointer in &pointers {
            assert_eq!(
                projected.has_known_cell_at(pointer),
                pointer.block.observable_by_load(&load.block),
                "{pointer:?} through {load:?}"
            );
        }
    }
    let updated = memory
        .clone()
        .store(pointers[0].clone(), CValue::Int32(9u32.into()));
    let projected = canonical_memory_for_pointer_load(&updated, &pointers[1]);
    assert_eq!(
        projected.known_value(&pointers[0]),
        Some(CValue::Int32(9u32.into()))
    );
    let removed = updated.without_cell(&pointers[0]);
    let projected = canonical_memory_for_pointer_load(&removed, &pointers[1]);
    assert!(!projected.has_known_cell_at(&pointers[0]));
    let original = canonical_memory_for_pointer_load(&memory, &pointers[1]);
    assert_eq!(
        original.known_value(&pointers[0]),
        Some(CValue::Int32(7u32.into()))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/reasoning/memory_resolution.rs");
}
