use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::binary_term;

/// A memory-resolution query in progress on this thread. The resolvers are
/// mutually recursive over pointers, offsets, index terms, loads, stored
/// cells, and range facts. A query met again while it is in progress is a
/// cycle through the facts and proves nothing on that path; distinct
/// queries nest freely, bounded by the terms and facts the query connects,
/// and each is answered once per fact set by the memo below.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::kernel) enum ResolutionQuery {
    PointerDistinct(Address, Address),
    CommonBaseDistinct(Address, Address),
    AddressEqual(Address, Address),
    OffsetEqual(AddressOffset, AddressOffset),
    BitvectorEqual(MachineTerm, MachineTerm),
    OperandEqual(
        crate::kernel::SharedMachineIntegerTerm,
        crate::kernel::SharedMachineIntegerTerm,
    ),
    StatesMatch(SharedMemory, SharedMemory, Address),
    CanonicalMemory(SharedMemory, Address),
    RangeDisjoint(Address, Address),
    RangesSeparate(MemoryRange, MemoryRange),
    RangeContained(MemoryRange, MemoryRange),
    PointerInRange(Address, Address, MachineTerm, MachineTerm, u32),
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
    let pointer = |index: u64| Address {
        base: "cell".into(),
        offset: AddressOffset::Constant(index as i64),
    };
    let first = ResolutionQuery::AddressEqual(pointer(0), pointer(1));
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
    let slot = Address {
        base: AddressBase::Symbolic(Variable(1000001)),
        offset: AddressOffset::Constant(16),
    };
    let read = Address {
        offset: AddressOffset::Constant(12),
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
    PointerDistinct(u64, bool, Address, Address),
    AddressEqual(u64, bool, Address, Address),
    AddressOffsetEqual(u64, bool, AddressOffset, AddressOffset),
    BitvectorEqual(u64, bool, MachineTerm, MachineTerm),
    OperandEqual(
        u64,
        bool,
        crate::kernel::SharedMachineIntegerTerm,
        crate::kernel::SharedMachineIntegerTerm,
    ),
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
        std::collections::HashMap<(super::SharedMemory, Address), SymbolicMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// [`source_holds_cells_observable_by`], by interned state and block.
    static SOURCE_OBSERVABLE_BY_BLOCK: std::cell::RefCell<
        std::collections::HashMap<(super::SharedMemory, crate::kernel::primitives::AddressBase), bool>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The producer-known source of one canonical load projection. The
    /// projected state is intentionally not given an ordinary memory-DAG
    /// derivation: one interned projection can be shared by several sources.
    /// This pointer-specific preferred edge preserves the oldest known sound
    /// source for checked load equality without pretending the projection has
    /// a unique memory parent.
    static CANONICAL_LOAD_PROJECTION_SOURCES: std::cell::RefCell<
        std::collections::HashMap<(super::SharedMemory, Address), super::SharedMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The latest producer observation of a named value read. Every stored
    /// edge is structural and valid only for its recorded access width.
    static VALUE_LOAD_ORIGINS: std::cell::RefCell<
        std::collections::HashMap<(super::SharedMemory, Address, u32), super::SharedMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Reverse definitions select a name from the exact observation. Keeping
    /// this direction preserves earlier observations when a name is reused.
    static VALUE_LOAD_NAMES: std::cell::RefCell<
        std::collections::HashMap<(super::SharedMemory, Address, u32), super::SharedMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static LOAD_DEFINITION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Every exact producer-known projection triple. Evidence checks this
    /// durable set rather than requiring its selected source to remain the
    /// preferred source if an older equivalent producer is registered later.
    static CANONICAL_LOAD_PROJECTIONS: std::cell::RefCell<
        std::collections::HashSet<(super::SharedMemory, super::SharedMemory, Address)>,
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
/// pointer-observable projection. This is a derivation record, not a cache: checked
/// evidence later names this exact edge and validates it by identity, without
/// rescanning either state. A canonical projection can be interned from
/// multiple equivalent sources, so all exact triples remain valid while the
/// oldest arena node is kept as the constant-time lookup preference.
pub(in crate::kernel) fn record_canonical_load_projection(
    source: &super::SharedMemory,
    projected: &super::SharedMemory,
    pointer: &Address,
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
    origin: &super::SharedMemory,
    named: &super::SharedMemory,
    pointer: &Address,
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
    named: &super::SharedMemory,
    pointer: &Address,
    bytes: u32,
) -> Option<super::SharedMemory> {
    VALUE_LOAD_ORIGINS.with(|origins| {
        origins
            .borrow()
            .get(&(named.clone(), pointer.clone(), bytes))
            .cloned()
    })
}

/// The structurally chosen name for this exact observation and width.
pub(in crate::kernel) fn value_load_name(
    origin: &super::SharedMemory,
    pointer: &Address,
    bytes: u32,
) -> Option<super::SharedMemory> {
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
    projected: &super::SharedMemory,
    pointer: &Address,
) -> Option<super::SharedMemory> {
    CANONICAL_LOAD_PROJECTION_SOURCES.with(|sources| {
        sources
            .borrow()
            .get(&(projected.clone(), pointer.clone()))
            .cloned()
    })
}

pub(in crate::kernel) fn canonical_load_projection_recorded(
    source: &super::SharedMemory,
    projected: &super::SharedMemory,
    pointer: &Address,
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
    let generation = crate::kernel::primitives::memory_derivation_generation();
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

    clear_memory_resolution_memos();
    let key = ResolutionQueryKey::BitvectorEqual(
        7_490_001,
        false,
        MachineTerm::Variable(Variable(7_490_002)),
        MachineTerm::constant(1),
    );
    // Expiry occurs inside the memo boundary, including at a helper which
    // formerly called the raw deadline checkpoint without recording a cut.
    assert!(!memoized_resolution_query(Some(key.clone()), || {
        crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            let assumptions = PureFactContext::new();
            crate::kernel::search::ProofSearch::proves(
                &(assumptions),
                &Proposition::condition_is(ConditionTerm::Constant(true), true),
            )
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
    left: Address,
    right: Address,
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
/// The state transport closure lowers one goal at every recorded state;
/// every state that holds the goal's cells unchanged lowers it to the same
/// source, so the same failing questions -- the goal's frame across the step
/// the proof could not see past -- ran once per such state, and again for
/// each of solve's strategies that reaches the closure. The key is the
/// question's whole input: its propositions (source, target, and any listed
/// facts, in order), the memory it lands in, the content id of its fact set,
/// its transition facts, the memory-DAG generation, the DAG scope modes, and
/// the cell lookups in progress. A failure that observed a cycle cut or a
/// limit is not remembered. Work is the key's size per question.
pub(crate) fn closure_memoized_fact_check(
    check: ClosureFactCheck,
    propositions: &[&Proposition],
    after: Option<&SymbolicMemory>,
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
        after: after.map(|after| crate::kernel::intern_memory_ref(after).arena_id()),
        assumptions: crate::kernel::assumptions::unsalted_assumptions_memo_id(assumptions),
        lookups: crate::kernel::resource_tracker::cell_source::memory_dag_cell_lookups_fingerprint(
        ),
        transitions: transitions.persistent_facts(),
        generation: crate::kernel::primitives::memory_derivation_generation(),
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
/// A closure that tries one goal against many candidates -- the state
/// transport closure lowers the goal at every recorded state -- asks the
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
    left: &Address,
    right: &Address,
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
        generation: crate::kernel::primitives::memory_derivation_generation(),
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
    let source = Proposition::condition_is(ConditionTerm::Constant(true), true);
    let target = Proposition::condition_is(ConditionTerm::Constant(false), true);
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
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return false;
    }
    if left.blocks_proven_distinct(right)
        || constant_byte_shift(left, right).is_some_and(|shift| shift != 0)
        || assumptions
            .exact_condition_value(&ConditionTerm::address_equal(left.clone(), right.clone()))
            == Some(false)
    {
        return true;
    }
    // The element indices of a common base, `int32` or 64-bit of one
    // signedness, each read by its exact comparison fact in its own format.
    // Native 64-bit equality facts keep their written orientation. Read
    // both orientations while retaining shared query operands.
    if let Some(indices) = common_base_store_indices(left, right) {
        let denied = |swapped| {
            assumptions
                .selected_comparison_value(&indices.comparison(CompareRelation::Equal, swapped))
                == Some(false)
        };
        let below = |swapped| {
            assumptions
                .selected_comparison_value(&indices.comparison(CompareRelation::LessThan, swapped))
                == Some(true)
        };
        if denied(false)
            || (indices.format != MachineIntegerType::Int32 && denied(true))
            || below(false)
            || below(true)
        {
            return true;
        }
    }
    let private_local = |local: &Address, value: &Address| {
        matches!(value.base, AddressBase::Symbolic(_))
            && crate::kernel::primitives::block_is_never_address_taken_local(&local.base)
            && assumptions.pointer_in_block(value, &local.base).is_none()
    };
    private_local(left, right) || private_local(right, left)
}

/// Alias check used while resolving a symbolic memory load. This deliberately
/// avoids general equality transport because that transport may itself resolve
/// memory loads.
pub(in crate::kernel) fn pointers_proven_distinct_for_memory_resolution(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    // Structural separation needs no recursive premise query. In particular,
    // a compact run's slot check may ask this while the same query is active.
    if left.blocks_proven_distinct(right)
        || (left.base == right.base
            && matches!((&left.offset, &right.offset),
                (AddressOffset::Constant(a), AddressOffset::Constant(b)) if a != b))
    {
        return true;
    }
    // Establish the same context identity used by nested scalar resolution at
    // the enclosing query boundary, so repeats reuse the whole answer. The
    // existing memo still excludes active cell lookups and explicit DAG checks.
    let _scope = assumptions.enter_id_scope();
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
    left: &Address,
    right: &Address,
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
                left.base == right.base
                    && pointer_offsets_equal_for_memory_resolution(
                        &left.offset,
                        &right.offset,
                        assumptions,
                    ) == Some(false)
            },
        )
        || assumptions
            .exact_condition_value(&ConditionTerm::address_equal(left.clone(), right.clone()))
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
/// `AddressBase::proven_distinct` can stay the narrower structural rule and
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
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    let separated = |local: &Address, value: &Address| {
        if !matches!(value.base, AddressBase::Symbolic(_))
            || !crate::kernel::primitives::block_is_never_address_taken_local(&local.base)
        {
            return false;
        }
        crate::instrumentation::record_deterministic_work(1);
        // Defer to a stated equality that puts the pointer in this object.
        !assumptions
            .exact_pointer_aliases(value)
            .any(|alias| alias.base == local.base)
    };
    separated(left, right) || separated(right, left)
}

/// Whether one exact pointer equality resolves an unresolved pointer to an
/// address the program names, and *that* address is proven distinct from the
/// other one.
///
/// A `Symbolic` block is a pointer value, not an object the function can name:
/// [`AddressBase::proven_distinct`] separates it from nothing at all, so a
/// load through a pointer a call returned is framed only by evidence. The most
/// direct evidence a contract can state is where the pointer points --
/// `ensures result == &g[0]`, `ensures result == p` -- and this is the rule
/// that spends it. Without it, the honest `observable_by_load` keeps every
/// cell in the question and the stated equality never gets a say.
///
/// Soundness. `exact_pointer_aliases` reads the index of *assumed*
/// `AddressEqual` facts: never a derived, heuristic or disjunctive conclusion,
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
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    let unresolved = |pointer: &Address| {
        matches!(
            pointer.base,
            AddressBase::Symbolic(_) | AddressBase::FunctionSymbolic(_)
        )
    };
    let resolved_side_is_distinct = |pointer: &Address, other: &Address| {
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
        if pointer.offset == AddressOffset::Constant(0) {
            return false;
        }
        // An exact base alias also identifies the object of q + d. Use
        // whole-object separation only: unequal translated starting addresses
        // would not establish that multi-byte accesses cannot overlap.
        let base = Address {
            base: pointer.base.clone(),
            offset: AddressOffset::Constant(0),
        };
        assumptions
            .exact_pointer_aliases(&base)
            .any(|alias| !unresolved(alias) && alias.blocks_proven_distinct(other))
    };
    resolved_side_is_distinct(left, right) || resolved_side_is_distinct(right, left)
}

fn pointer_offsets_with_common_base_proven_distinct_for_memory_resolution(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if left.base != right.base {
        return false;
    }
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::CommonBaseDistinct(
        left.clone(),
        right.clone(),
    )) else {
        return false;
    };
    let zero = AddressOffset::Constant(0);
    let offsets_equal = |left: &AddressOffset, right: &AddressOffset| {
        left == right
            || pointer_offsets_proven_equal_for_memory_resolution(left, right, assumptions)
    };
    let index_pair = match (&left.offset, &right.offset) {
        (
            AddressOffset::Add(left_base, left_index),
            AddressOffset::Add(right_base, right_index),
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
        (AddressOffset::Add(base, index), right) if offsets_equal(base, right) => {
            Some((index.as_ref(), &zero))
        }
        (AddressOffset::Add(index, base), right) if offsets_equal(base, right) => {
            Some((index.as_ref(), &zero))
        }
        (left, AddressOffset::Add(base, index)) if offsets_equal(left, base) => {
            Some((&zero, index.as_ref()))
        }
        (left, AddressOffset::Add(index, base)) if offsets_equal(left, base) => {
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
        shared_element_index_from_offset_with_facts(left_index, element_width, assumptions),
        shared_element_index_from_offset_with_facts(right_index, element_width, assumptions),
    ) else {
        return false;
    };

    assumptions.decide_bitvector_equality_shallow_views(
        left_index.operand_view(),
        right_index.operand_view(),
    ) == Some(false)
        || assumptions.proves_order_condition_for_memory_resolution(
            &crate::kernel::assumptions::index_comparison(
                CompareRelation::LessThan,
                left_index.operand_view(),
                right_index.operand_view(),
            ),
            true,
        )
        || assumptions.proves_order_condition_for_memory_resolution(
            &crate::kernel::assumptions::index_comparison(
                CompareRelation::LessThan,
                right_index.operand_view(),
                left_index.operand_view(),
            ),
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
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<bool> {
    // A constant offset of whole elements beside a scaled index is the
    // constant index: `base[0]` against `base[k]`.
    let (left, right) = match (left, right) {
        (
            AddressOffset::Int64Scaled {
                value: left,
                byte_width: left_width,
                unsigned: true,
            },
            AddressOffset::Int64Scaled {
                value: right,
                byte_width: right_width,
                unsigned: true,
            },
        ) => {
            if left_width != right_width || *left_width < 1 {
                return Some(false);
            }
            (left.clone(), right.clone())
        }
        (
            AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
            AddressOffset::Constant(bytes),
        )
        | (
            AddressOffset::Constant(bytes),
            AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
        ) if *byte_width >= 1 && *bytes >= 0 && bytes % byte_width == 0 => (
            value.clone(),
            crate::kernel::SharedMachineIntegerTerm::intern(
                MachineIntegerType::UInt64,
                MachineTerm::uint64_constant((bytes / byte_width) as u64),
            ),
        ),
        _ => return None,
    };
    let decided = |relation,
                   first: &crate::kernel::SharedMachineIntegerTerm,
                   second: &crate::kernel::SharedMachineIntegerTerm| {
        assumptions.decide(
            &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt64,
                relation,
                [first.operand_view(), second.operand_view()],
            ),
        )
    };
    Some(
        decided(CompareRelation::LessThan, &left, &right) == Some(true)
            || decided(CompareRelation::LessThan, &right, &left) == Some(true)
            || decided(CompareRelation::Equal, &left, &right) == Some(false)
            || decided(CompareRelation::Equal, &right, &left) == Some(false),
    )
}

pub(in crate::kernel) fn pointers_proven_equal_for_memory_resolution(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::AddressEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        pointers_proven_equal_for_memory_resolution_unmemoized(left, right, assumptions)
    })
}

pub(in crate::kernel) fn pointer_offsets_proven_equal_for_memory_resolution(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::AddressOffsetEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        pointer_offsets_equal_for_memory_resolution(left, right, assumptions) == Some(true)
    })
}

fn pointers_proven_equal_for_memory_resolution_unmemoized(
    left: &Address,
    right: &Address,
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
        ResolutionQueryGuard::enter(ResolutionQuery::AddressEqual(left.clone(), right.clone()))
    else {
        return false;
    };
    // The shared graph answers known equality first. Offset reasoning below
    // is a stronger, separately guarded judgment, not another alias walk.
    let candidate = assumptions.pointers_known_equal(left, right)
        || pointer_in_block_for_memory_resolution(right, &left.base, assumptions).is_some_and(
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
/// or two reads of one cell whose states agree on its bytes. This answers
/// where an address is; it grants no access, which the caller's provenance
/// check still decides.
pub(in crate::kernel) fn pointer_in_block_for_memory_resolution(
    pointer: &Address,
    block: &AddressBase,
    assumptions: &PureFactContext,
) -> Option<Address> {
    if pointer.base == *block {
        return Some(pointer.clone());
    }
    if let Some(aligned) = assumptions.equality_graph.pointer_in_block(pointer, block) {
        return Some(aligned);
    }
    // A cell holds a whole pointer, so two reads of it that see the same
    // bytes produce one value; the read in `block` is then this pointer
    // before its displacement.
    let read = pointer.as_loaded_value()?;
    let target = Address {
        base: block.clone(),
        offset: AddressOffset::Constant(0),
    }
    .as_loaded_value()?;
    // As for a retained read's stored value (`pointer_read_stored_value`),
    // the comparison may cross cache-forgetting edges: they discard
    // knowledge but write no program bytes. A projected read is compared
    // from its source state, as its provenance is.
    (pointers_proven_equal_for_memory_resolution(
        &read.defining_address,
        &target.defining_address,
        assumptions,
    ) && crate::kernel::memory_history::pointer_reads_see_one_cell_source(
        &read,
        &target,
        assumptions,
    ))
    .then(|| Address {
        base: block.clone(),
        offset: read.displacement,
    })
}

/// Equal exact observations of a native unsigned index and a signed index
/// denote the same displacement at the same element width. A truncated bit
/// pattern alone is insufficient: only the explicitly established Integer
/// equality participates, so high bits and the signed interpretation survive.
fn mixed_index_offsets_equal(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<bool> {
    use crate::kernel::MachineIntegerType;
    let (wide, narrow, wide_width, narrow_width) = match (left, right) {
        (
            AddressOffset::Int64Scaled {
                value: wide,
                byte_width: wide_width,
                unsigned: true,
            },
            AddressOffset::Int32Scaled {
                value: narrow,
                byte_width: narrow_width,
            },
        )
        | (
            AddressOffset::Int32Scaled {
                value: narrow,
                byte_width: narrow_width,
            },
            AddressOffset::Int64Scaled {
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
    let wide = wide.operand_view().observe(MachineIntegerType::UInt64)?;
    let narrow = narrow.operand_view().observe(MachineIntegerType::Int32)?;
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

/// A byte displacement `x * K` read as `x` elements of `K` bytes, for
/// comparison only.
///
/// `(char *)p + i * 4` keeps its written byte offset when it is formed
/// (`docs/internals/raise-lower-principle.md#lowering-is-fact-stable`), while `p + i`
/// over four-byte elements is the element index `i` at stride four. The two
/// name one address exactly when the `int32` product does not wrap: the
/// element form sign-extends `i` before scaling, the byte form sign-extends
/// the wrapped product. The C multiplication refused its overflowing path, so
/// the no-overflow fact is on the path or follows from its bounds; this asks
/// for it once per product, as the offset rebuilders ask for theirs.
///
/// The equality graph joins the two offsets once the path's `defined(x * K)`
/// fact is admitted (`byte_product_offsets`). SymbolicMemory resolution also runs
/// inside the statement that forms the byte offset, before that statement's
/// facts reach the graph, so a read or store through `(char *)q + 4 * i`
/// compared against `q[i]` there asks the question itself.
///
/// Only an `int32` product by a constant from two to `INT_MAX`, at byte width
/// one, is read, and only within the offset's own `Add` tree, so the work is
/// the size of the offset. `None` when no addend is such a product, or when
/// one is and its overflow is not decided false: the offset is then compared
/// as written.
pub(in crate::kernel) fn byte_products_as_elements(
    offset: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<AddressOffset> {
    use crate::kernel::machine_integer::{Operation, definedness::OverflowQueryView};
    match offset {
        AddressOffset::Add(left, right) => {
            let read_left = byte_products_as_elements(left, assumptions);
            let read_right = byte_products_as_elements(right, assumptions);
            if read_left.is_none() && read_right.is_none() {
                return None;
            }
            Some(AddressOffset::Add(
                Box::new(read_left.unwrap_or_else(|| left.as_ref().clone())),
                Box::new(read_right.unwrap_or_else(|| right.as_ref().clone())),
            ))
        }
        AddressOffset::Int32Scaled {
            value,
            byte_width: 1,
        } => {
            let (MachineIntegerType::Int32, MachineBinaryOp::Multiply, [left, right]) =
                value.operand_view().binary()?
            else {
                return None;
            };
            let (index, stride) = match (left.word32_constant(), right.word32_constant()) {
                (None, Some(stride)) => (left, stride),
                (Some(stride), None) => (right, stride),
                _ => return None,
            };
            if !(2..=i32::MAX as u32).contains(&stride) {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            let query = OverflowQueryView::from_operands(
                MachineIntegerType::Int32,
                Operation::Multiply,
                [left, right],
            )?;
            (assumptions.decide_overflow_query(&query) == Some(false)).then(|| {
                AddressOffset::Int32Scaled {
                    value: index.retain(MachineIntegerType::Int32),
                    byte_width: i64::from(stride),
                }
            })
        }
        _ => None,
    }
}

/// The number of addends a pointer offset sums.
fn addend_count(offset: &AddressOffset) -> usize {
    match offset {
        AddressOffset::Add(left, right) => addend_count(left) + addend_count(right),
        _ => 1,
    }
}

pub(in crate::kernel) fn pointer_offsets_equal_for_memory_resolution(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<bool> {
    use crate::kernel::assumptions::{wide_index_binary, wide_index_comparison};
    if left == right {
        return Some(true);
    }
    if resolution_interrupted() {
        return None;
    }
    // A written byte product and an element index name one address when the
    // product does not wrap; compare them in element coordinates.
    let left_elements = byte_products_as_elements(left, assumptions);
    let right_elements = byte_products_as_elements(right, assumptions);
    if left_elements.is_some() || right_elements.is_some() {
        return pointer_offsets_equal_for_memory_resolution(
            left_elements.as_ref().unwrap_or(left),
            right_elements.as_ref().unwrap_or(right),
            assumptions,
        );
    }
    if let Some(equal) = mixed_index_offsets_equal(left, right, assumptions) {
        return Some(equal);
    }
    // Two unsigned 64-bit indices at one element width. The offset is the
    // exact product `index * width`, so equal indices are one offset and
    // unequal ones are different offsets.
    if let (
        AddressOffset::Int64Scaled {
            value: left_index,
            byte_width: left_width,
            unsigned: true,
        },
        AddressOffset::Int64Scaled {
            value: right_index,
            byte_width: right_width,
            unsigned: true,
        },
    ) = (left, right)
        && left_width == right_width
        && *left_width > 0
    {
        let equal = assumptions.decide(
            &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt64,
                CompareRelation::Equal,
                [left_index.operand_view(), right_index.operand_view()],
            ),
        );
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
            AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
            AddressOffset::Constant(bytes),
        ) = (scaled, constant)
            && *byte_width >= 1
        {
            if *bytes < 0 || bytes % byte_width != 0 {
                return Some(false);
            }
            // A value the equalities pin to a constant is that constant.
            if let Some(pinned) =
                assumptions.wide_constant_from_equalities_view(value.operand_view())
            {
                return Some(pinned == (bytes / byte_width) as u64);
            }
            let index = MachineTerm::uint64_constant((bytes / byte_width) as u64);
            let stated = [
                wide_index_comparison(
                    CompareRelation::Equal,
                    value.operand_view(),
                    MachineOperandView::Legacy(&index),
                ),
                wide_index_comparison(
                    CompareRelation::Equal,
                    MachineOperandView::Legacy(&index),
                    value.operand_view(),
                ),
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
        let AddressOffset::Add(first, second) = stepped else {
            continue;
        };
        let (index, bytes) = match (first.as_ref(), second.as_ref()) {
            (index @ AddressOffset::Int64Scaled { .. }, AddressOffset::Constant(bytes))
            | (AddressOffset::Constant(bytes), index @ AddressOffset::Int64Scaled { .. }) => {
                (index, *bytes)
            }
            _ => continue,
        };
        let (
            AddressOffset::Int64Scaled {
                value: index,
                byte_width,
                unsigned: true,
            },
            AddressOffset::Int64Scaled {
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
        let advanced = wide_index_binary(
            MachineBinaryOp::Add,
            index.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(elements)),
        );
        let same = advanced == *whole_index
            || assumptions.decide(&wide_index_comparison(
                CompareRelation::Equal,
                advanced.operand_view(),
                whole_index.operand_view(),
            )) == Some(true);
        if same
            && assumptions.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                index.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(u64::MAX - elements)),
            )) == Some(true)
        {
            return Some(true);
        }
    }
    // Addends both offsets share cancel exactly, and constants regroup:
    // `s + 5` is `(s + 4) + 1`, which is how a field's element and a run's
    // base spell one address. Only sums are split, so a pair of leaves pays
    // nothing.
    if matches!(left, AddressOffset::Add(..)) || matches!(right, AddressOffset::Add(..)) {
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
                AddressOffset::Int64Scaled { unsigned: true, .. },
                AddressOffset::Constant(_)
            ) | (
                AddressOffset::Constant(_),
                AddressOffset::Int64Scaled { unsigned: true, .. }
            )
        ) && let Some(equal) =
            pointer_offsets_equal_for_memory_resolution(&rest_left, &rest_right, assumptions)
        {
            return Some(equal);
        }
    }
    let _query =
        ResolutionQueryGuard::enter(ResolutionQuery::OffsetEqual(left.clone(), right.clone()))?;
    if let Some(value) = assumptions.exact_condition_value(&ConditionTerm::address_offset_equal(
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
            let expected = MachineTerm::constant(expected as u32);
            if delta.index.operand_view().word32_constant() == expected.as_const() {
                return Some(true);
            }
            if let Some(value) = assumptions.exact_int32_equality_value_views(
                delta.index.operand_view(),
                MachineOperandView::Legacy(&expected),
            ) {
                return Some(value);
            }
            if assumptions.equality_graph.are_int32_equal_views(
                delta.index.operand_view(),
                MachineOperandView::Legacy(&expected),
            ) {
                return Some(true);
            }
        }
    }
    if let Some(element_width) = common_pointer_offset_element_width(left, right)
        && let (Some(left_index), Some(right_index)) = (
            shared_element_index_from_offset_with_facts(left, element_width, assumptions),
            shared_element_index_from_offset_with_facts(right, element_width, assumptions),
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
            crate::kernel::assumptions::exact_signed_constant_view(
                left_index.operand_view(),
                assumptions,
            ),
            crate::kernel::assumptions::exact_signed_constant_view(
                right_index.operand_view(),
                assumptions,
            ),
        ) {
            if left != right {
                return Some(false);
            }
            if exact() {
                return Some(true);
            }
        }
        if int32_operand_values_equal_for_memory_resolution(
            left_index.operand_view(),
            right_index.operand_view(),
            assumptions,
        ) && exact()
        {
            return Some(true);
        }
        if let Some(equal) = assumptions.decide_bitvector_equality_shallow_views(
            left_index.operand_view(),
            right_index.operand_view(),
        ) && (!equal || exact())
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
        let excluded = |symbolic: MachineOperandView<'_>, constant: MachineOperandView<'_>| {
            let Some(constant) = crate::kernel::assumptions::signed_index_constant(constant) else {
                return false;
            };
            assumptions
                .indexed_constant_interval_view(symbolic, false)
                .is_some_and(|(low, high)| constant < low || high < constant)
        };
        if excluded(left_index.operand_view(), right_index.operand_view())
            || excluded(right_index.operand_view(), left_index.operand_view())
        {
            return Some(false);
        }
    }
    // Addition of equal exact byte offsets preserves equality even when
    // folding the whole sum into an int32 index would wrap. Reach this only
    // after cheaper scalar comparisons have failed to decide the question.
    if let (AddressOffset::Add(left_a, left_b), AddressOffset::Add(right_a, right_b)) =
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

/// `(char *)q + i * 4` and `q + i` over four-byte elements are one address
/// where the product does not wrap: bounds that decide it make the two
/// offsets equal, in either operand order of the product and beside a shared
/// base, and an index the facts keep off `i` makes them differ. With no
/// bound, `i * 4` may wrap, and the two are not called equal.
#[cfg(test)]
#[test]
fn a_byte_product_offset_is_its_element_offset_only_where_it_does_not_wrap() {
    let index = MachineTerm::Variable(Variable(861));
    let other = MachineTerm::Variable(Variable(862));
    let base = AddressOffset::scale_int32(MachineTerm::Variable(Variable(863)), 4);
    let bytes = |product: MachineTerm| {
        AddressOffset::add(base.clone(), AddressOffset::scale_int32(product, 1))
    };
    let elements = |index: &MachineTerm| {
        AddressOffset::add(base.clone(), AddressOffset::scale_int32(index.clone(), 4))
    };
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), MachineTerm::constant(4)),
            true,
        );
    for product in [
        MachineTerm::multiply(index.clone(), MachineTerm::constant(4)),
        MachineTerm::multiply(MachineTerm::constant(4), index.clone()),
    ] {
        assert_eq!(
            pointer_offsets_equal_for_memory_resolution(
                &bytes(product.clone()),
                &elements(&index),
                &bounded
            ),
            Some(true)
        );
        assert_ne!(
            pointer_offsets_equal_for_memory_resolution(
                &bytes(product.clone()),
                &elements(&index),
                &PureFactContext::new()
            ),
            Some(true),
            "an unbounded product may wrap"
        );
        let apart = bounded
            .clone()
            .assume_condition(ConditionTerm::equal(index.clone(), other.clone()), false);
        assert_eq!(
            pointer_offsets_equal_for_memory_resolution(&bytes(product), &elements(&other), &apart),
            Some(false)
        );
    }
}

#[cfg(test)]
#[test]
fn indexed_field_offsets_use_exact_displacements() {
    let index = MachineTerm::Variable(Variable(849));
    let offset = AddressOffset::add(
        AddressOffset::Constant(4),
        AddressOffset::scale_int32(index.clone(), 4),
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index.clone(), MachineTerm::constant(1)),
        true,
    );
    let concrete = AddressOffset::Constant(8);
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&offset, &concrete, &assumptions),
        Some(true)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&concrete, &offset, &assumptions),
        Some(true)
    );
    let boundary = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index, MachineTerm::constant(i32::MAX as u32)),
        true,
    );
    // Adding the field offset happens after sign extension: it must not
    // wrap i32::MAX + 1 to i32::MIN before comparing byte addresses.
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &offset,
            &AddressOffset::Constant(i64::from(i32::MIN) * 4),
            &boundary
        ),
        Some(false)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &offset,
            &AddressOffset::Constant((i64::from(i32::MAX) + 1) * 4),
            &boundary
        ),
        Some(true)
    );
}

#[cfg(test)]
#[test]
fn a_constant_index_outside_the_recorded_bounds_is_a_different_offset() {
    let index = MachineTerm::Variable(Variable(851));
    let scaled = AddressOffset::scale_int32(index.clone(), 4);
    let at_least_one = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(MachineTerm::constant(1), index.clone()),
        true,
    );
    for constant in [0, -4] {
        let concrete = AddressOffset::Constant(constant);
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
            &AddressOffset::Constant(4),
            &at_least_one
        ),
        None
    );
    let unbounded = PureFactContext::new();
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &scaled,
            &AddressOffset::Constant(0),
            &unbounded
        ),
        None
    );
}

#[cfg(test)]
#[test]
fn memory_resolution_uses_graph_offset_congruence_in_branch_scope() {
    let scalar = |id: u64| MachineTerm::Variable(Variable(91_000 + id));
    let offset = |id| {
        AddressOffset::add(
            AddressOffset::Constant(4),
            AddressOffset::scale_int32(scalar(id), 4),
        )
    };
    let named = AddressOffset::Variable(Variable(91_100));
    let named_fact = ConditionTerm::address_offset_equal(offset(2), named.clone());
    let scalar_fact = ConditionTerm::equal(scalar(1), scalar(2));
    let parent = PureFactContext::new().assume_condition(named_fact.clone(), true);
    let branch = parent.clone().assume_condition(scalar_fact.clone(), true);
    let pointer = |offset| Address {
        base: AddressBase::ExternalArgument,
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

    let restricted = branch.restricted_to_facts(&[], &[]);
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &restricted),
        Some(true)
    );
    let scalar_only = PureFactContext::new().assume_condition(scalar_fact, true);
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&offset(1), &named, &scalar_only),
        Some(true)
    );
}

#[cfg(test)]
#[test]
fn memory_resolution_uses_pointer_classes_across_blocks() {
    let pointer = |block: u64, offset| Address {
        base: AddressBase::Symbolic(Variable(91_200 + block)),
        offset: AddressOffset::Constant(offset),
    };
    let first = ConditionTerm::address_equal(pointer(0, 0), pointer(1, 4));
    let second = ConditionTerm::address_equal(pointer(1, 4), pointer(2, 8));
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
}

#[cfg(test)]
#[test]
fn memory_resolution_graph_offsets_keep_load_states_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = crate::kernel::intern_memory(SymbolicMemory::new().with_block("offset-load", 16));
    let scalar = |id: u64| MachineTerm::Variable(Variable(95_000 + id));
    let address = |index| Address {
        base: "offset-load".into(),
        offset: AddressOffset::scale_int32(index, 4),
    };
    let loaded = |memory: &SharedMemory, index| {
        MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
            memory,
            &address(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let after = crate::kernel::intern_memory(before.memory().clone().store(
        address(scalar(1)),
        ProgramValue::Int32(MachineTerm::constant(9)),
    ));
    let left = AddressOffset::scale_int32(loaded(&before, scalar(1)), 4);
    let right = AddressOffset::scale_int32(loaded(&before, scalar(2)), 4);
    let changed = AddressOffset::scale_int32(loaded(&after, scalar(2)), 4);
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
fn pointer_with_exact_index_constants(pointer: &Address, assumptions: &PureFactContext) -> Address {
    enum Task<'a> {
        Visit(&'a AddressOffset),
        Add,
    }
    let mut work = vec![Task::Visit(&pointer.offset)];
    let mut values = Vec::new();
    while let Some(task) = work.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match task {
            Task::Visit(AddressOffset::Add(left, right)) => {
                work.push(Task::Add);
                work.push(Task::Visit(right));
                work.push(Task::Visit(left));
            }
            Task::Visit(offset @ AddressOffset::Int32Scaled { value, byte_width }) => {
                values.push(
                    crate::kernel::assumptions::exact_signed_constant_view(
                        value.operand_view(),
                        assumptions,
                    )
                    .and_then(|index| i32::try_from(index).ok())
                    .and_then(|index| i64::from(index).checked_mul(*byte_width))
                    .map(AddressOffset::Constant)
                    .unwrap_or_else(|| offset.clone()),
                );
            }
            Task::Visit(offset @ AddressOffset::Int64Scaled { .. }) => {
                values.push(
                    crate::kernel::assumptions::exact_wide_scaled_offset_constant(
                        offset,
                        assumptions,
                    )
                    .map(AddressOffset::Constant)
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
                values.push(AddressOffset::add(left, right));
            }
        }
    }
    Address {
        base: pointer.base.clone(),
        offset: values.pop().expect("pointer offset"),
    }
}

/// Resolve this address through exact cells, recorded scalar/pointer aliases,
/// and the indexed interval of cells with the same base address.
fn stored_value_at_equal_pointer(
    memory: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    if let Some(value) = memory.known_value(pointer) {
        return Some(value);
    }
    if let Some(value) = memory.known_union_value(pointer, ProgramType::Int32) {
        return Some(value);
    }
    let normalized = pointer_with_exact_index_constants(pointer, assumptions);
    if normalized != *pointer
        && let Some(value) = memory
            .known_value(&normalized)
            .or_else(|| memory.known_union_value(&normalized, ProgramType::Int32))
    {
        return Some(value);
    }
    if let AddressOffset::Int32Scaled {
        value: index,
        byte_width,
    } = &pointer.offset
        && let Some(value) = assumptions
            .recorded_equality_class_view(index.operand_view())
            .into_iter()
            .find_map(|member| {
                memory
                    .known_value(&Address {
                        base: pointer.base.clone(),
                        offset: AddressOffset::Int32Scaled {
                            value: member.clone(),
                            byte_width: *byte_width,
                        },
                    })
                    .or_else(|| {
                        memory.known_union_value(
                            &Address {
                                base: pointer.base.clone(),
                                offset: AddressOffset::Int32Scaled {
                                    value: member,
                                    byte_width: *byte_width,
                                },
                            },
                            ProgramType::Int32,
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
                .or_else(|| memory.known_union_value(&alias, ProgramType::Int32))
        })
        .or_else(|| {
            // Add(root, displacement) occupies one contiguous map interval.
            // Query that interval instead of visiting unrelated objects in
            // the shared ExternalArgument block.
            let mut root = &pointer.offset;
            while let AddressOffset::Add(left, _) = root { root = left; }
            if matches!(root, AddressOffset::Constant(_)) { return None; }
            let first = Address {
                base: pointer.base.clone(),
                offset: AddressOffset::Add(Box::new(root.clone()), Box::new(AddressOffset::Constant(i64::MIN))),
            };
            memory.cells.concrete().range(first..)
                .take_while(|(stored, _)| stored.base == pointer.base
                    && matches!(&stored.offset, AddressOffset::Add(left, _) if left.as_ref() == root))
                .find_map(|(stored, value)| {
                    crate::instrumentation::record_deterministic_work(1);
                    pointers_proven_equal_for_memory_resolution(pointer, stored, assumptions)
                        .then(|| value.native().clone())
                })
                .or_else(|| {
                    memory
                        .cells
                        .runs_based_at(&pointer.base, root)
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
    pointer: &Address,
    root: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    crate::instrumentation::record_deterministic_work(1);
    if run.base().base != pointer.base || run.base().offset != *root || run.live_count() == 0 {
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
            let pinned = crate::kernel::assumptions::exact_signed_constant_view(
                index.operand_view(),
                assumptions,
            )
            .or_else(|| {
                assumptions
                    .signed_interval_view(index.operand_view())
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
            let pinned = crate::kernel::assumptions::exact_sixty_four_bit_constant_view(
                index.operand_view(),
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
    left: &MachineTerm,
    right: &MachineTerm,
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
    // through the registry so memory-history reasoning fires exactly as it would
    // for the load term, then fall through to the variable-form
    // paths if the load view does not decide.
    let canonical_view = |term: &MachineTerm| {
        if let MachineTerm::Variable(variable) = term {
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
    // are equal after a bounded walk over named edges, with no state
    // comparison at all (see `atomic_loads_equal_along_memory_derivations`). The
    // walk applies only to two load terms of one pointer.
    if crate::kernel::api::atomic_loads_equal_along_memory_derivations(left, right, assumptions) {
        return true;
    }
    // Do not construct scaled query operands when there are no exact offset
    // equalities to select. Ordinary word equalities were queried above.
    if assumptions.has_recorded_address_offset_equalities()
        && [1, 4].into_iter().any(|byte_width| {
            assumptions.exact_condition_value(&ConditionTerm::address_offset_equal(
                AddressOffset::scale_int32(left.clone(), byte_width),
                AddressOffset::scale_int32(right.clone(), byte_width),
            )) == Some(true)
        })
    {
        return true;
    }
    if let MachineTerm::MemoryLoad(memory, pointer, LoadKind::Int32) = left
        && let Some(ProgramValue::Int32(value)) =
            stored_value_at_equal_pointer(memory.memory(), pointer, assumptions)
        && &value != left
        && bitvector_terms_proven_equal_for_memory_resolution(&value, right, assumptions)
    {
        return true;
    }
    if let MachineTerm::MemoryLoad(memory, pointer, LoadKind::Int32) = right
        && let Some(ProgramValue::Int32(value)) =
            stored_value_at_equal_pointer(memory.memory(), pointer, assumptions)
        && &value != right
        && bitvector_terms_proven_equal_for_memory_resolution(left, &value, assumptions)
    {
        return true;
    }
    if let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right) {
        return bitvector_terms_proven_equal_for_memory_resolution(&left, &right, assumptions);
    }
    let zero = MachineTerm::constant(0);
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
        (
            binary_term!(Bits32 @ left_format, Add, left_a, left_b),
            binary_term!(Bits32 @ right_format, Add, right_a, right_b),
        )
        | (
            binary_term!(Bits32 @ left_format, Subtract, left_a, left_b),
            binary_term!(Bits32 @ right_format, Subtract, right_a, right_b),
        )
        | (
            binary_term!(Bits32 @ left_format, Multiply, left_a, left_b),
            binary_term!(Bits32 @ right_format, Multiply, right_a, right_b),
        ) if left_format == right_format => {
            bitvector_terms_proven_equal_for_memory_resolution(left_a, right_a, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(left_b, right_b, assumptions)
        }
        (
            MachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
            MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
        ) => {
            // Equal addresses are not enough: two reads there are one value
            // only when they are one kind of read.
            left_kind == right_kind
                && pointers_proven_equal_for_memory_resolution(
                    left_pointer,
                    right_pointer,
                    assumptions,
                )
                && !loads_lack_recorded_equality(
                    left_memory.shared_memory(),
                    right_memory.shared_memory(),
                    left_pointer,
                    *left_kind,
                    assumptions,
                )
                && memory_states_match_for_resolution(
                    left_memory.shared_memory(),
                    right_memory.shared_memory(),
                    left_pointer,
                    assumptions,
                )
        }
        _ => false,
    }
}

pub(in crate::kernel) fn bitvector_terms_proven_equal_for_memory_resolution(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::BitvectorEqual(id, bridging, left.clone(), right.clone())
    });
    memoized_resolution_query(key, || {
        bitvector_terms_equal_for_memory_resolution_unmemoized(left, right, assumptions)
    })
}

/// The memory-resolution value rules over retained operands. Only selected
/// read leaves enter the native state machinery; arithmetic stays shared.
pub(in crate::kernel) fn int32_operand_values_equal_for_memory_resolution(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::machine_integer::{
        Relation,
        comparison::{ComparisonOperand, NativeComparisonView},
    };
    use crate::kernel::{MachineIntegerType as T, MachineOperandView as V};
    if let (V::Legacy(left), V::Legacy(right)) = (left, right) {
        return int32_values_proven_equal_for_memory_resolution(left, right, assumptions);
    }
    let _scope = assumptions.enter_id_scope();
    let operands = [left.retain(T::Int32), right.retain(T::Int32)];
    let key = resolution_query_memo_id(assumptions).map(|(id, bridging)| {
        ResolutionQueryKey::OperandEqual(id, bridging, operands[0].clone(), operands[1].clone())
    });
    memoized_resolution_query(key, || {
        if assumptions
            .equality_graph
            .are_int32_equal_views(left, right)
        {
            return true;
        }
        // Constants and selected reads are fixed-size leaves, not tree exports.
        fn leaf(v: V<'_>) -> Option<std::borrow::Cow<'_, MachineTerm>> {
            v.literal()
                .or_else(|| v.variable().copied().map(MachineTerm::Variable))
                .map(std::borrow::Cow::Owned)
                .or_else(|| v.read_source())
        }
        if let (Some(left), Some(right)) = (leaf(left), leaf(right)) {
            return int32_values_proven_equal_for_memory_resolution(&left, &right, assumptions);
        }
        if let (Some(a), Some(b)) = (
            crate::kernel::assumptions::exact_signed_constant_view(left, assumptions),
            crate::kernel::assumptions::exact_signed_constant_view(right, assumptions),
        ) {
            return a == b;
        }
        if resolution_interrupted() {
            return false;
        }
        let Some(_guard) = ResolutionQueryGuard::enter(ResolutionQuery::OperandEqual(
            operands[0].clone(),
            operands[1].clone(),
        )) else {
            return false;
        };
        let equal = |a: V<'_>, b: V<'_>| {
            int32_operand_values_equal_for_memory_resolution(a, b, assumptions)
        };
        let origins = [left, right].map(|operand| {
            operand
                .variable()
                .and_then(crate::kernel::eval::registered_load_origin_term_for_variable)
        });
        if origins.iter().any(Option::is_some)
            && equal(
                origins[0].as_ref().map(V::Legacy).unwrap_or(left),
                origins[1].as_ref().map(V::Legacy).unwrap_or(right),
            )
        {
            return true;
        }
        if assumptions.has_recorded_address_offset_equalities()
            && [1, 4].into_iter().any(|byte_width| {
                let offset = |v: V<'_>| {
                    v.word32_constant()
                        .map(|bits| AddressOffset::Constant(i64::from(bits as i32) * byte_width))
                        .unwrap_or_else(|| AddressOffset::Int32Scaled {
                            value: v.retain(T::Int32),
                            byte_width,
                        })
                };
                assumptions.exact_condition_value(&ConditionTerm::address_offset_equal(
                    offset(left),
                    offset(right),
                )) == Some(true)
            })
        {
            return true;
        }
        for (read, other) in [(left, right), (right, left)] {
            if let Some((memory, pointer, LoadKind::Int32)) = read.read()
                && let Some(ProgramValue::Int32(value)) =
                    stored_value_at_equal_pointer(memory, pointer, assumptions)
                && equal(V::Legacy(&value), other)
            {
                return true;
            }
        }
        let comparison = NativeComparisonView {
            format: T::Int32,
            relation: Relation::Equal,
            operands: operands.clone().map(ComparisonOperand::Observation),
        };
        if let Some(cancelled) = comparison.cancelled_equality() {
            return equal(
                cancelled.operands[0].operand_view(),
                cancelled.operands[1].operand_view(),
            );
        }
        let zero = MachineTerm::constant(0);
        for (sum, other) in [(left, right), (right, left)] {
            if let Some((T::Int32, MachineBinaryOp::Add, [a, b])) = sum.binary()
                && ((equal(a, other) && equal(b, V::Legacy(&zero)))
                    || (equal(b, other) && equal(a, V::Legacy(&zero))))
            {
                return true;
            }
        }
        match (left.binary(), right.binary()) {
            (Some((lf, lo, [la, lb])), Some((rf, ro, [ra, rb])))
                if lf == rf
                    && lf.format().bits() == 32
                    && lo == ro
                    && matches!(
                        lo,
                        MachineBinaryOp::Add
                            | MachineBinaryOp::Subtract
                            | MachineBinaryOp::Multiply
                    ) =>
            {
                equal(la, ra) && equal(lb, rb)
            }
            _ => false,
        }
    })
}

/// Compare int32 *values* through the trusted graph before broader memory
/// resolution. Callers proving exact byte-offset equality must use the
/// separate offset judgment rather than this wrapping value equality.
pub(in crate::kernel) fn int32_values_proven_equal_for_memory_resolution(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    assumptions.int32_values_known_equal(left, right)
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

pub(in crate::kernel) fn program_values_proven_equal_for_memory_resolution(
    left: &ProgramValue,
    right: &ProgramValue,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (ProgramValue::Void, ProgramValue::Void) => true,
        (ProgramValue::Int8(left), ProgramValue::Int8(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (ProgramValue::Int32(left), ProgramValue::Int32(right)) => {
            int32_values_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (ProgramValue::Int64(left), ProgramValue::Int64(right))
        | (ProgramValue::UInt64(left), ProgramValue::UInt64(right)) => {
            assumptions.uint64_values_known_equal(left, right)
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (ProgramValue::Int16(left), ProgramValue::Int16(right))
        | (ProgramValue::UInt8(left), ProgramValue::UInt8(right))
        | (ProgramValue::UInt16(left), ProgramValue::UInt16(right))
        | (ProgramValue::UInt32(left), ProgramValue::UInt32(right))
        | (ProgramValue::Float32(left), ProgramValue::Float32(right))
        | (ProgramValue::Float64(left), ProgramValue::Float64(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (ProgramValue::Pointer(left), ProgramValue::Pointer(right)) => {
            assumptions.pointer_provenance_match(left, right)
                && pointers_proven_equal_for_memory_resolution(
                    left.address(),
                    right.address(),
                    assumptions,
                )
        }
        _ => false,
    }
}

/// The only `local:` block a state comparison with **no load pointer** may
/// drop before comparing.
///
/// [`memories_proven_equal_for_memory_resolution`] and its certification twin
/// `memories_definitionally_equal` are whole-state equalities. They are
/// handed no pointer, so they cannot ask
/// [`AddressBase::observable_by_load`] which cells a particular read could
/// see, and both used to drop every cell and block spelled `local:` instead.
/// That is the withdrawn `Symbolic` exception of `observable_by_load` with the
/// sides swapped: instead of claiming an unresolved load reads only its own
/// block, it claims no automatic object is memory such a load reads.
/// `int32* echo(int32* p) { return p; } … q = echo(&x); x = 1;` refutes it —
/// `q` *is* `&x`, so two states differing only in `local:x` are two
/// different states for a read through `q`
/// (`mdtests/an_unresolved_pointer_sees_the_store_to_a_local.md` is the false
/// theorem the pointer-aware spelling of the same shortcut admitted).
///
/// What survives is the half of the claim that needs no pointer. An automatic
/// object whose address no function in this session's sources ever forms is
/// not memory any pointer value in the program designates, so *no* load
/// anywhere can tell two states apart by it. That is
/// [`crate::kernel::primitives::block_is_never_address_taken_local`], whose
/// soundness argument lives on that function; it is a property of the whole
/// program's source rather than of one proof path, which is exactly why a
/// comparison may spend it with neither a pointer nor a fact context — the
/// same reason the two naming walks may.
///
/// The object read under **its own name** is a different question, and not
/// this filter's to answer. A scalar local's program-visible value lives in
/// the `LocalEnvironment` binding, which the callers of these two
/// comparisons either compare exactly as part of `ExecutionState` equality or do not
/// ask about at all (an effect chain's two endpoints). A caller that needs the
/// slot cell itself compares `ExecutionState::local_cell_values` beside the memory,
/// as `function_entry_representation_states_match` does.
///
/// Cost: one registry lookup on a name of bounded length.
pub(in crate::kernel) fn local_block_no_pointer_can_reach(block: &AddressBase) -> bool {
    crate::kernel::primitives::block_is_never_address_taken_local(block)
}

pub(in crate::kernel) fn memories_proven_equal_for_memory_resolution(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
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
    // (see `state_objects_agree`).
    if left.forgotten.forgotten_from != right.forgotten.forgotten_from
        || left.forgotten.join_inputs != right.forgotten.join_inputs
    {
        return false;
    }
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| !local_block_no_pointer_can_reach(&pointer.base))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .all(|pointer| {
            let left_value = left.known_value(pointer);
            let right_value = right.known_value(pointer);
            match (&left_value, &right_value) {
                (Some(left), Some(right)) => {
                    program_values_proven_equal_for_memory_resolution(left, right, assumptions)
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
            .filter(|(pointer, _)| !local_block_no_pointer_can_reach(&pointer.base))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .all(|(pointer, value_type)| {
                match (
                    left.union_cells.get(&(pointer.clone(), *value_type)),
                    right.union_cells.get(&(pointer.clone(), *value_type)),
                ) {
                    (Some(left), Some(right)) => program_values_proven_equal_for_memory_resolution(
                        left.native(),
                        right.native(),
                        assumptions,
                    ),
                    (None, None) => true,
                    _ => false,
                }
            })
}

pub(in crate::kernel) fn memory_load_terms_equal_for_fact_transport(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let (Some(left_load), Some(right_load)) = (
        crate::kernel::eval::viewed_as_memory_load(left),
        crate::kernel::eval::viewed_as_memory_load(right),
    ) else {
        return false;
    };
    let (
        MachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
        MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (&left_load, &right_load)
    else {
        return false;
    };
    left_kind == right_kind
        && (pointers_proven_equal_for_memory_resolution(left_pointer, right_pointer, assumptions)
            || left_pointer.base == right_pointer.base
                && assumptions
                    .has_pointer_offset_state_fact(&left_pointer.offset, &right_pointer.offset))
        && memory_states_match_for_resolution(
            left_memory.shared_memory(),
            right_memory.shared_memory(),
            left_pointer,
            assumptions,
        )
}

/// Structural state equality needs positive evidence that the selected
/// reads agree. An undecided bounded history query is not preservation: its
/// unvisited suffix can contain a write or a released allocation.
/// Naming projections use their registered source, without discovering any
/// older source by walking history.
pub(in crate::kernel) fn loads_lack_recorded_equality(
    left: &SharedMemory,
    right: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> bool {
    let agrees = |left: &SharedMemory, right: &SharedMemory| {
        matches!(
            crate::kernel::api::with_extended_dag_bridging(|| {
                crate::kernel::api::recorded_load_history(left, right, pointer, kind, assumptions)
            }),
            crate::kernel::api::LoadHistory::OneVersion(_)
        )
    };
    if agrees(left, right) {
        return false;
    }
    let left_source = canonical_load_projection_source(left, pointer);
    let right_source = canonical_load_projection_source(right, pointer);
    !(left_source.is_some() || right_source.is_some())
        || !agrees(
            left_source.as_ref().unwrap_or(left),
            right_source.as_ref().unwrap_or(right),
        )
}

/// Gate structural comparisons of load terms on positive recorded evidence.
/// Stated equalities use the fact graph independently of this gate.
pub(in crate::kernel) fn load_equality_lacks_recorded_evidence(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let load = |term: &MachineTerm| match term {
        MachineTerm::MemoryLoad(_, _, _) => Some(term.clone()),
        MachineTerm::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        _ => None,
    };
    let (
        Some(MachineTerm::MemoryLoad(left_memory, left_pointer, left_kind)),
        Some(MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind)),
    ) = (load(left), load(right))
    else {
        return false;
    };
    // Two reads of one address that differ in kind are two values whatever
    // the history says, so no structural route may call them equal.
    left_pointer != right_pointer
        || left_kind != right_kind
        || loads_lack_recorded_equality(
            left_memory.shared_memory(),
            right_memory.shared_memory(),
            &left_pointer,
            left_kind,
            assumptions,
        )
}

fn memory_states_match_for_resolution(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
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
    if assumptions.memory_states_directly_proven_equal_for_memory_resolution(left, right, pointer) {
        return true;
    }
    if pointer.base.is_local_block() {
        return false;
    }
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::StatesMatch(
        super::intern_memory_ref(left),
        super::intern_memory_ref(right),
        pointer.clone(),
    )) else {
        return false;
    };
    if memory_has_materialized_load_from(left, right, pointer, assumptions)
        || memory_has_materialized_load_from(right, left, pointer, assumptions)
    {
        return true;
    }
    if !state_objects_agree(left, right, pointer) {
        return false;
    }

    // Slots of a run at a constant gap from the load that clears its bytes
    // are other addresses by arithmetic, as for
    // `memories_match_for_pointer_load_under_assumptions`; spelling each of
    // them out would cost the run's whole length.
    let load_bytes = crate::kernel::load_access_width_at_address_or_widest(pointer);
    let differing = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "state comparison: differing cells",
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
pub(in crate::kernel) fn cell_access_byte_width(value: &ProgramValue) -> u32 {
    match value.byte_width() {
        0 => crate::kernel::resource_tracker::widest_scalar_access_bytes(),
        bytes => bytes,
    }
}

/// How wide the cell the two states differ on is, in bytes.
///
/// The width comes from the value the cell holds, on whichever side holds
/// one, and from the wider of the two where both do and disagree: the entry
/// has to cover every byte either state keeps there. A cell that is only a
/// union view, or one holding `Void`, has no value width to read here and
/// stands in the widest scalar — over-stating a width can only shrink the
/// separated set.
pub(in crate::kernel) fn differing_cell_byte_width(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    cell_pointer: &Address,
) -> u32 {
    let stored_width = |memory: &SymbolicMemory| {
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
/// asking: they are deciding whether the two states hold the same value
/// for this load, and a cell at `p + 1` holding one byte is a different
/// address from `p` while being the second byte a four-byte read there
/// returns. Only where the bytes are shown separate may the ladder stand in
/// for them; provable overlap and an unknown gap both mean the states are
/// not shown to agree.
pub(in crate::kernel) fn differing_cell_bytes_miss_the_load(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    cell_pointer: &Address,
    load_pointer: &Address,
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

/// The filter the three "do these states agree about this load" comparisons
/// — [`memory_states_match_for_resolution`],
/// [`memories_match_for_pointer_load_bounded_alias`] and
/// [`memories_match_for_pointer_load_under_assumptions`] — apply to the cells
/// the two states differ on, before asking whether each one is separate
/// from the load.
///
/// It is [`AddressBase::observable_by_load`] — the same filter the rest of
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
/// in place, two states that differed only in `local:x` were declared to
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
/// `Temporary` — `AddressBase::proven_distinct` separates it from a `local:`
/// block, so those cells are answered `true` on the first rung of the
/// distinctness ladder instead of being skipped. What the filter keeps is
/// exactly the set of cells whose block the kernel cannot tell apart from the
/// load's, which is the set the comparison exists to decide.
fn cell_is_observable_by_load(cell_pointer: &Address, load: &Address) -> bool {
    cell_pointer.base.observable_by_load(&load.base)
}

/// Whether the three assumption-carrying comparisons agree about the
/// *objects* the two states hold, as against the values in their cells:
/// each block's size, and which automatic blocks have had their lifetimes
/// ended.
///
/// The cell filter beside this one was corrected to
/// [`cell_is_observable_by_load`]; this one was left as the same block-name
/// shortcut, `!block.is_local_block()`, and it makes the same claim about
/// a different map. A block's size is what says the object is there and how
/// big it is, so two states that disagree about a local's size or
/// liveness disagree about the object a load through a pointer that may
/// designate it reads — and `&a` may be handed to a callee and come back as
/// its result, so "the load's pointer is not spelled `local:`" does not mean
/// the load misses every local.
///
/// The filter is now [`local_block_no_pointer_can_reach`], the one
/// [`memories_proven_equal_for_memory_resolution`] spends in the same place: a
/// local whose address is never taken anywhere in the program is not memory
/// any pointer value designates, so no load can tell two states apart by
/// it. That is a property of the whole program's source, which is why it may
/// be spent with neither a pointer nor a fact context. Every other local stays
/// in the comparison.
fn state_objects_agree(left: &SymbolicMemory, right: &SymbolicMemory, pointer: &Address) -> bool {
    let reachable = |block: &AddressBase| !local_block_no_pointer_can_reach(block);
    // Every caller goes on to compare the two cell maps and treats an entry
    // neither side holds as agreement. That reading is only valid between
    // maps layered over one underlying state: a cell map is knowledge about
    // the state its forget mark names, and a store whose cell was later
    // forgotten leaves no entry on either side for a difference to show.
    // `memories_match_for_pointer_load` asks the same question first for the
    // same reason; two states with different marks are related by the
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

/// Whether the two states agree about which automatic objects the load may
/// reach have had their lifetimes ended.
///
/// None of the four "do these states agree about this load" comparisons
/// looked at this map. Once a retired block's cells are gone the tombstone is
/// the only record that its lifetime ended, and a load through a stale alias
/// is exactly the load these comparisons are asked about;
/// `memories_proven_equal_for_memory_resolution`, `SymbolicMemory`'s own `eq` and
/// `read_region_identity` all compare it.
///
/// Two exclusions, both sound, and each catches what the other does not: this
/// load's block is proven distinct from that object, or *no* pointer value in
/// the program designates it.
fn retirements_agree_for_load(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
) -> bool {
    left.forgotten
        .ended_local_blocks
        .symmetric_difference(&right.forgotten.ended_local_blocks)
        .into_iter()
        .all(|block| {
            !block.observable_by_load(&pointer.base) || local_block_no_pointer_can_reach(block)
        })
}

pub(in crate::kernel) fn memory_states_proven_equal_at_pointer(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    memory_states_match_for_resolution(left, right, pointer, assumptions)
}

fn memory_has_materialized_load_from(
    source: &SymbolicMemory,
    materialized: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    let Some(ProgramValue::Int32(MachineTerm::MemoryLoad(
        retained_state,
        load_pointer,
        LoadKind::Int32,
    ))) = materialized.known_value(pointer)
    else {
        return false;
    };
    // The cell holds four bytes of the source; it answers for the read at
    // this address only when the read is no wider.
    crate::kernel::load_access_width_at_address_or_widest(pointer) <= 4
        && pointers_proven_equal_for_memory_resolution(&load_pointer, pointer, assumptions)
        && memory_states_match_for_resolution(source, retained_state.memory(), pointer, assumptions)
}

pub(in crate::kernel) fn pointer_offsets_with_common_base_proven_distinct(
    left: &Address,
    right: &Address,
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
    left: &Address,
    right: &Address,
) -> Option<ConditionTerm> {
    let (left_index, right_index) = common_base_index_offsets(left, right)?;
    if let (Some(left), Some(right)) = (left_index.as_const(), right_index.as_const()) {
        return Some(ConditionTerm::Constant(left == right));
    }
    let (left_index, right_index, _) = element_indices_of(&left_index, &right_index)?;
    Some(crate::kernel::assumptions::index_comparison(
        CompareRelation::Equal,
        left_index.operand_view(),
        right_index.operand_view(),
    ))
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
    left: &Address,
    right: &Address,
) -> Option<(SharedMachineIntegerTerm, SharedMachineIntegerTerm, u32)> {
    let (left_index, right_index) = common_base_index_offsets(left, right)?;
    element_indices_of(&left_index, &right_index)
}

/// Two element indices a store compares to keep a cached cell, and the
/// machine format of the comparison it reads.
pub(in crate::kernel) struct StoreElementIndices {
    pub(in crate::kernel) left: SharedMachineIntegerTerm,
    pub(in crate::kernel) right: SharedMachineIntegerTerm,
    /// `Int32` for 32-bit scaled indices; `Int64` or `UInt64` for 64-bit
    /// scaled indices of that signedness.
    pub(in crate::kernel) format: MachineIntegerType,
}

impl StoreElementIndices {
    /// The comparison `left relation right` (or `right relation left` when
    /// `swapped`) in the indices' own format: the key of the exact fact the
    /// store reads. An `int32` pair is compared as the Integer values of its
    /// two words, as `index_comparison` builds it; a 64-bit pair as the
    /// retained comparison its stated fact lowers to, such as
    /// `((n - 1) as uint64) != 0`.
    pub(in crate::kernel) fn comparison(
        &self,
        relation: CompareRelation,
        swapped: bool,
    ) -> ConditionTerm {
        let (left, right) = if swapped {
            (&self.right, &self.left)
        } else {
            (&self.left, &self.right)
        };
        if self.format == MachineIntegerType::Int32 {
            return crate::kernel::assumptions::index_comparison(
                relation,
                left.operand_view(),
                right.operand_view(),
            );
        }
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            self.format,
            relation,
            [left.operand_view(), right.operand_view()],
        )
    }
}

/// The element indices of two addresses with a common base, in the format a
/// store compares them: the `int32` indices of [`common_base_element_indices`],
/// or two 64-bit scaled indices of one element width and one signedness, one
/// of which may instead be a constant offset of whole elements (`q[0]`
/// against `q[n - 1]` for a `size_t n`). A mixed 32/64-bit pair, a pair of
/// different signedness or width, or a constant the index format cannot hold
/// has none. This reads the two offsets' structure only.
pub(in crate::kernel) fn common_base_store_indices(
    left: &Address,
    right: &Address,
) -> Option<StoreElementIndices> {
    let (left_index, right_index) = common_base_index_offsets(left, right)?;
    if let Some((left, right, _)) = element_indices_of(&left_index, &right_index) {
        return Some(StoreElementIndices {
            left,
            right,
            format: MachineIntegerType::Int32,
        });
    }
    wide_element_indices_of(&left_index, &right_index)
}

fn wide_element_indices_of(
    left: &AddressOffset,
    right: &AddressOffset,
) -> Option<StoreElementIndices> {
    let scaled = |offset: &AddressOffset| match offset {
        AddressOffset::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } if *byte_width > 0 => Some((value.clone(), *byte_width, *unsigned)),
        _ => None,
    };
    let format = |unsigned: bool| {
        if unsigned {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::Int64
        }
    };
    // A constant offset of whole elements is that element's index, in the
    // format of the scaled index beside it.
    let constant = |offset: &AddressOffset, width: i64, unsigned: bool| {
        let AddressOffset::Constant(bytes) = offset else {
            return None;
        };
        if bytes % width != 0 {
            return None;
        }
        let index = bytes / width;
        let term = if unsigned {
            MachineTerm::uint64_constant(u64::try_from(index).ok()?)
        } else {
            MachineTerm::int64_constant(index)
        };
        Some(SharedMachineIntegerTerm::intern(format(unsigned), term))
    };
    let (left, right, unsigned) = match (scaled(left), scaled(right)) {
        (Some((left, left_width, left_unsigned)), Some((right, right_width, right_unsigned)))
            if left_width == right_width && left_unsigned == right_unsigned =>
        {
            (left, right, left_unsigned)
        }
        (Some((index, width, unsigned)), None) => {
            (index, constant(right, width, unsigned)?, unsigned)
        }
        (None, Some((index, width, unsigned))) => {
            (constant(left, width, unsigned)?, index, unsigned)
        }
        _ => return None,
    };
    Some(StoreElementIndices {
        left,
        right,
        format: format(unsigned),
    })
}

/// Convert a cancelled index pair into element indices of their common
/// width. A constant that is not a whole number of elements has no element
/// index, which is how an address sitting part-way into an element declines
/// the ladder rather than rounding itself onto an element boundary.
fn element_indices_of(
    left_index: &AddressOffset,
    right_index: &AddressOffset,
) -> Option<(SharedMachineIntegerTerm, SharedMachineIntegerTerm, u32)> {
    let element_width = common_pointer_offset_element_width(left_index, right_index)?;
    let left = shared_element_index_from_offset(left_index, element_width)?;
    let right = shared_element_index_from_offset(right_index, element_width)?;
    Some((left, right, element_width))
}

/// Cancel a structurally identical additive base from two same-block offsets
/// and return what remains on each side.
pub(in crate::kernel) fn common_base_index_offsets(
    left: &Address,
    right: &Address,
) -> Option<(AddressOffset, AddressOffset)> {
    if left.base != right.base {
        return None;
    }
    let zero = AddressOffset::Constant(0);
    // Cancel a structurally identical additive base before comparing indices.
    // This also avoids expanding memory-derived bases during alias checks.
    let index_pair = match (&left.offset, &right.offset) {
        (
            AddressOffset::Add(left_base, left_index),
            AddressOffset::Add(right_base, right_index),
        ) if left_base == right_base => Some((left_index.as_ref(), right_index.as_ref())),
        (
            AddressOffset::Add(left_base, left_index),
            AddressOffset::Add(right_base, right_index),
        ) if left_base == right_index => Some((left_index.as_ref(), right_base.as_ref())),
        (
            AddressOffset::Add(left_base, left_index),
            AddressOffset::Add(right_base, right_index),
        ) if left_index == right_base => Some((left_base.as_ref(), right_index.as_ref())),
        (
            AddressOffset::Add(left_base, left_index),
            AddressOffset::Add(right_base, right_index),
        ) if left_index == right_index => Some((left_base.as_ref(), right_base.as_ref())),
        (AddressOffset::Add(base, index), right) if base.as_ref() == right => {
            Some((index.as_ref(), &zero))
        }
        (AddressOffset::Add(index, base), right) if base.as_ref() == right => {
            Some((index.as_ref(), &zero))
        }
        (left, AddressOffset::Add(base, index)) if left == base.as_ref() => {
            Some((&zero, index.as_ref()))
        }
        (left, AddressOffset::Add(index, base)) if left == base.as_ref() => {
            Some((&zero, index.as_ref()))
        }
        // Neither address adds anything to its block: the common base is
        // the block itself, and the whole offsets are the indices. This is
        // `p[i]` against `p[j]` for a pointer that is its own block, such as
        // one loaded from memory.
        (left, right)
            if !matches!(left, AddressOffset::Add(..))
                && !matches!(right, AddressOffset::Add(..)) =>
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
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || left.base == right.base
            && assumptions.decide(&ConditionTerm::address_offset_equal(
                left.offset.clone(),
                right.offset.clone(),
            )) == Some(true)
        || assumptions.decide(&ConditionTerm::address_equal(left.clone(), right.clone()))
            == Some(true)
}

pub(in crate::kernel) fn memories_match_for_pointer_load(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
) -> bool {
    if left == right {
        return true;
    }
    if pointer.base.is_local_block() {
        return false;
    }

    // A cell map is knowledge layered over the state named by its forget
    // mark. Equal maps over different marks are not equal states: each may
    // have forgotten a different value at this very pointer. There is no
    // recorded history between the states handled by this matcher that
    // could recover that distinction later.
    //
    // Every comparison below is of the entries observable by the load, and
    // an entry in a block proven distinct from the load's is not observable,
    // so each side walks its candidate ranges (`AliasCandidates`) alone, in
    // the same order on both sides.
    let candidates = AliasCandidates::of_block(&pointer.base);
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
            |(cell_pointer, _)| cell_pointer.base.observable_by_load(&pointer.base),
        )
}

/// [`observable_entries_match`] over the cells of two memories: their runs
/// compared whole ([`CellStore::observable_runs_match`]) and then their
/// concrete cells, or their logical maps where the runs do not pair up.
///
/// [`CellStore::observable_runs_match`]: crate::kernel::primitives::CellStore::observable_runs_match
fn observable_cells_match(
    candidates: &AliasCandidates,
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
) -> bool {
    let observable = |cell_pointer: &Address| cell_pointer.base.observable_by_load(&pointer.base);
    let runs_match = left.cells.observable_runs_match(&right.cells, |run| {
        candidates.admits_block(&run.base().base) && observable(run.base())
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
    left: &HashedOrdMap<K, V>,
    right: &HashedOrdMap<K, V>,
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
    left: &HashedOrdSet<K>,
    right: &HashedOrdSet<K>,
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

/// Whether the two states agree about every object this load may name.
///
/// Havoc markers are global state identities and therefore remain even
/// though their synthetic concrete block names are distinct from ordinary
/// pointers. Every other block is selected with the same may-alias predicate
/// as cells. A never-address-taken local is the one safe omission: no pointer
/// value in the program can designate it.
fn observable_blocks_match_for_load(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    candidates: &AliasCandidates,
) -> bool {
    // The havoc markers by their name ranges, then the candidate blocks the
    // load may name. A marker that is also a candidate is compared twice,
    // on both sides alike.
    havoc_marker_blocks(&left.blocks).eq(havoc_marker_blocks(&right.blocks))
        && observable_entries_match(candidates, &left.blocks, &right.blocks, |block| {
            !local_block_no_pointer_can_reach(block) && block.observable_by_load(&pointer.base)
        })
}

/// Whether heap facts that can change this load agree in two unrelated
/// states.
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
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    candidates: &AliasCandidates,
) -> bool {
    let observable = |candidate: &Address| candidate.base.observable_by_load(&pointer.base);
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
        |candidate| candidate.base.observable_by_load(&pointer.base),
    ) && observable_entries_match(
        candidates,
        left.heap.initialized.as_map(),
        right.heap.initialized.as_map(),
        observable,
    ) && observable_entries_match(
        candidates,
        left.heap.initialized.partial_map(),
        right.heap.initialized.partial_map(),
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
fn unrelated_forgotten_states_do_not_prove_their_loads_equal() {
    let pointer = Address {
        base: "unrelated-forgotten".into(),
        offset: AddressOffset::Constant(0),
    };
    let shell = SymbolicMemory::new().with_block("unrelated-forgotten", 4);
    let left_source = crate::kernel::intern_memory_ref(&shell.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(1)),
    ));
    let right_source = crate::kernel::intern_memory_ref(&shell.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(2)),
    ));
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

    let load = |memory: &SymbolicMemory| {
        MachineTerm::MemoryLoad(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    assert!(
        !PureFactContext::new().memory_loads_proven_equal(&load(&left), &load(&right)),
        "unconnected states over different forgotten sources are not one load"
    );
}

#[cfg(test)]
#[test]
fn unrelated_states_do_not_erase_object_or_heap_state_visible_to_the_load() {
    let loads_proven_equal = |left: &SymbolicMemory, right: &SymbolicMemory, pointer: &Address| {
        let load = |memory: &SymbolicMemory| {
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        PureFactContext::new().memory_loads_proven_equal(&load(left), &load(right))
    };
    let symbolic = Address {
        base: AddressBase::Symbolic(Variable(7_620_001)),
        offset: AddressOffset::Constant(0),
    };
    let bare = SymbolicMemory::new();
    let with_global = bare
        .clone()
        .with_block_without_derivation("global:unrelated-retained_state", 4);
    assert!(
        !memories_match_for_pointer_load(&bare, &with_global, &symbolic),
        "a symbolic load can designate the object present on only one side"
    );
    assert!(
        !loads_proven_equal(&bare, &with_global, &symbolic),
        "object disagreement in unrelated states cannot prove load equality"
    );

    let heap_pointer = Address {
        base: AddressBase::Heap(7_620_002),
        offset: AddressOffset::Constant(0),
    };
    let heap_shell =
        SymbolicMemory::new().with_block_without_derivation(heap_pointer.base.clone(), 4);
    let mut uninitialized = heap_shell.clone();
    std::sync::Arc::make_mut(&mut uninitialized.heap)
        .live_allocations
        .insert(heap_pointer.clone(), AllocationSize::int32(4));
    std::sync::Arc::make_mut(&mut uninitialized.heap)
        .uninitialized_allocations
        .insert(heap_pointer.clone());
    let mut zeroed = heap_shell;
    std::sync::Arc::make_mut(&mut zeroed.heap)
        .live_allocations
        .insert(heap_pointer.clone(), AllocationSize::int32(4));
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

    let concrete = Address {
        base: "unrelated-concrete".into(),
        offset: AddressOffset::Constant(0),
    };
    let concrete_memory = SymbolicMemory::new().with_block("unrelated-concrete", 4);
    let mut with_unrelated_heap = concrete_memory.clone();
    std::sync::Arc::make_mut(&mut with_unrelated_heap.blocks)
        .insert(AddressBase::Heap(7_620_003), MemoryBlock::new(4));
    std::sync::Arc::make_mut(&mut with_unrelated_heap.heap)
        .live_allocations
        .insert(
            Address {
                base: AddressBase::Heap(7_620_003),
                offset: AddressOffset::Constant(0),
            },
            AllocationSize::int32(4),
        );
    assert!(
        memories_match_for_pointer_load(&concrete_memory, &with_unrelated_heap, &concrete),
        "a fresh allocation cannot affect a load through another concrete block"
    );
    assert!(
        !loads_proven_equal(&concrete_memory, &with_unrelated_heap, &concrete),
        "unrelated states need explicit preservation evidence"
    );
    let (_, _, equality) = crate::kernel::tests::explicit_frame(
        &concrete_memory,
        &with_unrelated_heap,
        &concrete,
        ProgramType::Int32,
        &[],
        &PureFactContext::new(),
    )
    .expect("the allocation footprint is separate from this concrete block");
    assert!(
        PureFactContext::new()
            .assume_proposition(equality.clone())
            .contains_known(&equality)
    );

    let pending_base = Address {
        base: AddressBase::Symbolic(Variable(7_620_004)),
        offset: AddressOffset::Constant(0),
    };
    let with_pending = concrete_memory.clone().with_pending_heap_allocation(
        pending_base,
        AllocationSize::int32(4),
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
/// are global state identities, so they remain observable at every
/// non-local pointer until an explicit effect fact frames that pointer.
pub(in crate::kernel) fn canonical_memory_for_pointer_load(
    memory: &SymbolicMemory,
    pointer: &Address,
) -> SymbolicMemory {
    // Canonicalization is assumption-free and deterministic, so memoize by
    // interned state identity; the intern also dedups the key storage.
    let key = (super::intern_memory_ref(memory), pointer.clone());
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
    if source_holds_cells_observable_by(run.source(), &run.base().base) {
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
    if !source_holds_cells_observable_by(run.source(), &run.base().base) {
        return false;
    }
    let source = run.source().memory();
    let candidates = AliasCandidates::of_block(&run.base().base);
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
        if !pointer.base.observable_by_load(&run.base().base) {
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
        pointer.base.observable_by_load(&run.base().base)
    }) {
        return true;
    }
    for held in source.cells.candidate_runs(&candidates) {
        crate::instrumentation::record_deterministic_work(1);
        if !held.base().base.observable_by_load(&run.base().base) {
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
/// load in `block` could observe. A function of the state and the block
/// alone, asked of a run's source by every walk that visits the run, so it
/// is memoized by interned state identity; a miss visits the source's
/// candidate entries up to the first observable one.
fn source_holds_cells_observable_by(
    source: &crate::kernel::primitives::SharedMemory,
    block: &crate::kernel::primitives::AddressBase,
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
        crate::kernel::primitives::AddressBase::Symbolic(_)
            | crate::kernel::primitives::AddressBase::LoadedPointer(_)
    ) {
        let mut visited = 0usize;
        let found = memory
            .cells
            .caught_up_pointer_reachable()
            .iter()
            .inspect(|_| visited += 1)
            .any(|(cell, _)| cell.base.observable_by_load(block));
        crate::instrumentation::record_deterministic_work(visited);
        found
    } else {
        candidates.any_entry(memory.cells.concrete(), |cell, _| {
            cell.base.observable_by_load(block)
        })
    };
    let observable = observable_cell
        || candidates.any_entry(&memory.union_cells, |(cell, _), _| {
            cell.base.observable_by_load(block)
        })
        || memory
            .cells
            .candidate_runs(&candidates)
            .any(|other| other.base().base.observable_by_load(block));
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
fn run_materialization_sources(
    run: &crate::kernel::primitives::CellRun,
) -> Vec<Option<SymbolicMemory>> {
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

fn canonical_memory_for_pointer_load_uncached(
    memory: &SymbolicMemory,
    pointer: &Address,
) -> SymbolicMemory {
    // A state met again while its own canonical form is being computed
    // is a cycle through the materialized cells and stands for itself.
    let Some(_query) = ResolutionQueryGuard::enter(ResolutionQuery::CanonicalMemory(
        super::intern_memory_ref(memory),
        pointer.clone(),
    )) else {
        return memory.clone();
    };
    // A cell in a block proven distinct from the load's is not observable
    // by it, so every scan below visits the candidates alone.
    let candidates = AliasCandidates::of_block(&pointer.base);
    let unresolved = matches!(
        pointer.base,
        AddressBase::Symbolic(_)
            | AddressBase::LoadedPointer(_)
            | AddressBase::ExternalArgument
            | AddressBase::ExternalObject(_)
    );
    // A load through an unresolved pointer observes only pointer-reachable
    // cells; reading them from the store's maintained reachable map skips
    // the slots no pointer value can reach without visiting each one.
    let reachable = unresolved.then(|| {
        if matches!(
            pointer.base,
            AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
        ) {
            memory.cells.caught_up_external_reachable()
        } else {
            memory.cells.caught_up_pointer_reachable()
        }
    });
    let mut visited = 0usize;
    // Lazily: the collection below stops at the first cell that is not a
    // cached load, so an ordinary store costs one visit, not every cell.
    let observable: Box<dyn Iterator<Item = (&Address, &ProgramValue)>> = match &reachable {
        Some(reachable) => Box::new(reachable.iter().map(|(p, v)| (p, v.native()))),
        None => Box::new(
            candidates
                .entries(memory.cells.concrete())
                .map(|(p, v)| (p, v.native())),
        ),
    };
    let materialization_sources = observable
        .inspect(|_| visited += 1)
        .filter(|(cell_pointer, _)| cell_pointer.base.observable_by_load(&pointer.base))
        .map(|(cell_pointer, value)| {
            let source = materialized_cell_source(cell_pointer, value)?;
            Some(canonical_memory_for_pointer_load(&source, cell_pointer))
        })
        .chain(
            memory
                .cells
                .candidate_runs(&candidates)
                .filter(|run| run.base().base.observable_by_load(&pointer.base))
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
        .get(&pointer.base)
        .map(|size| (pointer.base.clone(), size.clone()))
        .into_iter()
        .chain(
            havoc_marker_blocks(&canonical.blocks)
                .map(|(block, size)| (block.clone(), size.clone())),
        )
        .collect::<super::super::primitives::MemoryBlocks>();
    //
    // A jump keeps only the source cells this memory still holds: the
    // surviving cells are materializations of the source, but a source cell
    // this memory lacks was erased since (a havoc wrote it), and carrying it
    // over would make the state the load names record a value the cell no
    // longer holds (pinned by
    // `a_load_projection_jump_does_not_restore_a_havocked_cell`).
    let mut cells = (*canonical.cells).clone();
    let keep = |cell_pointer: &Address, value: &ProgramValue| {
        cell_pointer.base.observable_by_load(&pointer.base)
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
            cell_pointer.base.observable_by_load(&pointer.base)
                && !cell_disjoint_from_load_by_constant_offset(
                    cell_pointer,
                    value.native(),
                    pointer,
                )
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect::<HashedOrdMap<_, _>>();
    crate::instrumentation::record_deterministic_work(visited);
    canonical.blocks = std::sync::Arc::new(blocks);
    canonical.cells = std::sync::Arc::new(cells);
    canonical.union_cells = std::sync::Arc::new(union_cells);
    canonical.record_diagnostic_transform(
        "project memory for pointer read",
        vec![memory.clone()],
        vec![ProgramValue::pointer(pointer.clone())],
    );
    canonical
}

/// The loop- and call-havoc marker blocks of a block map, found as the two
/// key ranges their name prefixes occupy (concrete block names order as
/// strings, so the names sharing a prefix are contiguous).
pub(in crate::kernel) fn havoc_marker_blocks(
    blocks: &HashedOrdMap<AddressBase, MemoryBlock>,
) -> impl Iterator<Item = (&AddressBase, &MemoryBlock)> {
    ["call-havoc:", "havoc:"]
        .into_iter()
        .flat_map(move |prefix| {
            blocks
                .range::<_, AddressBase>(AddressBase::Concrete(prefix.to_string())..)
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
    offset: &AddressOffset,
) -> (Vec<AddressOffset>, i64) {
    fn collect(offset: &AddressOffset, atoms: &mut Vec<AddressOffset>, shift: &mut i64) {
        match offset {
            AddressOffset::Constant(value) => *shift += *value,
            AddressOffset::Add(left, right) => {
                collect(left, atoms, shift);
                collect(right, atoms, shift);
            }
            AddressOffset::Int32Scaled { value, byte_width } => {
                match value
                    .operand_view()
                    .word32_constant()
                    .map(|value| i64::from(value as i32))
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
        index: crate::kernel::SharedMachineIntegerTerm,
        scale: i64,
        shift: i64,
    },
    /// The same with an unsigned 64-bit index, which is not read as a
    /// signed word.
    ScaledWide {
        index: crate::kernel::SharedMachineIntegerTerm,
        scale: i64,
        shift: i64,
    },
    /// Anything else: another base, a block that may be the run's, or a
    /// shape with more than one extra atom.
    Other,
}

/// [`RunAccess`] for `pointer`, read structurally.
pub(in crate::kernel) fn run_access(run: &CellRun, pointer: &Address) -> RunAccess {
    if run.base().blocks_proven_distinct(pointer) {
        return RunAccess::DistinctBlock;
    }
    if run.base().base != pointer.base {
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
        [AddressOffset::Int32Scaled { value, byte_width }] if *byte_width > 0 => {
            RunAccess::Scaled {
                index: value.clone(),
                scale: *byte_width,
                shift: shift - base_shift,
            }
        }
        [
            AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned: true,
            },
        ] if *byte_width > 0 => RunAccess::ScaledWide {
            index: value.clone(),
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
    pointer: &Address,
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
    pointer: &Address,
    normalized: &std::cell::OnceCell<Address>,
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
/// renames the load at a state that does not record it, so the answer
/// has two obligations, not one: it may drop a slot only when the slot's
/// bytes provably miss the load's, which the constant byte arithmetic of a
/// `Shift` decides for every slot at once, and it may keep any slot, which is
/// what it does for a symbolic index (the ladder may still drop an element a
/// fact bounds away; keeping it names the load at a state that records
/// one more cell, which the load does not read).
fn run_slots_kept_by_load_reduction_set(
    run: &CellRun,
    normalized: &Address,
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
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
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
    // Cache retention is optional. Check only the selected endpoints; the
    // general membership evidence builder searches aliases after a miss.
    let contains_access = |pointer: &Address, bytes: u32, range: &MemoryRange| {
        let width = range.element_width();
        if bytes == 0 || width == 0 {
            return false;
        }
        let last = ((bytes - 1) / width) * width;
        crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
            pointer,
            range,
            assumptions,
        ) && (last == 0
            || crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
                &pointer.offset_by_bytes(last),
                range,
                assumptions,
            ))
    };
    let fits = |range, access| {
        contains_access(&run_pointer, run_bytes, range) && contains_access(pointer, bytes, access)
    };
    if fits(left, right) || fits(right, left) {
        crate::kernel::record_implicit_consulted_premises(assumptions, fact);
        true
    } else {
        false
    }
}

/// Which of `run`'s live slots a store of `bytes` bytes at `pointer` leaves
/// in place, and whether dropping the others forgot anything the store does
/// not itself replace ([`SymbolicMemory::without_possible_aliasing_cells`]).
///
/// At a constant shift from the run's base the store's bytes decide it: a
/// slot they meet is dropped, and forgotten unless the store covers all of
/// it, and every other slot keeps its value, being a different address whose
/// bytes the gap clears. A store the facts place outside the run's whole
/// span leaves every slot. A bounded symbolic store forgets its possible
/// window at once; an unplaced store forgets the whole run, regardless of its
/// value mode. One stated separation at the exact anchors may keep the whole
/// run. No range-fact search or per-slot query participates. Explicit
/// transport can recover required source loads from the recorded history.
/// Keeping a slot needs a proof its bytes are missed; dropping one only forgets.
pub(in crate::kernel) fn run_slots_kept_by_store(
    run: &CellRun,
    pointer: &Address,
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
            let width = i128::from(run.element_width()).max(1);
            let value_width = i128::from(run.value_width());
            let shift = i128::from(shift);
            let clamp = |index: i128| index.clamp(i128::from(low), i128::from(high)) as u32;
            // Fully covered slots form an interval. Only its two outside
            // intervals can lose untouched bytes; query their hole coverage
            // directly. This also handles runs whose values overlap because
            // their access width exceeds the slot stride.
            let covered_low = clamp((shift + width - 1).div_euclid(width));
            let covered_high =
                clamp((shift + i128::from(bytes) - value_width).div_euclid(width) + 1);
            crate::instrumentation::record_deterministic_work(2);
            let forgot = !run.holes().covers_range(low, covered_low)
                || !run.holes().covers_range(covered_high, high);
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
                && let Some((low, high)) = assumptions.signed_interval_view(index.operand_view())
                && let (Some(first), Some(span_bytes)) = (
                    low.checked_mul(scale)
                        .and_then(|bytes| bytes.checked_add(shift)),
                    high.checked_sub(low)
                        .and_then(|span| span.checked_mul(scale))
                        .and_then(|span| span.checked_add(i64::from(bytes))),
                )
            {
                let (low, high) = run_elements_meeting(run, first, span_bytes);
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
    pointer: &Address,
    normalized: &std::cell::OnceCell<Address>,
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
                if normalized.base == run.base().base {
                    return None;
                }
                crate::instrumentation::record_deterministic_work(1);
                let aligned = assumptions
                    .equality_graph
                    .pointer_in_block(normalized, &run.base().base)?;
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
    pointer: &Address,
) -> (SlotSet, RuleAnswer) {
    (
        run_slots_kept_by_load_projection_set(run, pointer),
        RuleAnswer::Exact,
    )
}

fn run_slots_kept_by_load_projection_set(run: &CellRun, pointer: &Address) -> SlotSet {
    if !run.base().base.observable_by_load(&pointer.base) {
        return SlotSet::Nothing;
    }
    if run.base().base != pointer.base {
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
/// [`ProgramValue::byte_width`] rather than from a second width table here: an
/// `int64`, a `uint64`, a `double` and an LP64 pointer are eight bytes, and a
/// cell whose width this function guessed too small would be dropped while
/// the load still reads part of it.
///
/// The load is named here by its address alone, so it contributes
/// [`MAX_SCALAR_ACCESS_BYTES`]. That is the only sound reading of an unknown
/// width here: dropping a cell makes two states compare equal at this
/// load, so every byte the load might read has to be considered. An
/// eight-byte load at the loaded pointer covers the four bytes above it, and
/// a fixed four here reported a cell exactly four bytes above the load as
/// disjoint from it.
fn cell_disjoint_from_load_by_constant_offset(
    cell_pointer: &Address,
    value: &ProgramValue,
    load_pointer: &Address,
) -> bool {
    // Offsets are only comparable inside one block. Two blocks that may be
    // the same object still carry unrelated bases — a parameter may point at
    // `g[1]` — so a constant byte shift proves nothing between them.
    if cell_pointer.base != load_pointer.base {
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
    left: &Address,
    left_bytes: u32,
    right: &Address,
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
    left: &Address,
    left_bytes: u32,
    right: &Address,
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
pub(in crate::kernel) fn constant_byte_shift(pointer: &Address, base: &Address) -> Option<i64> {
    exact_constant_byte_shift(pointer, base).or_else(|| constant_byte_shift_between(pointer, base))
}

/// The element-width half of [`access_byte_overlap`]: whether the gap an
/// address ladder can establish between two same-block offsets is wide enough
/// to clear both accesses. See that function's note for which access has to
/// fit and why the direction matters.
fn one_element_gap_separates_bytes(
    left: &Address,
    left_bytes: u32,
    right: &Address,
    right_bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    if left.base != right.base {
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
    let strictly_below = |low: &SharedMachineIntegerTerm, high: &SharedMachineIntegerTerm| {
        let condition = crate::kernel::assumptions::index_comparison(
            CompareRelation::LessThan,
            low.operand_view(),
            high.operand_view(),
        );
        // This preliminary byte-gap check runs inside memory-history walks.
        // Even a recorded-order graph walk grows with ambient facts. Read
        // one stated order only; a proof can establish that order explicitly
        // before requesting preservation across a store.
        assumptions.selected_comparison_value(&condition) == Some(true)
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
/// An `AddressOffset` is an exact `i64` sum, and a scaled summand is its
/// index sign- or zero-extended times its width, so each symbolic summand
/// contributes a multiple of its width whatever the index is. An opaque
/// offset variable that does not cancel has no stride, and so has the pair.
/// A difference that is a constant is left to exact geometry (`None`), as is
/// a difference with no summand at all, which is the equal pair.
fn offset_difference_stride(left: &AddressOffset, right: &AddressOffset) -> Option<i64> {
    fn summands<'a>(offset: &'a AddressOffset, into: &mut Vec<&'a AddressOffset>) {
        match offset {
            AddressOffset::Add(left, right) => {
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
            AddressOffset::Constant(value) => {
                constant = constant.checked_add(sign.checked_mul(*value)?)?;
            }
            AddressOffset::Variable(_) => return None,
            AddressOffset::Int32Scaled { value, byte_width } => {
                match value
                    .operand_view()
                    .word32_constant()
                    .map(|value| i64::from(value as i32))
                {
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
            AddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let index = if *unsigned {
                    value
                        .operand_view()
                        .uint64_constant()
                        .and_then(|index| i64::try_from(index).ok())
                } else {
                    value.operand_view().int64_constant()
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
            AddressOffset::Add(..) => unreachable!("summands are not sums"),
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
fn exact_constant_byte_shift(pointer: &Address, base: &Address) -> Option<i64> {
    fn summands(offset: &AddressOffset, atoms: &mut Vec<AddressOffset>, shift: &mut Option<i64>) {
        match offset {
            AddressOffset::Add(left, right) => {
                summands(left, atoms, shift);
                summands(right, atoms, shift);
            }
            AddressOffset::Constant(value) => {
                *shift = shift.and_then(|shift| shift.checked_add(*value));
            }
            AddressOffset::Int32Scaled { value, byte_width } => {
                match value
                    .operand_view()
                    .word32_constant()
                    .map(|value| i64::from(value as i32))
                {
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
    if pointer.base != base.base {
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
fn constant_byte_shift_between(pointer: &Address, base: &Address) -> Option<i64> {
    shared_pointer_byte_offset_from_base(pointer, base)
        .and_then(|index| crate::kernel::assumptions::signed_index_constant(index.operand_view()))
}

/// The bytes a store covers, as non-constant offset atoms plus a constant
/// byte interval, for the cells of the same block to be compared against.
/// `None` where the write has no constant span to compare.
pub(in crate::kernel) struct StoreByteInterval {
    atoms: Vec<AddressOffset>,
    shift: i64,
    bytes: i64,
}

impl StoreByteInterval {
    pub(in crate::kernel) fn of(write_pointer: &Address, write_bytes: u32) -> Option<Self> {
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
    pub(in crate::kernel) fn overwrites_typed(
        &self,
        cell_pointer: &Address,
        cell_type: ProgramType,
    ) -> bool {
        self.overwrites_bytes(cell_pointer, i64::from(cell_type.byte_width()))
    }

    /// Whether this store writes *every* byte the cell occupies.
    ///
    /// This is the difference between a cell that is stale and a cell that is
    /// forgotten. A store that covers the cell completely replaces exactly
    /// what dropping the cell lost, so the state it produces still says
    /// everything about the state it describes. A store that covers only some
    /// of the cell's bytes leaves the rest at values nothing records any more:
    /// the byte written into the middle of an `int64` is in the result, and
    /// the other seven bytes are knowledge the result no longer has. Calling
    /// that partial case stale let the produced state claim to be the state
    /// before the store.
    pub(in crate::kernel) fn overwrites_typed_completely(
        &self,
        cell_pointer: &Address,
        cell_type: ProgramType,
    ) -> bool {
        self.covers_bytes(cell_pointer, i64::from(cell_type.byte_width()))
    }

    fn covers_bytes(&self, cell_pointer: &Address, cell_width: i64) -> bool {
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

    fn overwrites_bytes(&self, cell_pointer: &Address, cell_width: i64) -> bool {
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

/// The source state a materialization cell stands for: a cell at `p`
/// whose value is `load(source, p)`, or — with terms canonical at creation —
/// the load variable registered for a load of `p`, whose source the registry
/// records. Materialization changes which cells are concrete, not what the
/// load means.
fn materialized_cell_source(cell_pointer: &Address, value: &ProgramValue) -> Option<SharedMemory> {
    let bits = match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Int8(bits)
        | ProgramValue::Bool(bits)
        | ProgramValue::Int16(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::Int64(bits)
        | ProgramValue::UInt64(bits)
        | ProgramValue::Int128(bits)
        | ProgramValue::UInt128(bits)
        | ProgramValue::Float32(bits)
        | ProgramValue::Float64(bits) => bits,
        // A pointer cell is a materialization when it holds the pointer a
        // typed load of this same cell produces (`symbolic_pointer_load`):
        // that read's own name, which records the complete value and
        // provenance of reading the cell's bytes in its defining memory. A
        // pointer given a symbolic identity, or one loaded from another cell,
        // is a write and never qualifies.
        ProgramValue::Pointer(value) => {
            let read = value.address().as_loaded_value()?;
            return (read.displacement == AddressOffset::Constant(0)
                && read.defining_address == *cell_pointer)
                .then_some(read.defining_memory);
        }
        ProgramValue::Parameter(_) => return None,
        ProgramValue::Void | ProgramValue::UInt32(_) => return None,
    };
    let load = match bits {
        MachineTerm::MemoryLoad(_, _, _) => bits.clone(),
        MachineTerm::Variable(variable) if crate::kernel::eval::is_load_variable(variable) => {
            crate::kernel::eval::registered_load_term_for_variable(variable)?
        }
        _ => return None,
    };
    let MachineTerm::MemoryLoad(source, source_pointer, kind) = load else {
        return None;
    };
    // The cell is the load only when it holds the load of its own kind: a
    // narrower or differently signed read stored in it is another value
    // than a read of the cell returns.
    (source_pointer.as_ref() == cell_pointer && kind.reads_value(value))
        .then_some(source.into_shared_memory())
}

/// The bounded-alias-only form of
/// [`memories_match_for_pointer_load_under_assumptions`]: every differing
/// cell must be provably distinct from the load through the memoized
/// resolution check alone. Used as a pre-pass before the derivation-DAG
/// walk, where paying the general composition-backed alias search per cell
/// would dominate a simple step's budget; a miss here is not a negative
/// answer, because the full comparison still runs later in the same query.
pub(in crate::kernel) fn memories_match_for_pointer_load_bounded_alias(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if pointer.base.is_local_block() {
        return false;
    }
    if !state_objects_agree(left, right, pointer) {
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
                            || crate::kernel::api::memories_canonically_equal(&source, left)
                            || crate::kernel::api::memories_canonically_equal(&source, right)
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
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if pointer.base.is_local_block() {
        return false;
    }
    if !state_objects_agree(left, right, pointer) {
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
                "state comparison: bounded alias",
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
    expected: &SymbolicMemory,
    actual: &SymbolicMemory,
    pointer: &Address,
) -> bool {
    expected == actual || memories_match_for_pointer_load(expected, actual, pointer)
}

pub(in crate::kernel) fn collect_memory_effect_write_accesses(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> BTreeSet<(Address, u32)> {
    // Concrete stores certify exact pointer-width pairs. Abstract calls and
    // loops certify ranges separately through MemoryEffectSummary; comparing
    // endpoint memories would mistake join abstraction and call havoc for
    // writes.
    let mut writes = BTreeSet::new();
    for fact in facts.fact_iter() {
        if let Proposition::MemoryMutatesOnly {
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
) -> BTreeSet<Address> {
    collect_memory_effect_write_accesses(facts)
        .into_iter()
        .map(|(pointer, _)| pointer)
        .collect()
}

#[cfg(test)]
#[test]
fn offset_resolution_does_not_promote_wrapped_index_equality() {
    let i = MachineTerm::Variable(Variable(90_001));
    let j = MachineTerm::Variable(Variable(90_002));
    let k = MachineTerm::Variable(Variable(90_003));
    let scaled = |index: MachineTerm| AddressOffset::scale_int32(index, 4);
    let sum = AddressOffset::Add(Box::new(scaled(i.clone())), Box::new(scaled(j.clone())));
    let other = scaled(k.clone());
    let index_sum = MachineTerm::add(i.clone(), j.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(index_sum.clone(), k.clone()), true)
        .assume_condition(
            ConditionTerm::equal(i.clone(), MachineTerm::constant(i32::MAX as u32)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(j.clone(), MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), MachineTerm::constant(i32::MIN as u32)),
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
        assumptions.decide(&ConditionTerm::address_offset_equal(sum, other)),
        Some(true)
    );
}

#[cfg(test)]
#[test]
fn offset_resolution_accepts_exact_index_equalities_at_each_width() {
    let i = MachineTerm::Variable(Variable(90_011));
    let j = MachineTerm::Variable(Variable(90_012));
    let k = MachineTerm::Variable(Variable(90_013));
    let index_sum = MachineTerm::add(i.clone(), j.clone());
    let fact = ConditionTerm::equal(index_sum, k.clone());
    let symbolic = PureFactContext::new().assume_condition(fact.clone(), true);
    let exact = symbolic
        .clone()
        .assume_condition(
            ConditionTerm::equal(i.clone(), MachineTerm::constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(j.clone(), MachineTerm::constant(3)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), MachineTerm::constant(5)),
            true,
        );
    for width in [1, 4, 8] {
        let scaled = |index: MachineTerm| AddressOffset::scale_int32(index, width);
        let sum = AddressOffset::Add(Box::new(scaled(i.clone())), Box::new(scaled(j.clone())));
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
    let wide = MachineTerm::Variable(Variable(81001));
    let narrow = MachineTerm::Variable(Variable(81002));
    let observed_wide =
        IntegerTerm::from_machine(MachineIntegerType::UInt64, wide.clone()).unwrap();
    let observed_narrow =
        IntegerTerm::from_machine(MachineIntegerType::Int32, narrow.clone()).unwrap();
    let fact =
        ConditionTerm::IntegerEqual(observed_wide.clone().into(), observed_narrow.clone().into());
    let native = |width| AddressOffset::scale_int64(wide.clone(), width, true);
    let signed = |width| AddressOffset::scale_int32(narrow.clone(), width);
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
            let common = AddressOffset::scale_int32(MachineTerm::Variable(Variable(81003)), 4);
            assert_eq!(
                pointer_offsets_equal_for_memory_resolution(
                    &AddressOffset::add(common.clone(), left),
                    &AddressOffset::add(common, right),
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
    let denied = empty.clone().assume_condition(fact, false);
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(1), &denied),
        None
    );
    let truncated = empty.assume_condition(
        ConditionTerm::equal(MachineTerm::uint32_from_64(wide.clone()), narrow.clone()),
        true,
    );
    assert_ne!(
        pointer_offsets_equal_for_memory_resolution(&native(1), &signed(1), &truncated),
        Some(true)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &AddressOffset::Constant(4294967296),
            &AddressOffset::Constant(0),
            &truncated
        ),
        Some(false)
    );
    assert_eq!(
        pointer_offsets_equal_for_memory_resolution(
            &AddressOffset::Constant(4294967295),
            &AddressOffset::Constant(-1),
            &truncated
        ),
        Some(false)
    );
}

#[test]
fn external_load_projection_retains_aliases_across_cell_updates() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointers = [
        AddressBase::Symbolic(Variable(998_900)),
        AddressBase::ExternalArgument,
        AddressBase::ExternalObject(Variable(998_901)),
        AddressBase::Concrete("global:projection".into()),
        AddressBase::Concrete("local:projection".into()),
        AddressBase::Heap(998_902),
        AddressBase::Temporary(998_903),
    ]
    .map(|block| Address {
        base: block,
        offset: AddressOffset::Constant(0),
    });
    let mut memory = SymbolicMemory::new();
    for pointer in &pointers {
        memory = memory.store(pointer.clone(), ProgramValue::Int32(7u32.into()));
    }
    for load in [&pointers[1], &pointers[2]] {
        let projected = canonical_memory_for_pointer_load(&memory, load);
        for pointer in &pointers {
            assert_eq!(
                projected.has_known_cell_at(pointer),
                pointer.base.observable_by_load(&load.base),
                "{pointer:?} through {load:?}"
            );
        }
    }
    let updated = memory
        .clone()
        .store(pointers[0].clone(), ProgramValue::Int32(9u32.into()));
    let projected = canonical_memory_for_pointer_load(&updated, &pointers[1]);
    assert_eq!(
        projected.known_value(&pointers[0]),
        Some(ProgramValue::Int32(9u32.into()))
    );
    let removed = updated.without_cell(&pointers[0]);
    let projected = canonical_memory_for_pointer_load(&removed, &pointers[1]);
    assert!(!projected.has_known_cell_at(&pointers[0]));
    let original = canonical_memory_for_pointer_load(&memory, &pointers[1]);
    assert_eq!(
        original.known_value(&pointers[0]),
        Some(ProgramValue::Int32(7u32.into()))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/reasoning/memory_resolution.rs");
}

#[cfg(test)]
mod retained_endpoint_tests {
    use super::*;
    use crate::kernel::{
        KernelTermExport, KernelTermImport, MachineIntegerType as T, MachineOperandView as V,
    };

    #[test]
    fn retained_endpoint_equality_preserves_memory_and_arithmetic_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(993811));
        let y = MachineTerm::Variable(Variable(993812));
        let zero = MachineTerm::constant(0);
        let one = MachineTerm::constant(1);
        let p = Address::symbolic(Variable(993813));
        let before = crate::kernel::intern_memory(SymbolicMemory::new());
        let load = MachineTerm::MemoryLoad(ProgramPoint::at(&before), Box::new(p), LoadKind::Int32);
        let terms = [
            x.clone(),
            y.clone(),
            zero.clone(),
            one.clone(),
            MachineTerm::add(x.clone(), one.clone()),
            MachineTerm::add(y.clone(), one),
            MachineTerm::add(x.clone(), y.clone()),
            load,
        ];
        let contexts = [
            PureFactContext::new(),
            PureFactContext::new().assume_condition(ConditionTerm::equal(x, y.clone()), true),
            PureFactContext::new().assume_condition(ConditionTerm::equal(y, zero), true),
        ];
        for context in contexts {
            let _scope = context.enter_id_scope();
            for (li, left) in terms.iter().enumerate() {
                for (ri, right) in terms.iter().enumerate() {
                    let expected =
                        int32_values_proven_equal_for_memory_resolution(left, right, &context);
                    let shared = KernelTermImport::default()
                        .machine_arithmetic(T::Int32, left)
                        .unwrap();
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        int32_operand_values_equal_for_memory_resolution(
                            V::Shared(&shared),
                            V::Legacy(right),
                            &context
                        ),
                        expected,
                        "operands={li},{ri}"
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
}

#[cfg(test)]
mod retained_run_access_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView,
        VerificationSession,
    };

    #[test]
    fn retained_index_constant_walkers_preserve_signed_word_values() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let base = Address {
            base: "retained_index_constants".into(),
            offset: AddressOffset::Constant(0),
        };
        for bits in [0, 1, 0x8000_0000, u32::MAX] {
            let literal =
                KernelTerm::retained_native_machine_operand(ty, &MachineTerm::constant(bits));
            let zero = KernelTerm::retained_native_machine_operand(ty, &MachineTerm::constant(0));
            let root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Subtract, [literal, zero]);
            let pointer = Address {
                base: base.base.clone(),
                offset: AddressOffset::Int32Scaled {
                    value: MachineOperandView::Shared(&root).retain(ty),
                    byte_width: 4,
                },
            };
            let expected = i64::from(bits as i32) * 4;
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                offset_atoms_and_constant(&pointer.offset),
                (Vec::new(), expected)
            );
            assert_eq!(exact_constant_byte_shift(&pointer, &base), Some(expected));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn retained_run_lookup_preserves_pinned_slots_and_holes() {
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let _session = VerificationSession::enter();
            let atom =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018602));
            let root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [atom.clone(), atom]);
            let index = MachineOperandView::Shared(&root).retain(ty);
            let base = Address {
                base: "retained_run_lookup".into(),
                offset: AddressOffset::Constant(0),
            };
            let run = CellRun::new_with_mode(
                base.clone(),
                4,
                ProgramType::Int32,
                8,
                crate::kernel::intern_memory(SymbolicMemory::new()),
                crate::kernel::primitives::RunValueMode::Constant(ProgramValue::Int32(7u32.into())),
                Default::default(),
            );
            let pointer = Address {
                base: base.base.clone(),
                offset: if ty == MachineIntegerType::Int32 {
                    AddressOffset::Int32Scaled {
                        value: index.clone(),
                        byte_width: 4,
                    }
                } else {
                    AddressOffset::Int64Scaled {
                        value: index.clone(),
                        byte_width: 4,
                        unsigned: true,
                    }
                },
            };
            let literal = if ty == MachineIntegerType::Int32 {
                MachineTerm::constant(2)
            } else {
                MachineTerm::uint64_constant(2)
            };
            let equality = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                ty,
                CompareRelation::Equal,
                [index.operand_view(), MachineOperandView::Legacy(&literal)],
            );
            let empty = PureFactContext::new();
            let pinned = empty.clone().assume_condition(equality, true);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                run_value_at_equal_displaced_pointer(&run, &pointer, &base.offset, &empty),
                None
            );
            assert_eq!(
                run_value_at_equal_displaced_pointer(&run, &pointer, &base.offset, &pinned),
                Some(ProgramValue::Int32(7u32.into()))
            );
            let mut holes = run.holes().clone();
            holes.insert(2);
            assert_eq!(
                run_value_at_equal_displaced_pointer(
                    &run.with_holes(holes),
                    &pointer,
                    &base.offset,
                    &pinned
                ),
                None
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[cfg(test)]
mod retained_wide_offset_tests {
    use super::*;
    use crate::kernel::assumptions::{wide_index_binary, wide_index_comparison};
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, VerificationSession,
    };

    #[test]
    fn wide_offset_equality_retains_indices_and_requires_no_wrap() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let root = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018701));
        let index = MachineOperandView::Shared(&root).retain(ty);
        let advanced = wide_index_binary(
            MachineBinaryOp::Add,
            index.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(1)),
        );
        let scaled = |value| AddressOffset::Int64Scaled {
            value,
            byte_width: 8,
            unsigned: true,
        };
        let stepped = AddressOffset::Add(
            Box::new(scaled(index.clone())),
            Box::new(AddressOffset::Constant(8)),
        );
        let whole = scaled(advanced);
        let empty = PureFactContext::new();
        let bounded = empty.clone().assume_condition(
            wide_index_comparison(
                CompareRelation::LessEqual,
                index.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(u64::MAX - 1)),
            ),
            true,
        );
        let exports = KernelTermExport::machine_export_count();
        for (left, right) in [(&stepped, &whole), (&whole, &stepped)] {
            assert_eq!(
                pointer_offsets_equal_for_memory_resolution(left, right, &bounded),
                Some(true)
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_ne!(
            pointer_offsets_equal_for_memory_resolution(&stepped, &whole, &empty),
            Some(true)
        );
        let wraps = empty.assume_condition(
            wide_index_comparison(
                CompareRelation::Equal,
                index.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(u64::MAX)),
            ),
            true,
        );
        assert_ne!(
            pointer_offsets_equal_for_memory_resolution(&stepped, &whole, &wraps),
            Some(true)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn wide_offset_pinning_keeps_the_high_word_without_export() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let root = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018702));
        let index = MachineOperandView::Shared(&root).retain(ty);
        let scaled = AddressOffset::Int64Scaled {
            value: index.clone(),
            byte_width: 8,
            unsigned: true,
        };
        let big = (1u64 << 40) + 2;
        let facts = PureFactContext::new().assume_condition(
            wide_index_comparison(
                CompareRelation::Equal,
                index.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(big)),
            ),
            true,
        );
        let exports = KernelTermExport::machine_export_count();
        for (offset, expected) in [
            (big as i64 * 8, true),
            (16, false),
            (-8, false),
            (17, false),
        ] {
            for (left, right) in [
                (&scaled, &AddressOffset::Constant(offset)),
                (&AddressOffset::Constant(offset), &scaled),
            ] {
                assert_eq!(
                    pointer_offsets_equal_for_memory_resolution(left, right, &facts),
                    Some(expected)
                );
            }
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[cfg(test)]
#[path = "memory_resolution/retained_index_checks.rs"]
mod retained_index_checks;
