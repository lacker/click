use super::primitives::*;
use super::reasoning::*;
use std::collections::BTreeSet;

pub(crate) fn canonical_c_memory_for_pointer_load(memory: &CMemory, pointer: &Pointer) -> CMemory {
    canonical_memory_for_pointer_load(memory, pointer)
}

/// Checks whether two resource spellings denote the same resource using only
/// exact facts and the bounded memory-resolution relation. This is intended
/// for certificate replay: it does not search for containment or separation.
pub(crate) fn c_resources_directly_match(
    left: &CResource,
    right: &CResource,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let values_match = |left: &CValue, right: &CValue| match (left, right) {
        (CValue::Void, CValue::Void) => true,
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "resource direct match: bitvector value",
            || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
        ),
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: pointer value",
                || pointers_match_for_resource_replay(left, right, assumptions),
            )
        }
        _ => false,
    };
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            left == right
                || (crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource memory match: start",
                    || {
                        bitvectors_match_for_resource_replay(
                            left.start(),
                            right.start(),
                            assumptions,
                        )
                    },
                ) && crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource memory match: end",
                    || bitvectors_match_for_resource_replay(left.end(), right.end(), assumptions),
                ) && crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource memory match: base",
                    || pointers_match_for_resource_replay(left.base(), right.base(), assumptions),
                ))
        }
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| values_match(left, right))
        }
        _ => false,
    }
}

fn bitvectors_match_for_resource_replay(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if assumptions.bitvector_terms_equal_from_facts(left, right) {
        return true;
    }
    if explicit_atomic_equality_from_memory_derivations(left, right, assumptions) {
        return true;
    }
    let transported_matches = |term: &Bitvector32Term, target: &Bitvector32Term| {
        let mut memories = Vec::new();
        collect_bitvector_memories(target, &mut memories);
        memories.into_iter().any(|memory| {
            let transported = crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource bitvector transport: rewrite",
                || transport_framed_atomic_bitvector(term, &memory, Some((assumptions, false))),
            );
            transported.is_some_and(|transported| {
                crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource bitvector transport: compare",
                    || {
                        bitvector_terms_proven_equal_for_memory_resolution(
                            &transported,
                            target,
                            assumptions,
                        )
                    },
                )
            })
        })
    };
    if transported_matches(left, right) || transported_matches(right, left) {
        return true;
    }
    // Resource endpoints normally differ only by a framed load. Keep the
    // broader recursive solver as the fallback after targeted transport.
    bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

fn pointer_offsets_match_from_memory_derivations(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_match_from_memory_derivations(left_a, right_a, assumptions)
                && pointer_offsets_match_from_memory_derivations(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && (assumptions.bitvector_terms_equal_from_facts(left, right)
                    || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
                    || explicit_atomic_equality_from_memory_derivations(left, right, assumptions))
        }
        _ => false,
    }
}

fn pointer_offsets_match_for_resource_replay(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer offset: derivation edges",
        || pointer_offsets_match_from_memory_derivations(left, right, assumptions),
    ) {
        return true;
    }
    let transported_matches = |offset: &PointerOffsetTerm, target: &PointerOffsetTerm| {
        let mut memories = Vec::new();
        collect_pointer_offset_memories(target, &mut memories);
        memories.into_iter().any(|memory| {
            let transported = crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource pointer offset transport: rewrite",
                || {
                    transport_framed_atomic_pointer_offset(
                        offset,
                        &memory,
                        Some((assumptions, false)),
                    )
                },
            );
            transported.is_some_and(|transported| {
                crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource pointer offset transport: compare",
                    || {
                        pointer_offsets_proven_equal_for_memory_resolution(
                            &transported,
                            target,
                            assumptions,
                        )
                    },
                )
            })
        })
    };
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer offset: framed transport",
        || transported_matches(left, right) || transported_matches(right, left),
    ) {
        return true;
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer offset: effect equality",
        || c_pointer_offsets_proven_equal_for_effect(left, right, assumptions),
    )
}

fn pointers_match_for_resource_replay(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if left.block == right.block
        && pointer_offsets_match_for_resource_replay(&left.offset, &right.offset, assumptions)
    {
        return true;
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer: general equality",
        || pointers_proven_equal_for_memory_resolution(left, right, assumptions),
    )
}

/// Assumption-free canonical form of a whole memory: every cell key and
/// value canonicalizes its embedded loads. Spellings of the same memory
/// produced at different execution points compare equal when their
/// difference is representational.
pub(crate) fn canonical_c_memory_deep(memory: &CMemory) -> CMemory {
    thread_local! {
        static CACHE: std::cell::RefCell<
            std::collections::HashMap<crate::kernel::SharedCMemory, CMemory>,
        > = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    // Assumption-free and deterministic; keyed by interned snapshot identity.
    let key = crate::kernel::intern_c_memory_ref(memory);
    if let Some(hit) = CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = canonical_c_memory_deep_uncached(memory);
    CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

fn canonical_c_memory_deep_uncached(memory: &CMemory) -> CMemory {
    let mut canonical = memory.clone();
    let cells = std::mem::take(&mut canonical.cells);
    for (pointer, value) in cells.iter() {
        let key = canonicalize_pointer_loads(&pointer, 0);
        let value = match value {
            CValue::Void => CValue::Void,
            CValue::Int32(term) => CValue::Int32(canonicalize_atomic_loads(&term)),
            CValue::UInt8(term) => CValue::UInt8(canonicalize_atomic_loads(&term)),
            CValue::Pointer(pointer) => CValue::Pointer(canonicalize_pointer_loads(&pointer, 0)),
        };
        std::sync::Arc::make_mut(&mut canonical.cells).insert(key, value);
    }
    canonical
}

/// Deep-canonical memory equality; see [`canonical_c_memory_deep`].
pub(crate) fn c_memories_canonically_equal(left: &CMemory, right: &CMemory) -> bool {
    left == right || canonical_c_memory_deep(left) == canonical_c_memory_deep(right)
}

pub(crate) fn c_memory_load_is_unchanged(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    let memo_key = crate::kernel::assumptions::ambient_assumptions_memo_id(assumptions).map(
        |assumptions_id| {
            let before = intern_c_memory_ref(before).arena_id();
            let after = intern_c_memory_ref(after).arena_id();
            UnchangedLoadMemoKey {
                assumptions_id,
                memories: if before <= after {
                    (before, after)
                } else {
                    (after, before)
                },
                pointer: pointer.clone(),
            }
        },
    );
    if let Some(key) = &memo_key
        && UNCHANGED_LOAD_POSITIVE_MEMO.with(|memo| memo.borrow().contains(key))
    {
        return true;
    }
    let derivation_generation = c_memory_derivation_generation();
    if let Some(key) = &memo_key
        && UNCHANGED_LOAD_NEGATIVE_MEMO.with(|memo| {
            memo.borrow()
                .contains(&(derivation_generation, key.clone()))
        })
    {
        return false;
    }
    let truncations_before = crate::kernel::assumptions::search_truncations();
    let result = c_memory_load_is_unchanged_unmemoized(before, after, pointer, assumptions);
    if let Some(key) = memo_key {
        if result {
            UNCHANGED_LOAD_POSITIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= UNCHANGED_LOAD_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key);
            });
        } else if !crate::instrumentation::deadline_exceeded()
            && crate::kernel::assumptions::search_truncations() == truncations_before
        {
            UNCHANGED_LOAD_NEGATIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= UNCHANGED_LOAD_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert((derivation_generation, key));
            });
        }
    }
    result
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UnchangedLoadMemoKey {
    assumptions_id: u64,
    memories: ((u32, u32), (u32, u32)),
    pointer: Pointer,
}

thread_local! {
    static UNCHANGED_LOAD_POSITIVE_MEMO: std::cell::RefCell<
        std::collections::HashSet<UnchangedLoadMemoKey>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
    static UNCHANGED_LOAD_NEGATIVE_MEMO: std::cell::RefCell<
        std::collections::HashSet<(u64, UnchangedLoadMemoKey)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

const UNCHANGED_LOAD_MEMO_LIMIT: usize = 200_000;

fn c_memory_load_is_unchanged_unmemoized(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if memories_match_for_pointer_load(before, after, pointer) {
        return true;
    }
    if canonical_memory_for_pointer_load(before, pointer)
        == canonical_memory_for_pointer_load(after, pointer)
    {
        return true;
    }
    // Small field-update snapshots usually differ at only one or two cells.
    // Compare those directly before paying for a derivation-DAG walk — but
    // with the bounded, memoized alias check only. The general alias check
    // consults the composition-backed separation provers, whose per-query
    // cost scales with the carrier count; running it per differing cell
    // before the bounded DAG walk turned this "fast path" into the dominant
    // cost of a simple step (measured at 370k of a 500k budget on
    // bounded-pool). The full comparison still runs after the DAG walk, so
    // nothing provable is lost — only reordered behind the bounded answers.
    let small_snapshot_pair = before.cells.len() <= 8 && after.cells.len() <= 8;
    if small_snapshot_pair
        && crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "framed load: small snapshot comparison",
            || memories_match_for_pointer_load_bounded_alias(before, after, pointer, assumptions),
        )
    {
        return true;
    }
    // For larger snapshots the DAG walk runs before the snapshot comparison:
    // it answers from recorded edges in a bounded number of hops, where
    // `memories_match_for_pointer_load_under_assumptions` first compares
    // whole non-local block sets and then every differing cell.
    // This API is a certificate-replay query. No-op block declarations,
    // forgotten caches, and allocations of a distinct block are sound DAG
    // bridges here; enabling them keeps replay on the bounded derivation walk
    // instead of falling into whole-snapshot alias search.
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "framed load: memory derivation walk",
        || {
            with_extended_dag_bridging(|| {
                load_unchanged_along_memory_derivations(before, after, pointer, assumptions)
            })
        },
    ) {
        return true;
    }
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    if memories_match_for_pointer_load_under_assumptions(before, after, pointer, assumptions) {
        return true;
    }
    // Predicate framing is deliberately bounded: use exact certified writes
    // and direct address cancellation, without invoking general alias search.
    if assumptions.prop_facts.iter().any(|proposition| {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        match proposition {
            Proposition::CMemoryMutatesOnly {
                before: effect_before,
                after: effect_after,
                pointers,
            } => {
                (effect_before == before
                    || memory_materializes_atomic_load(effect_before, before, pointer)
                    || c_memories_canonically_equal(effect_before, before)
                    || canonical_memory_for_pointer_load(effect_before, pointer)
                        == canonical_memory_for_pointer_load(before, pointer))
                    && (effect_after == after
                        || c_memories_canonically_equal(effect_after, after)
                        || canonical_memory_for_pointer_load(effect_after, pointer)
                            == canonical_memory_for_pointer_load(after, pointer))
                    && pointers.iter().all(|write| {
                        write.blocks_proven_distinct(pointer)
                            || pointer_offsets_with_common_base_proven_distinct(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointers_proven_distinct_for_memory_resolution(
                                write,
                                pointer,
                                assumptions,
                            )
                            || assumptions.pointers_proven_disjoint_by_range(write, pointer)
                            || pointer_byte_offset_from_base(write, pointer)
                                .and_then(|offset| offset.as_const())
                                .is_some_and(|offset| offset != 0)
                    })
            }
            Proposition::CMemoryEffectSummary {
                before: effect_before,
                after: effect_after,
                mutable_ranges,
            } => {
                let before_matches =
                    memory_matches_effect_summary_endpoint(effect_before, before, pointer);
                let after_matches =
                    memory_matches_effect_summary_endpoint(effect_after, after, pointer);
                before_matches
                    && after_matches
                    && assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
            }
            Proposition::CHeapLifetimeRetired {
                before: effect_before,
                after: effect_after,
                allocation_base,
                bytes,
            } => {
                let before_matches =
                    memory_matches_effect_summary_endpoint(effect_before, before, pointer);
                let after_matches =
                    memory_matches_effect_summary_endpoint(effect_after, after, pointer);
                before_matches
                    && after_matches
                    && heap_allocation_proven_separate_from_pointer(
                        allocation_base,
                        bytes,
                        pointer,
                        assumptions,
                    )
            }
            _ => false,
        }
    }) {
        return true;
    }
    load_unchanged_via_effect_chain(before, after, pointer, assumptions)
}

/// Answers load preservation from the memory DAG rather than by searching
/// recorded effect facts: follows the derivations that execution recorded
/// when it built the snapshots, refusing any edge that could have written
/// the pointer.
///
/// This is the first consumer of the named-memory-states representation
/// (`docs/advanced/memory-dag.md`). Where
/// [`load_unchanged_via_effect_chain`] reconstructs a write history at proof
/// time from `CMemoryMutatesOnly` / `CMemoryEffectSummary` facts and links
/// hops by deep-canonical snapshot equality, this walks the history itself
/// and links hops by arena identity, so two spellings of one location cannot
/// drift apart between program points.
///
/// Soundness rests on three things. Each `Store` hop is crossed only when
/// the written pointer is *provably distinct* from the loaded one, using the
/// same distinctness predicates as the fact-based paths. Each `CallHavoc`
/// hop is crossed only when the call's mutable ranges are provably disjoint
/// from the pointer, matching the `CMemoryEffectSummary` arm above. And a
/// `LoopHavoc` hop is never crossed at all: loop havoc has no write set, so
/// its freshness marker is honoured here at the edge, which is where
/// conventions.md's havoc-identity trap is disarmed for this arc.
///
/// The walk terminates because a derivation's base always holds a strictly
/// smaller arena id (see `record_c_memory_derivation`); the hop cap and the
/// reentrancy guard are the belt-and-braces conventions.md asks of any new
/// recursive prover arm, since the per-hop distinctness checks can re-enter
/// memory reasoning.
fn load_unchanged_along_memory_derivations(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if memory_dag_disabled() {
        return false;
    }
    thread_local! {
        static DERIVATION_WALK_ACTIVE: std::cell::Cell<bool> =
            const { std::cell::Cell::new(false) };
    }
    if DERIVATION_WALK_ACTIVE.with(std::cell::Cell::get) {
        return false;
    }
    DERIVATION_WALK_ACTIVE.with(|active| active.set(true));
    let before = intern_c_memory_ref(before);
    let after = intern_c_memory_ref(after);
    // "Unchanged" is symmetric, and callers pass the pair in either order.
    let reached = memory_derivations_reach(&after, &before, pointer, assumptions)
        || memory_derivations_reach(&before, &after, pointer, assumptions);
    DERIVATION_WALK_ACTIVE.with(|active| active.set(false));
    reached
}

/// Walks `from` back along its derivations looking for `target`, crossing
/// only edges that provably leave `pointer`'s cell alone. See
/// [`load_unchanged_along_memory_derivations`] for the soundness argument.
fn memory_derivations_reach(
    from: &SharedCMemory,
    target: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    const MEMORY_DERIVATION_HOP_LIMIT: usize = 64;
    let mut current = from.clone();
    for _ in 0..MEMORY_DERIVATION_HOP_LIMIT {
        if current == *target {
            return true;
        }
        // The replay and the independent kernel certification build parallel
        // derivation chains for one execution, so the target is often a
        // sibling spelling of a snapshot on this chain rather than the same
        // interned object. Decide that pair with the bounded pointer-load
        // matcher — havoc marker sets must agree, so this never crosses a
        // mutation event the edge rules would have refused.
        if memories_match_for_pointer_load(current.memory(), target.memory(), pointer)
            || memories_match_for_pointer_load_bounded_alias(
                current.memory(),
                target.memory(),
                pointer,
                assumptions,
            )
        {
            return true;
        }

        // Ids strictly decrease along `base`, so an id at or below the
        // target's can no longer reach the target *object* — but a sibling
        // spelling of the target on this chain can still match below that
        // point, so the walk continues under its hop cap instead of exiting.
        let Some(derivation) = current.derivation() else {
            return false;
        };
        let edge_name = match derivation.as_ref() {
            CMemoryDerivation::Store { .. } => "memory derivation edge: store",
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::CellsForgotten { .. } => "memory derivation edge: bookkeeping",
            CMemoryDerivation::HeapAllocated { .. } => "memory derivation edge: allocation",
            CMemoryDerivation::HeapFreed { .. } => "memory derivation edge: free",
            CMemoryDerivation::CallHavoc { .. } => "memory derivation edge: call havoc",
            CMemoryDerivation::LoopHavoc { .. } => "memory derivation edge: loop havoc",
        };
        let crossable = crate::instrumentation::measure_operation(
            "kernel",
            "memory derivation walk",
            edge_name,
            || match derivation.as_ref() {
                CMemoryDerivation::Store { pointer: write, .. } => {
                    crate::instrumentation::measure_operation(
                        "kernel",
                        "memory derivation store edge",
                        "store edge: distinct blocks",
                        || write.blocks_proven_distinct(pointer),
                    ) || crate::instrumentation::measure_operation(
                        "kernel",
                        "memory derivation store edge",
                        "store edge: common-base offsets",
                        || {
                            pointer_offsets_with_common_base_proven_distinct(
                                write,
                                pointer,
                                assumptions,
                            )
                        },
                    ) || crate::instrumentation::measure_operation(
                        "kernel",
                        "memory derivation store edge",
                        "store edge: general pointer distinctness",
                        || {
                            pointers_proven_distinct_for_memory_resolution(
                                write,
                                pointer,
                                assumptions,
                            )
                        },
                    )
                }
                // Declaring a block or forgetting cached cells writes nothing,
                // so every load is untouched — but only the extended-bridging
                // scope may exploit that: elsewhere these edges must look like
                // the pre-arc absence of an edge.
                CMemoryDerivation::BlockDeclared { .. }
                | CMemoryDerivation::HeapAllocationPending { .. }
                | CMemoryDerivation::CellsForgotten { .. } => extended_dag_bridging_active(),
                CMemoryDerivation::HeapAllocated { block, .. } => {
                    pointer.block != *block && extended_dag_bridging_active()
                }
                CMemoryDerivation::HeapFreed {
                    allocation_base,
                    bytes,
                    ..
                } => {
                    extended_dag_bridging_active()
                        && (allocation_base.blocks_proven_distinct(pointer)
                            || pointers_proven_distinct_for_memory_resolution(
                                allocation_base,
                                pointer,
                                assumptions,
                            )
                            || heap_allocation_proven_separate_from_pointer(
                                allocation_base,
                                bytes,
                                pointer,
                                assumptions,
                            ))
                }
                CMemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                    assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
                }
                // Loop havoc may write anything the body can reach.
                CMemoryDerivation::LoopHavoc { .. } => false,
            },
        );
        if !crossable {
            return false;
        }
        current = derivation.base().clone();
    }
    false
}

/// Where the memory DAG says the cell at a pointer came from: the
/// select-over-store answer to "what does this cell hold after these
/// stores", read off the write history execution recorded rather than
/// reconstructed by canonicalizing and deep-comparing snapshot values.
///
/// Both variants name the node the walk stopped at, and both denote the same
/// thing — the value of loading the pointer *in that node*. That is what
/// makes two lookups comparable by node identity alone.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MemoryDagCell {
    /// `node`'s derivation is a `Store` whose pointer is provably the loaded
    /// one, so the load reads `value`.
    Stored { node: SharedCMemory, value: CValue },
    /// The walk reached `node` without crossing any edge that could have
    /// written the cell, and stopped: `node` carries no derivation, its
    /// derivation is undecidable against this pointer, or the hop cap ran
    /// out. The load therefore reads whatever `node` holds at the pointer.
    Unwritten { node: SharedCMemory },
}

impl MemoryDagCell {
    fn node(&self) -> &SharedCMemory {
        match self {
            Self::Stored { node, .. } | Self::Unwritten { node } => node,
        }
    }

    /// The concrete value the lookup pins down, when it pins one down.
    fn resolved_value(&self, pointer: &Pointer) -> Option<CValue> {
        match self {
            Self::Stored { value, .. } => Some(value.clone()),
            Self::Unwritten { node } => node.known_value(pointer),
        }
    }
}

// The hop predicates reach `decide` and the range-disjointness provers,
// which reach the cell-source provers again. One nested level is allowed —
// a hop's range certificate may itself need a single DAG hop to match the
// spelling of its base — and the cap makes the recursion depth-gated per
// conventions.md. Answers computed at depth 1 see the cutoff and are never
// memoized.
const CELL_LOOKUP_DEPTH_LIMIT: u8 = 2;

thread_local! {
    static CELL_LOOKUP_DEPTH: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

/// Walks a snapshot's derivation edges backwards resolving one cell.
///
/// Every hop is decided by the *cheap* predicates only — block distinctness
/// and additive-base cancellation for stores, recorded range disjointness for
/// call havoc — because this is the arm that runs before canonicalization and
/// has to stay cheaper than what it short-circuits. A hop it cannot decide is
/// not a failure: the walk stops and reports the node it stopped at, which is
/// still a true statement about the load.
///
/// `LoopHavoc` is never crossed (conventions.md's soundness trap; loop havoc
/// has no write set to be disjoint from), and the hop cap plus the strictly
/// decreasing arena ids along `base` bound the walk.
/// Budget for one `Store`-hop distinctness check inside the cell-source
/// walk, isolated from the enclosing query's fuel. Small on purpose: the
/// certificates these hops need name their ranges close to the surface.
const MEMORY_DAG_HOP_DISTINCTNESS_FUEL: usize = 128;

// The extended DAG bridging (crossing block-declaration and cell-forgetting
// edges, range-certificate store hops, stored-value pinning, and the
// order-path load matching in assumptions.rs) runs ONLY inside the loadable
// prover. Everywhere else — execution pruning, load canonicalization, simp
// planning — behavior must stay byte-identical to the pre-arc path, because
// certified spellings and case-split structure replay against it. The flag
// is scoped, not global, so generation and replay of the same query always
// agree.
thread_local! {
    static EXTENDED_DAG_BRIDGING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static EXPLICIT_DAG_REPLAY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn extended_dag_bridging_active() -> bool {
    EXTENDED_DAG_BRIDGING.with(std::cell::Cell::get)
}

/// True while explicit certificate replay widens the DAG walk (see
/// `explicit_atomic_equality_from_memory_derivations`); resolution answers
/// computed in that mode must not be shared with the planner-facing arms.
pub(super) fn explicit_dag_replay_active() -> bool {
    EXPLICIT_DAG_REPLAY.with(std::cell::Cell::get)
}

/// True outside any memory-DAG cell lookup. Answers computed inside a
/// lookup see the `CELL_LOOKUP_DEPTH` cutoff and are weaker than the
/// depth-zero answer, so they must not be memoized under a depth-free key.
pub(super) fn memory_dag_cell_lookup_depth_is_zero() -> bool {
    CELL_LOOKUP_DEPTH.with(std::cell::Cell::get) == 0
}

/// Runs `body` with the extended DAG bridging enabled (see above).
pub(super) fn with_extended_dag_bridging<T>(body: impl FnOnce() -> T) -> T {
    let previous = EXTENDED_DAG_BRIDGING.with(|flag| flag.replace(true));
    let result = body();
    EXTENDED_DAG_BRIDGING.with(|flag| flag.set(previous));
    result
}

fn memory_dag_cell_source(
    memory: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> MemoryDagCell {
    const MEMORY_DAG_CELL_HOP_LIMIT: usize = 64;
    let mut current = memory.clone();
    for _ in 0..MEMORY_DAG_CELL_HOP_LIMIT {
        let Some(derivation) = current.derivation() else {
            return MemoryDagCell::Unwritten { node: current };
        };
        match derivation.as_ref() {
            CMemoryDerivation::Store {
                pointer: write,
                value,
                ..
            } => {
                if write == pointer
                    || EXPLICIT_DAG_REPLAY.with(std::cell::Cell::get)
                        && write.block == pointer.block
                        && pointer_offsets_match_from_memory_derivations(
                            &write.offset,
                            &pointer.offset,
                            assumptions,
                        )
                    || write.block == pointer.block
                        && assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                            write.offset.clone(),
                            pointer.offset.clone(),
                        )) == Some(true)
                {
                    return MemoryDagCell::Stored {
                        node: current,
                        value: value.clone(),
                    };
                }
                // The recorded-range fallback covers writes into a
                // proven-separate region (a buffer store crossed while
                // resolving a struct field); the same predicate
                // `memory_derivations_reach` crosses `Store` hops with.
                // Extended-bridging scope only, and under its own capped
                // budget so this advisory walk can never drain the
                // enclosing query's fuel — fuel-coupled spellings elsewhere
                // must replay byte-for-byte.
                if !(write.blocks_proven_distinct(pointer)
                    || pointer_offsets_with_common_base_proven_distinct(
                        write,
                        pointer,
                        assumptions,
                    )
                    || EXPLICIT_DAG_REPLAY.with(std::cell::Cell::get)
                        && assumptions
                            .pointers_proven_disjoint_by_shallow_explicit_range(write, pointer)
                    || extended_dag_bridging_active()
                        && super::reasoning::with_isolated_memory_resolution_fuel(
                            MEMORY_DAG_HOP_DISTINCTNESS_FUEL,
                            || {
                                pointers_proven_distinct_for_memory_resolution(
                                    write,
                                    pointer,
                                    assumptions,
                                )
                            },
                        ))
                {
                    return MemoryDagCell::Unwritten { node: current };
                }
            }
            // Declaring a block or forgetting cached cells writes nothing,
            // so every load is untouched — but only the extended-bridging
            // scope may exploit that: elsewhere these edges must look like
            // the pre-arc absence of an edge.
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::CellsForgotten { .. } => {
                if !extended_dag_bridging_active() {
                    return MemoryDagCell::Unwritten { node: current };
                }
            }
            CMemoryDerivation::HeapAllocated { block, .. } => {
                if pointer.block == *block || !extended_dag_bridging_active() {
                    return MemoryDagCell::Unwritten { node: current };
                }
            }
            CMemoryDerivation::HeapFreed {
                allocation_base,
                bytes,
                ..
            } => {
                if !extended_dag_bridging_active()
                    || !(allocation_base.blocks_proven_distinct(pointer)
                        || pointers_proven_distinct_for_memory_resolution(
                            allocation_base,
                            pointer,
                            assumptions,
                        )
                        || heap_allocation_proven_separate_from_pointer(
                            allocation_base,
                            bytes,
                            pointer,
                            assumptions,
                        ))
                {
                    return MemoryDagCell::Unwritten { node: current };
                }
            }
            CMemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                if !assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer) {
                    return MemoryDagCell::Unwritten { node: current };
                }
            }
            // Loop havoc may write anything the body can reach.
            CMemoryDerivation::LoopHavoc { .. } => {
                return MemoryDagCell::Unwritten { node: current };
            }
        }
        current = derivation.base().clone();
    }
    MemoryDagCell::Unwritten { node: current }
}

pub(super) fn heap_allocation_proven_separate_from_pointer(
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let allocation_token = CResourceFact::own_allocation(allocation_base.clone(), bytes.clone())
        .resource()
        .clone();
    let cell = CResource::Memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    assumptions.proves_resource_separate(&allocation_token, &cell)
        || int32_element_count_from_bytes(bytes).is_some_and(|count| {
            let allocation_memory = CResource::Memory(CMemoryRange::new(
                allocation_base.clone(),
                Bitvector32Term::Constant(0),
                count,
            ));
            assumptions.proves_resource_separate(&allocation_memory, &cell)
        })
}

/// Answers "are these two loads equal" from the memory DAG: both sides are
/// resolved to their source cell by [`memory_dag_cell_source`], and the loads
/// are equal when the two lookups land on the same node or pin down the same
/// value.
///
/// This is stage 4 of `docs/advanced/memory-dag.md`, and it is
/// wired in *ahead* of the canonicalizing comparisons rather than beside
/// them. Where those take two embedded snapshots, deep-canonicalize both and
/// compare the results structurally, this follows named edges and compares
/// arena ids, so the common case — two spellings of one cell separated only
/// by stores that provably missed it — costs a short walk instead of a deep
/// term rewrite.
///
/// Advisory as ever: a `false` here means "the DAG did not answer", and every
/// caller falls through to its previous path. Derivations are not guaranteed
/// to connect every pair of snapshots, so falling through is the normal case,
/// not an error.
pub(super) fn loads_equal_along_memory_derivations_at(
    left_memory: &SharedCMemory,
    right_memory: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if memory_dag_disabled() {
        return false;
    }
    if left_memory == right_memory {
        return true;
    }
    let Some((left, right)) = with_cell_lookup_depth(|| {
        (
            memory_dag_cell_source(left_memory, pointer, assumptions),
            memory_dag_cell_source(right_memory, pointer, assumptions),
        )
    }) else {
        return false;
    };
    if left.node() == right.node() {
        return true;
    }
    match (left.resolved_value(pointer), right.resolved_value(pointer)) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

/// Runs `body` one cell-lookup level deeper, or returns `None` at the cap.
fn with_cell_lookup_depth<T>(body: impl FnOnce() -> T) -> Option<T> {
    let depth = CELL_LOOKUP_DEPTH.with(std::cell::Cell::get);
    if depth >= CELL_LOOKUP_DEPTH_LIMIT {
        return None;
    }
    CELL_LOOKUP_DEPTH.with(|cell| cell.set(depth + 1));
    let result = body();
    CELL_LOOKUP_DEPTH.with(|cell| cell.set(depth));
    Some(result)
}

/// The [`loads_equal_along_memory_derivations_at`] arm as a term-level test:
/// true only when both sides are atomic loads the DAG resolves alike.
///
/// Beyond the node-identity comparison, one side's walk may land on a
/// `Store` whose recorded value IS the other side verbatim — the common case
/// for a load-caching store (`cells[p] := load(older, p)`): the newer
/// snapshot's cell literally pins the older spelling. That is still a pure
/// DAG answer (the value comes off a derivation edge, compared structurally),
/// so it stays inside the exact-facts-plus-edges determinism boundary.
pub(super) fn atomic_loads_equal_along_memory_derivations(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer),
    ) = (left, right)
    else {
        return false;
    };
    if left_pointer != right_pointer {
        return false;
    }
    if memory_dag_disabled() {
        return false;
    }
    if left_memory == right_memory {
        return true;
    }
    if !extended_dag_bridging_active() {
        // Pre-arc behavior outside the loadable prover: node-identity
        // comparison only, no memo, no value pinning.
        return loads_equal_along_memory_derivations_at(
            left_memory,
            right_memory,
            left_pointer,
            assumptions,
        );
    }
    // The same (snapshot, snapshot, pointer) triple is asked thousands of
    // times per proof. A proven equality stays true as new first-wins DAG
    // edges are recorded: the edges only add faithful derivations of already
    // existing snapshots. Cache those positive answers independently of the
    // derivation generation. A negative answer only means "not connected
    // yet", so it remains generation-scoped and is retried after any new
    // edge. Only depth-zero answers participate: a nested lookup sees the
    // depth cutoff and its weaker answer must not shadow the full one.
    let memo_key = (CELL_LOOKUP_DEPTH.with(std::cell::Cell::get) == 0)
        .then(|| super::assumptions::dag_memo_assumptions_id(assumptions))
        .flatten()
        .map(|assumptions_id| DagLoadEqualityMemoKey {
            assumptions_id,
            left_memory: left_memory.arena_id(),
            right_memory: right_memory.arena_id(),
            pointer: left_pointer.as_ref().clone(),
        });
    if let Some(key) = &memo_key
        && DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| memo.borrow().contains(key))
    {
        return true;
    }
    let derivation_generation = c_memory_derivation_generation();
    if let Some(key) = &memo_key
        && DAG_LOAD_EQUALITY_NEGATIVE_MEMO.with(|memo| {
            memo.borrow()
                .contains(&(derivation_generation, key.clone()))
        })
    {
        return false;
    }
    let result = loads_equal_along_memory_derivations_at(
        left_memory,
        right_memory,
        left_pointer,
        assumptions,
    ) || with_cell_lookup_depth(|| {
        let left_cell = memory_dag_cell_source(left_memory, left_pointer, assumptions);
        let right_cell = memory_dag_cell_source(right_memory, right_pointer, assumptions);
        matches!(
            left_cell.resolved_value(left_pointer),
            Some(CValue::Int32(value)) if &value == right
        ) || matches!(
            right_cell.resolved_value(right_pointer),
            Some(CValue::Int32(value)) if &value == left
        )
    })
    .unwrap_or(false);
    if let Some(key) = memo_key {
        if result {
            DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key);
            });
        } else {
            DAG_LOAD_EQUALITY_NEGATIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert((derivation_generation, key));
            });
        }
    }
    result
}

/// Resolves an equality from the execution-recorded memory DAG for explicit
/// certificate replay. Unlike the planner-facing DAG arm, this may cross
/// no-op block declarations and stores whose distinctness follows from the
/// certificate's separation facts; every crossed edge remains justified by
/// exact facts and the bounded DAG walk.
pub(crate) fn explicit_atomic_equality_from_memory_derivations(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    let previous = EXPLICIT_DAG_REPLAY.with(|flag| flag.replace(true));
    let result = with_extended_dag_bridging(|| {
        if atomic_loads_equal_along_memory_derivations(left, right, assumptions) {
            return true;
        }
        let resolves_to = |load: &Bitvector32Term, value: &Bitvector32Term| {
            let Bitvector32Term::MemoryLoad(memory, pointer) = load else {
                return false;
            };
            with_cell_lookup_depth(|| {
                matches!(
                    memory_dag_cell_source(memory, pointer, assumptions).resolved_value(pointer),
                    Some(CValue::Int32(resolved) | CValue::UInt8(resolved))
                        if resolved == *value
                )
            })
            .unwrap_or(false)
        };
        resolves_to(left, right) || resolves_to(right, left)
    });
    EXPLICIT_DAG_REPLAY.with(|flag| flag.set(previous));
    result
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct DagLoadEqualityMemoKey {
    assumptions_id: u64,
    left_memory: (u32, u32),
    right_memory: (u32, u32),
    pointer: Pointer,
}

thread_local! {
    static DAG_LOAD_EQUALITY_POSITIVE_MEMO: std::cell::RefCell<
        std::collections::HashSet<DagLoadEqualityMemoKey>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
    static DAG_LOAD_EQUALITY_NEGATIVE_MEMO: std::cell::RefCell<
        std::collections::HashSet<(u64, DagLoadEqualityMemoKey)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

const DAG_LOAD_EQUALITY_MEMO_LIMIT: usize = 200_000;

/// Bounded search for a chain of recorded effects carrying a load from one
/// snapshot to another with the pointer untouched at every hop. Endpoints
/// link by deep-canonical equality, and each hop's write set must be
/// provably distinct from the pointer, so the chain never crosses a write
/// to the loaded cell and never bridges havoc without a recorded effect.
fn load_unchanged_via_effect_chain(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    // Real allocator/copy/install/free paths routinely cross more than eight
    // individually certified effects. The effect graph is finite, so a proof
    // must not fail merely because its certified chain is long.
    let mut steps = Vec::new();
    for proposition in assumptions.prop_facts.iter() {
        match proposition {
            Proposition::CMemoryMutatesOnly {
                before: step_before,
                after: step_after,
                pointers,
            } => {
                let untouched = pointers.iter().all(|write| {
                    write.blocks_proven_distinct(pointer)
                        || pointer_offsets_with_common_base_proven_distinct(
                            write,
                            pointer,
                            assumptions,
                        )
                        || pointers_proven_distinct_for_memory_resolution(
                            write,
                            pointer,
                            assumptions,
                        )
                });
                if untouched {
                    steps.push((step_before, step_after));
                }
            }
            Proposition::CMemoryEffectSummary {
                before: step_before,
                after: step_after,
                mutable_ranges,
            } => {
                if assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer) {
                    steps.push((step_before, step_after));
                }
            }
            Proposition::CHeapLifetimeRetired {
                before: step_before,
                after: step_after,
                allocation_base,
                bytes,
            } => {
                if heap_allocation_proven_separate_from_pointer(
                    allocation_base,
                    bytes,
                    pointer,
                    assumptions,
                ) {
                    steps.push((step_before, step_after));
                }
            }
            _ => {}
        }
    }
    if steps.is_empty() {
        return false;
    }
    // Hops link pointer-relatively: two spellings of one snapshot may carry
    // different unrelated cells (deep-canonical equality then fails), but a
    // load-preservation chain only needs the pointed-at cell to agree at
    // every junction. The effect graph is finite, so traverse it to a fixed
    // point instead of rejecting valid chains after an arbitrary hop count.
    let joins = |expected: &CMemory, actual: &CMemory| {
        memory_matches_effect_summary_endpoint(expected, actual, pointer)
    };
    let mut frontier: Vec<&CMemory> = vec![before];
    let mut seen: Vec<&CMemory> = vec![before];
    while !frontier.is_empty() {
        let mut next = Vec::new();
        for current in frontier {
            for (step_before, step_after) in &steps {
                for (from, to) in [(step_before, step_after), (step_after, step_before)] {
                    if joins(from, current) {
                        if joins(to, after) {
                            return true;
                        }
                        if !seen.iter().any(|seen| joins(seen, to)) {
                            seen.push(*to);
                            next.push(*to);
                        }
                    }
                }
            }
        }
        frontier = next;
    }
    false
}

/// Searches the finite graph of recorded effects connecting two memory
/// snapshots, regardless of what the effects wrote. Used for properties that
/// survive writes, such as loadability of a still-present range.
pub(crate) fn c_memories_connected_by_effects(
    before: &CMemory,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let mut steps = Vec::new();
    for proposition in assumptions.prop_facts.iter() {
        match proposition {
            Proposition::CMemoryMutatesOnly {
                before: step_before,
                after: step_after,
                ..
            }
            | Proposition::CMemoryEffectSummary {
                before: step_before,
                after: step_after,
                ..
            } => {
                steps.push((
                    canonical_c_memory_deep(step_before),
                    canonical_c_memory_deep(step_after),
                ));
            }
            _ => {}
        }
    }
    if steps.is_empty() {
        return false;
    }
    let target = canonical_c_memory_deep(after);
    let start = canonical_c_memory_deep(before);
    if start == target {
        return true;
    }
    let mut seen = vec![start.clone()];
    let mut frontier = vec![start];
    while !frontier.is_empty() {
        let mut next = Vec::new();
        for current in &frontier {
            for (step_before, step_after) in &steps {
                for (from, to) in [(step_before, step_after), (step_after, step_before)] {
                    if from == current && !seen.contains(to) {
                        if to == &target {
                            return true;
                        }
                        seen.push(to.clone());
                        next.push(to.clone());
                    }
                }
            }
        }
        frontier = next;
    }
    false
}

fn c_memory_load_is_directly_unchanged(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    if memories_directly_match_for_pointer_load(before, after, pointer, assumptions) {
        return true;
    }
    assumptions.prop_facts.iter().any(|proposition| {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        match proposition {
            Proposition::CMemoryMutatesOnly {
                before: effect_before,
                after: effect_after,
                pointers,
            } => {
                (effect_before == before
                    || memory_materializes_atomic_load(effect_before, before, pointer))
                    && effect_after == after
                    && pointers.iter().all(|write| {
                        write.blocks_proven_distinct(pointer)
                            || pointer_offsets_with_common_base_proven_distinct(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointers_proven_distinct_for_memory_resolution(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointer_byte_offset_from_base(write, pointer)
                                .and_then(|offset| offset.as_const())
                                .is_some_and(|offset| offset != 0)
                    })
            }
            Proposition::CMemoryEffectSummary {
                before: effect_before,
                after: effect_after,
                mutable_ranges,
            } => {
                let before_matches = memories_directly_match_for_pointer_load(
                    effect_before,
                    before,
                    pointer,
                    assumptions,
                );
                let after_matches = before_matches
                    && memories_directly_match_for_pointer_load(
                        effect_after,
                        after,
                        pointer,
                        assumptions,
                    );
                let disjoint = after_matches
                    && assumptions.ranges_directly_disjoint_from_pointer(mutable_ranges, pointer);
                before_matches && after_matches && disjoint
            }
            Proposition::CHeapLifetimeRetired {
                before: effect_before,
                after: effect_after,
                allocation_base,
                bytes,
            } => {
                let before_matches = memories_directly_match_for_pointer_load(
                    effect_before,
                    before,
                    pointer,
                    assumptions,
                );
                let after_matches = before_matches
                    && memories_directly_match_for_pointer_load(
                        effect_after,
                        after,
                        pointer,
                        assumptions,
                    );
                after_matches
                    && heap_allocation_proven_separate_from_pointer(
                        allocation_base,
                        bytes,
                        pointer,
                        assumptions,
                    )
            }
            _ => false,
        }
    })
}

fn memories_directly_match_for_pointer_load(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if pointer.block.starts_with("local:")
        || !left
            .blocks
            .iter()
            .filter(|(block, _)| block.starts_with("havoc:") || block.starts_with("call-havoc:"))
            .eq(right.blocks.iter().filter(|(block, _)| {
                block.starts_with("havoc:") || block.starts_with("call-havoc:")
            }))
        || left.blocks.get(&pointer.block) != right.blocks.get(&pointer.block)
    {
        return false;
    }
    differing_cell_pointers_in_block(left, right, &pointer.block)
        .into_iter()
        .all(|cell| {
            cell.blocks_proven_distinct(pointer)
                || pointer_offsets_with_common_base_proven_distinct(&cell, pointer, assumptions)
                || pointers_proven_distinct_for_memory_resolution(&cell, pointer, assumptions)
                || pointer_byte_offset_from_base(&cell, pointer)
                    .and_then(|offset| offset.as_const())
                    .is_some_and(|offset| offset != 0)
                || assumptions.ranges_directly_disjoint_from_pointer(
                    &[CMemoryRange::new(
                        cell,
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(1),
                    )],
                    pointer,
                )
        })
}

fn differing_cell_pointers_in_block(
    left: &CMemory,
    right: &CMemory,
    block: &PointerBlock,
) -> BTreeSet<Pointer> {
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| &pointer.block == block)
        .filter(|pointer| left.cells.get(*pointer) != right.cells.get(*pointer))
        .cloned()
        .collect()
}

fn memory_materializes_atomic_load(
    materialized: &CMemory,
    symbolic: &CMemory,
    pointer: &Pointer,
) -> bool {
    matches!(
        materialized.known_value(pointer),
        Some(CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer))
            | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer)))
            if source_pointer.as_ref() == pointer
                && memories_match_for_pointer_load(&source, symbolic, pointer)
    )
}

/// Certifies the narrow frame rule used by execution proofs for ordinary C
/// conditions. Address-dependent loads are transported from the inside out;
/// other proposition forms must be re-established explicitly.
pub(crate) fn prove_c_condition_fact_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, false)))
}

pub(crate) fn prove_c_condition_fact_direct_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, true)))
}

/// Instantiates one universally quantified int32 fact and records the exact
/// implication premises consumed from its body. The theorem remains
/// conditional on the quantified fact and every listed premise.
pub fn prove_forall_int32_application(
    quantified: &Proposition,
    value: Bitvector32Term,
    premises: &[Proposition],
) -> Option<Theorem> {
    let Proposition::ForAll { var, sort, body } = quantified else {
        return None;
    };
    if *sort != Sort::CInt32 {
        return None;
    }
    let mut instantiated = substitute_bitvector_variable_in_proposition(body, *var, &value);
    for premise in premises {
        let Proposition::Implies(expected, body) = instantiated else {
            return None;
        };
        if expected.as_ref() != premise {
            return None;
        }
        instantiated = *body;
    }
    if matches!(instantiated, Proposition::Implies(_, _)) {
        return None;
    }
    let application = premises.iter().rev().fold(instantiated, |body, premise| {
        Proposition::Implies(Box::new(premise.clone()), Box::new(body))
    });
    Some(Theorem::new(Proposition::Implies(
        Box::new(quantified.clone()),
        Box::new(application),
    )))
}

fn prove_c_condition_fact_transport_with_assumptions(
    fact: &Proposition,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Theorem> {
    let Proposition::ConditionIs(condition, value) = fact else {
        return None;
    };
    let transported = transport_framed_atomic_condition(condition, after, assumptions)?;
    if &transported == condition {
        return None;
    }
    let conclusion = Proposition::ConditionIs(transported, *value);
    Some(Theorem::new(Proposition::Implies(
        Box::new(fact.clone()),
        Box::new(conclusion),
    )))
}

/// Rewrites subterms of a condition fact that equal a certified store's
/// value into loads from that store's post-memory, so a fact spelled in
/// pre-store terms can be transported across the store. The rewriting is
/// definitional: a certified store guarantees `load(after, pointer)` equals
/// the stored value.
pub(crate) fn rewrite_condition_through_certified_stores(
    fact: &Proposition,
    transitions: &[ExecutionPureFact],
) -> Proposition {
    let mut equations = Vec::new();
    for transition in transitions {
        let Some(store) = &transition.certified_store else {
            continue;
        };
        let value_term = match &store.value {
            CValue::Int32(term) | CValue::UInt8(term) => term.clone(),
            _ => continue,
        };
        equations.push((
            canonicalize_atomic_loads(&value_term),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(store.after.clone()),
                Box::new(store.pointer.clone()),
            ),
        ));
    }
    if equations.is_empty() {
        return fact.clone();
    }
    fn rewrite_term(
        term: &Bitvector32Term,
        equations: &[(Bitvector32Term, Bitvector32Term)],
    ) -> Bitvector32Term {
        let canonical = canonicalize_atomic_loads(term);
        for (value, load) in equations {
            if &canonical == value {
                return load.clone();
            }
        }
        match term {
            Bitvector32Term::Add(left, right) => Bitvector32Term::Add(
                Box::new(rewrite_term(left, equations)),
                Box::new(rewrite_term(right, equations)),
            ),
            Bitvector32Term::Subtract(left, right) => Bitvector32Term::Subtract(
                Box::new(rewrite_term(left, equations)),
                Box::new(rewrite_term(right, equations)),
            ),
            Bitvector32Term::Multiply(left, right) => Bitvector32Term::Multiply(
                Box::new(rewrite_term(left, equations)),
                Box::new(rewrite_term(right, equations)),
            ),
            other => other.clone(),
        }
    }
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(rewrite_term(left, &equations)),
            Box::new(rewrite_term(right, &equations)),
        )
    };
    let rewritten = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32Equal(left, right)
        }
        _ => return fact.clone(),
    };
    Proposition::ConditionIs(rewritten, *value)
}

/// Canonicalizes every load in a term for structural comparison: cached
/// cells resolve to their values and remaining loads use the canonical
/// memory for their pointer.
pub(crate) fn canonicalize_atomic_loads(term: &Bitvector32Term) -> Bitvector32Term {
    thread_local! {
        static CACHE: std::cell::RefCell<
            std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
        > = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    // Assumption-free and deterministic; term hashing is cheap now that
    // embedded snapshots hash by interned identity.
    if let Some(hit) = CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return hit;
    }
    let result = canonicalize_atomic_loads_with_depth(term, 0);
    CACHE.with(|cache| cache.borrow_mut().insert(term.clone(), result.clone()));
    result
}

const CANONICAL_LOAD_DEPTH_LIMIT: usize = 24;

/// Deep, assumption-free canonical form for a term: every load resolves its
/// cached cell or canonicalizes its snapshot and pointer, at every depth,
/// including inside conditionals, folds, and pointer offsets. Two spellings
/// of the same value produced at different execution points canonicalize
/// identically whenever the difference is representational.
pub(super) fn canonicalize_atomic_loads_with_depth(
    term: &Bitvector32Term,
    depth: usize,
) -> Bitvector32Term {
    if depth >= CANONICAL_LOAD_DEPTH_LIMIT {
        return term.clone();
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(canonicalize_atomic_loads_with_depth(left, depth + 1)),
            Box::new(canonicalize_atomic_loads_with_depth(right, depth + 1)),
        )
    };
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            let canonical_pointer = canonicalize_pointer_loads(pointer, depth + 1);
            match memory.load(&canonical_pointer) {
                CExpressionOutcome::Value(CValue::Int32(value) | CValue::UInt8(value))
                    if &value != term =>
                {
                    canonicalize_atomic_loads_with_depth(&value, depth + 1)
                }
                _ => match memory.load(pointer) {
                    CExpressionOutcome::Value(CValue::Int32(value) | CValue::UInt8(value))
                        if &value != term =>
                    {
                        canonicalize_atomic_loads_with_depth(&value, depth + 1)
                    }
                    _ => Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(canonical_c_memory_for_pointer_load(
                            memory,
                            &canonical_pointer,
                        )),
                        Box::new(canonical_pointer),
                    ),
                },
            }
        }
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Multiply(left, right)
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Divide(left, right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Remainder(left, right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ShiftLeft(left, right)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ArithmeticShiftRight(left, right)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseAnd(left, right)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseOr(left, right)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseXor(left, right)
        }
        Bitvector32Term::BitwiseNot(value) => Bitvector32Term::BitwiseNot(Box::new(
            canonicalize_atomic_loads_with_depth(value, depth + 1),
        )),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: Box::new(
                condition_with_canonical_loads_with_depth(condition, depth + 1)
                    .unwrap_or_else(|| condition.as_ref().clone()),
            ),
            then_term: Box::new(canonicalize_atomic_loads_with_depth(then_term, depth + 1)),
            else_term: Box::new(canonicalize_atomic_loads_with_depth(else_term, depth + 1)),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::RangeFold {
            start: Box::new(canonicalize_atomic_loads_with_depth(start, depth + 1)),
            end: Box::new(canonicalize_atomic_loads_with_depth(end, depth + 1)),
            initial: Box::new(canonicalize_atomic_loads_with_depth(initial, depth + 1)),
            accumulator: *accumulator,
            item: *item,
            body: Box::new(canonicalize_atomic_loads_with_depth(body, depth + 1)),
        },
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| canonicalize_atomic_loads_with_depth(argument, depth + 1))
                    .collect(),
            }
        }
    }
}

/// Canonicalizes the loads inside a pointer's offset.
pub(super) fn canonicalize_pointer_loads(pointer: &Pointer, depth: usize) -> Pointer {
    fn canonical_offset(offset: &PointerOffsetTerm, depth: usize) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
            PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                canonical_offset(left, depth),
                canonical_offset(right, depth),
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
                canonicalize_atomic_loads_with_depth(value, depth),
                *byte_width,
            ),
        }
    }
    Pointer {
        block: pointer.block.clone(),
        offset: canonical_offset(&pointer.offset, depth),
    }
}

/// Compares two condition facts operandwise under memory-resolution
/// equality, so spellings that differ only in provably-irrelevant cached
/// cells compare equal.
pub(crate) fn c_condition_facts_equivalent_for_memory_resolution(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (Proposition::ConditionIs(left, left_value), Proposition::ConditionIs(right, right_value)) =
        (left, right)
    else {
        return false;
    };
    if left_value != right_value {
        return false;
    }
    let operands = match (left, right) {
        (
            ConditionTerm::Bitvector32SignedLessThan(a, b),
            ConditionTerm::Bitvector32SignedLessThan(c, d),
        )
        | (
            ConditionTerm::Bitvector32SignedLessEqual(a, b),
            ConditionTerm::Bitvector32SignedLessEqual(c, d),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterThan(a, b),
            ConditionTerm::Bitvector32SignedGreaterThan(c, d),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterEqual(a, b),
            ConditionTerm::Bitvector32SignedGreaterEqual(c, d),
        )
        | (ConditionTerm::Bitvector32Equal(a, b), ConditionTerm::Bitvector32Equal(c, d)) => {
            Some((a, b, c, d))
        }
        _ => None,
    };
    let Some((a, b, c, d)) = operands else {
        return false;
    };
    bitvector_terms_proven_equal_for_memory_resolution(a, c, assumptions)
        && bitvector_terms_proven_equal_for_memory_resolution(b, d, assumptions)
}

/// Exports each certified store as the condition fact its record proves:
/// loading the stored pointer from the post-store memory yields the stored
/// value. These are execution-certified equations usable by replay.
pub(crate) fn certified_store_equations(facts: &[ExecutionPureFact]) -> Vec<Proposition> {
    facts
        .iter()
        .filter_map(|fact| {
            let store = fact.certified_store_data()?;
            let value = match &store.value {
                CValue::Int32(term) | CValue::UInt8(term) => term.clone(),
                CValue::Void | CValue::Pointer(_) => return None,
            };
            Some(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(store.after.clone()),
                        Box::new(store.pointer.clone()),
                    )),
                    Box::new(value),
                ),
                true,
            ))
        })
        .collect()
}

pub(crate) fn certified_store_loadability_facts(facts: &[ExecutionPureFact]) -> Vec<Proposition> {
    facts
        .iter()
        .filter_map(|fact| {
            let store = fact.certified_store_data()?;
            let byte_width = match store.value {
                CValue::Void => return None,
                CValue::UInt8(_) => 1,
                CValue::Int32(_) | CValue::Pointer(_) => 4,
            };
            Some(Proposition::CMemoryLoadable {
                memory: store.after.clone(),
                base: store.pointer.clone(),
                bytes: Bitvector32Term::Constant(byte_width),
            })
        })
        .collect()
}

pub(crate) fn c_condition_fact_memories(fact: &Proposition) -> Vec<CMemory> {
    let Proposition::ConditionIs(condition, _) = fact else {
        return Vec::new();
    };
    let mut memories = Vec::new();
    collect_condition_memories(condition, &mut memories);
    memories
        .into_iter()
        .map(|memory| memory.as_ref().clone())
        .collect()
}

pub(crate) fn c_condition_fact_has_memory(fact: &Proposition) -> bool {
    fn bitvector_has_memory(term: &Bitvector32Term) -> bool {
        match term {
            Bitvector32Term::MemoryLoad(_, _) => true,
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
                bitvector_has_memory(left) || bitvector_has_memory(right)
            }
            Bitvector32Term::BitwiseNot(term) => bitvector_has_memory(term),
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => bitvector_has_memory(then_term) || bitvector_has_memory(else_term),
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                bitvector_has_memory(start)
                    || bitvector_has_memory(end)
                    || bitvector_has_memory(initial)
                    || bitvector_has_memory(body)
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                arguments.iter().any(bitvector_has_memory)
            }
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
        }
    }
    fn offset_has_memory(offset: &PointerOffsetTerm) -> bool {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                offset_has_memory(left) || offset_has_memory(right)
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => bitvector_has_memory(value),
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        }
    }
    let Proposition::ConditionIs(condition, _) = fact else {
        return false;
    };
    match condition {
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
            bitvector_has_memory(left) || bitvector_has_memory(right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            offset_has_memory(left) || offset_has_memory(right)
        }
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | ConditionTerm::PointerEqual(_, _) => false,
    }
}

fn collect_condition_memories(condition: &ConditionTerm, memories: &mut Vec<SharedCMemory>) {
    let mut collect_binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        collect_bitvector_memories(left, memories);
        collect_bitvector_memories(right, memories);
    };
    match condition {
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
            collect_binary(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | ConditionTerm::PointerEqual(_, _) => {}
    }
}

fn collect_pointer_offset_memories(offset: &PointerOffsetTerm, memories: &mut Vec<SharedCMemory>) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => collect_bitvector_memories(value, memories),
    }
}

fn collect_bitvector_memories(term: &Bitvector32Term, memories: &mut Vec<SharedCMemory>) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(memory, _) => {
            if !memories.contains(memory) {
                memories.push(memory.clone());
            }
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
            collect_bitvector_memories(left, memories);
            collect_bitvector_memories(right, memories);
        }
        Bitvector32Term::BitwiseNot(term) => collect_bitvector_memories(term, memories),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memories(condition, memories);
            collect_bitvector_memories(then_term, memories);
            collect_bitvector_memories(else_term, memories);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memories(start, memories);
            collect_bitvector_memories(end, memories);
            collect_bitvector_memories(initial, memories);
            collect_bitvector_memories(body, memories);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_memories(argument, memories);
            }
        }
    }
}

fn transport_framed_atomic_condition(
    condition: &ConditionTerm,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<ConditionTerm> {
    if crate::instrumentation::deadline_exceeded() {
        return None;
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        Some((
            transport_framed_atomic_bitvector(left, after, assumptions)?,
            transport_framed_atomic_bitvector(right, after, assumptions)?,
        ))
    };
    Some(match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_less_than(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_less_equal(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_greater_than(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_greater_equal(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::equal(left, right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_add_overflows(left, right)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_subtract_overflows(left, right)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_multiply_overflows(left, right)
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_divide_overflows(left, right)
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_shift_left_overflows(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            Pointer {
                block: left.block.clone(),
                offset: transport_framed_atomic_pointer_offset(&left.offset, after, assumptions)?,
            },
            Pointer {
                block: right.block.clone(),
                offset: transport_framed_atomic_pointer_offset(&right.offset, after, assumptions)?,
            },
        ),
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => return None,
    })
}

fn transport_framed_atomic_pointer_offset(
    offset: &PointerOffsetTerm,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<PointerOffsetTerm> {
    if crate::instrumentation::deadline_exceeded() {
        return None;
    }
    Some(match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
            *byte_width,
        ),
    })
}

fn transport_framed_atomic_bitvector(
    term: &Bitvector32Term,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Bitvector32Term> {
    if crate::instrumentation::deadline_exceeded() {
        return None;
    }
    Some(match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            let transported_pointer = Pointer {
                block: pointer.block.clone(),
                offset: transport_framed_atomic_pointer_offset(
                    &pointer.offset,
                    after,
                    assumptions,
                )?,
            };
            if memories_match_for_pointer_load(memory, after, pointer)
                || memory_materializes_atomic_load(after, memory, pointer)
                || assumptions.is_some_and(|(assumptions, direct)| {
                    if direct {
                        c_memory_load_is_directly_unchanged(memory, after, pointer, assumptions)
                    } else {
                        c_memory_load_is_unchanged(memory, after, pointer, assumptions)
                    }
                })
            {
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(after.clone()),
                    Box::new(transported_pointer),
                )
            } else {
                term.clone()
            }
        }
        Bitvector32Term::Add(left, right) => Bitvector32Term::Add(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::Subtract(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::Multiply(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Divide(left, right) => Bitvector32Term::Divide(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Remainder(left, right) => Bitvector32Term::Remainder(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::ShiftLeft(left, right) => Bitvector32Term::ShiftLeft(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            Bitvector32Term::ArithmeticShiftRight(
                Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
                Box::new(transport_framed_atomic_bitvector(
                    right,
                    after,
                    assumptions,
                )?),
            )
        }
        Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::BitwiseAnd(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::BitwiseOr(left, right) => Bitvector32Term::BitwiseOr(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::BitwiseXor(left, right) => Bitvector32Term::BitwiseXor(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::BitwiseNot(term) => Bitvector32Term::BitwiseNot(Box::new(
            transport_framed_atomic_bitvector(term, after, assumptions)?,
        )),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: Box::new(transport_framed_atomic_condition(
                condition,
                after,
                assumptions,
            )?),
            then_term: Box::new(transport_framed_atomic_bitvector(
                then_term,
                after,
                assumptions,
            )?),
            else_term: Box::new(transport_framed_atomic_bitvector(
                else_term,
                after,
                assumptions,
            )?),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::RangeFold {
            start: Box::new(transport_framed_atomic_bitvector(
                start,
                after,
                assumptions,
            )?),
            end: Box::new(transport_framed_atomic_bitvector(end, after, assumptions)?),
            initial: Box::new(transport_framed_atomic_bitvector(
                initial,
                after,
                assumptions,
            )?),
            accumulator: *accumulator,
            item: *item,
            body: Box::new(transport_framed_atomic_bitvector(body, after, assumptions)?),
        },
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| transport_framed_atomic_bitvector(argument, after, assumptions))
                    .collect::<Option<Vec<_>>>()?,
            }
        }
    })
}

pub(crate) fn c_pointer_offsets_proven_equal_for_effect(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    let left = normalize_exact_memory_loads_in_pointer_offset(left, assumptions, 0);
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    let right = normalize_exact_memory_loads_in_pointer_offset(right, assumptions, 0);
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    left == right
        || pointer_offsets_proven_equal_for_memory_resolution(&left, &right, assumptions)
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left), Box::new(right)),
            true,
        ))
}

pub(super) fn normalize_exact_memory_loads_in_pointer_offset(
    offset: &PointerOffsetTerm,
    assumptions: &PureFactContext,
    depth: usize,
) -> PointerOffsetTerm {
    if depth >= 64 || crate::instrumentation::deadline_exceeded() {
        return offset.clone();
    }
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            normalize_exact_memory_loads_in_pointer_offset(left, assumptions, depth + 1),
            normalize_exact_memory_loads_in_pointer_offset(right, assumptions, depth + 1),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            normalize_exact_memory_loads_in_bitvector(value, assumptions, depth + 1),
            *byte_width,
        ),
    }
}

pub(super) fn normalize_exact_memory_loads_in_bitvector(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
    depth: usize,
) -> Bitvector32Term {
    if depth >= 64 || crate::instrumentation::deadline_exceeded() {
        return term.clone();
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            normalize_exact_memory_loads_in_bitvector(left, assumptions, depth + 1),
            normalize_exact_memory_loads_in_bitvector(right, assumptions, depth + 1),
        )
    };
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::multiply(left, right)
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::divide(left, right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::remainder(left, right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::shift_left(left, right)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::arithmetic_shift_right(left, right)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::bitwise_and(left, right)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::bitwise_or(left, right)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::bitwise_xor(left, right)
        }
        Bitvector32Term::BitwiseNot(value) => Bitvector32Term::bitwise_not(
            normalize_exact_memory_loads_in_bitvector(value, assumptions, depth + 1),
        ),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: condition.clone(),
            then_term: Box::new(normalize_exact_memory_loads_in_bitvector(
                then_term,
                assumptions,
                depth + 1,
            )),
            else_term: Box::new(normalize_exact_memory_loads_in_bitvector(
                else_term,
                assumptions,
                depth + 1,
            )),
        },
        Bitvector32Term::RangeFold { .. } => term.clone(),
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        normalize_exact_memory_loads_in_bitvector(argument, assumptions, depth + 1)
                    })
                    .collect(),
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            if let Some(CValue::Int32(value)) = memory.known_value(pointer)
                && &value != term
            {
                return normalize_exact_memory_loads_in_bitvector(&value, assumptions, depth + 1);
            }
            let Some(value) = assumptions.resolve_memory_load_term(term) else {
                return term.clone();
            };
            normalize_exact_memory_loads_in_bitvector(&value, assumptions, depth + 1)
        }
    }
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_stops_at_the_verification_deadline() {
    let offset = PointerOffsetTerm::Constant(0);
    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(!c_pointer_offsets_proven_equal_for_effect(
            &offset,
            &offset,
            &PureFactContext::new(),
        ));
    });
}

/// Canonicalizes the loads inside a binary condition so spellings differing
/// only in redundant cached cells compare and prove identically.
pub(super) fn condition_with_canonical_loads(condition: &ConditionTerm) -> Option<ConditionTerm> {
    condition_with_canonical_loads_with_depth(condition, 0)
}

fn condition_with_canonical_loads_with_depth(
    condition: &ConditionTerm,
    depth: usize,
) -> Option<ConditionTerm> {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(canonicalize_atomic_loads_with_depth(left, depth)),
            Box::new(canonicalize_atomic_loads_with_depth(right, depth)),
        )
    };
    Some(match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32Equal(left, right)
        }
        _ => return None,
    })
}

/// Public form of canonical-load rewriting for condition facts: spellings
/// that differ only in redundant cached cells canonicalize identically.
pub(crate) fn c_condition_fact_with_canonical_loads(fact: &Proposition) -> Proposition {
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    match condition_with_canonical_loads(condition) {
        Some(canonical) => Proposition::ConditionIs(canonical, *value),
        None => fact.clone(),
    }
}
