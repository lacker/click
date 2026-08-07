use super::prelude::*;

pub fn int32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int32(bits.into())
}

pub fn uint8(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt8(bits.into())
}

pub(crate) fn canonical_c_memory_for_pointer_load(memory: &CMemory, pointer: &Pointer) -> CMemory {
    canonical_memory_for_pointer_load(memory, pointer)
}

/// Checks whether two resource spellings denote the same resource using only
/// exact facts and the bounded memory-resolution relation. This is intended
/// for certificate replay: it does not search for containment or separation.
pub(crate) fn c_resources_directly_match(
    left: &CResource,
    right: &CResource,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    let values_match = |left: &CValue, right: &CValue| match (left, right) {
        (CValue::Void, CValue::Void) => true,
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        _ => false,
    };
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            left == right
                || (bitvectors_match_for_resource_replay(left.start(), right.start(), assumptions)
                    && bitvectors_match_for_resource_replay(left.end(), right.end(), assumptions)
                    && pointers_match_for_resource_replay(left.base(), right.base(), assumptions))
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
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    if assumptions.bitvector_terms_equal_from_facts(left, right) {
        return true;
    }
    // Resource endpoints are usually the same arithmetic shape with leaf
    // loads related by explicit field equalities. Check that bounded
    // structural relation before invoking the broader memory-DAG search.
    if bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions) {
        return true;
    }
    if explicit_atomic_equality_from_memory_derivations(left, right, assumptions) {
        return true;
    }
    let transported_matches = |term: &Bitvector32Term, target: &Bitvector32Term| {
        let mut memories = Vec::new();
        collect_bitvector_memories(target, &mut memories);
        memories.into_iter().any(|memory| {
            transport_framed_atomic_bitvector(term, &memory, Some((assumptions, false)))
                .is_some_and(|transported| {
                    bitvector_terms_proven_equal_for_memory_resolution(
                        &transported,
                        target,
                        assumptions,
                    )
                })
        })
    };
    transported_matches(left, right) || transported_matches(right, left)
}

fn pointer_offsets_match_from_memory_derivations(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
) -> bool {
    if pointer_offsets_match_from_memory_derivations(left, right, assumptions) {
        return true;
    }
    if c_pointer_offsets_proven_equal_for_effect(left, right, assumptions) {
        return true;
    }
    let transported_matches = |offset: &PointerOffsetTerm, target: &PointerOffsetTerm| {
        let mut memories = Vec::new();
        collect_pointer_offset_memories(target, &mut memories);
        memories.into_iter().any(|memory| {
            transport_framed_atomic_pointer_offset(offset, &memory, Some((assumptions, false)))
                .is_some_and(|transported| {
                    c_pointer_offsets_proven_equal_for_effect(&transported, target, assumptions)
                })
        })
    };
    transported_matches(left, right) || transported_matches(right, left)
}

fn pointers_match_for_resource_replay(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    left == right
        || (left.block == right.block
            && pointer_offsets_match_for_resource_replay(&left.offset, &right.offset, assumptions))
        || pointers_proven_equal_for_memory_resolution(left, right, assumptions)
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
    for (pointer, value) in cells {
        let key = canonicalize_pointer_loads(&pointer, 0);
        let value = match value {
            CValue::Void => CValue::Void,
            CValue::Int32(term) => CValue::Int32(canonicalize_atomic_loads(&term)),
            CValue::UInt8(term) => CValue::UInt8(canonicalize_atomic_loads(&term)),
            CValue::Pointer(pointer) => CValue::Pointer(canonicalize_pointer_loads(&pointer, 0)),
        };
        canonical.cells.insert(key, value);
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
    assumptions: &Assumptions,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    if memories_match_for_pointer_load(before, after, pointer) {
        return true;
    }
    if canonical_memory_for_pointer_load(before, pointer)
        == canonical_memory_for_pointer_load(after, pointer)
    {
        return true;
    }
    // Small field-update snapshots usually differ at only one or two cells.
    // Compare those directly before paying for a derivation-DAG walk; large
    // snapshots retain the DAG-first order so they do not scan a broad cell
    // set unless the named history cannot answer.
    let small_snapshot_pair = before.cells.len() <= 8 && after.cells.len() <= 8;
    if small_snapshot_pair
        && memories_match_for_pointer_load_under_assumptions(before, after, pointer, assumptions)
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
    if with_extended_dag_bridging(|| {
        load_unchanged_along_memory_derivations(before, after, pointer, assumptions)
    }) {
        return true;
    }
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    if !small_snapshot_pair
        && memories_match_for_pointer_load_under_assumptions(before, after, pointer, assumptions)
    {
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
) -> bool {
    const MEMORY_DERIVATION_HOP_LIMIT: usize = 64;
    let mut current = from.clone();
    for _ in 0..MEMORY_DERIVATION_HOP_LIMIT {
        if current == *target {
            return true;
        }
        // Ids strictly decrease along `base`, so within one arena an id at
        // or below the target's cannot reach it and the walk can stop early.
        let (current_arena, current_id) = current.arena_id();
        let (target_arena, target_id) = target.arena_id();
        if current_arena == target_arena && current_id <= target_id {
            return false;
        }
        let Some(derivation) = current.derivation() else {
            return false;
        };
        let crossable = match derivation.as_ref() {
            CMemoryDerivation::Store { pointer: write, .. } => {
                write.blocks_proven_distinct(pointer)
                    || pointer_offsets_with_common_base_proven_distinct(write, pointer, assumptions)
                    || pointers_proven_distinct_for_memory_resolution(write, pointer, assumptions)
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
        };
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
) -> bool {
    // Real allocator/copy/install/free paths routinely cross more than eight
    // individually certified effects. Keep the search bounded, but leave
    // enough room for an ordinary multi-call helper rather than treating it
    // as an unrelated write merely because its proof is longer.
    const EFFECT_CHAIN_HOP_LIMIT: usize = 8;
    let mut steps = Vec::new();
    for proposition in &assumptions.prop_facts {
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
    // every junction. Each effect is traversed at most once.
    let joins = |expected: &CMemory, actual: &CMemory| {
        memory_matches_effect_summary_endpoint(expected, actual, pointer)
    };
    let mut used = vec![false; steps.len()];
    let mut frontier: Vec<&CMemory> = vec![before];
    for _ in 0..EFFECT_CHAIN_HOP_LIMIT {
        let mut next = Vec::new();
        for current in frontier {
            for (index, (step_before, step_after)) in steps.iter().enumerate() {
                if used[index] {
                    continue;
                }
                for (from, to) in [(step_before, step_after), (step_after, step_before)] {
                    if joins(from, current) {
                        if joins(to, after) {
                            return true;
                        }
                        used[index] = true;
                        next.push(*to);
                        break;
                    }
                }
            }
        }
        if next.is_empty() {
            return false;
        }
        frontier = next;
    }
    false
}

/// Bounded search for any chain of recorded effects connecting two memory
/// snapshots, regardless of what the effects wrote. Used for properties
/// that survive writes, such as loadability of a still-present range.
pub(crate) fn c_memories_connected_by_effects(
    before: &CMemory,
    after: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    const EFFECT_CHAIN_HOP_LIMIT: usize = 8;
    let mut steps = Vec::new();
    for proposition in &assumptions.prop_facts {
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
    for _ in 0..EFFECT_CHAIN_HOP_LIMIT {
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
        if next.is_empty() {
            return false;
        }
        frontier = next;
    }
    false
}

fn c_memory_load_is_directly_unchanged(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, false)))
}

pub(crate) fn prove_c_condition_fact_direct_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
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
    assumptions: Option<(&Assumptions, bool)>,
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
fn canonicalize_atomic_loads_with_depth(term: &Bitvector32Term, depth: usize) -> Bitvector32Term {
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
    assumptions: &Assumptions,
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

fn collect_condition_memories(condition: &ConditionTerm, memories: &mut Vec<CMemory>) {
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

fn collect_pointer_offset_memories(offset: &PointerOffsetTerm, memories: &mut Vec<CMemory>) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => collect_bitvector_memories(value, memories),
    }
}

fn collect_bitvector_memories(term: &Bitvector32Term, memories: &mut Vec<CMemory>) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(memory, _) => {
            if !memories.contains(memory) {
                memories.push(memory.as_ref().clone());
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
    assumptions: Option<(&Assumptions, bool)>,
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
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | ConditionTerm::Bitvector32SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _) => return None,
    })
}

fn transport_framed_atomic_pointer_offset(
    offset: &PointerOffsetTerm,
    after: &CMemory,
    assumptions: Option<(&Assumptions, bool)>,
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
    assumptions: Option<(&Assumptions, bool)>,
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
    assumptions: &Assumptions,
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
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left), Box::new(right)),
            true,
        ))
}

pub(super) fn normalize_exact_memory_loads_in_pointer_offset(
    offset: &PointerOffsetTerm,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
            &Assumptions::new(),
        ));
    });
}

#[derive(Clone, Debug)]
pub struct CLoopPreservationContext {
    state: CState,
    loop_entry_state: CState,
    pure_facts: Vec<Proposition>,
}

impl CLoopPreservationContext {
    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn loop_entry_state(&self) -> &CState {
        &self.loop_entry_state
    }

    pub fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }
}

#[allow(clippy::too_many_arguments)]
pub fn c_loop_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &Assumptions,
) -> Result<Vec<CLoopPreservationContext>, String> {
    let mut budget = ExecutionBudget::default();
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(loop_entry_state, &mut existing_variables);
    collect_c_expression_bitvector_variables(condition, &mut existing_variables);
    for check in invariant_checks {
        collect_spec_proposition_bitvector_variables(check.proposition(), &mut existing_variables);
    }
    for check in effect_checks {
        collect_loop_effect_bitvector_variables(check.effect(), &mut existing_variables);
    }
    collect_c_statement_bitvector_variables(body, &mut existing_variables);
    collect_assumption_variables(assumptions, &mut existing_variables);
    let mut variables = VerificationVariableGenerator::fresh_for(
        budget.next_verification_variable,
        existing_variables,
    );
    let (top_state, whole_loop_effect_summaries) = prepare_loop_top_state(
        loop_entry_state,
        effect_checks,
        body,
        assumptions,
        &mut budget,
        &mut variables,
    )
    .map_err(|error| format!("could not prepare loop effects: {error:?}"))?;
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let mut contexts = Vec::new();
    for (invariant_facts, invariant_obligations) in assume_invariant_checks(
        &top_state,
        loop_entry_state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        &mut budget,
    )
    .map_err(|error| format!("could not assume loop invariants: {error:?}"))?
    {
        for (facts, obligations) in assume_condition_truthiness(
            &top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            &mut budget,
        )
        .map_err(|error| format!("could not assume the loop condition: {error:?}"))?
        {
            let context_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
            if let Some(obligation) = obligations
                .iter()
                .find(|obligation| !context_assumptions.proves(obligation.proposition()))
            {
                return Err(format!(
                    "missing loop-head prerequisite{}: {:?}",
                    obligation
                        .context()
                        .map(|context| format!(" ({context})"))
                        .unwrap_or_default(),
                    obligation.proposition()
                ));
            }
            let mut pure_facts = facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            pure_facts.sort();
            pure_facts.dedup();
            contexts.push(CLoopPreservationContext {
                state: top_state.clone(),
                loop_entry_state: top_state.clone(),
                pure_facts,
            });
        }
    }
    Ok(contexts)
}

pub fn c_loop_invariants_hold_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<(), String> {
    let obligations = c_loop_invariant_obligations_at_back_edge(
        state,
        iteration_entry_state,
        invariant_checks,
        assumptions,
    )?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

pub fn c_loop_invariant_obligations_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        iteration_entry_state,
        invariant_checks,
        InvariantPhase::Preservation,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower back-edge invariants: {error:?}"))
}

pub fn c_loop_invariants_hold_at_back_edge_using(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<(), String> {
    verify_invariant_checks_at_back_edge_using(
        state,
        iteration_entry_state,
        invariant_checks,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not replay invariant closer: {error}"))
}

pub fn c_loop_invariant_obligations_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower entry invariants: {error:?}"))
}

pub fn c_loop_effects_hold_at_back_edge(
    iteration_entry_state: &CState,
    state: &CState,
    effect_checks: &[CLoopEffectCheck],
    pure_facts: &[Proposition],
    assumptions: &Assumptions,
) -> Result<(), String> {
    let execution_facts = pure_facts
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let obligations = collect_loop_effect_check_obligations(
        iteration_entry_state,
        state,
        effect_checks,
        &execution_facts,
        &[],
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower back-edge effects: {error:?}"))?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing loop effect fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

pub fn c_loop_invariants_hold_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<(), String> {
    let obligations = collect_invariant_check_obligations(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower entry invariants: {error:?}"))?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

/// Builds a branch-independent symbolic state for a proof join.
///
/// Locals that still equal a stable function-entry value retain that identity.
/// Other scalar and pointer locals become fresh symbolic values, and non-stack
/// memory is forgotten. Exported facts and resources constrain those values at
/// the abstract frontier.
pub fn abstract_c_state_for_join(
    state: &CState,
    stable_entry_locals: &BTreeMap<String, CValue>,
) -> Result<CState, String> {
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing_variables);
    for value in stable_entry_locals.values() {
        collect_c_value_bitvector_variables(value, &mut existing_variables);
    }
    let mut variables = VerificationVariableGenerator::fresh_for(1_000_000, existing_variables);
    let mut abstract_state = state.clone();
    let mut abstract_objects = Vec::new();
    let mut preserved_blocks = BTreeSet::new();

    for (name, binding) in &state.locals.bindings {
        let CLocalBinding::Object { value, c_type } = binding else {
            continue;
        };
        let abstract_value = if stable_entry_locals.get(name) == Some(value) {
            value.clone()
        } else {
            match c_type {
                CType::Void => continue,
                CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
                CType::UInt8 => uint8(Bitvector32Term::Variable(variables.next())),
                CType::Int32Pointer | CType::UInt8Pointer => {
                    CValue::Pointer(Pointer::symbolic(variables.next()))
                }
                CType::Int32Array(_) | CType::UInt8Array(_) => {
                    unreachable!("array objects use CLocalBinding::ArrayObject")
                }
            }
        };
        preserved_blocks.insert(CMemory::local_pointer(name).block);
        abstract_objects.push((name.clone(), abstract_value, *c_type));
    }

    abstract_state.memory = abstract_state
        .memory
        .with_loop_memory_havoc(variables.next(), &preserved_blocks);
    for (name, value, c_type) in abstract_objects {
        sync_stack_local(&mut abstract_state, &name, &value);
        abstract_state.locals.set_typed(name, value, c_type);
    }
    abstract_state.resources = ResourceContext::new();
    Ok(abstract_state)
}

pub fn c_variable(name: impl Into<String>) -> CExpression {
    CExpression::Variable(name.into())
}

pub fn c_addr_of(name: impl Into<String>) -> CExpression {
    CExpression::AddressOf(Box::new(c_variable(name)))
}

pub fn c_pointer_offset_bytes(pointer: CExpression, bytes: u32) -> CExpression {
    if bytes == 0 {
        pointer
    } else {
        CExpression::PointerOffsetBytes {
            pointer: Box::new(pointer),
            bytes,
        }
    }
}

pub fn c_int32_literal(value: u32) -> CExpression {
    CExpression::Value(int32(Bitvector32Term::Constant(value)))
}

pub fn c_uint8_literal(value: u8) -> CExpression {
    CExpression::Value(uint8(Bitvector32Term::Constant(u32::from(value))))
}

pub fn c_pointer_value(pointer: Pointer) -> CExpression {
    CExpression::Value(CValue::Pointer(pointer))
}

pub fn c_less_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessThan(Box::new(left), Box::new(right))
}

pub fn c_less_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessEqual(Box::new(left), Box::new(right))
}

pub fn c_greater_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterThan(Box::new(left), Box::new(right))
}

pub fn c_greater_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterEqual(Box::new(left), Box::new(right))
}

pub fn c_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Equal(Box::new(left), Box::new(right))
}

pub fn c_not_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::NotEqual(Box::new(left), Box::new(right))
}

pub fn c_not(expression: CExpression) -> CExpression {
    CExpression::Not(Box::new(expression))
}

pub fn c_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::And(Box::new(left), Box::new(right))
}

pub fn c_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Or(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Add(Box::new(left), Box::new(right))
}

pub fn c_subtract(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Subtract(Box::new(left), Box::new(right))
}

pub fn c_multiply(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Multiply(Box::new(left), Box::new(right))
}

pub fn c_divide(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Divide(Box::new(left), Box::new(right))
}

pub fn c_remainder(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Remainder(Box::new(left), Box::new(right))
}

pub fn c_shift_left(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftLeft(Box::new(left), Box::new(right))
}

pub fn c_shift_right(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftRight(Box::new(left), Box::new(right))
}

pub fn c_bitwise_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseAnd(Box::new(left), Box::new(right))
}

pub fn c_bitwise_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseOr(Box::new(left), Box::new(right))
}

pub fn c_bitwise_xor(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseXor(Box::new(left), Box::new(right))
}

pub fn c_bitwise_not(expression: CExpression) -> CExpression {
    CExpression::BitwiseNot(Box::new(expression))
}

pub fn c_load(pointer: CExpression) -> CExpression {
    CExpression::Load(Box::new(pointer))
}

pub fn c_typed_load(pointer: CExpression, value_type: CType) -> CExpression {
    CExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
    }
}

pub fn c_index(base: CExpression, index: CExpression) -> CExpression {
    CExpression::Index(Box::new(base), Box::new(index))
}

pub fn c_assign(name: impl Into<String>, expression: CExpression) -> CStatement {
    CStatement::Assign {
        name: name.into(),
        expression,
    }
}

pub fn c_call_assign(
    target: impl Into<String>,
    function_name: impl Into<String>,
    arguments: Vec<CExpression>,
) -> CStatement {
    CStatement::CallAssign {
        target: target.into(),
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_call(function_name: impl Into<String>, arguments: Vec<CExpression>) -> CStatement {
    CStatement::Call {
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_heap_allocate(target: impl Into<String>, bytes: u32) -> CStatement {
    c_heap_allocate_sized(target, c_int32_literal(bytes))
}

pub fn c_heap_allocate_sized(target: impl Into<String>, bytes: CExpression) -> CStatement {
    CStatement::HeapAllocate {
        target: target.into(),
        bytes,
    }
}

pub fn c_heap_free(pointer: CExpression) -> CStatement {
    CStatement::HeapFree { pointer }
}

pub fn c_declare(name: impl Into<String>, c_type: CType) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
    }
}

pub fn c_assert(condition: CExpression) -> CStatement {
    CStatement::Assert {
        condition,
        label: None,
    }
}

pub fn c_labeled_assert(condition: CExpression, label: impl Into<String>) -> CStatement {
    CStatement::Assert {
        condition,
        label: Some(label.into()),
    }
}

pub fn c_seq(first: CStatement, second: CStatement) -> CStatement {
    CStatement::Seq(Box::new(first), Box::new(second))
}

pub fn c_skip() -> CStatement {
    CStatement::Skip
}

pub fn c_return(expression: CExpression) -> CStatement {
    CStatement::Return(expression)
}

pub fn c_void_value() -> CExpression {
    CExpression::Value(CValue::Void)
}

pub fn c_store(pointer: CExpression, value: CExpression) -> CStatement {
    CStatement::Store { pointer, value }
}

pub fn c_typed_store(pointer: CExpression, value: CExpression, value_type: CType) -> CStatement {
    CStatement::TypedStore {
        pointer,
        value,
        value_type,
    }
}

pub fn c_if(
    condition: CExpression,
    then_branch: CStatement,
    else_branch: CStatement,
) -> CStatement {
    CStatement::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_while(
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(condition, invariant, Vec::new(), Vec::new(), body)
}

pub fn c_while_with_invariant_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        invariant_checks,
        Vec::new(),
        body,
    )
}

pub fn c_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body: Box::new(body),
    }
}

pub fn c_parameter(name: impl Into<String>, c_type: CType) -> CParameter {
    CParameter::new(name, c_type)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    parameters: Vec<CParameter>,
    body: CStatement,
) -> CFunction {
    CFunction::new(return_type, name, parameters, body)
}

pub fn c_function_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Option<CState> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    bind_c_function_arguments(caller_state, function, &values)
}

/// Produces the exact callee entry state used by contract verification.
///
/// Composite requirements normally use their canonical contained resources.
/// When proof replay has explicitly observed or unfolded part of a recursive
/// resource, independent certification preserves that equivalent spelling so
/// both executions use the same boundary state.
pub fn c_function_contract_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
) -> Result<CState, String> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| "contract entry arguments must be concrete symbolic values".to_string())?;
    let mut budget = ExecutionBudget::default();
    match prepare_function_contract_entry_state_with_values(
        caller_state,
        function,
        &values,
        assumptions,
        &mut budget,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(format!("could not prepare contract resources: {error:?}")),
        Err(limit) => Err(format!(
            "contract resource preparation hit execution limit {limit:?}"
        )),
    }
}

pub fn c_function_outcome_from_statement_outcome(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    function_outcome_from_body(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
        None,
    )
}

pub fn c_function_specification(
    state: CState,
    arguments: Vec<CExpression>,
    requires: Vec<Proposition>,
    outcome: CFunctionOutcome,
) -> CFunctionSpecification {
    CFunctionSpecification::new(state, arguments, requires, outcome)
}

pub fn proposition_and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And(Box::new(left), Box::new(right))
}

pub fn proposition_and_all(mut propositions: Vec<Proposition>) -> Proposition {
    let Some(first) = propositions.pop() else {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    };

    propositions
        .into_iter()
        .rev()
        .fold(first, |right, left| proposition_and(left, right))
}

/// Expands C expression definedness into the exact pure proposition under
/// which evaluation reaches a value rather than undefined behavior.
pub fn c_expression_definedness_proposition(
    state: &CState,
    expression: &CExpression,
) -> Result<Proposition, ExecutionLimit> {
    let paths = evaluate_c_expression_paths(
        state,
        expression,
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )?;
    let mut normal_paths = paths.into_iter().filter_map(|path| {
        if !matches!(path.outcome, CExpressionOutcome::Value(_)) {
            return None;
        }
        Some(proposition_and_all(
            path.facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .chain(
                    path.obligations
                        .into_iter()
                        .map(|obligation| obligation.proposition().clone()),
                )
                .collect(),
        ))
    });
    let Some(first) = normal_paths.next() else {
        return Ok(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
    };
    Ok(normal_paths.fold(first, |left, right| {
        Proposition::Or(Box::new(left), Box::new(right))
    }))
}

pub fn substitute_int32_variable_in_proposition(
    proposition: &Proposition,
    variable: Variable,
    value: Bitvector32Term,
) -> Proposition {
    substitute_bitvector_variable_in_proposition(proposition, variable, &value)
}

/// Chooses a variable identity absent from both the free variables and logical
/// binders of the supplied propositions.
pub fn fresh_int32_variable_for_propositions(propositions: &[Proposition]) -> Variable {
    let mut reserved = BTreeSet::new();
    for proposition in propositions {
        collect_proposition_bitvector_variables(proposition, &mut reserved);
        collect_proposition_bound_variables(proposition, &mut reserved);
    }
    VerificationVariableGenerator::fresh_for(0, reserved).next()
}

pub fn c_max_body() -> CStatement {
    c_if(
        c_less_than(c_variable("a"), c_variable("b")),
        c_return(c_variable("b")),
        c_return(c_variable("a")),
    )
}

pub fn c_max_function() -> CFunction {
    c_function(
        CType::Int32,
        "max",
        vec![
            c_parameter("a", CType::Int32),
            c_parameter("b", CType::Int32),
        ],
        c_max_body(),
    )
}

pub fn c_max_environment(a: CValue, b: CValue) -> CLocalEnvironment {
    CLocalEnvironment::new().with("a", a).with("b", b)
}

pub fn c_max_state(a: CValue, b: CValue) -> CState {
    CState::new().with_local("a", a).with_local("b", b)
}

pub fn c_max_lt_condition(a: Bitvector32Term, b: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a, b)
}

pub fn prove_c_expression_evaluation(state: CState, expression: CExpression) -> Option<Theorem> {
    let outcome = evaluate_c_expression(
        &state,
        &expression,
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )?;
    Some(Theorem::new(Proposition::CExpressionEvaluates {
        state,
        expression,
        outcome,
    }))
}

pub fn prove_symbolic_c_condition_evaluation(
    state: CState,
    condition: CExpression,
    assumptions: Assumptions,
) -> SymbolicCConditionEvaluation {
    let mut budget = ExecutionBudget::default();
    let expression_paths =
        match evaluate_c_expression_paths(&state, &condition, &assumptions, &mut budget) {
            Ok(paths) => paths,
            Err(limit) => {
                return SymbolicCConditionEvaluation {
                    paths: Vec::new(),
                    limit: Some(limit),
                };
            }
        };
    let mut outcomes = Vec::new();
    for path in expression_paths {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                outcomes.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, &assumptions)
                        .into_iter()
                        .map(|path| {
                            (
                                CConditionOutcome::Value(path.is_true),
                                path.facts,
                                path.obligations,
                            )
                        }),
                );
            }
            CExpressionOutcome::UndefinedBehavior(kind) => outcomes.push((
                CConditionOutcome::UndefinedBehavior(kind),
                path.facts,
                path.obligations,
            )),
            CExpressionOutcome::RuntimeError(error) => outcomes.push((
                CConditionOutcome::RuntimeError(error),
                path.facts,
                path.obligations,
            )),
        }
    }
    let paths = outcomes
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let facts = public_execution_pure_facts(&facts);
            let proposition = Proposition::CConditionEvaluates {
                state: state.clone(),
                condition: condition.clone(),
                outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &obligations,
            ));
            SymbolicCConditionEvaluationPath {
                facts,
                obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCConditionEvaluation { paths, limit: None }
}

pub fn prove_c_statement_execution(state: CState, statement: CStatement) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, Assumptions::new())
}

pub fn prove_c_statement_execution_under_assumptions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_execution_paths(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let paths = match execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = if execution_semantics == CExecutionSemantics::EXECUTE_BODIES {
                Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement: statement.clone(),
                    outcome: path.outcome,
                }
            } else {
                Proposition::CStatementVerifies {
                    state: state.clone(),
                    statement: statement.clone(),
                    outcome: path.outcome,
                }
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
    )
    .0
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::default();
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        &mut budget,
    )
}

fn statement_verification_variables(
    lower_bound: u64,
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
) -> VerificationVariableGenerator {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing);
    collect_c_statement_bitvector_variables(statement, &mut existing);
    collect_assumption_variables(assumptions, &mut existing);
    collect_execution_environment_variables(environment, &mut existing);
    VerificationVariableGenerator::fresh_for(lower_bound, existing)
}

pub(crate) fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut variables = statement_verification_variables(
        budget.next_verification_variable,
        &state,
        &statement,
        &assumptions,
        &environment,
    );
    let execution = execute_c_statement_verification_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        budget,
        &mut variables,
    );
    budget.next_verification_variable = budget.next_verification_variable.max(variables.next);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

#[cfg(test)]
pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::default();
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
        state,
        statement,
        assumptions,
        environment,
        initialization_proven,
        preservation_proven,
        &mut budget,
    )
}

pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
    } = &statement
    else {
        return (
            SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
            None,
        );
    };
    let mut variables = statement_verification_variables(
        budget.next_verification_variable,
        &state,
        &statement,
        &assumptions,
        &environment,
    );
    let execution = execute_c_while_exit_paths_with_proven_phases(
        &state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
        &assumptions,
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        initialization_proven,
        preservation_proven,
        budget,
        &mut variables,
    );
    budget.next_verification_variable = budget.next_verification_variable.max(variables.next);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

fn symbolic_c_statement_execution_with_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    paths: Vec<CStatementExecutionPath>,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let loop_rule = (matches!(statement, CStatement::While { .. })
        && paths.iter().all(|path| {
            matches!(
                path.outcome,
                CStatementOutcome::Normal(_) | CStatementOutcome::VerificationDiverges
            ) && path.obligations.iter().all(ProofObligation::is_assumable)
        }))
    .then(|| CVerifiedLoopRule {
        symbolic_entry_state: state.clone(),
        loop_statement: statement.clone(),
        required_assumptions: assumptions.clone(),
        paths: paths.clone(),
        composite_resource_definitions: Vec::new(),
    });
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CStatementVerifies {
                state: state.clone(),
                statement: statement.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    (SymbolicCExecution { paths, limit: None }, loop_rule)
}

pub fn prove_symbolic_c_function_execution(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_function_execution_paths(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let paths = match execute_c_function_paths_with_contract_resources(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
        prepare_contract_resources,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = if execution_semantics == CExecutionSemantics::EXECUTE_BODIES {
                Proposition::CFunctionExecutes {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: path.outcome,
                }
            } else {
                Proposition::CFunctionVerifies {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: path.outcome,
                }
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_function_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_verification_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

/// Verifies an exact function body from its declared contract-entry resources.
///
/// Unlike ordinary proof replay, this canonicalizes composite requirements
/// before body execution. It is the independent execution used to certify
/// opaque contract claims.
pub fn prove_symbolic_c_function_contract_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
        true,
    )
}

/// Produces the only execution frontier accepted for opaque contract
/// certification.
///
/// The initial assumptions are derived inside the kernel solely from the
/// function's exact contract and resource entry state. Callers cannot inject
/// additional hypotheses.
pub fn prove_c_function_contract_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CFunctionContractExecution {
    let selection_assumptions =
        assumptions_with_propositions(&Assumptions::new(), &derived_entry_facts);
    let Some(base_assumptions) = c_function_contract_certification_assumptions(
        &state,
        &function,
        &arguments,
        Assumptions::new(),
        &selection_assumptions,
    ) else {
        return CFunctionContractExecution {
            execution: SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
        };
    };
    let Some(resource_condition_cases) =
        contract_resource_condition_cases(&state, &function, &arguments, &base_assumptions)
    else {
        return CFunctionContractExecution {
            execution: SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
        };
    };
    let mut combined_paths = Vec::new();
    for case_facts in resource_condition_cases {
        let case_seed = assumptions_with_propositions(&Assumptions::new(), &case_facts);
        let Some(mut assumptions) = c_function_contract_certification_assumptions(
            &state,
            &function,
            &arguments,
            case_seed,
            &selection_assumptions,
        ) else {
            return CFunctionContractExecution {
                execution: SymbolicCExecution {
                    paths: Vec::new(),
                    limit: None,
                },
            };
        };
        let Some(mut entry_state) = c_function_entry_state(&state, &function, &arguments) else {
            return CFunctionContractExecution {
                execution: SymbolicCExecution {
                    paths: Vec::new(),
                    limit: None,
                },
            };
        };
        let has_recursive_resources = function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
        if !has_recursive_resources {
            let Some(entry_resources) = expand_all_composite_resource_facts(
                entry_state.resources(),
                function.composite_resource_definitions(),
                entry_state.memory(),
                &assumptions,
            ) else {
                return CFunctionContractExecution {
                    execution: SymbolicCExecution {
                        paths: Vec::new(),
                        limit: None,
                    },
                };
            };
            entry_state.resources = entry_resources.clone();
            for fact in &derived_entry_facts {
                if certification_proves_proposition(&assumptions, fact)
                    || resources_certify_loadability(
                        &entry_state,
                        &entry_resources,
                        fact,
                        &assumptions,
                    )
                {
                    assumptions = assumptions.assume_proposition(fact.clone());
                }
            }
        } else {
            // The caller state already contains the proof-directed
            // recursive projections certified above. Preserve that
            // targeted boundary; globally expanding it would erase child
            // composites and expose unrelated recursive branches.
            let mut entry_resources = entry_state.resources().clone();
            for fact in &derived_entry_facts {
                if assumptions.proves_exact(fact) {
                    assumptions = assumptions.assume_proposition(fact.clone());
                    continue;
                }
                if let Proposition::CMemoryLoadable { base, bytes, .. } = &fact
                    && let Some(bytes) = bytes.as_const()
                {
                    let projected = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(1),
                    ));
                    if let Some(exposed) = expose_composite_resource_fact(
                        &entry_resources,
                        &projected,
                        function.composite_resource_definitions(),
                        entry_state.memory(),
                        &assumptions,
                    ) {
                        entry_resources = exposed.unchecked_with_fact(projected);
                        assumptions = assumptions.assume_proposition(fact.clone());
                        continue;
                    }
                    if resource_context_has_structural_read(
                        &entry_resources,
                        base,
                        bytes,
                        &assumptions,
                    ) {
                        entry_resources = entry_resources.unchecked_with_fact(projected);
                        assumptions = assumptions.assume_proposition(fact.clone());
                        continue;
                    }
                }
                if resources_certify_loadability(&entry_state, &entry_resources, fact, &assumptions)
                {
                    if let Proposition::CMemoryLoadable { base, .. } = &fact {
                        entry_resources = entry_resources.unchecked_with_fact(
                            CResourceFact::view_memory(CMemoryRange::new(
                                base.clone(),
                                Bitvector32Term::Constant(0),
                                Bitvector32Term::Constant(1),
                            )),
                        );
                    }
                    assumptions = assumptions.assume_proposition(fact.clone());
                    continue;
                }
                let proves_fact = match &fact {
                    Proposition::ConditionIs(condition, value) => {
                        assumptions.proves_condition_exact_or_snapshot(condition, *value)
                            || assumptions.decide(condition) == Some(*value)
                    }
                    Proposition::Not(body) => match body.as_ref() {
                        Proposition::ConditionIs(condition, value) => {
                            assumptions.proves_condition_exact_or_snapshot(condition, !*value)
                                || assumptions.decide(condition) == Some(!*value)
                        }
                        _ => assumptions.proves_exact(fact),
                    },
                    _ => assumptions.proves_exact(fact),
                };
                if proves_fact {
                    assumptions = assumptions.assume_proposition(fact.clone());
                }
            }
            entry_state.resources = entry_resources;
        }
        let execution = match mode {
            CFunctionContractExecutionMode::VerifyLoops => {
                prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
                    state.clone(),
                    function.clone(),
                    arguments.clone(),
                    assumptions,
                    environment.clone(),
                    execution_semantics,
                    ExecutionBudget::default(),
                    true,
                )
            }
            CFunctionContractExecutionMode::ExecuteLoops => {
                prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
                    state.clone(),
                    function.clone(),
                    arguments.clone(),
                    assumptions,
                    environment.clone(),
                    execution_semantics,
                    ExecutionBudget::default(),
                    true,
                )
            }
        };
        if let Some(limit) = execution.limit {
            return CFunctionContractExecution {
                execution: SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
            };
        }
        combined_paths.extend(execution.paths);
    }
    CFunctionContractExecution {
        execution: SymbolicCExecution {
            paths: combined_paths,
            limit: None,
        },
    }
}

/// Returns an exhaustive set of proof-only cases for undecided guards on
/// composite resources required directly at function entry.
///
/// A contract such as `owns nullable(p)` denotes either an empty resource or
/// its guarded body. Exact certification must check both meanings when the
/// caller leaves the guard symbolic, even if the C body contains no matching
/// `if`. The cases below are generated wholly from the kernel contract and
/// always include both truth values, so they add no trusted hypothesis.
fn contract_resource_condition_cases(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
) -> Option<Vec<Vec<Proposition>>> {
    let entry_state = c_function_entry_state(caller_state, function, arguments)?;
    let mut budget = ExecutionBudget::default();
    let required_resources = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        assumptions,
        &mut budget,
    )
    .ok()?
    .ok()?;
    let mut guards = Vec::new();
    for resource in required_resources.facts() {
        let CResource::Composite {
            name,
            arguments: resource_arguments,
        } = resource.resource()
        else {
            continue;
        };
        let definition = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name)?;
        let Some(condition) = definition.condition() else {
            continue;
        };
        if definition.parameters().len() != resource_arguments.len() {
            return None;
        }
        let mut condition_state = CState::new()
            .with_memory(entry_state.memory().clone())
            .with_resource_context(required_resources.clone());
        for (parameter, value) in definition.parameters().iter().zip(resource_arguments) {
            if parameter.c_type() != value.c_type() {
                return None;
            }
            condition_state.locals.set_typed(
                parameter.name().to_string(),
                value.clone(),
                parameter.c_type(),
            );
        }
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &condition_state,
            condition,
            None,
            &lowering_assumptions,
            &mut budget,
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        if !path.obligations.iter().all(|obligation| {
            certification_proves_proposition(assumptions, obligation.proposition())
        }) {
            return None;
        }
        if !guards.contains(&path.proposition) {
            guards.push(path.proposition.clone());
        }
    }

    let mut cases = vec![Vec::new()];
    for guard in guards {
        let negated = negate_contract_case_proposition(&guard);
        let mut next = Vec::new();
        for facts in cases {
            let case_assumptions = assumptions_with_propositions(assumptions, &facts);
            if certification_proves_proposition(&case_assumptions, &guard)
                || certification_proves_proposition(&case_assumptions, &negated)
            {
                next.push(facts);
                continue;
            }
            let mut when_true = facts.clone();
            when_true.push(guard.clone());
            next.push(when_true);
            let mut when_false = facts;
            when_false.push(negated.clone());
            next.push(when_false);
        }
        budget.consume_paths(next.len()).ok()?;
        cases = next;
    }
    Some(cases)
}

fn negate_contract_case_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !*value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// Splits a proposition into its conjunct leaves.
fn proposition_conjuncts(proposition: &Proposition, into: &mut Vec<Proposition>) {
    match proposition {
        Proposition::And(left, right) => {
            proposition_conjuncts(left, into);
            proposition_conjuncts(right, into);
        }
        other => into.push(other.clone()),
    }
}

/// Converts a pointer offset to its size in bytes as a bitvector term.
fn pointer_offset_bytes(offset: &PointerOffsetTerm) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(value) => {
            u32::try_from(*value).ok().map(Bitvector32Term::Constant)
        }
        PointerOffsetTerm::Variable(_) => None,
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            pointer_offset_bytes(left)?,
            pointer_offset_bytes(right)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let width = u32::try_from(*byte_width).ok()?;
            if width == 1 {
                Some(value.as_ref().clone())
            } else {
                Some(Bitvector32Term::multiply(
                    value.as_ref().clone(),
                    Bitvector32Term::Constant(width),
                ))
            }
        }
    }
}

/// The byte distance from `fact_offset` to `goal_offset` when the goal
/// offset extends the fact offset additively.
fn pointer_offset_byte_delta(
    goal_offset: &PointerOffsetTerm,
    fact_offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    if goal_offset == fact_offset {
        return Some(Bitvector32Term::Constant(0));
    }
    if let PointerOffsetTerm::Add(left, right) = goal_offset {
        if left.as_ref() == fact_offset {
            return pointer_offset_bytes(right);
        }
        if right.as_ref() == fact_offset {
            return pointer_offset_bytes(left);
        }
    }
    None
}

/// Splits `term + c` into its base term and additive constant (0 when none).
fn split_additive_constant(term: &Bitvector32Term) -> (Bitvector32Term, u32) {
    match term {
        Bitvector32Term::Add(left, right) => {
            if let Bitvector32Term::Constant(value) = right.as_ref() {
                return (left.as_ref().clone(), *value);
            }
            if let Bitvector32Term::Constant(value) = left.as_ref() {
                return (right.as_ref().clone(), *value);
            }
            (term.clone(), 0)
        }
        _ => (term.clone(), 0),
    }
}

/// Certifies a loadability goal from an assumed wider loadable fact over the
/// same memory snapshot: the goal's base must sit at a provably in-bounds
/// byte offset within the fact's span.
pub fn loadable_covered_by_fact(assumptions: &Assumptions, goal: &Proposition) -> bool {
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = goal
    else {
        return false;
    };
    assumptions.prop_facts.iter().any(|fact| {
        let Proposition::CMemoryLoadable {
            memory: fact_memory,
            base: fact_base,
            bytes: fact_bytes,
        } = fact
        else {
            return false;
        };
        if fact_base.block != base.block {
            return false;
        }
        // Loadability of a covering span transports across snapshot spelling
        // differences and recorded write effects just like an exact-range
        // fact does.
        if fact_memory != memory
            && !crate::kernel::reasoning::memory_range_still_available(fact_memory, memory, base)
            && !c_memories_canonically_equal(fact_memory, memory)
            && !c_memories_connected_by_effects(fact_memory, memory, assumptions)
        {
            return false;
        }
        let Some(delta_bytes) = pointer_offset_byte_delta(&base.offset, &fact_base.offset) else {
            return false;
        };
        let start = assumptions.simplify_bitvector_under_assumptions(&Bitvector32Term::Constant(0));
        let delta = assumptions.simplify_bitvector_under_assumptions(&delta_bytes);
        let end = assumptions.simplify_bitvector_under_assumptions(&Bitvector32Term::add(
            delta_bytes,
            bytes.clone(),
        ));
        let span = assumptions.simplify_bitvector_under_assumptions(fact_bytes);
        let starts_in_bounds = assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(start.clone(), delta.clone()),
            true,
        )) || assumptions.proves_order_condition_for_memory_resolution(
            &ConditionTerm::signed_less_equal(start, delta),
            true,
        );
        let ends_in_bounds = assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(end.clone(), span.clone()),
            true,
        )) || assumptions.proves_order_condition_for_memory_resolution(
            &ConditionTerm::signed_less_equal(end.clone(), span.clone()),
            true,
        ) || {
            // Strip a shared additive constant: `a + b <= x + c` follows
            // from `a <= x` when `b <= c`.
            let (end_base, end_shift) = split_additive_constant(&end);
            let (span_base, span_shift) = split_additive_constant(&span);
            (end_shift as i32) <= (span_shift as i32)
                && (assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(end_base.clone(), span_base.clone()),
                    true,
                )) || assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(end_base, span_base),
                    true,
                ))
        };
        if starts_in_bounds && ends_in_bounds {
            return true;
        }
        // Byte-scaled bounds can overflow the arithmetic the order prover
        // handles; retry at element granularity when the goal width folds to
        // a constant.
        assumptions
            .simplify_bitvector_under_assumptions(bytes)
            .as_const()
            .is_some_and(|byte_width| {
                assumptions
                    .proves_loadable_cell_from_region(fact_base, fact_bytes, base, byte_width)
            })
    })
}

/// Certifies a universally-quantified loadability side-obligation from
/// assumed loadable facts: the bound premises become facts about the free
/// bound variable, and the loadable body must then be covered by a wider
/// assumed span.
fn forall_loadable_covered_by_fact(assumptions: &Assumptions, goal: &Proposition) -> bool {
    let Proposition::ForAll {
        sort: Sort::CInt32 | Sort::Bitvector32,
        body,
        ..
    } = goal
    else {
        return false;
    };
    let mut premises = Vec::new();
    let mut conclusion = body.as_ref();
    while let Proposition::Implies(premise, rest) = conclusion {
        proposition_conjuncts(premise, &mut premises);
        conclusion = rest.as_ref();
    }
    if !matches!(conclusion, Proposition::CMemoryLoadable { .. }) {
        return false;
    }
    let premise_assumptions = assumptions_with_propositions(assumptions, &premises);
    loadable_covered_by_fact(&premise_assumptions, conclusion)
}

/// Certifies a quantified single-byte loadability obligation from an assumed
/// quantified fact that constrains a load of the same address under premises
/// the obligation also assumes. Facts enter assumptions only through
/// safety-checked lowering, so a stated fact about `load(p)` witnesses that
/// the first byte at `p` is loadable.
fn quantified_load_fact_certifies_loadable(assumptions: &Assumptions, goal: &Proposition) -> bool {
    fn implication_parts(body: &Proposition) -> (Vec<Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            proposition_conjuncts(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }
    let Proposition::ForAll { var, sort, body } = goal else {
        return false;
    };
    let (goal_premises, conclusion) = implication_parts(body);
    let Proposition::CMemoryLoadable { base, bytes, .. } = conclusion else {
        return false;
    };
    // A load of any width witnesses its first byte.
    if bytes.as_const() != Some(1) {
        return false;
    }
    assumptions.prop_facts.iter().any(|fact| {
        let Proposition::ForAll {
            var: fact_var,
            sort: fact_sort,
            body: fact_body,
        } = fact
        else {
            return false;
        };
        if fact_sort != sort {
            return false;
        }
        let renamed = substitute_bitvector_variable_in_proposition(
            fact_body,
            *fact_var,
            &Bitvector32Term::Variable(*var),
        );
        let (fact_premises, fact_conclusion) = implication_parts(&renamed);
        // The fact applies whenever its premises hold, so they must be among
        // the obligation's assumed premises.
        if !fact_premises.iter().all(|fact_premise| {
            goal_premises.iter().any(|goal_premise| {
                goal_premise == fact_premise
                    || propositions_alpha_equivalent(fact_premise, goal_premise)
            })
        }) {
            return false;
        }
        condition_fact_mentions_load_of(fact_conclusion, base, assumptions)
    })
}

/// True when a condition fact constrains a load of exactly this pointer, so
/// the fact witnesses that the pointer's first byte is loadable.
fn condition_fact_mentions_load_of(
    fact: &Proposition,
    base: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    fn collect_load_pointers(term: &Bitvector32Term, pointers: &mut Vec<Pointer>) {
        match term {
            Bitvector32Term::MemoryLoad(_, pointer) => pointers.push(pointer.as_ref().clone()),
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right) => {
                collect_load_pointers(left, pointers);
                collect_load_pointers(right, pointers);
            }
            _ => {}
        }
    }
    let Proposition::ConditionIs(condition, _) = fact else {
        return false;
    };
    let mut load_pointers = Vec::new();
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
            collect_load_pointers(left, &mut load_pointers);
            collect_load_pointers(right, &mut load_pointers);
        }
        ConditionTerm::PointerOffsetEqual(_, _)
        | ConditionTerm::PointerEqual(_, _)
        | ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_) => {}
    }
    load_pointers.iter().any(|pointer| {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        canonicalize_pointer_loads(pointer, 0) == canonicalize_pointer_loads(base, 0)
            || pointers_proven_equal_for_memory_resolution(pointer, base, assumptions)
    })
}

/// The leaf form of the load-fact witness: a single-byte loadability goal is
/// certified by any assumed condition fact constraining a load of the same
/// pointer.
fn load_fact_certifies_loadable(assumptions: &Assumptions, goal: &Proposition) -> bool {
    let Proposition::CMemoryLoadable { base, bytes, .. } = goal else {
        return false;
    };
    if bytes.as_const() != Some(1) {
        return false;
    }
    assumptions
        .pure_facts()
        .iter()
        .any(|fact| condition_fact_mentions_load_of(fact, base, assumptions))
}

/// An instantiated int32 load from an already-certified quantified fact is
/// loadable whenever that fact's guard holds for the requested index. This is
/// the pointwise form used while lowering another quantified proposition: the
/// bound variable has become an ordinary symbolic variable and its guard is
/// already present in `assumptions`.
pub(super) fn quantified_int32_fact_certifies_loadable_cell(
    assumptions: &Assumptions,
    base: &Pointer,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    fn collect_shallow_term_variables(term: &Bitvector32Term, variables: &mut BTreeSet<Variable>) {
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
                collect_shallow_term_variables(left, variables);
                collect_shallow_term_variables(right, variables);
            }
            Bitvector32Term::BitwiseNot(inner) => {
                collect_shallow_term_variables(inner, variables);
            }
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                collect_shallow_term_variables(then_term, variables);
                collect_shallow_term_variables(else_term, variables);
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                collect_shallow_term_variables(start, variables);
                collect_shallow_term_variables(end, variables);
                collect_shallow_term_variables(initial, variables);
                collect_shallow_term_variables(body, variables);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    collect_shallow_term_variables(argument, variables);
                }
            }
            // The memory snapshot may contain a large symbolic state. Only
            // variables outside nested loads can be the surrounding
            // quantified index. Variables in the loaded address belong to
            // the base expression (for example the owner parameter), not to
            // that index.
            Bitvector32Term::MemoryLoad(_, _) => {}
        }
    }

    fn collect_shallow_offset_variables(
        offset: &PointerOffsetTerm,
        variables: &mut BTreeSet<Variable>,
    ) {
        match offset {
            PointerOffsetTerm::Constant(_) => {}
            PointerOffsetTerm::Variable(variable) => {
                variables.insert(*variable);
            }
            PointerOffsetTerm::Add(left, right) => {
                collect_shallow_offset_variables(left, variables);
                collect_shallow_offset_variables(right, variables);
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => {
                collect_shallow_term_variables(value, variables);
            }
        }
    }

    fn implication_parts(body: &Proposition) -> (Vec<Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            proposition_conjuncts(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }

    let mut target_variables = BTreeSet::new();
    if let PointerBlock::Symbolic(variable) = base.block {
        target_variables.insert(variable);
    }
    collect_shallow_offset_variables(&base.offset, &mut target_variables);
    let exact_binder_candidates = assumptions.prop_facts.iter().filter(
        |fact| matches!(fact, Proposition::ForAll { var, .. } if target_variables.contains(var)),
    );
    let renamed_binder_candidates = assumptions.prop_facts.iter().filter(
        |fact| matches!(fact, Proposition::ForAll { var, .. } if !target_variables.contains(var)),
    );
    exact_binder_candidates
        .chain(renamed_binder_candidates)
        .any(|fact| {
            if crate::instrumentation::deadline_exceeded() {
                return false;
            }
            let Proposition::ForAll {
                var: fact_var,
                sort: Sort::CInt32 | Sort::Bitvector32,
                body,
            } = fact
            else {
                return false;
            };
            let exact_target = target_variables.contains(fact_var).then_some(*fact_var);
            exact_target
                .into_iter()
                .chain(
                    target_variables
                        .iter()
                        .copied()
                        .filter(|target| target != fact_var),
                )
                .any(|target_var| {
                    if crate::instrumentation::deadline_exceeded() {
                        return false;
                    }
                    let renamed = (target_var != *fact_var).then(|| {
                        substitute_bitvector_variable_in_proposition(
                            body,
                            *fact_var,
                            &Bitvector32Term::Variable(target_var),
                        )
                    });
                    let instantiated = renamed.as_ref().unwrap_or(body.as_ref());
                    let (premises, conclusion) = implication_parts(instantiated);
                    let premises_hold = premises.iter().all(|premise| {
                        !crate::instrumentation::deadline_exceeded()
                            && matches!(premise, Proposition::ConditionIs(_, _))
                            && certification_proves_proposition(assumptions, premise)
                    });
                    premises_hold && condition_fact_mentions_load_of(conclusion, base, assumptions)
                })
        })
}

/// A checked universal fact that reads every int32 cell in a guarded prefix
/// certifies that complete prefix as loadable. This is the range form needed
/// after modular initialization helpers: their postcondition can expose the
/// value of each written cell without returning a separate ad-hoc permission
/// proposition.
pub(super) fn quantified_int32_fact_certifies_loadable_range(
    assumptions: &Assumptions,
    memory: &CMemory,
    base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }

    let element_count = match bytes {
        Bitvector32Term::Multiply(left, right) if right.as_const() == Some(4) => left.as_ref(),
        Bitvector32Term::Multiply(left, right) if left.as_const() == Some(4) => right.as_ref(),
        _ => return false,
    };

    fn conjunct_refs<'a>(proposition: &'a Proposition, output: &mut Vec<&'a Proposition>) {
        match proposition {
            Proposition::And(left, right) => {
                conjunct_refs(left, output);
                conjunct_refs(right, output);
            }
            proposition => output.push(proposition),
        }
    }

    fn implication_parts(body: &Proposition) -> (Vec<&Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            conjunct_refs(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }

    fn collect_loads<'a>(term: &'a Bitvector32Term, loads: &mut Vec<(&'a CMemory, &'a Pointer)>) {
        match term {
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                loads.push((memory, pointer));
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
                collect_loads(left, loads);
                collect_loads(right, loads);
            }
            Bitvector32Term::BitwiseNot(inner) => collect_loads(inner, loads),
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                collect_loads(then_term, loads);
                collect_loads(else_term, loads);
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                collect_loads(start, loads);
                collect_loads(end, loads);
                collect_loads(initial, loads);
                collect_loads(body, loads);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    collect_loads(argument, loads);
                }
            }
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        }
    }

    fn condition_loads<'a>(
        proposition: &'a Proposition,
        loads: &mut Vec<(&'a CMemory, &'a Pointer)>,
    ) {
        let Proposition::ConditionIs(condition, _) = proposition else {
            return;
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
                collect_loads(left, loads);
                collect_loads(right, loads);
            }
            ConditionTerm::PointerOffsetEqual(_, _)
            | ConditionTerm::PointerEqual(_, _)
            | ConditionTerm::Constant(_)
            | ConditionTerm::Variable(_) => {}
        }
    }

    let guard_matches = |premises: &[&Proposition], target: &ConditionTerm| {
        premises.iter().any(|premise| {
            matches!(premise, Proposition::ConditionIs(condition, true)
                if condition == target || assumptions.condition_matches(condition, target))
        })
    };

    assumptions.prop_facts.iter().any(|fact| {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        let Proposition::ForAll {
            var,
            sort: Sort::CInt32 | Sort::Bitvector32,
            body,
        } = fact
        else {
            return false;
        };
        let (premises, conclusion) = implication_parts(body);
        let index = Bitvector32Term::Variable(*var);
        let lower = ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone());
        let upper = ConditionTerm::signed_less_than(index.clone(), element_count.clone());
        if !guard_matches(&premises, &lower) || !guard_matches(&premises, &upper) {
            return false;
        }
        let mut loads = Vec::new();
        condition_loads(conclusion, &mut loads);
        loads.iter().any(|(load_memory, pointer)| {
            *load_memory == memory
                && pointer
                    .element_index_from_base(base)
                    .is_some_and(|load_index| load_index == index)
        })
    })
}

/// Certifies an existential requirement side-obligation (typically the
/// loadability safety of an existential requirement body): the witness of an
/// assumed existential over the same sort supplies the bound variable, its
/// body conjuncts become facts, and the obligation body must then certify
/// pointwise.
fn certification_proves_exists_obligation_from_facts(
    assumptions: &Assumptions,
    obligation: &Proposition,
) -> bool {
    let Proposition::Exists {
        var, sort, body, ..
    } = obligation
    else {
        return false;
    };
    let fact_candidates = assumptions.prop_facts.iter().cloned().collect::<Vec<_>>();
    fact_candidates.iter().any(|fact| {
        let Proposition::Exists {
            var: fact_var,
            sort: fact_sort,
            body: fact_body,
            ..
        } = fact
        else {
            return false;
        };
        if fact_sort != sort {
            return false;
        }
        let renamed = substitute_bitvector_variable_in_proposition(
            fact_body,
            *fact_var,
            &Bitvector32Term::Variable(*var),
        );
        let mut witness_facts = Vec::new();
        proposition_conjuncts(&renamed, &mut witness_facts);
        let witness_assumptions = assumptions_with_propositions(assumptions, &witness_facts);
        let mut goals = Vec::new();
        proposition_conjuncts(body, &mut goals);
        goals.iter().all(|goal| {
            certification_proves_proposition(&witness_assumptions, goal)
                || loadable_covered_by_fact(&witness_assumptions, goal)
                || quantified_load_fact_certifies_loadable(&witness_assumptions, goal)
                || load_fact_certifies_loadable(&witness_assumptions, goal)
                // Nested existentials recurse: the inner obligation matches
                // an inner assumed existential the same way.
                || certification_proves_exists_obligation_from_facts(&witness_assumptions, goal)
        })
    })
}

fn c_function_contract_certification_assumptions(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    mut assumptions: Assumptions,
    selection_assumptions: &Assumptions,
) -> Option<Assumptions> {
    let mut entry_state = c_function_entry_state(caller_state, function, arguments)?;
    let mut budget = ExecutionBudget::default();
    // Entry facts derived from declared parameter spellings (for example
    // sized array parameters) carry loadability that is part of the calling
    // convention; assume them before lowering requirements so requirement
    // side-obligations can be certified against them.
    for fact in &selection_assumptions.prop_facts {
        if matches!(fact, Proposition::CMemoryLoadable { .. }) {
            assumptions = assumptions.assume_proposition(fact.clone());
        }
        // Universally-quantified implications concluding in an opaque
        // predicate are surface-verified theorem facts. The predicate has no
        // kernel definition, so the surface verifier is their authority,
        // like the loadability calling convention above.
        if quantified_predicate_implication_fact(fact) {
            assumptions = assumptions.assume_proposition(fact.clone());
        }
    }
    let mut requirement_obligations = Vec::new();
    for requirement in function.contract_requires() {
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &entry_state,
            requirement,
            None,
            &lowering_assumptions,
            &mut budget,
        )
        .ok()?;
        let path = if let [path] = paths.as_slice() {
            path
        } else {
            let selection_context =
                assumptions_with_propositions(&assumptions, &selection_assumptions.pure_facts());
            let proposition_matches = paths
                .iter()
                .filter(|path| {
                    certification_proves_proposition(&selection_context, &path.proposition)
                })
                .collect::<Vec<_>>();
            if let [path] = proposition_matches.as_slice() {
                *path
            } else {
                let consistent = paths
                    .iter()
                    .filter(|path| {
                        !assumptions_with_propositions(
                            &selection_context,
                            &path
                                .facts
                                .iter()
                                .map(|fact| fact.proposition().clone())
                                .collect::<Vec<_>>(),
                        )
                        .is_inconsistent()
                    })
                    .collect::<Vec<_>>();
                let [path] = consistent.as_slice() else {
                    return None;
                };
                *path
            }
        };
        for obligation in &path.obligations {
            if !requirement_obligations.contains(obligation) {
                requirement_obligations.push(obligation.clone());
            }
        }
        for fact in &path.facts {
            assumptions = assumptions.assume_proposition(fact.proposition().clone());
        }
        assumptions = assumptions.assume_proposition(path.proposition.clone());
    }
    let required_resources = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        &assumptions,
        &mut budget,
    )
    .ok()
    .and_then(Result::ok);
    let required_resources = required_resources?;
    let expanded = expand_all_composite_resource_facts_and_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    );
    let (_, resource_definition_facts) = expanded?;
    for proposition in resource_definition_facts {
        assumptions = assumptions.assume_proposition(proposition);
    }
    let expanded_required_resources = expand_all_composite_resource_facts(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    )?;
    let mut entry_resources = entry_state.resources().clone();
    let mut missing = Vec::new();
    for (index, required) in expanded_required_resources.facts().iter().enumerate() {
        let exposed = expose_composite_resource_fact(
            &entry_resources,
            required,
            function.composite_resource_definitions(),
            entry_state.memory(),
            &assumptions,
        )
        .or_else(|| {
            let CResource::Memory(required_range) = required.resource() else {
                return None;
            };
            let has_same_base = entry_resources.facts().iter().any(|available| {
                let CResource::Memory(available_range) = available.resource() else {
                    return false;
                };
                super::assumptions::pointers_equal_ignoring_memories(
                    available_range.base(),
                    required_range.base(),
                )
            });
            (has_same_base && entry_resources.satisfies_fact(required, &assumptions))
                .then(|| entry_resources.clone())
        });
        let Some(exposed) = exposed else {
            missing.push((index, required));
            continue;
        };
        entry_resources = exposed;
    }
    if !missing.is_empty() {
        if crate::instrumentation::enabled() {
            let missing = missing
                .into_iter()
                .map(|(index, required)| {
                    let kind = match required.resource() {
                        CResource::Memory(range) => {
                            format!("memory in {}", range.base().block)
                        }
                        CResource::Composite { name, .. } => format!("composite {name}"),
                        CResource::Token { name, .. } => format!("token {name}"),
                    };
                    format!("{index}: {kind}")
                })
                .collect::<Vec<_>>();
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                format!(
                    "contract entry resources do not satisfy requirements ({}/{}, missing {})",
                    entry_resources.facts().len(),
                    expanded_required_resources.facts().len(),
                    missing.join(", ")
                ),
            ));
        }
        return None;
    }
    if !requirement_obligations.iter().all(|obligation| {
        // Definedness travels with the assumption. A heap-dependent
        // `requires` cannot be true in a state where its loads do not
        // denote, so assuming the requirement already entails the
        // loadability its evaluation needed: the caller had to establish
        // the requirement, and the same obligations are proof obligations
        // on the caller's side (see the path-obligation check in
        // `prepare_function_claim_path`, which does not exempt them).
        //
        // Only assumable obligations — the definedness kind — ride along.
        // A genuine verification condition still has to be discharged here.
        if obligation.is_assumable() {
            return true;
        }

        certification_proves_proposition(&assumptions, obligation.proposition())
            || resources_certify_loadability(
                &entry_state,
                &entry_resources,
                obligation.proposition(),
                &assumptions,
            )
            || loadable_covered_by_fact(&assumptions, obligation.proposition())
            || forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
            || certification_proves_exists_obligation_from_facts(
                &assumptions,
                obligation.proposition(),
            )
    }) {
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                "contract entry resources do not certify requirement safety".to_string(),
            ));
        }
        return None;
    }
    for obligation in requirement_obligations {
        assumptions = assumptions.assume_proposition(obligation.proposition().clone());
    }
    for proposition in entry_resources.observable_facts(&assumptions).ok()? {
        assumptions = assumptions.assume_proposition(proposition);
    }
    entry_state.resources = entry_resources.clone();
    Some(assumptions)
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(&state, &mut existing);
    collect_c_function_bitvector_variables(&function, &mut existing);
    for argument in &arguments {
        collect_c_expression_bitvector_variables(argument, &mut existing);
    }
    collect_assumption_variables(&assumptions, &mut existing);
    collect_execution_environment_variables(&environment, &mut existing);
    let mut variables =
        VerificationVariableGenerator::fresh_for(budget.next_verification_variable, existing);
    let paths = match execute_c_function_verification_paths(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
        &mut variables,
        prepare_contract_resources,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CFunctionVerifies {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn c_function_execution_candidates_from_outcomes(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    paths: Vec<(
        CFunctionOutcome,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    )>,
) -> CFunctionExecutionCandidates {
    let paths = paths
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let effect_facts = memory_effect_execution_facts(&facts);
            let facts = public_execution_pure_facts(&facts);
            CFunctionExecutionCandidate {
                outcome,
                facts,
                effect_facts,
                obligations,
            }
        })
        .collect();

    CFunctionExecutionCandidates {
        state,
        function,
        arguments,
        paths,
    }
}

pub fn prove_c_function_satisfies_specification_from_symbolic_path(
    function: CFunction,
    specification: CFunctionSpecification,
    path: &SymbolicCExecutionPath,
) -> Option<Theorem> {
    let mut proved = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proved {
        premises.push(premise.as_ref().clone());
        proved = body;
    }
    let (state, proved_function, arguments, outcome, verifies) = match proved {
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, false),
        Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, true),
        _ => return None,
    };
    if state != specification.state()
        || proved_function != &function
        || arguments != specification.arguments()
        || outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let conclusion = if verifies {
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        }
    } else {
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        }
    };
    let proposition = requires
        .into_iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement), Box::new(body))
        });
    Some(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(proposition, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

fn certified_function_path_parts<'a>(
    function: &CFunction,
    path: &'a SymbolicCExecutionPath,
) -> Option<(
    &'a CState,
    &'a [CExpression],
    &'a CFunctionOutcome,
    Assumptions,
)> {
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let (state, proved_function, arguments, outcome) = match proposition {
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        }
        | Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome),
        _ => return None,
    };
    if proved_function != function {
        return None;
    }
    let mut assumptions = path.assumptions.clone();
    assumptions = assumptions_with_propositions(
        &assumptions,
        &path
            .execution_facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    Some((state, arguments, outcome, assumptions))
}

fn resource_contexts_definitionally_equal(
    function: &CFunction,
    left_memory: &CMemory,
    left: &ResourceContext,
    right_memory: &CMemory,
    right: &ResourceContext,
    assumptions: &Assumptions,
) -> bool {
    resource_contexts_definitionally_equal_with_definitions(
        function.composite_resource_definitions(),
        left_memory,
        left,
        right_memory,
        right,
        assumptions,
    )
}

pub(super) fn resource_contexts_definitionally_equal_with_definitions(
    composite_resource_definitions: &[CCompositeResourceDefinition],
    left_memory: &CMemory,
    left: &ResourceContext,
    right_memory: &CMemory,
    right: &ResourceContext,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    let relation_facts = [(left, left_memory), (right, right_memory)]
        .into_iter()
        .flat_map(|(resources, memory)| {
            resources.facts().iter().filter_map(move |fact| {
                matches!(fact.resource(), CResource::Composite { .. })
                    .then(|| {
                        evaluate_composite_resource_relation_propositions(
                            fact,
                            composite_resource_definitions,
                            memory,
                            assumptions,
                        )
                    })
                    .flatten()
            })
        })
        .flatten()
        .collect::<Vec<_>>();
    let enriched_assumptions = assumptions_with_propositions(assumptions, &relation_facts);
    let assumptions = &enriched_assumptions;
    let facts_directly_match = |left: &CResourceFact, right: &CResourceFact| match (left, right) {
        (CResourceFact::Own(left), CResourceFact::Own(right))
        | (CResourceFact::View(left), CResourceFact::View(right)) => {
            super::assumptions::resources_equal_ignoring_memories(left, right)
                && c_resources_directly_match(left, right, assumptions)
        }
        _ => false,
    };
    let directly_equal = |left: &ResourceContext, right: &ResourceContext| {
        left.facts().iter().all(|fact| {
            right
                .facts()
                .iter()
                .any(|available| facts_directly_match(available, fact))
                || right.satisfies_fact(fact, assumptions)
        }) && right.facts().iter().all(|fact| {
            left.facts()
                .iter()
                .any(|available| facts_directly_match(available, fact))
                || left.satisfies_fact(fact, assumptions)
        })
    };
    let definitionally_covers =
        |available: &ResourceContext, required: &ResourceContext, memory: &CMemory| {
            required.facts().iter().all(|fact| {
                expose_composite_resource_fact(
                    available,
                    fact,
                    composite_resource_definitions,
                    memory,
                    assumptions,
                )
                .is_some()
            })
        };
    if directly_equal(left, right) {
        return true;
    }
    if left_memory == right_memory
        && ((definitionally_covers(left, right, left_memory)
            && definitionally_covers(right, left, left_memory))
            || resource_contexts_definitionally_equivalent_by_consumption(
                left,
                right,
                composite_resource_definitions,
                left_memory,
                assumptions,
            ))
    {
        return true;
    }
    let expanded_left = expand_all_composite_resource_facts(
        left,
        composite_resource_definitions,
        left_memory,
        assumptions,
    );
    let expanded_right = expand_all_composite_resource_facts(
        right,
        composite_resource_definitions,
        right_memory,
        assumptions,
    );
    let Some(left) = expanded_left else {
        return false;
    };
    let Some(right) = expanded_right else {
        return false;
    };

    directly_equal(&left, &right)
}

/// Extracts constant bounds `lo <= var < hi` from a universal premise made
/// exclusively of constant comparisons against `var`. Returns `None` when any
/// conjunct is not such a bound, so instantiating the conclusion stays sound.
fn constant_variable_bounds(var: Variable, premise: &Proposition) -> Option<(u32, u32)> {
    fn collect(
        var: Variable,
        premise: &Proposition,
        lo: &mut Option<u32>,
        hi: &mut Option<u32>,
    ) -> bool {
        let bound = Bitvector32Term::Variable(var);
        match premise {
            Proposition::And(left, right) => {
                collect(var, left, lo, hi) && collect(var, right, lo, hi)
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(left, right),
                true,
            ) if **right == bound => {
                let Bitvector32Term::Constant(value) = **left else {
                    return false;
                };
                if value > i32::MAX as u32 {
                    return false;
                }
                *lo = Some(lo.map_or(value, |current: u32| current.max(value)));
                true
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(left, right),
                true,
            ) if **left == bound => {
                let Bitvector32Term::Constant(value) = **right else {
                    return false;
                };
                if value > i32::MAX as u32 {
                    return false;
                }
                *hi = Some(hi.map_or(value, |current: u32| current.min(value)));
                true
            }
            _ => false,
        }
    }
    let mut lo = None;
    let mut hi = None;
    if !collect(var, premise, &mut lo, &mut hi) {
        return None;
    }
    Some((lo?, hi?))
}

const FORALL_INSTANTIATION_LIMIT: u32 = 16;

/// Evaluates a premise whose variables have been substituted away to a
/// constant truth value; `None` when it is not a closed constant condition.
fn constant_premise_value(premise: &Proposition) -> Option<bool> {
    match premise {
        Proposition::And(left, right) => {
            Some(constant_premise_value(left)? && constant_premise_value(right)?)
        }
        Proposition::ConditionIs(condition, expected) => {
            let holds = match condition {
                ConditionTerm::Constant(value) => *value,
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32) <= (*right as i32)
                }
                ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32) < (*right as i32)
                }
                ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32).checked_add(*right as i32).is_none()
                }
                _ => return None,
            };
            Some(holds == *expected)
        }
        _ => None,
    }
}

/// Instantiates finitely-bounded universal facts (`forall x. guards -> lo <=
/// x < hi -> P(x)` with small constant bounds) at every point in the bound,
/// so the certifier can use per-index conclusions the way an unfolded proof
/// does. Guard premises (such as overflow side conditions) must evaluate to
/// constant truth after substitution, or the point is skipped.
fn finite_forall_instantiations(facts: &[Proposition]) -> Vec<Proposition> {
    let mut instantiated = Vec::new();
    for fact in facts {
        let Proposition::ForAll {
            var,
            sort: Sort::CInt32 | Sort::Bitvector32,
            body,
        } = fact
        else {
            continue;
        };
        let mut premises = Vec::new();
        let mut conclusion = body.as_ref();
        while let Proposition::Implies(premise, rest) = conclusion {
            premises.push(premise.as_ref());
            conclusion = rest.as_ref();
        }
        let Some((lo, hi)) = premises
            .iter()
            .find_map(|premise| constant_variable_bounds(*var, premise))
        else {
            continue;
        };
        if hi <= lo || hi - lo > FORALL_INSTANTIATION_LIMIT {
            continue;
        }
        for value in lo..hi {
            let witness = Bitvector32Term::Constant(value);
            let premises_hold = premises.iter().all(|premise| {
                constant_variable_bounds(*var, premise).is_some()
                    || constant_premise_value(&substitute_bitvector_variable_in_proposition(
                        premise, *var, &witness,
                    )) == Some(true)
            });
            if premises_hold {
                instantiated.push(substitute_bitvector_variable_in_proposition(
                    conclusion, *var, &witness,
                ));
            }
        }
    }
    instantiated
}

/// Structural equality up to renaming of bound variables at every quantifier
/// depth; bound variables are freshened per lowering pass, so nested
/// quantified facts never match syntactically.
pub(crate) fn propositions_alpha_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::Exists {
                var: left_var,
                sort: left_sort,
                body: left_body,
                ..
            },
            Proposition::Exists {
                var: right_var,
                sort: right_sort,
                body: right_body,
                ..
            },
        ) => {
            left_sort == right_sort && {
                let renamed = substitute_bitvector_variable_in_proposition(
                    left_body,
                    *left_var,
                    &Bitvector32Term::Variable(*right_var),
                );
                propositions_alpha_equivalent(&renamed, right_body)
            }
        }
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort && {
                let renamed = substitute_bitvector_variable_in_proposition(
                    left_body,
                    *left_var,
                    &Bitvector32Term::Variable(*right_var),
                );
                propositions_alpha_equivalent(&renamed, right_body)
            }
        }
        (Proposition::And(al, ar), Proposition::And(bl, br))
        | (Proposition::Or(al, ar), Proposition::Or(bl, br))
        | (Proposition::Implies(al, ar), Proposition::Implies(bl, br)) => {
            propositions_alpha_equivalent(al, bl) && propositions_alpha_equivalent(ar, br)
        }
        (Proposition::Not(a), Proposition::Not(b)) => propositions_alpha_equivalent(a, b),
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && condition_with_canonical_loads(left_condition)
                    .zip(condition_with_canonical_loads(right_condition))
                    .is_some_and(|(left, right)| left == right)
        }
        (
            Proposition::CMemoryLoadable {
                memory: left_memory,
                base: left_base,
                bytes: left_bytes,
            },
            Proposition::CMemoryLoadable {
                memory: right_memory,
                base: right_base,
                bytes: right_bytes,
            },
        ) => {
            canonicalize_pointer_loads(left_base, 0) == canonicalize_pointer_loads(right_base, 0)
                && canonicalize_atomic_loads(left_bytes)
                    == canonicalize_atomic_loads(right_bytes)
                // Loadability depends on the snapshot's blocks, not its
                // cached cell values.
                && left_memory.blocks == right_memory.blocks
        }
        _ => false,
    }
}

/// Collects one-point-rule witness candidates for an existential body: any
/// conjunct shaped `var == term` (on either side) pins the bound variable to
/// `term`, provided `term` does not itself mention the variable.
fn exists_equality_witness_candidates(
    var: Variable,
    body: &Proposition,
    candidates: &mut Vec<Bitvector32Term>,
) {
    match body {
        Proposition::And(left, right) => {
            exists_equality_witness_candidates(var, left, candidates);
            exists_equality_witness_candidates(var, right, candidates);
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            let bound = Bitvector32Term::Variable(var);
            for (side, other) in [(left, right), (right, left)] {
                let mentions_var = super::reasoning::substitute_bitvector_variable(
                    other,
                    var,
                    &Bitvector32Term::Constant(0),
                ) != **other;
                if **side == bound && !mentions_var {
                    candidates.push((**other).clone());
                }
            }
        }
        _ => {}
    }
}

/// Proves an order condition against a constant by removing an additive
/// constant shift from the term side, when the assumptions prove the shifted
/// addition overflow-free (the executing code already checked it). For
/// example `x + 1 > 0` becomes `x >= 0` under `!AddOverflows(x, 1)`.
fn shifted_order_condition_proven(
    assumptions: &Assumptions,
    condition: &ConditionTerm,
    value: bool,
) -> bool {
    if !value {
        return false;
    }
    // Normalize to `left OP right` with OP in {<, <=}.
    let (left, right, strict) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right, true),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => (left, right, false),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => (right, left, true),
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => (right, left, false),
        _ => return false,
    };
    let overflow_free = |base: &Bitvector32Term, shift: u32| {
        // Any exact strict signed upper bound on `base` keeps `base + 1`
        // below overflow: the bound itself is an int32 and therefore at
        // most INT_MAX. This is the same direct increment certificate the
        // executor uses for `x < capacity` before evaluating `x + 1`.
        if shift == 1 && assumptions.has_exact_strict_upper_bound(base) {
            return true;
        }
        let exact = assumptions.proves_exact(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedAddOverflows(
                Box::new(base.clone()),
                Box::new(Bitvector32Term::Constant(shift)),
            ),
            false,
        )) || assumptions.proves_exact(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedAddOverflows(
                Box::new(Bitvector32Term::Constant(shift)),
                Box::new(base.clone()),
            ),
            false,
        ));
        if exact {
            return true;
        }
        // A recorded overflow fact may spell the operand through loads at a
        // different snapshot; compare canonically.
        let canonical_base = canonicalize_atomic_loads(base);
        let recorded = assumptions.condition_facts.iter().any(|(condition, value)| {
            !*value
                && match condition {
                    ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                        (matches!(right.as_ref(), Bitvector32Term::Constant(c) if *c == shift)
                            && canonicalize_atomic_loads(left) == canonical_base)
                            || (matches!(left.as_ref(), Bitvector32Term::Constant(c) if *c == shift)
                                && canonicalize_atomic_loads(right) == canonical_base)
                    }
                    _ => false,
                }
        });
        if recorded {
            return true;
        }
        // Overflow-freedom also follows from a proven bound keeping the
        // shifted sum inside the signed range.
        let signed_shift = shift as i32;
        if signed_shift > 0 {
            let le_bound = Bitvector32Term::Constant((i32::MAX - signed_shift) as u32);
            let le = ConditionTerm::signed_less_equal(base.clone(), le_bound);
            let lt_bound = Bitvector32Term::Constant((i32::MAX - signed_shift + 1) as u32);
            let lt = ConditionTerm::signed_less_than(base.clone(), lt_bound);
            assumptions.proves_exact(&Proposition::ConditionIs(le.clone(), true))
                || assumptions.proves_order_condition_for_memory_resolution(&le, true)
                || assumptions.proves_exact(&Proposition::ConditionIs(lt.clone(), true))
                || assumptions.proves_order_condition_for_memory_resolution(&lt, true)
        } else if signed_shift < 0 {
            let bound = Bitvector32Term::Constant((i32::MIN - signed_shift) as u32);
            let condition = ConditionTerm::signed_less_equal(bound, base.clone());
            assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), true))
                || assumptions.proves_order_condition_for_memory_resolution(&condition, true)
        } else {
            true
        }
    };
    // `a + 1 <= b` follows from `a < b` for any terms when `a + 1` is
    // provably overflow-free; this converts a strict requirement into the
    // non-strict spelling a successor produces.
    if !strict {
        let (base, shift) = split_additive_constant(left);
        if shift == 1 {
            // `a < b` alone implies both that `a + 1` cannot overflow
            // (`a < b <= i32::MAX`) and the goal `a + 1 <= b`.
            let strict_form = ConditionTerm::signed_less_than(base, right.as_ref().clone());
            if certification_proves_proposition(
                assumptions,
                &Proposition::ConditionIs(strict_form, true),
            ) {
                return true;
            }
        }
    }
    let shifted = match (left.as_ref(), right.as_ref()) {
        (shifted_term, Bitvector32Term::Constant(bound)) => {
            let (base, shift) = split_additive_constant(shifted_term);
            if shift == 0 || !overflow_free(&base, shift) {
                return false;
            }
            let Some(new_bound) = (*bound as i32).checked_sub(shift as i32) else {
                return false;
            };
            (base, Bitvector32Term::Constant(new_bound as u32), false)
        }
        (Bitvector32Term::Constant(bound), shifted_term) => {
            let (base, shift) = split_additive_constant(shifted_term);
            if shift == 0 || !overflow_free(&base, shift) {
                return false;
            }
            let Some(new_bound) = (*bound as i32).checked_sub(shift as i32) else {
                return false;
            };
            (Bitvector32Term::Constant(new_bound as u32), base, true)
        }
        _ => return false,
    };
    let (new_left, new_right, constant_on_left) = shifted;
    let condition = match (strict, constant_on_left) {
        (true, false) | (true, true) => ConditionTerm::signed_less_than(new_left, new_right),
        (false, _) => ConditionTerm::signed_less_equal(new_left, new_right),
    };
    certification_proves_proposition(assumptions, &Proposition::ConditionIs(condition, true))
}

/// Compares two range folds up to renaming of their bound accumulator and
/// item variables; bound variables are freshened per lowering pass.
fn range_folds_alpha_equivalent(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
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
    left_start == right_start && left_end == right_end && left_initial == right_initial && {
        let renamed = super::reasoning::substitute_bitvector_variable(
            &super::reasoning::substitute_bitvector_variable(
                right_body,
                *right_accumulator,
                &Bitvector32Term::Variable(*left_accumulator),
            ),
            *right_item,
            &Bitvector32Term::Variable(*left_item),
        );
        renamed == **left_body
    }
}

/// Canonicalizes the loads inside a binary condition so spellings differing
/// only in redundant cached cells compare and prove identically.
fn condition_with_canonical_loads(condition: &ConditionTerm) -> Option<ConditionTerm> {
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

/// Splits both offsets into non-constant atoms plus a constant shift,
/// resolves atoms whose scaled values equality facts pin to a constant, and
/// requires the remaining atoms to match pairwise. Runs the bounded constant
/// resolver once per atom at top level, never inside the resolution
/// recursion.
fn pointer_offsets_equal_with_resolved_atoms(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    let resolve = |offset: &PointerOffsetTerm| {
        let (atoms, mut constant) = super::reasoning::offset_atoms_and_constant(offset);
        let mut unresolved = Vec::new();
        for atom in atoms {
            if let PointerOffsetTerm::Int32Scaled { value, byte_width } = &atom
                && let Some(known) = assumptions.known_signed_constant_after_normalization(value)
            {
                constant += known * byte_width;
                continue;
            }
            unresolved.push(atom);
        }
        (unresolved, constant)
    };
    let (left_atoms, left_constant) = resolve(left);
    let (mut right_atoms, right_constant) = resolve(right);
    if left_constant != right_constant {
        return false;
    }
    // Scaled values compare through snapshot-bridged load equality: two
    // spellings of one loaded field, or a recorded PointerOffsetEqual fact
    // whose sides bridge to the compared values.
    let scaled_values_bridged = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
            || assumptions.memory_loads_proven_equal(left, right)
    };
    let atoms_match = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
        if left == right
            || assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                left.clone(),
                right.clone(),
            )) == Some(true)
            || assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                right.clone(),
                left.clone(),
            )) == Some(true)
        {
            return true;
        }
        let (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) = (left, right)
        else {
            return false;
        };
        if left_width != right_width {
            return false;
        }
        if scaled_values_bridged(left_value, right_value) {
            return true;
        }
        // Walk the PointerOffsetEqual fact graph transitively: each edge's
        // endpoints connect to the frontier through snapshot-bridged load
        // equality, so a chain like right->data == left->data == data closes.
        let edges = assumptions
            .condition_facts
            .iter()
            .filter(|(_, value)| **value)
            .filter_map(|(condition, _)| {
                let ConditionTerm::PointerOffsetEqual(fact_left, fact_right) = condition else {
                    return None;
                };
                let (
                    PointerOffsetTerm::Int32Scaled {
                        value: a_value,
                        byte_width: a_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: b_value,
                        byte_width: b_width,
                    },
                ) = (fact_left.as_ref(), fact_right.as_ref())
                else {
                    return None;
                };
                (a_width == left_width && b_width == left_width)
                    .then_some((a_value.as_ref().clone(), b_value.as_ref().clone()))
            })
            .collect::<Vec<_>>();
        let mut frontier = vec![left_value.as_ref().clone()];
        let mut visited = Vec::new();
        while let Some(current) = frontier.pop() {
            if visited.contains(&current) {
                continue;
            }
            if scaled_values_bridged(&current, right_value) {
                return true;
            }
            for (a_value, b_value) in &edges {
                if scaled_values_bridged(&current, a_value) {
                    frontier.push(b_value.clone());
                }
                if scaled_values_bridged(&current, b_value) {
                    frontier.push(a_value.clone());
                }
            }
            visited.push(current);
        }
        false
    };
    for atom in &left_atoms {
        let Some(position) = right_atoms
            .iter()
            .position(|candidate| atoms_match(atom, candidate))
        else {
            return false;
        };
        right_atoms.remove(position);
    }
    right_atoms.is_empty()
}

/// The load spellings a term denotes: the term itself when it is a load,
/// plus every load one equality fact away.
fn load_spellings_of<'a>(
    assumptions: &'a Assumptions,
    term: &'a Bitvector32Term,
) -> Vec<(&'a CMemory, &'a Pointer)> {
    let mut loads = Vec::new();
    if let Bitvector32Term::MemoryLoad(memory, pointer) = term {
        loads.push((&**memory, pointer.as_ref()));
    }
    for (condition, value) in &assumptions.condition_facts {
        if !*value {
            continue;
        }
        let ConditionTerm::Bitvector32Equal(fact_left, fact_right) = condition else {
            continue;
        };
        for (fact_term, fact_load) in [(fact_left, fact_right), (fact_right, fact_left)] {
            if fact_term.as_ref() != term {
                continue;
            }
            if let Bitvector32Term::MemoryLoad(memory, pointer) = fact_load.as_ref() {
                loads.push((&**memory, pointer.as_ref()));
            }
        }
    }
    loads
}

/// Certifies an equality by resolving each side to a load spelling (itself,
/// or one equality fact away) and proving some pair of spellings denotes one
/// framed cell: same block, offsets equal with constant-resolved atoms, and
/// the loaded cell provably unchanged between the two snapshots.
fn certification_proves_equality_via_load_fact(
    assumptions: &Assumptions,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    let left_loads = load_spellings_of(assumptions, left);
    if left_loads.is_empty() {
        return false;
    }
    let right_loads = load_spellings_of(assumptions, right);
    left_loads.iter().any(|(left_memory, left_pointer)| {
        right_loads.iter().any(|(right_memory, right_pointer)| {
            left_pointer.block == right_pointer.block
                && pointer_offsets_equal_with_resolved_atoms(
                    &left_pointer.offset,
                    &right_pointer.offset,
                    assumptions,
                )
                && [left_pointer, right_pointer].into_iter().any(|pointer| {
                    c_memory_load_is_unchanged(left_memory, right_memory, pointer, assumptions)
                        || c_memory_load_is_unchanged(
                            right_memory,
                            left_memory,
                            pointer,
                            assumptions,
                        )
                })
        })
    })
}

fn certification_proves_proposition(assumptions: &Assumptions, proposition: &Proposition) -> bool {
    if assumptions.proves_exact(proposition) {
        return true;
    }
    if let Proposition::ConditionIs(condition, value) = proposition
        && let Some(canonical) = condition_with_canonical_loads(condition)
        && &canonical != condition
        && certification_proves_proposition(
            assumptions,
            &Proposition::ConditionIs(canonical, *value),
        )
    {
        return true;
    }
    if let Proposition::ConditionIs(condition, value) = proposition
        && assumptions.prop_facts.iter().any(|fact| {
            assumptions
                .forall_instantiations_for_condition(fact, condition)
                .into_iter()
                .any(|instance| {
                    let mut body = &instance;
                    let mut premises = Vec::new();
                    while let Proposition::Implies(premise, rest) = body {
                        premises.push(premise.as_ref());
                        body = rest;
                    }
                    let Proposition::ConditionIs(_, instance_value) = body else {
                        return false;
                    };
                    instance_value == value
                        && c_condition_facts_equivalent_for_memory_resolution(
                            body,
                            &Proposition::ConditionIs(condition.clone(), *value),
                            assumptions,
                        )
                        && premises
                            .into_iter()
                            .all(|premise| certification_proves_proposition(assumptions, premise))
                })
        })
    {
        return true;
    }
    match proposition {
        // Order conditions use the deterministic bounded order prover; the
        // fuel-dependent simp decision procedure stays out of certification.
        Proposition::ConditionIs(condition, value)
            if assumptions.proves_order_condition_for_memory_resolution(condition, *value) =>
        {
            true
        }
        Proposition::ConditionIs(condition, value)
            if shifted_order_condition_proven(assumptions, condition, *value) =>
        {
            true
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if range_folds_alpha_equivalent(left, right) =>
        {
            true
        }
        // Both sides resolve to one known constant through equality facts
        // and per-load snapshot bridging (deterministic and fuel-free).
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && assumptions.constants_known_equal_after_normalization(left, right) =>
        {
            true
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && assumptions
                    .exact_signed_intervals_equal(left, right)
                    .is_some_and(|equal| equal) =>
        {
            true
        }
        // A signed comparison whose sides both resolve to known constants
        // through equality facts and per-load snapshot bridging.
        Proposition::ConditionIs(condition, value)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && assumptions
                    .signed_comparison_by_constant_normalization(condition)
                    .is_some_and(|known| known == *value) =>
        {
            true
        }
        // One side equals a recorded load spelling by an equality fact and
        // the two loads denote the same framed cell.
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && certification_proves_equality_via_load_fact(assumptions, left, right) =>
        {
            true
        }
        Proposition::And(left, right) => {
            certification_proves_proposition(assumptions, left)
                && certification_proves_proposition(assumptions, right)
        }
        Proposition::Or(left, right) => {
            certification_proves_proposition(assumptions, left)
                || certification_proves_proposition(assumptions, right)
                // Excluded middle over decidable conditions: `L or R` holds
                // when assuming `not L` certifies `R` (and symmetrically).
                || match left.as_ref() {
                    Proposition::ConditionIs(condition, value) => {
                        let negated = assumptions.clone().assume_proposition(
                            Proposition::ConditionIs(condition.clone(), !value),
                        );
                        certification_proves_proposition(&negated, right)
                    }
                    _ => false,
                }
                || match right.as_ref() {
                    Proposition::ConditionIs(condition, value) => {
                        let negated = assumptions.clone().assume_proposition(
                            Proposition::ConditionIs(condition.clone(), !value),
                        );
                        certification_proves_proposition(&negated, left)
                    }
                    _ => false,
                }
        }
        Proposition::Exists {
            var,
            sort: sort @ (Sort::CInt32 | Sort::Bitvector32),
            body,
            ..
        } => {
            // An assumed existential proves the goal up to renaming of the
            // bound variable; bound variables are freshened per lowering
            // pass, so exact matching alone would never fire.
            let alpha_matched = assumptions.prop_facts.iter().any(|fact| {
                let Proposition::Exists {
                    var: fact_var,
                    sort: fact_sort,
                    body: fact_body,
                    ..
                } = fact
                else {
                    return false;
                };
                if fact_sort != sort {
                    return false;
                }
                let renamed = substitute_bitvector_variable_in_proposition(
                    fact_body,
                    *fact_var,
                    &Bitvector32Term::Variable(*var),
                );
                if propositions_alpha_equivalent(&renamed, body) {
                    return true;
                }
                // Weakening under the binder: an existential of a
                // conjunction proves the existential of any subset of its
                // conjuncts.
                let mut fact_conjuncts = Vec::new();
                proposition_conjuncts(&renamed, &mut fact_conjuncts);
                let mut goal_conjuncts = Vec::new();
                proposition_conjuncts(body, &mut goal_conjuncts);
                goal_conjuncts.iter().all(|goal| {
                    fact_conjuncts
                        .iter()
                        .any(|fact| propositions_alpha_equivalent(fact, goal))
                })
            });
            if alpha_matched {
                return true;
            }
            // One-point rule: `P[t/x]` proves `exists x. P` when a conjunct
            // pins `x` to a witness term `t`.
            let mut candidates = Vec::new();
            exists_equality_witness_candidates(*var, body, &mut candidates);
            candidates.into_iter().any(|witness| {
                let instantiated =
                    substitute_bitvector_variable_in_proposition(body, *var, &witness);
                certification_proves_proposition(assumptions, &instantiated)
            })
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
                || assumptions
                    .has_anchored_bitvector_equality_fact_for_memory_resolution(left, right)
                || assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(
                        left.as_ref().clone(),
                        right.as_ref().clone(),
                    ),
                    true,
                ) && assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ),
                    true,
                )
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
                || assumptions.has_pointer_equality_path(left, right)
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            pointer_offsets_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        Proposition::Equal(Term::CValue(left), Term::CValue(right)) => {
            c_values_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_order_condition_for_memory_resolution(condition, *value)
                || assumptions.has_matching_condition_fact_for_memory_resolution(condition, *value)
        }
        Proposition::Predicate { .. } => {
            assumptions.proves(proposition)
                || certification_proves_predicate_from_quantified_implication(
                    assumptions,
                    proposition,
                )
        }
        _ => assumptions.proves(proposition),
    }
}

/// True for a closed universally-quantified implication chain that concludes
/// in an opaque predicate — the shape of a surface-verified theorem fact.
fn quantified_predicate_implication_fact(fact: &Proposition) -> bool {
    let mut body = fact;
    let mut binders = 0usize;
    while let Proposition::ForAll { body: inner, .. } = body {
        binders += 1;
        body = inner.as_ref();
    }
    if binders == 0 {
        return false;
    }
    while let Proposition::Implies(_, rest) = body {
        body = rest.as_ref();
    }
    matches!(body, Proposition::Predicate { .. })
}

/// Certifies an opaque predicate goal by instantiating an assumed
/// universally-quantified implication (typically a verified theorem): the
/// fact's predicate conclusion pins each bound variable against the goal's
/// arguments, and every premise must then certify under that instantiation.
fn certification_proves_predicate_from_quantified_implication(
    assumptions: &Assumptions,
    goal: &Proposition,
) -> bool {
    let Proposition::Predicate { name, arguments } = goal else {
        return false;
    };
    assumptions.prop_facts.iter().any(|fact| {
        let mut binders = Vec::new();
        let mut body = fact;
        while let Proposition::ForAll {
            var, body: inner, ..
        } = body
        {
            binders.push(*var);
            body = inner.as_ref();
        }
        if binders.is_empty() {
            return false;
        }
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            premises.push(premise.as_ref().clone());
            conclusion = rest.as_ref();
        }
        let Proposition::Predicate {
            name: fact_name,
            arguments: fact_arguments,
        } = conclusion
        else {
            return false;
        };
        if fact_name != name || fact_arguments.len() != arguments.len() {
            return false;
        }
        let mut substitution: Vec<(Variable, Bitvector32Term)> = Vec::new();
        for (fact_argument, goal_argument) in fact_arguments.iter().zip(arguments) {
            let bound_variable = match fact_argument {
                Term::CValue(
                    CValue::Int32(Bitvector32Term::Variable(var))
                    | CValue::UInt8(Bitvector32Term::Variable(var)),
                ) if binders.contains(var) => Some(*var),
                _ => None,
            };
            let Some(var) = bound_variable else {
                if fact_argument != goal_argument {
                    return false;
                }
                continue;
            };
            let goal_term = match goal_argument {
                Term::CValue(CValue::Int32(term) | CValue::UInt8(term)) => term.clone(),
                Term::Bitvector32(term) => term.clone(),
                _ => return false,
            };
            match substitution.iter().find(|(existing, _)| *existing == var) {
                None => substitution.push((var, goal_term)),
                Some((_, existing)) if *existing == goal_term => {}
                Some(_) => return false,
            }
        }
        if binders
            .iter()
            .any(|var| !substitution.iter().any(|(bound, _)| bound == var))
        {
            return false;
        }
        premises.into_iter().all(|premise| {
            let mut instantiated = premise;
            for (var, witness) in &substitution {
                instantiated =
                    substitute_bitvector_variable_in_proposition(&instantiated, *var, witness);
            }
            certification_proves_proposition(assumptions, &instantiated)
        })
    })
}

fn certification_proves_post_proposition(
    assumptions: &Assumptions,
    proposition: &Proposition,
    post_memory: &CMemory,
    execution_facts: &[ExecutionPureFact],
) -> bool {
    if certification_proves_proposition(assumptions, proposition) {
        return true;
    }
    // Verified calls contribute independently certified public
    // postconditions. Keep their explicit snapshots and reason from the
    // complete set: a later call may relate the final state to an earlier
    // snapshot while another postcondition relates that snapshot to a local
    // result. Checking one call fact at a time loses exactly that valid
    // composition.
    let public_condition_facts = execution_facts
        .iter()
        .filter(|fact| fact.is_public() && fact.is_certified())
        .filter_map(|fact| match fact.proposition() {
            proposition @ Proposition::ConditionIs(_, _) => Some(proposition.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !public_condition_facts.is_empty()
        && certification_proves_proposition(
            &assumptions_with_propositions(assumptions, &public_condition_facts),
            proposition,
        )
    {
        return true;
    }
    if execution_facts
        .iter()
        .enumerate()
        .filter(|(_, fact)| fact.is_certified())
        .any(|(source_index, fact)| {
            let Some(CertifiedMemoryStore {
                after,
                pointer,
                value: CValue::Int32(value) | CValue::UInt8(value),
                authorized_range,
                ..
            }) = fact.certified_store_data()
            else {
                return false;
            };
            let mut current = after;
            for later in &execution_facts[source_index + 1..] {
                let Some(CertifiedMemoryStore {
                    before,
                    after,
                    pointer: later_pointer,
                    authorized_range: later_range,
                    ..
                }) = later.certified_store_data()
                else {
                    continue;
                };
                if before != current {
                    continue;
                }
                let disjoint = pointer.blocks_proven_distinct(later_pointer)
                    || pointers_proven_distinct_for_memory_resolution(
                        pointer,
                        later_pointer,
                        assumptions,
                    )
                    || authorized_range.as_ref().is_some_and(|source_range| {
                        later_range.as_ref().is_some_and(|later_range| {
                            assumptions
                                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                                    source_range,
                                    later_range,
                                )
                        })
                    });
                if !disjoint {
                    return false;
                }
                current = after;
            }
            if current != post_memory
                && !c_memory_load_is_unchanged(current, post_memory, pointer, assumptions)
            {
                return false;
            }
            let stored_fact = Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(post_memory.clone()),
                        Box::new(pointer.clone()),
                    ),
                    value.clone(),
                ),
                true,
            );
            let stored_assumptions =
                assumptions_with_propositions(assumptions, &[stored_fact]);
            certification_proves_proposition(&stored_assumptions, proposition)
        })
    {
        return true;
    }
    let transported_fact_proves = |fact: &Proposition| {
        let Some(theorem) = prove_c_condition_fact_transport(fact, post_memory, assumptions) else {
            return false;
        };
        let Proposition::Implies(source, target) = theorem.proposition() else {
            return false;
        };
        if source.as_ref() != fact {
            return false;
        }
        let transported_assumptions =
            assumptions_with_propositions(assumptions, &[target.as_ref().clone()]);
        certification_proves_proposition(&transported_assumptions, proposition)
    };
    let explicit_facts = execution_facts
        .iter()
        .filter(|fact| fact.is_certified())
        .filter_map(|fact| match fact.proposition() {
            proposition @ Proposition::ConditionIs(_, _) => Some(proposition.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    explicit_facts
        .iter()
        .filter(|fact| {
            matches!(
                (*fact, proposition),
                (
                    Proposition::ConditionIs(_, _),
                    Proposition::ConditionIs(_, _)
                ) | (Proposition::Equal(_, _), Proposition::Equal(_, _))
            )
        })
        .any(transported_fact_proves)
}

fn resources_certify_loadability(
    state: &CState,
    resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    match proposition {
        Proposition::ForAll { body, .. } => {
            return resources_certify_loadability(state, resources, body, assumptions);
        }
        Proposition::Implies(premise, conclusion) => {
            let assumptions = assumptions
                .clone()
                .assume_proposition(premise.as_ref().clone());
            return resources_certify_loadability(state, resources, conclusion, &assumptions);
        }
        Proposition::And(left, right) => {
            return resources_certify_loadability(state, resources, left, assumptions)
                && resources_certify_loadability(state, resources, right, assumptions);
        }
        _ => {}
    }
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = proposition
    else {
        return false;
    };
    memory_snapshots_proven_equal_at_pointer(memory, state.memory(), base, assumptions)
        && bytes
            .as_const()
            .is_some_and(|bytes| resource_context_has_read(resources, base, bytes, assumptions))
}

fn contract_endpoints_certify_loadability(
    entry_state: &CState,
    entry_resources: &ResourceContext,
    post_state: &CState,
    post_resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    resources_certify_loadability(entry_state, entry_resources, proposition, assumptions)
        || resources_certify_loadability(post_state, post_resources, proposition, assumptions)
}

pub fn c_function_outcomes_definitionally_equal(
    function: &CFunction,
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &Assumptions,
) -> bool {
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: _,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: _,
                state: right_state,
            },
        ) => {
            if !c_function_outcomes_program_state_definitionally_equal(left, right, assumptions) {
                return false;
            }
            resource_context_definitionally_contains(
                left_state.resources(),
                right_state.resources(),
                function.composite_resource_definitions(),
                left_state.memory(),
                assumptions,
            ) || resource_context_definitionally_contains(
                right_state.resources(),
                left_state.resources(),
                function.composite_resource_definitions(),
                left_state.memory(),
                assumptions,
            ) || resource_contexts_definitionally_equal(
                function,
                left_state.memory(),
                left_state.resources(),
                right_state.memory(),
                right_state.resources(),
                assumptions,
            )
        }
        _ => left == right,
    }
}

/// Compares the observable program portion of two outcomes, leaving ghost
/// resource representation to a separate kernel certificate.
///
/// Proof replay uses this only to select the independently reproduced path;
/// [`certify_c_function_execution_path_resource_representation`] remains the
/// authority that accepts the selected path's resources.
pub fn c_function_outcomes_program_state_definitionally_equal(
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &Assumptions,
) -> bool {
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: left_value,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: right_value,
                state: right_state,
            },
        ) => {
            c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
                && c_memories_definitionally_equal(
                    left_state.memory(),
                    right_state.memory(),
                    assumptions,
                )
        }
        _ => left == right,
    }
}

/// Proves two return outcomes equal by store provenance: when both
/// executions performed the same ordered sequence of certified stores
/// (pointers and values definitionally equal), their final external
/// memories are equal by construction, so the deep memory comparison is
/// unnecessary and only return values and resources need checking.
pub fn c_function_outcomes_equal_by_store_provenance(
    function: &CFunction,
    left: &CFunctionOutcome,
    left_facts: &[ExecutionPureFact],
    right: &CFunctionOutcome,
    right_facts: &[ExecutionPureFact],
    assumptions: &Assumptions,
) -> bool {
    if !c_function_outcomes_program_state_equal_by_store_provenance(
        left,
        left_facts,
        right,
        right_facts,
        assumptions,
    ) {
        return false;
    }
    let (
        CFunctionOutcome::Return {
            state: left_state, ..
        },
        CFunctionOutcome::Return {
            state: right_state, ..
        },
    ) = (left, right)
    else {
        return false;
    };
    resource_context_definitionally_contains(
        left_state.resources(),
        right_state.resources(),
        function.composite_resource_definitions(),
        left_state.memory(),
        assumptions,
    ) || resource_context_definitionally_contains(
        right_state.resources(),
        left_state.resources(),
        function.composite_resource_definitions(),
        left_state.memory(),
        assumptions,
    ) || resource_contexts_definitionally_equal(
        function,
        left_state.memory(),
        left_state.resources(),
        right_state.memory(),
        right_state.resources(),
        assumptions,
    )
}

/// Compares the observable program state of two return paths by their
/// independently certified store sequences. Resource representation remains
/// the responsibility of the separate resource certificate.
pub fn c_function_outcomes_program_state_equal_by_store_provenance(
    left: &CFunctionOutcome,
    left_facts: &[ExecutionPureFact],
    right: &CFunctionOutcome,
    right_facts: &[ExecutionPureFact],
    assumptions: &Assumptions,
) -> bool {
    let (
        CFunctionOutcome::Return {
            value: left_value, ..
        },
        CFunctionOutcome::Return {
            value: right_value, ..
        },
    ) = (left, right)
    else {
        return false;
    };
    let left_stores = left_facts
        .iter()
        .filter_map(|fact| fact.certified_store_data())
        .collect::<Vec<_>>();
    let right_stores = right_facts
        .iter()
        .filter_map(|fact| fact.certified_store_data())
        .collect::<Vec<_>>();
    if left_stores.len() != right_stores.len() {
        return false;
    }
    let chains_equal = left_stores.iter().zip(&right_stores).all(|(left, right)| {
        pointers_proven_equal_for_memory_resolution(&left.pointer, &right.pointer, assumptions)
            && c_values_proven_equal_for_memory_resolution(&left.value, &right.value, assumptions)
    });
    chains_equal
        && c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
}

fn c_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    if memories_proven_equal_for_memory_resolution(left, right, assumptions) {
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
    memory_cells_definitionally_contained(left, right, assumptions)
        && memory_cells_definitionally_contained(right, left, assumptions)
}

fn memory_cells_definitionally_contained(
    source: &CMemory,
    target: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    for (source_pointer, source_value) in source
        .cells
        .iter()
        .filter(|(pointer, _)| !pointer.block.starts_with("local:"))
    {
        let matching = target.cells.iter().find(|(target_pointer, _)| {
            pointers_proven_equal_for_memory_resolution(source_pointer, target_pointer, assumptions)
        });
        let equal = if let Some((_, target_value)) = matching {
            c_values_proven_equal_for_memory_resolution(source_value, target_value, assumptions)
        } else {
            materialized_load_is_unchanged(source_value, target, source_pointer, assumptions)
        };
        if !equal {
            return false;
        }
    }
    true
}

fn materialized_load_is_unchanged(
    value: &CValue,
    symbolic_memory: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    let load = match value {
        CValue::Int32(Bitvector32Term::MemoryLoad(memory, load_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(memory, load_pointer)) => {
            (memory.as_ref(), load_pointer.as_ref())
        }
        _ => return false,
    };
    pointers_proven_equal_for_memory_resolution(load.1, pointer, assumptions)
        && c_memory_load_is_unchanged(load.0, symbolic_memory, pointer, assumptions)
}

/// Changes only the bounded symbolic representation of a certified return path.
///
/// Program values and memory must be definitionally equal using the path's
/// certified pure, memory-effect, and resource-separation facts. The old and
/// new resource contexts must mutually satisfy every fact under those same
/// assumptions.
pub fn certify_c_function_execution_path_resource_representation(
    path: &SymbolicCExecutionPath,
    desired_outcome: CFunctionOutcome,
    desired_facts: &[ExecutionPureFact],
) -> Option<SymbolicCExecutionPath> {
    let mut proposition = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proposition {
        premises.push(premise.as_ref().clone());
        proposition = body;
    }
    let (state, function, arguments, outcome, verifies) = match proposition {
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, false),
        Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, true),
        _ => return None,
    };
    let (
        CFunctionOutcome::Return {
            value,
            state: return_state,
        },
        CFunctionOutcome::Return {
            value: desired_value,
            state: desired_state,
        },
    ) = (outcome, &desired_outcome)
    else {
        return (outcome == &desired_outcome).then(|| path.clone());
    };
    premises.extend(
        path.execution_facts()
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    let preliminary_assumptions = assumptions_with_propositions(&path.assumptions, &premises);
    let observable_resource_facts = return_state
        .resources()
        .observable_facts(&preliminary_assumptions)
        .ok()?;
    premises.extend(observable_resource_facts);
    let assumptions = assumptions_with_propositions(&path.assumptions, &premises);
    let values_equal =
        c_values_proven_equal_for_memory_resolution(value, desired_value, &assumptions);
    let memories_equal = c_memories_definitionally_equal(
        return_state.memory(),
        desired_state.memory(),
        &assumptions,
    ) || {
        // Store provenance: the same ordered certified stores from the same
        // entry produce the same external memory by construction.
        let certified_stores = path
            .execution_facts()
            .iter()
            .filter_map(|fact| fact.certified_store_data().cloned())
            .collect::<Vec<_>>();
        let desired_stores = desired_facts
            .iter()
            .filter_map(|fact| fact.certified_store_data())
            .collect::<Vec<_>>();
        certified_stores.len() == desired_stores.len()
            && certified_stores
                .iter()
                .zip(&desired_stores)
                .all(|(left, right)| {
                    pointers_proven_equal_for_memory_resolution(
                        &left.pointer,
                        &right.pointer,
                        &assumptions,
                    ) || (left.pointer.block == right.pointer.block
                        && c_pointer_offsets_proven_equal_for_effect(
                            &left.pointer.offset,
                            &right.pointer.offset,
                            &assumptions,
                        ))
                })
            && certified_stores
                .iter()
                .zip(&desired_stores)
                .all(|(left, right)| {
                    c_values_proven_equal_for_memory_resolution(
                        &left.value,
                        &right.value,
                        &assumptions,
                    )
                })
    };
    if !values_equal || !memories_equal {
        return None;
    }
    let resources_equal = resource_context_definitionally_contains(
        return_state.resources(),
        desired_state.resources(),
        function.composite_resource_definitions(),
        return_state.memory(),
        &assumptions,
    ) || resource_contexts_definitionally_equal(
        function,
        return_state.memory(),
        return_state.resources(),
        desired_state.memory(),
        desired_state.resources(),
        &assumptions,
    );
    if !resources_equal {
        return None;
    }

    let conclusion = if verifies {
        Proposition::CFunctionVerifies {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: desired_outcome,
        }
    } else {
        Proposition::CFunctionExecutes {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: desired_outcome,
        }
    };
    let theorem = Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    );
    Some(SymbolicCExecutionPath {
        assumptions: path.assumptions.clone(),
        facts: path.facts.clone(),
        effect_facts: path.effect_facts.clone(),
        obligations: path.obligations.clone(),
        theorem,
    })
}

struct CertifiedFunctionClaimPath {
    caller_state: CState,
    return_state: Option<CState>,
    entry_state: CState,
    entry_resources: ResourceContext,
    post_state: Option<CState>,
    post_resources: Option<ResourceContext>,
    assumptions: Assumptions,
    execution_facts: Vec<ExecutionPureFact>,
    effect_facts: Vec<ExecutionPureFact>,
}

fn prepare_function_claim_path(
    function: &CFunction,
    path: &SymbolicCExecutionPath,
) -> Result<CertifiedFunctionClaimPath, String> {
    let Some((caller_state, arguments, outcome, assumptions)) =
        certified_function_path_parts(function, path)
    else {
        return Err("the certified path does not belong to the exact function".to_string());
    };
    let Some(mut entry_state) = c_function_entry_state(caller_state, function, arguments) else {
        return Err("the function entry state cannot be reconstructed".to_string());
    };
    let mut budget = ExecutionBudget::default();
    let Ok(Ok(required_resources)) = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        &assumptions,
        &mut budget,
    ) else {
        return Err("the required resource context cannot be evaluated".to_string());
    };
    let Some((_, definition_facts)) = expand_all_composite_resource_facts_and_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    ) else {
        return Err("the required composite resources cannot be expanded".to_string());
    };
    let assumptions = assumptions_with_propositions(&assumptions, &definition_facts);
    let Some(entry_resources) = expand_all_composite_resource_facts(
        entry_state.resources(),
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    ) else {
        return Err("the entry resource context cannot be expanded".to_string());
    };
    let Ok(resource_facts) = entry_resources.observable_facts(&assumptions) else {
        return Err("the entry resource context is not observable".to_string());
    };
    entry_state.resources = entry_resources.clone();
    let execution_facts = path.execution_facts();
    let assumptions = assumptions_with_propositions(&assumptions, &resource_facts);
    // A verification condition may be local to one symbolic path. Branch
    // guards and independently certified callee postconditions are evidence
    // on that path, just as assumable definedness obligations are; omitting
    // them here incorrectly rejects safe guarded calls after certification.
    // Non-assumable obligations are deliberately excluded by
    // `assumptions_with_path_context`, so this cannot prove a verification
    // condition by assuming the condition itself.
    let assumptions =
        assumptions_with_path_context(&assumptions, &execution_facts, path.obligations());
    let effect_facts = path.effect_facts.clone();
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        if let Some(obligation) = path.obligations().iter().find(|obligation| {
            !certification_proves_proposition(&assumptions, obligation.proposition())
                && !loadable_covered_by_fact(&assumptions, obligation.proposition())
                && !forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
        }) {
            return Err(format!(
                "the divergent verification path has an unproved condition: {:?} ({})",
                obligation.proposition(),
                obligation.context().unwrap_or("no context")
            ));
        }
        return Ok(CertifiedFunctionClaimPath {
            caller_state: caller_state.clone(),
            return_state: None,
            entry_state,
            entry_resources,
            post_state: None,
            post_resources: None,
            assumptions,
            execution_facts,
            effect_facts,
        });
    }
    let CFunctionOutcome::Return {
        value,
        state: return_state,
    } = outcome
    else {
        return Err(format!("the certified path is not safe: {outcome:?}"));
    };
    let Some(post_resources) = expand_all_composite_resource_facts(
        return_state.resources(),
        function.composite_resource_definitions(),
        return_state.memory(),
        &assumptions,
    ) else {
        return Err("the returned resource context cannot be expanded".to_string());
    };
    let Ok(post_resource_facts) = post_resources.observable_facts(&assumptions) else {
        return Err("the returned resource context is not observable".to_string());
    };
    let assumptions = assumptions_with_propositions(&assumptions, &post_resource_facts);
    let mut post_state = entry_state
        .clone()
        .with_memory(return_state.memory().clone());
    post_state.resources = post_resources.clone();
    if function.return_type() != CType::Void {
        post_state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    if let Some(obligation) = path.obligations().iter().find(|obligation| {
        let proved = certification_proves_proposition(&assumptions, obligation.proposition())
            || loadable_covered_by_fact(&assumptions, obligation.proposition())
            || forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
            || contract_endpoints_certify_loadability(
                &entry_state,
                &entry_resources,
                &post_state,
                &post_resources,
                obligation.proposition(),
                &assumptions,
            );
        !proved
    }) {
        return Err(format!(
            "the execution path has an unproved verification condition: {:?} ({})",
            obligation.proposition(),
            obligation.context().unwrap_or("no context")
        ));
    }

    Ok(CertifiedFunctionClaimPath {
        caller_state: caller_state.clone(),
        return_state: Some(return_state.clone()),
        entry_state,
        entry_resources,
        post_state: Some(post_state),
        post_resources: Some(post_resources),
        assumptions,
        execution_facts,
        effect_facts,
    })
}

fn function_claim_holds_on_prepared_path(
    function: &CFunction,
    claim: &CFunctionContractClaim,
    path: &CertifiedFunctionClaimPath,
) -> bool {
    let CertifiedFunctionClaimPath {
        caller_state,
        return_state,
        entry_state,
        entry_resources,
        post_state,
        post_resources,
        assumptions,
        execution_facts,
        effect_facts,
    } = path;
    let mut budget = ExecutionBudget::default();
    match claim.target() {
        CFunctionContractClaimTarget::BodySafety => true,
        CFunctionContractClaimTarget::EnsureProposition(index) => {
            let (Some(return_state), Some(post_state), Some(post_resources)) =
                (return_state, post_state, post_resources)
            else {
                return true;
            };
            let Some(ensure) = function.contract_ensures().get(*index) else {
                return false;
            };
            let lowering_assumptions = assumptions.clone().allow_symbolic_contract_loads();
            let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
                post_state,
                ensure,
                Some(entry_state),
                &lowering_assumptions,
                &mut budget,
            ) else {
                return false;
            };
            !paths.is_empty()
                && paths.into_iter().all(|path| {
                    let obligations_hold = path.obligations.iter().all(|obligation| {
                        certification_proves_proposition(assumptions, obligation.proposition())
                            || contract_endpoints_certify_loadability(
                                entry_state,
                                entry_resources,
                                post_state,
                                post_resources,
                                obligation.proposition(),
                                assumptions,
                            )
                            || loadable_covered_by_fact(assumptions, obligation.proposition())
                            || forall_loadable_covered_by_fact(
                                assumptions,
                                obligation.proposition(),
                            )
                            || certification_proves_exists_obligation_from_facts(
                                assumptions,
                                obligation.proposition(),
                            )
                    });
                    let mut path_propositions = path
                        .facts
                        .iter()
                        .map(|fact| fact.proposition().clone())
                        .collect::<Vec<_>>();
                    let assumption_facts =
                        assumptions.prop_facts.iter().cloned().collect::<Vec<_>>();
                    path_propositions.extend(finite_forall_instantiations(&assumption_facts));
                    path_propositions
                        .extend(finite_forall_instantiations(&path_propositions.clone()));
                    let path_assumptions =
                        assumptions_with_propositions(assumptions, &path_propositions);
                    let proposition_holds = certification_proves_post_proposition(
                        &path_assumptions,
                        &path.proposition,
                        return_state.memory(),
                        execution_facts,
                    );
                    obligations_hold && proposition_holds
                })
        }
        CFunctionContractClaimTarget::EnsureResource(index) => {
            let (Some(return_state), Some(post_state)) = (return_state, post_state) else {
                return true;
            };
            let Some(resource) = function.resource_ensures().get(*index) else {
                return false;
            };
            let Ok(Ok(expected)) = evaluate_function_resource_context(
                post_state,
                std::slice::from_ref(resource),
                assumptions,
                &mut budget,
            ) else {
                return false;
            };
            expected.facts().iter().all(|fact| {
                resource_context_satisfies_definitional_fact(
                    return_state.resources(),
                    fact,
                    function.composite_resource_definitions(),
                    return_state.memory(),
                    assumptions,
                )
            })
        }
        CFunctionContractClaimTarget::Effect => {
            let mut mutable_ranges = Vec::new();
            for segment in function.contract_mutable() {
                if segment.guard().is_some_and(|guard| {
                    evaluate_guarded_contract_condition(
                        guard,
                        entry_state,
                        assumptions,
                        &mut budget,
                    ) == Some(false)
                }) {
                    continue;
                }
                let Ok(Ok(segment)) =
                    evaluate_loop_effect_segment(entry_state, segment, assumptions, &mut budget)
                else {
                    return false;
                };
                mutable_ranges.push(CMemoryRange::new(segment.base, segment.start, segment.end));
            }
            let mut effect_memory = caller_state.memory().clone();
            let mut seen_transitions = Vec::<(CMemory, CMemory)>::new();
            let is_function_fresh_heap_pointer = |pointer: &Pointer, current: &CMemory| {
                let matches_allocation = |memory: &CMemory| {
                    memory.heap.live_allocations.keys().any(|base| {
                        base == pointer
                            || super::assumptions::pointers_equal_ignoring_memories(base, pointer)
                            || pointers_proven_equal_for_memory_resolution(
                                base,
                                pointer,
                                assumptions,
                            )
                    })
                };
                !matches_allocation(entry_state.memory())
                    && (matches!(pointer.block, PointerBlock::Heap(_))
                        || matches_allocation(current))
            };
            let effects_are_bounded = effect_facts.iter().all(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly {
                    before,
                    after,
                    pointers,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    pointers
                        .iter()
                        .filter(|pointer| !pointer.block.starts_with("local:"))
                        .all(|pointer| {
                            is_function_fresh_heap_pointer(pointer, before)
                                || mutable_ranges.iter().any(|range| {
                                    assumptions.pointer_access_in_range(
                                        pointer,
                                        4,
                                        range.base(),
                                        range.start(),
                                        range.end(),
                                    )
                                })
                        })
                }
                Proposition::CMemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges: nested_ranges,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    nested_ranges.iter().all(|nested| {
                        is_function_fresh_heap_pointer(nested.base(), before)
                            || mutable_ranges
                                .iter()
                                .any(|allowed| memory_range_covers(allowed, nested, assumptions))
                    })
                }
                Proposition::CHeapLifetimeRetired {
                    before,
                    after,
                    allocation_base,
                    bytes,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !heap_retirement_effect_is_valid(before, after, allocation_base, bytes) {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    true
                }
                _ => true,
            });
            let endpoint_matches = return_state.as_ref().is_none_or(|return_state| {
                c_effect_memories_definitionally_equal(
                    &effect_memory,
                    return_state.memory(),
                    assumptions,
                ) || c_effect_memory_advances_over_internal_heap_state(
                    &effect_memory,
                    return_state.memory(),
                    entry_state.memory(),
                    assumptions,
                )
            });
            effects_are_bounded && endpoint_matches
        }
    }
}

pub(super) fn c_effect_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    let without_locals = |memory: &CMemory| {
        let mut external = memory.clone();
        external
            .blocks
            .retain(|block, _| !block.starts_with("local:"));
        external
            .cells
            .retain(|pointer, _| !pointer.block.starts_with("local:"));
        external
    };
    let left = without_locals(left);
    let right = without_locals(right);
    left.heap == right.heap && c_memories_definitionally_equal(&left, &right, assumptions)
}

/// Accepts internal heap bookkeeping between externally visible effects:
/// newly allocated trusted blocks and the registration of an already-owned
/// symbolic allocation before direct `free`. Removing only those additions
/// leaves a memory that must still match the preceding endpoint exactly.
pub(super) fn c_effect_memory_advances_over_internal_heap_state(
    before: &CMemory,
    after: &CMemory,
    function_entry: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    let fresh_blocks = after
        .blocks
        .keys()
        .filter(|block| {
            matches!(block, PointerBlock::Heap(_))
                && !before.blocks.contains_key(*block)
                && !function_entry.blocks.contains_key(*block)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let added_allocation_claims = after
        .heap
        .live_allocations
        .keys()
        .filter(|pointer| !before.heap.live_allocations.contains_key(*pointer))
        .cloned()
        .collect::<BTreeSet<_>>();
    if fresh_blocks.is_empty() && added_allocation_claims.is_empty() {
        return false;
    }
    let mut stripped = after.clone();
    stripped
        .blocks
        .retain(|block, _| !fresh_blocks.contains(block));
    stripped
        .cells
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    stripped.heap.live_allocations.retain(|pointer, _| {
        !fresh_blocks.contains(&pointer.block) && !added_allocation_claims.contains(pointer)
    });
    stripped
        .heap
        .retired_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    stripped
        .heap
        .pending_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    stripped
        .heap
        .uninitialized_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.block));
    c_effect_memories_definitionally_equal(before, &stripped, assumptions)
}

fn heap_retirement_effect_is_valid(
    before: &CMemory,
    after: &CMemory,
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    let Some(live) = (if before.live_heap_block_size(allocation_base).is_some() {
        Some(before.clone())
    } else {
        before
            .clone()
            .with_heap_allocation_claim(allocation_base.clone(), bytes.clone())
    }) else {
        return false;
    };
    live.live_heap_block_size(allocation_base) == Some(bytes)
        && live
            .free_heap_block(allocation_base)
            .is_ok_and(|expected| expected == *after)
}

/// Certifies every exact contract claim in one pass over a kernel-produced,
/// complete execution frontier.
///
/// Path validity, resource expansion, and verification conditions are checked
/// once per path and then shared by the individual claim checks.
pub fn c_verified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Option<Vec<CVerifiedFunctionContractClaim>> {
    let execution = &contract_execution.execution;
    if execution.limit().is_some() || execution.paths().is_empty() {
        return None;
    }
    let timings = crate::instrumentation::enabled();
    let prepare_started = std::time::Instant::now();
    let paths = execution
        .paths()
        .iter()
        .map(|path| prepare_function_claim_path(function, path))
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    if timings {
        crate::instrumentation::emit(
            crate::instrumentation::VerificationEvent::ClaimPathsPrepared {
                function: function.name().to_string(),
                count: paths.len(),
                elapsed: prepare_started.elapsed(),
            },
        );
    }
    function
        .contract_claims()
        .iter()
        .map(|claim| {
            let claim_started = std::time::Instant::now();
            let holds = paths
                .iter()
                .all(|path| function_claim_holds_on_prepared_path(function, claim, path));
            if timings {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::ClaimFinished {
                        function: function.name().to_string(),
                        key: format!("{:?}", claim.key()),
                        elapsed: claim_started.elapsed(),
                    },
                );
            }
            holds.then(|| CVerifiedFunctionContractClaim {
                function: function.clone(),
                key: claim.key().clone(),
            })
        })
        .collect()
}

/// Reports the exact contract claims that the checked execution frontier does
/// not establish. This is diagnostic information only: unlike the companion
/// certification API, it cannot mint proof objects.
///
/// `None` means the frontier itself is incomplete or could not be prepared for
/// claim checking. An empty vector means every claim holds.
pub fn c_unverified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Result<Vec<CFunctionContractClaimKey>, String> {
    let execution = &contract_execution.execution;
    if let Some(limit) = execution.limit() {
        return Err(format!("symbolic execution reached its {limit:?} limit"));
    }
    if execution.paths().is_empty() {
        return Err("symbolic execution produced no paths".to_string());
    }
    let paths = execution
        .paths()
        .iter()
        .enumerate()
        .map(|(index, path)| {
            prepare_function_claim_path(function, path)
                .map_err(|reason| format!("execution path {index} is invalid: {reason}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(function
        .contract_claims()
        .iter()
        .filter(|claim| {
            !paths
                .iter()
                .all(|path| function_claim_holds_on_prepared_path(function, claim, path))
        })
        .map(|claim| claim.key().clone())
        .collect())
}

/// Certifies one contract claim only after a kernel-produced complete
/// execution frontier establishes that exact claim for the exact function.
pub fn c_verified_function_contract_claim(
    function: &CFunction,
    key: CFunctionContractClaimKey,
    execution: &CFunctionContractExecution,
) -> Option<CVerifiedFunctionContractClaim> {
    c_verified_function_contract_claims(function, execution)?
        .into_iter()
        .find(|proof| proof.key == key)
}

/// Packages an opaque rule only after every recorded contract claim has a
/// certificate for this exact function.
pub fn c_verified_function_rule(
    function: CFunction,
    proofs: &[CVerifiedFunctionContractClaim],
) -> Option<CVerifiedFunctionRule> {
    if !function.opaque_contract_supported()
        || function.contract_claims().is_empty()
        || proofs.iter().any(|proof| proof.function != function)
        || function
            .contract_claims()
            .iter()
            .any(|claim| !proofs.iter().any(|proof| proof.key == *claim.key()))
    {
        return None;
    }
    Some(CVerifiedFunctionRule { function })
}

/// Builds an untrusted ranking plan. Supplying a plan is not evidence; the
/// kernel validates it together with the exact verified C functions in
/// [`c_verified_function_termination_rules`].
pub fn c_function_termination_plan(
    function_name: impl Into<String>,
    recursive_measure: Option<CFunctionTerminationMeasure>,
    loop_measures: impl IntoIterator<Item = (usize, String)>,
) -> CFunctionTerminationPlan {
    CFunctionTerminationPlan {
        function_name: function_name.into(),
        recursive_measure,
        loop_measures: loop_measures.into_iter().collect(),
    }
}

/// Creates a scoped hypothesis used only while the language layer verifies one
/// closed set of mutually dependent C contracts. The verification transaction
/// returns no rules if any hypothesized contract fails independent kernel
/// certification, which is the standard partial-correctness recursion rule.
///
/// This is crate-private so an external caller cannot install an unverified
/// recursive contract into a kernel execution environment.
pub(crate) fn c_recursive_function_contract_hypothesis(
    function: CFunction,
) -> Option<CVerifiedFunctionRule> {
    (function.opaque_contract_supported() && !function.contract_claims().is_empty())
        .then_some(CVerifiedFunctionRule { function })
}

pub fn prove_c_function_satisfies_specification(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification_with_environment(
        function,
        specification,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
}

pub fn prove_c_function_satisfies_specification_with_environment(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    let paths = execute_c_function_paths(
        specification.state(),
        &function,
        specification.arguments(),
        &specification_assumptions,
        &environment,
        execution_semantics,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some()
        || path.facts.iter().any(ExecutionPureFact::is_public)
        || !path.obligations.is_empty()
        || &path.outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let proposition = requires.iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        },
        |body, requirement| Proposition::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_function_satisfies_specification_and_propositions(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        assumptions.clone(),
    )?;

    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    if propositions
        .iter()
        .any(|proposition| !specification_assumptions.proves(proposition))
    {
        return None;
    }

    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CFunctionSatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        })
        .chain(propositions)
        .collect(),
    );
    let proposition = specification
        .requires()
        .iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
        });
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_statement_executes_and_propositions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.facts.is_empty() || !path.obligations.is_empty() {
        return None;
    }
    if propositions
        .iter()
        .any(|proposition| !assumptions.proves(proposition))
    {
        return None;
    }
    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CStatementExecutes {
            state,
            statement,
            outcome: path.outcome,
        })
        .chain(propositions)
        .collect(),
    );
    Some(Theorem::new(wrap_proof_facts(
        conclusion,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_max_lt_returns_right(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(a_value, b_value.clone());
    let assumptions = Assumptions::new().assume_condition(condition.clone(), true);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: b_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_c_max_not_lt_returns_left(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits, b_bits);
    let state = c_max_state(a_value.clone(), b_value);
    let assumptions = Assumptions::new().assume_condition(condition.clone(), false);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: a_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_memory_load(memory: CMemory, pointer: Pointer) -> Theorem {
    let outcome = memory.load(&pointer);
    Theorem::new(Proposition::CMemoryLoads {
        memory,
        pointer,
        outcome,
    })
}

pub fn prove_memory_load_after_store_same(
    memory: CMemory,
    pointer: Pointer,
    value: CValue,
) -> Theorem {
    let stored = memory.store(pointer.clone(), value.clone());
    Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer,
        outcome: CExpressionOutcome::Value(value),
    })
}

pub fn prove_memory_load_after_store_other(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
) -> Option<Theorem> {
    if stored_pointer == loaded_pointer {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer: loaded_pointer,
        outcome,
    }))
}

pub fn prove_memory_load_after_store_distinct_under_assumptions(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
    assumptions: Assumptions,
) -> Option<Theorem> {
    if !pointers_proven_distinct(&stored_pointer, &loaded_pointer, &assumptions) {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CMemoryLoads {
            memory: stored,
            pointer: loaded_pointer,
            outcome,
        },
        &assumptions,
        &[],
        &[],
    )))
}

/// Unsound partial while-rule, fenced to kernel tests. NOT an axiom.
///
/// This is deliberately not exported: it is `#[cfg(test)]`-only and
/// `pub(super)`, so it does not exist in a release build and no caller
/// outside `crate::kernel` can reach it. `Theorem::new` is `pub(super)`, so
/// `Proposition::CWhileInvariantRule` is unconstructible as a theorem from
/// outside the kernel too.
///
/// What it checks:
/// - every proposition in `invariant` is provable from `assumptions`, i.e.
///   the invariant holds on entry in the caller's `state`;
/// - there is *at least one* condition-fork context in which the condition is
///   true where the body runs to a single `Normal` path with no leftover
///   facts or obligations, and every proposition in `preserved` is provable;
/// - there is *at least one* condition-fork context in which the condition is
///   false where `postcondition` is provable.
///
/// What it does NOT check, and why that makes it unsound as a while rule:
/// - preservation in *every* condition-true fork, and the exit postcondition
///   in *every* condition-false fork. Both quantifiers are `any`, not `all`,
///   so a fork that breaks the invariant is simply skipped.
/// - any relation between `preserved` and what `body` actually does. The
///   body's post-state is matched as `CStatementOutcome::Normal(_)` and
///   discarded, and `preserved` is discharged against the *pre-body*
///   assumption context. A `preserved` list that holds before the body and
///   fails after it is accepted; see the kernel test
///   `while_invariant_rule_ignores_what_the_body_does_to_the_invariant`.
/// - genericity of `state` / `assumptions`. There is no havoc of the
///   locations the loop modifies, so preservation is shown for one step out
///   of the caller's specific state and does not generalize to an arbitrary
///   iteration.
/// - termination, and framing of memory across iterations.
///
/// Why it is fenced rather than fixed: the sound loop path already exists as
/// `c_loop_preservation_contexts` / `c_loop_invariants_hold_at_back_edge`
/// over state-parametric `CLoopInvariantCheck` (`SpecProposition`), with
/// `prepare_loop_top_state` supplying the havoc. Making this rule sound means
/// evaluating the invariant at the body's post-state, which a flat
/// `Vec<Proposition>` invariant plus a caller-supplied `preserved` cannot
/// express — the fix is to carry `CLoopInvariantCheck` instead, which changes
/// the shape of `Proposition::CWhileInvariantRule` and duplicates machinery
/// that already exists. That redesign is not worth it for a rule with no
/// callers, so the rule is fenced instead.
#[cfg(test)]
pub(super) fn prove_c_while_invariant_rule(
    state: CState,
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
    assumptions: Assumptions,
    preserved: Vec<Proposition>,
    postcondition: Proposition,
) -> Option<Theorem> {
    if invariant
        .iter()
        .any(|invariant| !assumptions.proves(invariant))
    {
        return None;
    }

    let loop_assumptions = assumptions_with_propositions(&assumptions, &invariant);
    let step_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, true)
        .into_iter()
        .any(|step_assumptions| {
            let body_paths = execute_c_statement_paths(
                &state,
                &body,
                &step_assumptions,
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::default(),
            );
            let Ok(body_paths) = body_paths else {
                return false;
            };
            let mut body_paths = body_paths.into_iter();
            let Some(body_path) = body_paths.next() else {
                return false;
            };
            if body_paths.next().is_some()
                || !body_path.facts.is_empty()
                || !body_path.obligations.is_empty()
                || !matches!(body_path.outcome, CStatementOutcome::Normal(_))
            {
                return false;
            }
            preserved
                .iter()
                .all(|preserved| step_assumptions.proves(preserved))
        });

    if !step_ok {
        return None;
    }

    let exit_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, false)
        .into_iter()
        .any(|exit_assumptions| exit_assumptions.proves(&postcondition));

    if !exit_ok {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition: Box::new(postcondition),
        },
        &assumptions,
        &[],
        &[],
    )))
}

/// True when a term's nesting depth exceeds the limit, counting through
/// embedded memory snapshots. Bounded walk: returns as soon as the limit is
/// crossed, so the check itself stays shallow-stack on pathological terms.
pub(crate) fn bitvector_term_deeper_than(term: &Bitvector32Term, limit: usize) -> bool {
    fn term_depth_exceeds(term: &Bitvector32Term, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        match term {
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                memory_depth_exceeds(memory, remaining - 1)
                    || pointer_depth_exceeds(pointer, remaining - 1)
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
                term_depth_exceeds(left, remaining - 1) || term_depth_exceeds(right, remaining - 1)
            }
            Bitvector32Term::BitwiseNot(value) => term_depth_exceeds(value, remaining - 1),
            Bitvector32Term::If {
                condition,
                then_term,
                else_term,
            } => {
                condition_depth_exceeds(condition, remaining - 1)
                    || term_depth_exceeds(then_term, remaining - 1)
                    || term_depth_exceeds(else_term, remaining - 1)
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                term_depth_exceeds(start, remaining - 1)
                    || term_depth_exceeds(end, remaining - 1)
                    || term_depth_exceeds(initial, remaining - 1)
                    || term_depth_exceeds(body, remaining - 1)
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => arguments
                .iter()
                .any(|argument| term_depth_exceeds(argument, remaining - 1)),
        }
    }
    fn condition_depth_exceeds(condition: &ConditionTerm, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
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
                term_depth_exceeds(left, remaining - 1) || term_depth_exceeds(right, remaining - 1)
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                offset_depth_exceeds(left, remaining - 1)
                    || offset_depth_exceeds(right, remaining - 1)
            }
            ConditionTerm::PointerEqual(left, right) => {
                pointer_depth_exceeds(left, remaining - 1)
                    || pointer_depth_exceeds(right, remaining - 1)
            }
            ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
        }
    }
    fn pointer_depth_exceeds(pointer: &Pointer, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        offset_depth_exceeds(&pointer.offset, remaining - 1)
    }
    fn offset_depth_exceeds(offset: &PointerOffsetTerm, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
            PointerOffsetTerm::Add(left, right) => {
                offset_depth_exceeds(left, remaining - 1)
                    || offset_depth_exceeds(right, remaining - 1)
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => {
                term_depth_exceeds(value, remaining - 1)
            }
        }
    }
    fn memory_depth_exceeds(memory: &CMemory, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        memory.cells.iter().any(|(pointer, value)| {
            pointer_depth_exceeds(pointer, remaining - 1)
                || match value {
                    CValue::Void => false,
                    CValue::Int32(term) | CValue::UInt8(term) => {
                        term_depth_exceeds(term, remaining - 1)
                    }
                    CValue::Pointer(pointer) => pointer_depth_exceeds(pointer, remaining - 1),
                }
        })
    }
    term_depth_exceeds(term, limit)
}
