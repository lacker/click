use super::primitives::*;
use super::reasoning::*;
use std::collections::BTreeSet;

pub(crate) fn canonical_c_memory_for_pointer_load(memory: &CMemory, pointer: &Pointer) -> CMemory {
    canonical_memory_for_pointer_load(memory, pointer)
}

/// Checks whether two resource forms denote the same resource using only
/// exact facts and the bounded memory-resolution relation. This is intended
/// for certificate validation: it does not search for containment or separation.
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
        (CValue::Int16(left), CValue::Int16(right))
        | (CValue::UInt16(left), CValue::UInt16(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: bitvector value",
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
            )
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: pointer value",
                || pointers_match_for_resource_check(left, right, assumptions),
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
                    "resource memory match: width",
                    || left.element_width() == right.element_width(),
                ) && crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource memory match: start",
                    || {
                        bitvectors_match_for_resource_check(
                            left.start(),
                            right.start(),
                            assumptions,
                        )
                    },
                ) && crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource memory match: end",
                    || bitvectors_match_for_resource_check(left.end(), right.end(), assumptions),
                ) && crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource memory match: base",
                    || pointers_match_for_resource_check(left.base(), right.base(), assumptions),
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

fn bitvectors_match_for_resource_check(
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
    false
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

fn pointer_offsets_match_for_resource_check(
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

fn pointers_match_for_resource_check(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if left.block == right.block
        && pointer_offsets_match_for_resource_check(&left.offset, &right.offset, assumptions)
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
/// value canonicalizes its embedded loads. Forms of the same memory
/// produced from different memory snapshots compare equal when their
/// difference is representational.
pub(crate) fn canonical_c_memory_deep(memory: &CMemory) -> CMemory {
    // Assumption-free and deterministic; keyed by interned snapshot identity.
    let key = crate::kernel::intern_c_memory_ref(memory);
    if let Some(hit) = DEEP_MEMORY_CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = canonical_c_memory_deep_uncached(memory);
    DEEP_MEMORY_CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

fn canonical_c_memory_deep_uncached(memory: &CMemory) -> CMemory {
    let mut canonical = memory.clone();
    let cells = std::mem::take(&mut canonical.cells);
    for (pointer, value) in cells.iter() {
        let key = canonicalize_pointer_loads(&pointer);
        let value = match value {
            CValue::Void => CValue::Void,
            CValue::Int16(term) => CValue::Int16(canonicalize_atomic_loads(&term)),
            CValue::Int32(term) => CValue::Int32(canonicalize_atomic_loads(&term)),
            CValue::UInt8(term) => CValue::UInt8(canonicalize_atomic_loads(&term)),
            CValue::UInt16(term) => CValue::UInt16(canonicalize_atomic_loads(&term)),
            CValue::UInt32(term) => CValue::UInt32(canonicalize_atomic_loads(&term)),
            CValue::Int64(term) => CValue::Int64(canonicalize_atomic_loads(&term)),
            CValue::UInt64(term) => CValue::UInt64(canonicalize_atomic_loads(&term)),
            CValue::Float32(term) => CValue::Float32(canonicalize_atomic_loads(&term)),
            CValue::Float64(term) => CValue::Float64(canonicalize_atomic_loads(&term)),
            CValue::Pointer(pointer) => CValue::typed_pointer(
                canonicalize_pointer_loads(pointer.pointer()),
                pointer.c_type(),
            ),
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
    // This API is a certificate-check query. No-op block declarations,
    // forgotten caches, and allocations of a distinct block are sound DAG
    // bridges here; enabling them keeps check on the bounded derivation walk
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
            Proposition::CHeapAllocationFreed {
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
/// (`docs/internals/memory-dag.md`). Where
/// [`load_unchanged_via_effect_chain`] reconstructs a write history at proof
/// time from `CMemoryMutatesOnly` / `CMemoryEffectSummary` facts and links
/// hops by deep-canonical snapshot equality, this walks the history itself
/// and links hops by arena identity, so two forms of one location cannot
/// drift apart between program points.
///
/// Soundness rests on three things. Each `Store` hop is crossed only when
/// the written pointer is *provably distinct* from the loaded one, using the
/// same distinctness predicates as the fact-based paths. Each `CallHavoc`
/// hop is crossed only when the call's mutable ranges are provably disjoint
/// from the pointer, matching the `CMemoryEffectSummary` arm above. A
/// `LoopHavoc` hop follows the same rule when a checked whole-loop footprint
/// is present; an unevaluated footprint is never crossed, so its freshness
/// marker is honoured here at the edge, which is where conventions.md's
/// havoc-identity trap is disarmed for this arc.
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
    let mut current = from.clone();
    // The walk ends at a snapshot with no derivation: ids strictly
    // decrease along `base` (see `record_c_memory_derivation`), so every
    // chain is finite and the work is the chain's length.
    loop {
        if current == *target {
            return true;
        }
        // The check and the independent kernel certification build parallel
        // derivation chains for one execution, so the target is often a
        // sibling form of a snapshot on this chain rather than the same
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
        // form of the target on this chain can still match below that
        // point, so the walk continues to the chain's end instead of exiting.
        let Some(derivation) = current.derivation() else {
            return false;
        };
        let edge_name = match derivation.as_ref() {
            CMemoryDerivation::Store { .. } => "memory derivation edge: store",
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
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
                CMemoryDerivation::Store {
                    pointer: write,
                    context,
                    ..
                } => {
                    write != pointer
                        && (crate::instrumentation::measure_operation(
                            "kernel",
                            "memory derivation store edge",
                            "store edge: distinct blocks",
                            || write.blocks_proven_distinct(pointer),
                        ) || store_frozen_order_crosses(&current, context, write, pointer)
                            || crate::instrumentation::measure_operation(
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
                            )
                            || crate::instrumentation::measure_operation(
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
                            || crate::instrumentation::measure_operation(
                                "kernel",
                                "memory derivation store edge",
                                "store edge: range-separated pointers",
                                // The same range-membership route the fact-based
                                // MutatesOnly arm uses: the write inside one
                                // separated range and the load inside the other.
                                || {
                                    crate::kernel::reasoning::pointers_disjoint_by_range_memoized(
                                        write,
                                        pointer,
                                        assumptions,
                                    )
                                },
                            ))
                }
                // Declaring a block or forgetting cached cells writes nothing,
                // so every load is untouched — but only the extended-bridging
                // scope may exploit that: elsewhere these edges must look like
                // the pre-arc absence of an edge.
                CMemoryDerivation::BlockDeclared { .. }
                | CMemoryDerivation::HeapAllocationPending { .. }
                | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
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
                CMemoryDerivation::CallHavoc {
                    mutable_ranges,
                    context,
                    ..
                } => {
                    assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                        mutable_ranges,
                        pointer,
                        current.memory(),
                    ) || call_havoc_frozen_context_crosses(
                        &current,
                        mutable_ranges,
                        context,
                        pointer,
                    )
                }
                CMemoryDerivation::LoopHavoc {
                    mutable_ranges: Some(mutable_ranges),
                    ..
                } => {
                    explicit_dag_check_active()
                        && typed_ranges_disjoint_from_pointer_evidence(
                            mutable_ranges,
                            pointer,
                            assumptions,
                        )
                        .is_some()
                }
                // An interface or otherwise unevaluated loop footprint is a
                // hard provenance barrier.
                CMemoryDerivation::LoopHavoc {
                    mutable_ranges: None,
                    ..
                } => false,
            },
        );
        if !crossable {
            return false;
        }
        current = derivation.base().clone();
    }
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
    Stored {
        node: SharedCMemory,
        value: CValue,
        path: Vec<MemoryDagHop>,
    },
    /// The walk reached `node` without crossing any edge that could have
    /// written the cell, and stopped: `node` carries no derivation, its
    /// derivation is undecidable against this pointer, or the hop cap ran
    /// out. The load therefore reads whatever `node` holds at the pointer.
    Unwritten {
        node: SharedCMemory,
        path: Vec<MemoryDagHop>,
    },
}

/// One exact edge traversed while resolving a cell through the named memory
/// DAG. Retaining the edge is only the first half of a proof object: callers
/// that expose this walk as a certificate must additionally retain the typed
/// derivation that justified crossing assumption-dependent edges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MemoryDagHop {
    pub(super) derived: SharedCMemory,
    pub(super) derivation: std::sync::Arc<CMemoryDerivation>,
    pub(super) justification: MemoryDagHopJustification,
}

/// Why one exact memory-DAG edge was known not to affect the queried cell.
///
/// The first variants are complete local proof steps: they can be checked
/// from the edge, query pointer, and exact named premise without invoking an
/// alias or range solver. `AssumptionDependent` keeps the decision kind for
/// existing boolean consumers but deliberately is not a checkable proof;
/// those branches must gain typed child derivations before an atomic
/// certificate may consume the path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MemoryDagHopJustification {
    StoreDistinctBlocks,
    StoreCommonBaseUnequalConstants {
        condition: ConditionTerm,
    },
    StoreCommonBaseExactInequality {
        condition: ConditionTerm,
    },
    IntrinsicNoWrite,
    AllocationOfOtherBlock,
    HeapFreeOfDistinctBlock,
    CallHavocRanges {
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    LoopHavocRanges {
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    /// The havoc edge's frozen context proves the pointer outside the
    /// callee's mutable ranges by range reasoning or ownership.
    CallHavocFrozenContext,
    /// The store edge's frozen context records a strict order separating
    /// the written index from the loaded one.
    StoreFrozenOrder {
        condition: ConditionTerm,
    },
    AssumptionDependent(MemoryDagAssumptionKind),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MemoryDagAssumptionKind {
    StoreCommonBaseDistinctness,
    StoreExplicitRange,
    StoreGeneralDistinctness,
    HeapFreeGeneralDistinctness,
    HeapFreeResourceSeparation,
    CallHavocRangeSeparation,
    LoopHavocRangeSeparation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum RangeDisjointFromPointerEvidence {
    DistinctBlocks,
    ExactSeparationFact(Proposition),
    DirectConstantOutside {
        index: i64,
        start: i64,
        end: i64,
    },
    ForwardOffset {
        offset: Bitvector32Term,
        positive: PositiveTermEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PositiveTermEvidence {
    Constant,
    ExactCondition(ConditionTerm),
    OneLowerBound(ConditionTerm),
}

impl MemoryDagHopJustification {
    fn is_typed(&self) -> bool {
        !matches!(self, Self::AssumptionDependent(_))
    }

    /// Check one completed local edge proof without asking a general solver
    /// to rediscover it. Returns false for the not-yet-typed branches.
    pub(super) fn checks(
        &self,
        derivation: &CMemoryDerivation,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::StoreDistinctBlocks => matches!(
                derivation,
                CMemoryDerivation::Store { pointer: write, .. }
                    if write.blocks_proven_distinct(pointer)
            ),
            Self::StoreCommonBaseUnequalConstants { condition } => {
                let CMemoryDerivation::Store { pointer: write, .. } = derivation else {
                    return false;
                };
                pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                    == Some(condition.clone())
                    && condition == &ConditionTerm::Constant(false)
            }
            Self::StoreCommonBaseExactInequality { condition } => {
                let CMemoryDerivation::Store { pointer: write, .. } = derivation else {
                    return false;
                };
                pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                    == Some(condition.clone())
                    && assumptions.exact_condition_value(condition) == Some(false)
            }
            Self::IntrinsicNoWrite => matches!(
                derivation,
                CMemoryDerivation::BlockDeclared { .. }
                    | CMemoryDerivation::HeapAllocationPending { .. }
                    | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
                    | CMemoryDerivation::CellsForgotten { .. }
            ),
            Self::AllocationOfOtherBlock => matches!(
                derivation,
                CMemoryDerivation::HeapAllocated { block, .. } if pointer.block != *block
            ),
            Self::HeapFreeOfDistinctBlock => matches!(
                derivation,
                CMemoryDerivation::HeapFreed {
                    allocation_base, ..
                } if allocation_base.blocks_proven_distinct(pointer)
            ),
            Self::CallHavocRanges { ranges } => {
                let CMemoryDerivation::CallHavoc { mutable_ranges, .. } = derivation else {
                    return false;
                };
                ranges.len() == mutable_ranges.len()
                    && ranges
                        .iter()
                        .zip(mutable_ranges)
                        .all(|(evidence, range)| evidence.checks(range, pointer, assumptions))
            }
            Self::LoopHavocRanges { ranges } => {
                let CMemoryDerivation::LoopHavoc {
                    mutable_ranges: Some(mutable_ranges),
                    ..
                } = derivation
                else {
                    return false;
                };
                ranges.len() == mutable_ranges.len()
                    && ranges
                        .iter()
                        .zip(mutable_ranges)
                        .all(|(evidence, range)| evidence.checks(range, pointer, assumptions))
            }
            Self::CallHavocFrozenContext => {
                let CMemoryDerivation::CallHavoc {
                    mutable_ranges,
                    context,
                    base,
                    ..
                } = derivation
                else {
                    return false;
                };
                context.ranges_proven_disjoint_from_pointer_for_frame(
                    mutable_ranges,
                    pointer,
                    base.memory(),
                )
            }
            Self::StoreFrozenOrder { condition } => {
                let CMemoryDerivation::Store {
                    pointer: write,
                    context,
                    ..
                } = derivation
                else {
                    return false;
                };
                store_frozen_order_condition(context, write, pointer).as_ref() == Some(condition)
            }
            Self::AssumptionDependent(_) => false,
        }
    }
}

/// The common-base distinctness condition of a store and a load that the
/// store edge's frozen context refutes by one recorded strict order.
fn store_frozen_order_condition(
    context: &PureFactContext,
    write: &Pointer,
    pointer: &Pointer,
) -> Option<ConditionTerm> {
    let condition = pointer_offsets_with_common_base_distinctness_condition(write, pointer)?;
    let ConditionTerm::Bitvector32Equal(left, right) = &condition else {
        return None;
    };
    context
        .direct_strict_order_recorded(left, right)
        .then_some(condition)
}

/// Whether a store edge's frozen context proves the load misses the written
/// cell. Memoized per edge and pointer like the call-havoc crossing: the
/// derived snapshot identifies the edge, and every later naming walk crosses
/// it for the same cells.
fn store_frozen_order_crosses(
    derived: &crate::kernel::SharedCMemory,
    context: &PureFactContext,
    write: &Pointer,
    pointer: &Pointer,
) -> bool {
    let key = (derived.clone(), pointer.clone());
    if let Some(hit) = FROZEN_CROSSING_MEMO.with(|memo| memo.borrow().get(&key).copied()) {
        return hit;
    }
    let crosses = store_frozen_order_condition(context, write, pointer).is_some();
    FROZEN_CROSSING_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len() >= 100_000 {
            memo.clear();
        }
        memo.insert(key, crosses);
    });
    crosses
}

impl PositiveTermEvidence {
    fn for_term(term: &Bitvector32Term, assumptions: &PureFactContext) -> Option<Self> {
        if signed_bitvector_constant(term).is_some_and(|value| value > 0) {
            return Some(Self::Constant);
        }
        let exact = ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), term.clone());
        if assumptions.exact_condition_value(&exact) == Some(true) {
            return Some(Self::ExactCondition(exact));
        }
        let lower_bound =
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), term.clone());
        (assumptions.exact_condition_value(&lower_bound) == Some(true))
            .then_some(Self::OneLowerBound(lower_bound))
    }

    fn checks(&self, term: &Bitvector32Term, assumptions: &PureFactContext) -> bool {
        match self {
            Self::Constant => signed_bitvector_constant(term).is_some_and(|value| value > 0),
            Self::ExactCondition(condition) => {
                condition
                    == &ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), term.clone())
                    && assumptions.exact_condition_value(condition) == Some(true)
            }
            Self::OneLowerBound(condition) => {
                condition
                    == &ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), term.clone())
                    && assumptions.exact_condition_value(condition) == Some(true)
            }
        }
    }
}

impl RangeDisjointFromPointerEvidence {
    fn checks(
        &self,
        range: &CMemoryRange,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::DistinctBlocks => range.base.blocks_proven_distinct(pointer),
            Self::ExactSeparationFact(fact) => {
                assumptions.prop_facts.contains(fact)
                    && exact_separation_fact_covers_range_and_pointer(fact, range, pointer)
            }
            Self::DirectConstantOutside { index, start, end } => {
                direct_constant_element_index(pointer, range.base()) == Some(*index)
                    && signed_bitvector_constant(range.start()) == Some(*start)
                    && signed_bitvector_constant(range.end()) == Some(*end)
                    && (index < start || end <= index)
            }
            Self::ForwardOffset { offset, positive } => {
                forward_range_offset_from_pointer(range, pointer) == Some(offset.clone())
                    && positive.checks(
                        &Bitvector32Term::add(offset.clone(), range.start.clone()),
                        assumptions,
                    )
            }
        }
    }
}

impl MemoryDagCell {
    pub(super) fn node(&self) -> &SharedCMemory {
        match self {
            Self::Stored { node, .. } | Self::Unwritten { node, .. } => node,
        }
    }

    /// The concrete value the lookup pins down, when it pins one down.
    fn resolved_value(&self, pointer: &Pointer) -> Option<CValue> {
        match self {
            Self::Stored { value, .. } => Some(value.clone()),
            Self::Unwritten { node, .. } => node.known_value(pointer),
        }
    }

    fn checks_walk_from(
        &self,
        memory: &SharedCMemory,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        let path = match self {
            Self::Stored { path, .. } | Self::Unwritten { path, .. } => path,
        };
        let mut current = memory.clone();
        for hop in path {
            if hop.derived != current
                || current.derivation().as_ref() != Some(&hop.derivation)
                || !hop
                    .justification
                    .checks(hop.derivation.as_ref(), pointer, assumptions)
            {
                return false;
            }
            current = hop.derivation.base().clone();
        }
        &current == self.node()
    }

    fn has_only_typed_hops(&self) -> bool {
        match self {
            Self::Stored { path, .. } | Self::Unwritten { path, .. } => {
                path.iter().all(|hop| hop.justification.is_typed())
            }
        }
    }
}

/// The exact successful result of resolving two loads through the memory
/// DAG. This is retained decision evidence, not yet a complete certificate:
/// each assumption-dependent hop still needs its own typed justification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MemoryDagLoadEqualityEvidence {
    pub(super) left: MemoryDagCell,
    pub(super) right: MemoryDagCell,
    pub(super) reason: MemoryDagLoadEqualityReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MemoryDagLoadEqualityReason {
    CommonSource,
    EqualResolvedValue(CValue),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum AtomicMemoryLoadEqualityEvidence {
    SameCell(MemoryDagLoadEqualityEvidence),
    LeftResolvesToRight { left: MemoryDagCell },
    RightResolvesToLeft { right: MemoryDagCell },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PointerOffsetEqualityEvidence {
    Exact,
    Add {
        first: Box<PointerOffsetEqualityEvidence>,
        second: Box<PointerOffsetEqualityEvidence>,
        swapped: bool,
    },
    Int32Scaled {
        byte_width: i64,
        values: AtomicMemoryLoadEqualityEvidence,
    },
}

pub(super) fn pointer_offset_equality_evidence(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<PointerOffsetEqualityEvidence> {
    if left == right {
        return Some(PointerOffsetEqualityEvidence::Exact);
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            if let Some((first, second)) =
                pointer_offset_equality_evidence(left_a, right_a, assumptions).zip(
                    pointer_offset_equality_evidence(left_b, right_b, assumptions),
                )
            {
                return Some(PointerOffsetEqualityEvidence::Add {
                    first: Box::new(first),
                    second: Box::new(second),
                    swapped: false,
                });
            }
            let (first, second) =
                pointer_offset_equality_evidence(left_a, right_b, assumptions).zip(
                    pointer_offset_equality_evidence(left_b, right_a, assumptions),
                )?;
            Some(PointerOffsetEqualityEvidence::Add {
                first: Box::new(first),
                second: Box::new(second),
                swapped: true,
            })
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
        ) if left_width == right_width => {
            let values = atomic_memory_load_equality_evidence(left, right, assumptions)?;
            values
                .is_fully_typed()
                .then_some(PointerOffsetEqualityEvidence::Int32Scaled {
                    byte_width: *left_width,
                    values,
                })
        }
        _ => None,
    }
}

impl PointerOffsetEqualityEvidence {
    pub(super) fn checks(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::Exact => left == right,
            Self::Add {
                first,
                second,
                swapped,
            } => {
                let (
                    PointerOffsetTerm::Add(left_a, left_b),
                    PointerOffsetTerm::Add(right_a, right_b),
                ) = (left, right)
                else {
                    return false;
                };
                let (right_first, right_second) = if *swapped {
                    (right_b.as_ref(), right_a.as_ref())
                } else {
                    (right_a.as_ref(), right_b.as_ref())
                };
                first.checks(left_a, right_first, assumptions)
                    && second.checks(left_b, right_second, assumptions)
            }
            Self::Int32Scaled { byte_width, values } => {
                let (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) = (left, right)
                else {
                    return false;
                };
                left_width == byte_width
                    && right_width == byte_width
                    && values.checks(
                        &Proposition::ConditionIs(
                            ConditionTerm::equal(left.as_ref().clone(), right.as_ref().clone()),
                            true,
                        ),
                        assumptions,
                    )
            }
        }
    }
}

impl AtomicMemoryLoadEqualityEvidence {
    /// Whether this evidence uses only rule families whose local structural
    /// checker is implemented. This inspects the already-built object; it
    /// does not walk the memory DAG or consult assumptions again.
    pub(super) fn is_fully_typed(&self) -> bool {
        matches!(
            self,
            Self::SameCell(MemoryDagLoadEqualityEvidence {
                left,
                right,
                reason: MemoryDagLoadEqualityReason::CommonSource,
            }) if left.has_only_typed_hops() && right.has_only_typed_hops()
        )
    }

    /// Check the currently completed typed subset of retained DAG equality
    /// evidence. Unsupported terminal-value and assumption-dependent edge
    /// proofs return false instead of invoking a solver.
    pub(super) fn checks(&self, proposition: &Proposition, assumptions: &PureFactContext) -> bool {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            proposition
        else {
            return false;
        };
        let Self::SameCell(MemoryDagLoadEqualityEvidence {
            left: left_evidence,
            right: right_evidence,
            reason: MemoryDagLoadEqualityReason::CommonSource,
        }) = self
        else {
            return false;
        };
        let (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) = (left.as_ref(), right.as_ref())
        else {
            return false;
        };
        left_pointer == right_pointer
            && left_evidence.node() == right_evidence.node()
            && left_evidence.checks_walk_from(left_memory, left_pointer, assumptions)
            && right_evidence.checks_walk_from(right_memory, right_pointer, assumptions)
    }
}

// The hop predicates reach `decide` and the range-disjointness provers,
// which reach the cell-source provers again. A lookup already in progress
// for the same cell is a cycle through the facts and has no answer: the
// cell's source is what the outer lookup is computing, and an answer
// invented here would let each nested query pose the next one without
// end. Distinct cells nest freely, bounded by the cells the facts connect
// to the query. Answers computed inside another lookup may have met an
// in-progress cell, are weaker than a top-level answer, and are never
// memoized.
thread_local! {
    static CELL_LOOKUPS_IN_PROGRESS: std::cell::RefCell<
        std::collections::BTreeSet<((u32, u32), Pointer)>,
    > = std::cell::RefCell::new(std::collections::BTreeSet::new());
}

struct CellLookupGuard {
    key: ((u32, u32), Pointer),
}

impl CellLookupGuard {
    fn enter(memory: &SharedCMemory, pointer: &Pointer) -> Option<Self> {
        let key = (memory.arena_id(), pointer.clone());
        // `then`, not `then_some`: a guard built eagerly and discarded on
        // the cycle path would run `drop` and unregister the outer lookup.
        CELL_LOOKUPS_IN_PROGRESS
            .with(|lookups| lookups.borrow_mut().insert(key.clone()))
            .then(|| Self { key })
    }
}

impl Drop for CellLookupGuard {
    fn drop(&mut self) {
        CELL_LOOKUPS_IN_PROGRESS.with(|lookups| {
            lookups.borrow_mut().remove(&self.key);
        });
    }
}

// The extended DAG bridging (crossing block-declaration and cell-forgetting
// edges, range-certificate store hops, stored-value pinning, and the
// order-path load matching in assumptions.rs) runs ONLY inside the loadable
// prover. Everywhere else — execution pruning, load canonicalization, simp
// planning — behavior must stay byte-identical to the pre-arc path, because
// certified forms and case-split structure check against it. The flag
// is scoped, not global, so generation and check of the same query always
// agree.
thread_local! {
    static EXTENDED_DAG_BRIDGING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static EXPLICIT_DAG_CHECK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn extended_dag_bridging_active() -> bool {
    EXTENDED_DAG_BRIDGING.with(std::cell::Cell::get)
}

/// True while explicit certificate validation widens the DAG walk (see
/// `explicit_atomic_equality_from_memory_derivations`); resolution answers
/// computed in that mode must not be shared with the planner-facing arms.
pub(super) fn explicit_dag_check_active() -> bool {
    EXPLICIT_DAG_CHECK.with(std::cell::Cell::get)
}

/// True outside any memory-DAG cell lookup. Answers computed inside a
/// lookup may have met an in-progress cell and are weaker than a top-level
/// answer, so they must not be memoized under a lookup-free key.
pub(super) fn memory_dag_cell_lookup_depth_is_zero() -> bool {
    CELL_LOOKUPS_IN_PROGRESS.with(|lookups| lookups.borrow().is_empty())
}

/// Runs `body` with the extended DAG bridging enabled (see above).
pub(super) fn with_extended_dag_bridging<T>(body: impl FnOnce() -> T) -> T {
    let previous = EXTENDED_DAG_BRIDGING.with(|flag| flag.replace(true));
    let result = body();
    EXTENDED_DAG_BRIDGING.with(|flag| flag.set(previous));
    result
}

fn exact_separation_fact_covers_range_and_pointer(
    fact: &Proposition,
    range: &CMemoryRange,
    pointer: &Pointer,
) -> bool {
    let (left, right) = match fact {
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => (
            CMemoryRange::new(left_base.clone(), left_start.clone(), left_end.clone()),
            CMemoryRange::new(right_base.clone(), right_start.clone(), right_end.clone()),
        ),
        Proposition::CResourceSeparate {
            left: CResource::Memory(left),
            right: CResource::Memory(right),
        } => (left.clone(), right.clone()),
        _ => return false,
    };
    super::assumptions::memory_range_shallowly_contained(range, &left)
        && super::assumptions::pointer_in_memory_range_shallow(pointer, &right)
        || super::assumptions::memory_range_shallowly_contained(range, &right)
            && super::assumptions::pointer_in_memory_range_shallow(pointer, &left)
}

fn forward_range_offset_from_pointer(
    range: &CMemoryRange,
    pointer: &Pointer,
) -> Option<Bitvector32Term> {
    if range.base.block != pointer.block {
        return None;
    }
    let PointerOffsetTerm::Add(left, right) = &range.base.offset else {
        return None;
    };
    if pointer.offset == **left {
        element_index_from_offset(right, range.element_width())
    } else if pointer.offset == **right {
        element_index_from_offset(left, range.element_width())
    } else {
        None
    }
}

fn direct_constant_element_index(pointer: &Pointer, base: &Pointer) -> Option<i64> {
    let bytes = signed_bitvector_constant(&pointer_byte_offset_from_base(pointer, base)?)?;
    (bytes % 4 == 0).then_some(bytes / 4)
}

fn typed_range_disjoint_from_pointer_evidence(
    range: &CMemoryRange,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Option<RangeDisjointFromPointerEvidence> {
    if range.base.blocks_proven_distinct(pointer) {
        return Some(RangeDisjointFromPointerEvidence::DistinctBlocks);
    }
    if let Some(fact) = assumptions
        .prop_facts
        .iter()
        .find(|fact| exact_separation_fact_covers_range_and_pointer(fact, range, pointer))
    {
        return Some(RangeDisjointFromPointerEvidence::ExactSeparationFact(
            fact.clone(),
        ));
    }
    if let (Some(index), Some(start), Some(end)) = (
        direct_constant_element_index(pointer, range.base()),
        signed_bitvector_constant(range.start()),
        signed_bitvector_constant(range.end()),
    ) && (index < start || end <= index)
    {
        return Some(RangeDisjointFromPointerEvidence::DirectConstantOutside { index, start, end });
    }
    let offset = forward_range_offset_from_pointer(range, pointer)?;
    let range_start = Bitvector32Term::add(offset.clone(), range.start.clone());
    let positive = PositiveTermEvidence::for_term(&range_start, assumptions)?;
    Some(RangeDisjointFromPointerEvidence::ForwardOffset { offset, positive })
}

fn typed_ranges_disjoint_from_pointer_evidence(
    ranges: &[CMemoryRange],
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Vec<RangeDisjointFromPointerEvidence>> {
    ranges
        .iter()
        .map(|range| typed_range_disjoint_from_pointer_evidence(range, pointer, assumptions))
        .collect()
}

/// The DAG epoch used to construct one cell's load variable: the snapshot at
/// which the loaded cell was last written or entered the world, walked
/// assumption-free over recorded edges. Snapshots that differ only by
/// effects the DAG proves disjoint from the cell share an epoch, so
/// load variables stay stable across them.
pub(crate) fn cell_epoch_for_load_variable(
    memory: &SharedCMemory,
    pointer: &Pointer,
) -> Option<SharedCMemory> {
    // Assumption-free and a function of the interned snapshot, the pointer,
    // and the recorded edges (a havoc edge's frozen context included), so
    // the answer is memoized per query.
    let key = (memory.clone(), pointer.clone());
    if let Some(hit) = CELL_EPOCH_MEMO.with(|memo| memo.borrow().get(&key).cloned()) {
        return hit;
    }
    let epoch = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "cell epoch walk",
        || {
            // Declaring a block, forgetting cached cells, or allocating
            // another block writes nothing; a name must not change across
            // them, so the naming walk crosses those edges unconditionally.
            with_extended_dag_bridging(|| {
                memory_dag_cell_source(memory, pointer, &PureFactContext::new(), false)
                    .map(|cell| cell.node().clone())
            })
        },
    );
    CELL_EPOCH_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len() >= 100_000 {
            memo.clear();
        }
        memo.insert(key, epoch.clone());
    });
    epoch
}

/// Whether a call-havoc edge's frozen context proves `pointer` outside the
/// callee's mutable ranges. The answer is a function of the edge (its
/// derived snapshot identifies it) and the pointer, so it is memoized per
/// edge rather than per querying snapshot: every later snapshot's naming
/// walk crosses the same edge for the same cells.
fn call_havoc_frozen_context_crosses(
    derived: &crate::kernel::SharedCMemory,
    mutable_ranges: &[CMemoryRange],
    context: &PureFactContext,
    pointer: &Pointer,
) -> bool {
    let key = (derived.clone(), pointer.clone());
    if let Some(hit) = FROZEN_CROSSING_MEMO.with(|memo| memo.borrow().get(&key).copied()) {
        return hit;
    }
    let crosses = context.ranges_proven_disjoint_from_pointer_for_frame(
        mutable_ranges,
        pointer,
        derived.memory(),
    );
    FROZEN_CROSSING_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len() >= 100_000 {
            memo.clear();
        }
        memo.insert(key, crosses);
    });
    crosses
}

thread_local! {
    static FROZEN_CROSSING_MEMO: std::cell::RefCell<
        std::collections::HashMap<(crate::kernel::SharedCMemory, Pointer), bool>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static CELL_EPOCH_MEMO: std::cell::RefCell<
        std::collections::HashMap<(crate::kernel::SharedCMemory, Pointer), Option<crate::kernel::SharedCMemory>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

fn memory_dag_cell_source(
    memory: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
) -> Option<MemoryDagCell> {
    // A lookup of a cell already being looked up is a cycle and has no
    // answer; see `CELL_LOOKUPS_IN_PROGRESS`.
    let _lookup = CellLookupGuard::enter(memory, pointer)?;
    Some(memory_dag_cell_source_walk(
        memory,
        pointer,
        assumptions,
        cross_loop_havoc,
    ))
}

fn memory_dag_cell_source_walk(
    memory: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
) -> MemoryDagCell {
    let mut current = memory.clone();
    let mut path = Vec::new();
    // The walk ends at a snapshot with no derivation: ids strictly
    // decrease along `base`, so every chain is finite.
    loop {
        // Each hop is one unit of deterministic work, so a scaling
        // regression sees a walk that grows with the proof.
        crate::instrumentation::record_deterministic_work(1);
        let Some(derivation) = current.derivation() else {
            return MemoryDagCell::Unwritten {
                node: current,
                path,
            };
        };
        let justification = match derivation.as_ref() {
            CMemoryDerivation::Store {
                pointer: write,
                value,
                context,
                ..
            } => {
                if write == pointer
                    || EXPLICIT_DAG_CHECK.with(std::cell::Cell::get)
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
                        path,
                    };
                }
                // The recorded-range fallback covers writes into a
                // proven-separate region (a buffer store crossed while
                // resolving a struct field); the same predicate
                // `memory_derivations_reach` crosses `Store` hops with.
                // Extended-bridging scope only, and under its own capped
                // budget so this advisory walk can never drain the
                // enclosing query's fuel — fuel-coupled forms elsewhere
                // must check byte-for-byte.
                if write.blocks_proven_distinct(pointer) {
                    MemoryDagHopJustification::StoreDistinctBlocks
                } else if let Some(condition) =
                    store_frozen_order_condition(context, write, pointer)
                {
                    MemoryDagHopJustification::StoreFrozenOrder { condition }
                } else if pointer_offsets_with_common_base_proven_distinct(
                    write,
                    pointer,
                    assumptions,
                ) {
                    let condition =
                        pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                            .expect("a successful common-base check has a cancellation condition");
                    let unequal_constants = condition == ConditionTerm::Constant(false);
                    if unequal_constants {
                        MemoryDagHopJustification::StoreCommonBaseUnequalConstants { condition }
                    } else if assumptions.exact_condition_value(&condition) == Some(false) {
                        MemoryDagHopJustification::StoreCommonBaseExactInequality { condition }
                    } else {
                        MemoryDagHopJustification::AssumptionDependent(
                            MemoryDagAssumptionKind::StoreCommonBaseDistinctness,
                        )
                    }
                } else if EXPLICIT_DAG_CHECK.with(std::cell::Cell::get)
                    && assumptions
                        .pointers_proven_disjoint_by_shallow_explicit_range(write, pointer)
                {
                    MemoryDagHopJustification::AssumptionDependent(
                        MemoryDagAssumptionKind::StoreExplicitRange,
                    )
                } else if extended_dag_bridging_active()
                    && pointers_proven_distinct_for_memory_resolution(write, pointer, assumptions)
                {
                    MemoryDagHopJustification::AssumptionDependent(
                        MemoryDagAssumptionKind::StoreGeneralDistinctness,
                    )
                } else {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
            }
            // Declaring a block or forgetting cached cells writes nothing,
            // so every load is untouched — but only the extended-bridging
            // scope may exploit that: elsewhere these edges must look like
            // the pre-arc absence of an edge.
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. } => {
                if !extended_dag_bridging_active() {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
                MemoryDagHopJustification::IntrinsicNoWrite
            }
            CMemoryDerivation::HeapAllocated { block, .. } => {
                if pointer.block == *block || !extended_dag_bridging_active() {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
                MemoryDagHopJustification::AllocationOfOtherBlock
            }
            CMemoryDerivation::HeapFreed {
                allocation_base,
                bytes,
                ..
            } => {
                if !extended_dag_bridging_active() {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
                if allocation_base.blocks_proven_distinct(pointer) {
                    MemoryDagHopJustification::HeapFreeOfDistinctBlock
                } else if pointers_proven_distinct_for_memory_resolution(
                    allocation_base,
                    pointer,
                    assumptions,
                ) {
                    MemoryDagHopJustification::AssumptionDependent(
                        MemoryDagAssumptionKind::HeapFreeGeneralDistinctness,
                    )
                } else if heap_allocation_proven_separate_from_pointer(
                    allocation_base,
                    bytes,
                    pointer,
                    assumptions,
                ) {
                    MemoryDagHopJustification::AssumptionDependent(
                        MemoryDagAssumptionKind::HeapFreeResourceSeparation,
                    )
                } else {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
            }
            CMemoryDerivation::CallHavoc {
                mutable_ranges,
                context,
                ..
            } => {
                if let Some(ranges) = typed_ranges_disjoint_from_pointer_evidence(
                    mutable_ranges,
                    pointer,
                    assumptions,
                ) {
                    MemoryDagHopJustification::CallHavocRanges { ranges }
                } else if call_havoc_frozen_context_crosses(
                    &current,
                    mutable_ranges,
                    context,
                    pointer,
                ) {
                    // Decided by the edge's own frozen context: checkable
                    // from the edge and the pointer alone.
                    MemoryDagHopJustification::CallHavocFrozenContext
                } else if assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                    mutable_ranges,
                    pointer,
                    current.memory(),
                ) {
                    MemoryDagHopJustification::AssumptionDependent(
                        MemoryDagAssumptionKind::CallHavocRangeSeparation,
                    )
                } else {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
            }
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(mutable_ranges),
                ..
            } => {
                if !cross_loop_havoc
                    || !extended_dag_bridging_active()
                    || !explicit_dag_check_active()
                {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
                if let Some(ranges) = typed_ranges_disjoint_from_pointer_evidence(
                    mutable_ranges,
                    pointer,
                    assumptions,
                ) {
                    MemoryDagHopJustification::LoopHavocRanges { ranges }
                } else if explicit_dag_check_active()
                    && assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                        mutable_ranges,
                        pointer,
                        current.memory(),
                    )
                {
                    MemoryDagHopJustification::AssumptionDependent(
                        MemoryDagAssumptionKind::LoopHavocRangeSeparation,
                    )
                } else {
                    return MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    };
                }
            }
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            } => {
                return MemoryDagCell::Unwritten {
                    node: current,
                    path,
                };
            }
        };
        path.push(MemoryDagHop {
            derived: current.clone(),
            derivation: derivation.clone(),
            justification,
        });
        current = derivation.base().clone();
    }
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
/// This is stage 4 of `docs/internals/memory-dag.md`, and it is
/// wired in *ahead* of the canonicalizing comparisons rather than beside
/// them. Where those take two embedded snapshots, deep-canonicalize both and
/// compare the results structurally, this follows named edges and compares
/// arena ids, so the common case — two forms of one cell separated only
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
    memory_load_equality_evidence_at(left_memory, right_memory, pointer, assumptions).is_some()
}

/// Evidence-producing form of [`loads_equal_along_memory_derivations_at`].
/// Successful certificate-producing callers must retain this value rather
/// than calling the boolean adapter and later searching for the walk again.
pub(super) fn memory_load_equality_evidence_at(
    left_memory: &SharedCMemory,
    right_memory: &SharedCMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Option<MemoryDagLoadEqualityEvidence> {
    if left_memory == right_memory {
        let cell = MemoryDagCell::Unwritten {
            node: left_memory.clone(),
            path: Vec::new(),
        };
        return Some(MemoryDagLoadEqualityEvidence {
            left: cell.clone(),
            right: cell,
            reason: MemoryDagLoadEqualityReason::CommonSource,
        });
    }
    let (Some(left), Some(right)) = (
        memory_dag_cell_source(left_memory, pointer, assumptions, true),
        memory_dag_cell_source(right_memory, pointer, assumptions, true),
    ) else {
        return None;
    };
    if left.node() == right.node() {
        return Some(MemoryDagLoadEqualityEvidence {
            left,
            right,
            reason: MemoryDagLoadEqualityReason::CommonSource,
        });
    }
    match (left.resolved_value(pointer), right.resolved_value(pointer)) {
        (Some(left_value), Some(right_value)) if left_value == right_value => {
            Some(MemoryDagLoadEqualityEvidence {
                left,
                right,
                reason: MemoryDagLoadEqualityReason::EqualResolvedValue(left_value),
            })
        }
        _ => None,
    }
}

/// The [`loads_equal_along_memory_derivations_at`] arm as a term-level test:
/// true only when both sides are atomic loads the DAG resolves alike.
///
/// Beyond the node-identity comparison, one side's walk may land on a
/// `Store` whose recorded value IS the other side verbatim — the common case
/// for a load-caching store (`cells[p] := load(older, p)`): the newer
/// snapshot's cell literally pins the older form. That is still a pure
/// DAG answer (the value comes off a derivation edge, compared structurally),
/// so it stays inside the exact-facts-plus-edges determinism boundary.
pub(super) fn atomic_loads_equal_along_memory_derivations(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    atomic_memory_load_equality_evidence(left, right, assumptions).is_some()
}

/// Evidence-producing form of
/// [`atomic_loads_equal_along_memory_derivations`]. Positive memo entries
/// retain this evidence instead of caching only the boolean answer.
pub(super) fn atomic_memory_load_equality_evidence(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<AtomicMemoryLoadEqualityEvidence> {
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer != right_pointer {
        return None;
    }
    if !extended_dag_bridging_active() {
        // Pre-arc behavior outside the loadable prover: node-identity
        // comparison only, no memo, no value pinning.
        return memory_load_equality_evidence_at(
            left_memory,
            right_memory,
            left_pointer,
            assumptions,
        )
        .map(AtomicMemoryLoadEqualityEvidence::SameCell);
    }
    // The same (snapshot, snapshot, pointer) triple is asked thousands of
    // times per proof. A proven equality stays true as new first-wins DAG
    // edges are recorded: the edges only add faithful derivations of already
    // existing snapshots. Cache those positive answers independently of the
    // derivation generation. A negative answer only means "not connected
    // yet", so it remains generation-scoped and is retried after any new
    // edge. Only top-level answers participate: a nested lookup may meet
    // an in-progress cell and its weaker answer must not shadow the full one.
    let memo_key = memory_dag_cell_lookup_depth_is_zero()
        .then(|| super::assumptions::dag_memo_assumptions_id(assumptions))
        .map(|assumptions_id| DagLoadEqualityMemoKey {
            assumptions_id,
            left_memory: left_memory.arena_id(),
            right_memory: right_memory.arena_id(),
            pointer: left_pointer.as_ref().clone(),
        });
    if let Some(key) = &memo_key
        && let Some(evidence) =
            DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| memo.borrow().get(key).cloned())
    {
        return Some(evidence);
    }
    let derivation_generation = c_memory_derivation_generation();
    if let Some(key) = &memo_key
        && DAG_LOAD_EQUALITY_NEGATIVE_MEMO.with(|memo| {
            memo.borrow()
                .contains(&(derivation_generation, key.clone()))
        })
    {
        return None;
    }
    let result =
        memory_load_equality_evidence_at(left_memory, right_memory, left_pointer, assumptions)
            .map(AtomicMemoryLoadEqualityEvidence::SameCell)
            .or_else(|| {
                let (Some(left_cell), Some(right_cell)) = (
                    memory_dag_cell_source(left_memory, left_pointer, assumptions, true),
                    memory_dag_cell_source(right_memory, right_pointer, assumptions, true),
                ) else {
                    return None;
                };
                if matches!(
                    left_cell.resolved_value(left_pointer),
                    Some(CValue::Int16(value) | CValue::Int32(value) | CValue::UInt8(value) | CValue::UInt16(value) | CValue::UInt32(value)) if &value == right
                ) {
                    Some(AtomicMemoryLoadEqualityEvidence::LeftResolvesToRight { left: left_cell })
                } else if matches!(
                    right_cell.resolved_value(right_pointer),
                    Some(CValue::Int16(value) | CValue::Int32(value) | CValue::UInt8(value) | CValue::UInt16(value) | CValue::UInt32(value)) if &value == left
                ) {
                    Some(AtomicMemoryLoadEqualityEvidence::RightResolvesToLeft {
                        right: right_cell,
                    })
                } else {
                    None
                }
            });
    if let Some(key) = memo_key {
        if let Some(evidence) = &result {
            DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key, evidence.clone());
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
/// certificate validation. Unlike the planner-facing DAG arm, this may cross
/// no-op block declarations and stores whose distinctness follows from the
/// certificate's separation facts; every crossed edge remains justified by
/// exact facts and the bounded DAG walk.
pub(crate) fn explicit_atomic_equality_from_memory_derivations(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
    let result = with_extended_dag_bridging(|| {
        if atomic_loads_equal_along_memory_derivations(left, right, assumptions) {
            return true;
        }
        let resolves_to = |load: &Bitvector32Term, value: &Bitvector32Term| {
            let Bitvector32Term::MemoryLoad(memory, pointer) = load else {
                return false;
            };
            matches!(
                memory_dag_cell_source(memory, pointer, assumptions, true)
                    .and_then(|cell| cell.resolved_value(pointer)),
                Some(CValue::Int16(resolved) | CValue::Int32(resolved) | CValue::UInt8(resolved) | CValue::UInt16(resolved) | CValue::UInt32(resolved))
                    if resolved == *value
            )
        };
        resolves_to(left, right) || resolves_to(right, left)
    });
    EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
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
        std::collections::HashMap<DagLoadEqualityMemoKey, AtomicMemoryLoadEqualityEvidence>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
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
            Proposition::CHeapAllocationFreed {
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
    // Hops link pointer-relatively: two forms of one snapshot may carry
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
                    || memory_materializes_atomic_load(effect_before, before, pointer)
                    || directly_matched_effect_endpoint(
                        effect_before,
                        before,
                        pointer,
                        assumptions,
                    ))
                    && (effect_after == after
                        || directly_matched_effect_endpoint(
                            effect_after,
                            after,
                            pointer,
                            assumptions,
                        ))
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
                // The direct check decides most disjointness structurally;
                // ranges owned through composites need the bounded deep
                // prover, exactly as the mutates-only arm's per-write
                // distinctness already does.
                let disjoint = after_matches
                    && (assumptions.ranges_directly_disjoint_from_pointer(mutable_ranges, pointer)
                        || assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                            mutable_ranges,
                            pointer,
                            before,
                        ));
                before_matches && after_matches && disjoint
            }
            Proposition::CHeapAllocationFreed {
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
    // Two snapshots that name the cell by one DAG epoch hold the same
    // cell: every hop the naming walk crossed is a write proven (without
    // assumptions) to miss the cell. This is how a fact carried unchanged
    // through earlier steps, and so still named at its mint epoch, meets an
    // effect summary whose `before` is the later live snapshot.
    if !pointer.block.starts_with("local:")
        && let (Some(left_epoch), Some(right_epoch)) = (
            cell_epoch_for_load_variable(&crate::kernel::intern_c_memory(left.clone()), pointer),
            cell_epoch_for_load_variable(&crate::kernel::intern_c_memory(right.clone()), pointer),
        )
        && left_epoch == right_epoch
    {
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
        Some(CValue::Int16(Bitvector32Term::MemoryLoad(source, source_pointer))
            | CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer))
            | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer))
            | CValue::UInt16(Bitvector32Term::MemoryLoad(source, source_pointer))
            | CValue::UInt32(Bitvector32Term::MemoryLoad(source, source_pointer)))
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
    // Per-arm returns, no shared conclusion local: this function sits in
    // transport recursion, and a by-value `Proposition` local overflows the
    // expansion stack.
    match fact {
        Proposition::ConditionIs(condition, value) => {
            let transported = transport_framed_atomic_condition(condition, after, assumptions)?;
            if &transported == condition {
                return None;
            }
            Some(Theorem::new(Proposition::Implies(
                Box::new(fact.clone()),
                Box::new(Proposition::ConditionIs(transported, *value)),
            )))
        }
        _ => None,
    }
}

/// Rewrites subterms of a condition fact that equal a certified store's
/// value into loads from that store's post-memory, so a fact written in
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
            CValue::Int16(term)
            | CValue::Int32(term)
            | CValue::UInt8(term)
            | CValue::UInt16(term)
            | CValue::UInt32(term) => term.clone(),
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
    let cacheable = term_is_shallow_structural_cache_key(term);
    if cacheable
        && let Some(hit) = ATOMIC_LOADS_CACHE.with(|cache| cache.borrow().get(term).cloned())
    {
        return hit;
    }
    let result = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "canonicalize atomic loads: miss",
        || canonicalize_atomic_loads_deep(term),
    );
    if cacheable {
        ATOMIC_LOADS_CACHE.with(|cache| cache.borrow_mut().insert(term.clone(), result.clone()));
    }
    result
}

thread_local! {
    static DEEP_MEMORY_CACHE: std::cell::RefCell<
        std::collections::HashMap<crate::kernel::SharedCMemory, CMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static ATOMIC_LOADS_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    #[cfg(test)]
    static ATOMIC_CANONICALIZATION_TERM_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_atomic_canonicalization_term_visits() {
    ATOMIC_CANONICALIZATION_TERM_VISITS.with(|visits| visits.set(0));
}

#[cfg(test)]
pub(crate) fn atomic_canonicalization_term_visits() -> usize {
    ATOMIC_CANONICALIZATION_TERM_VISITS.with(std::cell::Cell::get)
}

pub(crate) fn clear_provenance_memos() {
    UNCHANGED_LOAD_POSITIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    UNCHANGED_LOAD_NEGATIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    DAG_LOAD_EQUALITY_NEGATIVE_MEMO.with(|memo| memo.borrow_mut().clear());
}

pub(crate) fn clear_canonical_form_caches() {
    DEEP_MEMORY_CACHE.with(|cache| cache.borrow_mut().clear());
    ATOMIC_LOADS_CACHE.with(|cache| cache.borrow_mut().clear());
    CELL_EPOCH_MEMO.with(|memo| memo.borrow_mut().clear());
    FROZEN_CROSSING_MEMO.with(|memo| memo.borrow_mut().clear());
}

/// Recursive `Hash` and `Eq` implementations make a whole-term cache key
/// unsafe at arbitrary depth. This iterative preflight controls only whether
/// memoization is used; canonicalization itself always traverses the complete
/// term. Embedded snapshots hash by interned identity, so only the explicit
/// term and pointer-offset structure matters here.
pub(crate) fn term_is_shallow_structural_cache_key(term: &Bitvector32Term) -> bool {
    const MAX_RECURSIVE_KEY_DEPTH: usize = 256;
    enum Node<'a> {
        Term(&'a Bitvector32Term, usize),
        Condition(&'a ConditionTerm, usize),
        Offset(&'a PointerOffsetTerm, usize),
    }
    let mut pending = vec![Node::Term(term, 1)];
    while let Some(node) = pending.pop() {
        let depth = match node {
            Node::Term(_, depth) | Node::Condition(_, depth) | Node::Offset(_, depth) => depth,
        };
        if depth > MAX_RECURSIVE_KEY_DEPTH {
            return false;
        }
        match node {
            Node::Term(term, depth) => match term {
                Bitvector32Term::Constant(_)
                | Bitvector32Term::Variable(_)
                | Bitvector32Term::Int64Constant(_)
                | Bitvector32Term::UInt64Constant(_) => {}
                Bitvector32Term::MemoryLoad(_, pointer) => {
                    pending.push(Node::Offset(&pointer.offset, depth + 1));
                }
                Bitvector32Term::Add(left, right)
                | Bitvector32Term::Subtract(left, right)
                | Bitvector32Term::Multiply(left, right)
                | Bitvector32Term::Divide(left, right)
                | Bitvector32Term::UnsignedDivide(left, right)
                | Bitvector32Term::Remainder(left, right)
                | Bitvector32Term::UnsignedRemainder(left, right)
                | Bitvector32Term::ShiftLeft(left, right)
                | Bitvector32Term::ArithmeticShiftRight(left, right)
                | Bitvector32Term::LogicalShiftRight(left, right)
                | Bitvector32Term::BitwiseAnd(left, right)
                | Bitvector32Term::BitwiseOr(left, right)
                | Bitvector32Term::BitwiseXor(left, right)
                | Bitvector32Term::Int64Add(left, right)
                | Bitvector32Term::Int64Subtract(left, right)
                | Bitvector32Term::Int64Multiply(left, right)
                | Bitvector32Term::Int64Divide(left, right)
                | Bitvector32Term::Int64Remainder(left, right)
                | Bitvector32Term::Int64ShiftLeft(left, right)
                | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
                | Bitvector32Term::Int64BitwiseAnd(left, right)
                | Bitvector32Term::Int64BitwiseOr(left, right)
                | Bitvector32Term::Int64BitwiseXor(left, right)
                | Bitvector32Term::UInt64Add(left, right)
                | Bitvector32Term::UInt64Subtract(left, right)
                | Bitvector32Term::UInt64Multiply(left, right)
                | Bitvector32Term::UInt64Divide(left, right)
                | Bitvector32Term::UInt64Remainder(left, right)
                | Bitvector32Term::UInt64ShiftLeft(left, right)
                | Bitvector32Term::UInt64LogicalShiftRight(left, right)
                | Bitvector32Term::UInt64BitwiseAnd(left, right)
                | Bitvector32Term::UInt64BitwiseOr(left, right)
                | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                Bitvector32Term::BitwiseNot(value)
                | Bitvector32Term::Int64From32(value)
                | Bitvector32Term::Int64FromUInt32(value)
                | Bitvector32Term::UInt64From32(value)
                | Bitvector32Term::UInt64FromInt32(value)
                | Bitvector32Term::UInt64FromInt64(value)
                | Bitvector32Term::Int64BitwiseNot(value)
                | Bitvector32Term::UInt64BitwiseNot(value) => {
                    pending.push(Node::Term(value, depth + 1));
                }
                Bitvector32Term::If {
                    condition,
                    then_term,
                    else_term,
                } => {
                    pending.push(Node::Term(else_term, depth + 1));
                    pending.push(Node::Term(then_term, depth + 1));
                    pending.push(Node::Condition(condition, depth + 1));
                }
                Bitvector32Term::RangeFold {
                    start,
                    end,
                    initial,
                    body,
                    ..
                } => {
                    pending.push(Node::Term(body, depth + 1));
                    pending.push(Node::Term(initial, depth + 1));
                    pending.push(Node::Term(end, depth + 1));
                    pending.push(Node::Term(start, depth + 1));
                }
                Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|argument| Node::Term(argument, depth + 1)),
                    );
                }
            },
            Node::Condition(condition, depth) => match condition {
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
                ConditionTerm::Bitvector32SignedLessThan(left, right)
                | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector32Equal(left, right)
                | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
                | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
                | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
                | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
                | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
                | ConditionTerm::Bitvector64SignedLessThan(left, right)
                | ConditionTerm::Bitvector64SignedLessEqual(left, right)
                | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
                | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
                | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
                | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector64Equal(left, right)
                | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
                | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
                | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
                | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
                | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    pending.push(Node::Offset(right, depth + 1));
                    pending.push(Node::Offset(left, depth + 1));
                }
                ConditionTerm::PointerEqual(left, right) => {
                    pending.push(Node::Offset(&right.offset, depth + 1));
                    pending.push(Node::Offset(&left.offset, depth + 1));
                }
            },
            Node::Offset(offset, depth) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(Node::Offset(right, depth + 1));
                    pending.push(Node::Offset(left, depth + 1));
                }
                PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } => {
                    pending.push(Node::Term(value, depth + 1));
                }
            },
        }
    }
    true
}

type AtomicBinaryConstructor = fn(Box<Bitvector32Term>, Box<Bitvector32Term>) -> Bitvector32Term;
type AtomicUnaryConstructor = fn(Box<Bitvector32Term>) -> Bitvector32Term;
type AtomicConditionConstructor = fn(Box<Bitvector32Term>, Box<Bitvector32Term>) -> ConditionTerm;

enum AtomicCanonicalizationTask<'a> {
    Visit(&'a Bitvector32Term),
    VisitCondition(&'a ConditionTerm),
    VisitOffset(&'a PointerOffsetTerm),
    RebuildBinary(AtomicBinaryConstructor),
    RebuildUnary(AtomicUnaryConstructor),
    RebuildConditionBinary(AtomicConditionConstructor),
    RebuildPointerOffsetEqual,
    RebuildPointerEqual {
        left_block: PointerBlock,
        right_block: PointerBlock,
    },
    RebuildOffsetAdd,
    RebuildInt32Scaled(i64),
    RebuildInt64Scaled {
        byte_width: i64,
        unsigned: bool,
    },
    RebuildIf,
    RebuildRangeFold {
        accumulator: Variable,
        item: Variable,
    },
    RebuildPureFunction {
        name: String,
        argument_count: usize,
    },
}

/// Deep, assumption-free canonical form for a term: every load resolves its
/// cached cell or canonicalizes its snapshot and pointer, at every depth,
/// including inside conditionals, folds, and pointer offsets. Two forms
/// of the same value produced from different memory snapshots canonicalize
/// identically whenever the difference is representational. The walk is
/// over the term and the values its loads resolve to, each recorded before
/// the snapshot that holds it, so it is finite with no depth cut.
pub(super) fn canonicalize_atomic_loads_deep(term: &Bitvector32Term) -> Bitvector32Term {
    macro_rules! visit_binary {
        ($constructor:path, $left:expr, $right:expr, $tasks:expr) => {{
            $tasks.push(AtomicCanonicalizationTask::RebuildBinary($constructor));
            $tasks.push(AtomicCanonicalizationTask::Visit($right));
            $tasks.push(AtomicCanonicalizationTask::Visit($left));
        }};
    }
    macro_rules! visit_unary {
        ($constructor:path, $value:expr, $tasks:expr) => {{
            $tasks.push(AtomicCanonicalizationTask::RebuildUnary($constructor));
            $tasks.push(AtomicCanonicalizationTask::Visit($value));
        }};
    }
    macro_rules! visit_condition_binary {
        ($constructor:path, $left:expr, $right:expr, $tasks:expr) => {{
            $tasks.push(AtomicCanonicalizationTask::RebuildConditionBinary(
                $constructor,
            ));
            $tasks.push(AtomicCanonicalizationTask::Visit($right));
            $tasks.push(AtomicCanonicalizationTask::Visit($left));
        }};
    }

    let mut tasks = vec![AtomicCanonicalizationTask::Visit(term)];
    let mut results = Vec::new();
    let mut condition_results = Vec::new();
    let mut offset_results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            AtomicCanonicalizationTask::Visit(term) => {
                #[cfg(test)]
                ATOMIC_CANONICALIZATION_TERM_VISITS.with(|visits| visits.set(visits.get() + 1));
                match term {
                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::Variable(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_) => results.push(term.clone()),
                    Bitvector32Term::MemoryLoad(memory, pointer) => {
                        let canonical_pointer = canonicalize_pointer_loads(pointer);
                        let resolved = match memory.load(&canonical_pointer) {
                            CExpressionOutcome::Value(
                                CValue::Int16(value)
                                | CValue::Int32(value)
                                | CValue::UInt8(value)
                                | CValue::UInt16(value)
                                | CValue::UInt32(value),
                            ) if &value != term => Some(value),
                            _ => match memory.load(pointer) {
                                CExpressionOutcome::Value(
                                    CValue::Int16(value)
                                    | CValue::Int32(value)
                                    | CValue::UInt8(value)
                                    | CValue::UInt16(value)
                                    | CValue::UInt32(value),
                                ) if &value != term => Some(value),
                                _ => None,
                            },
                        };
                        let Some(mut value) = resolved else {
                            // Name the cell by its DAG epoch before restricting
                            // the snapshot: the restriction is a fresh intern
                            // with no derivation, so an epoch walk over it
                            // could not cross anything. Walking the original
                            // snapshot lets two loads of one unwritten cell at
                            // different points share one canonical form.
                            let epoch = cell_epoch_for_load_variable(memory, &canonical_pointer);
                            let epoch = epoch.as_ref().unwrap_or(memory);
                            results.push(Bitvector32Term::MemoryLoad(
                                crate::kernel::intern_c_memory(
                                    canonical_c_memory_for_pointer_load(epoch, &canonical_pointer),
                                ),
                                Box::new(canonical_pointer),
                            ));
                            continue;
                        };

                        // A materialized cell may itself contain a load from
                        // another snapshot. Follow that root-load chain here
                        // rather than recursively entering one Rust frame per
                        // cell. Composite recorded values re-enter the normal
                        // structural worklist below.
                        loop {
                            let Bitvector32Term::MemoryLoad(next_memory, next_pointer) = &value
                            else {
                                results.push(canonicalize_atomic_loads_deep(&value));
                                break;
                            };
                            let canonical_pointer = canonicalize_pointer_loads(next_pointer);
                            let resolved = match next_memory.load(&canonical_pointer) {
                                CExpressionOutcome::Value(
                                    CValue::Int16(next)
                                    | CValue::Int32(next)
                                    | CValue::UInt8(next)
                                    | CValue::UInt16(next)
                                    | CValue::UInt32(next),
                                ) if next != value => Some(next),
                                _ => match next_memory.load(next_pointer) {
                                    CExpressionOutcome::Value(
                                        CValue::Int16(next)
                                        | CValue::Int32(next)
                                        | CValue::UInt8(next)
                                        | CValue::UInt16(next)
                                        | CValue::UInt32(next),
                                    ) if next != value => Some(next),
                                    _ => None,
                                },
                            };
                            if let Some(next) = resolved {
                                value = next;
                                continue;
                            }
                            let epoch =
                                cell_epoch_for_load_variable(next_memory, &canonical_pointer);
                            let epoch = epoch.as_ref().unwrap_or(next_memory);
                            results.push(Bitvector32Term::MemoryLoad(
                                crate::kernel::intern_c_memory(
                                    canonical_c_memory_for_pointer_load(epoch, &canonical_pointer),
                                ),
                                Box::new(canonical_pointer),
                            ));
                            break;
                        }
                    }
                    Bitvector32Term::Add(left, right) => {
                        visit_binary!(Bitvector32Term::Add, left, right, tasks)
                    }
                    Bitvector32Term::Subtract(left, right) => {
                        visit_binary!(Bitvector32Term::Subtract, left, right, tasks)
                    }
                    Bitvector32Term::Multiply(left, right) => {
                        visit_binary!(Bitvector32Term::Multiply, left, right, tasks)
                    }
                    Bitvector32Term::Divide(left, right) => {
                        visit_binary!(Bitvector32Term::Divide, left, right, tasks)
                    }
                    Bitvector32Term::UnsignedDivide(left, right) => {
                        visit_binary!(Bitvector32Term::UnsignedDivide, left, right, tasks)
                    }
                    Bitvector32Term::Remainder(left, right) => {
                        visit_binary!(Bitvector32Term::Remainder, left, right, tasks)
                    }
                    Bitvector32Term::UnsignedRemainder(left, right) => {
                        visit_binary!(Bitvector32Term::UnsignedRemainder, left, right, tasks)
                    }
                    Bitvector32Term::ShiftLeft(left, right) => {
                        visit_binary!(Bitvector32Term::ShiftLeft, left, right, tasks)
                    }
                    Bitvector32Term::ArithmeticShiftRight(left, right) => {
                        visit_binary!(Bitvector32Term::ArithmeticShiftRight, left, right, tasks)
                    }
                    Bitvector32Term::LogicalShiftRight(left, right) => {
                        visit_binary!(Bitvector32Term::LogicalShiftRight, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseAnd(left, right) => {
                        visit_binary!(Bitvector32Term::BitwiseAnd, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseOr(left, right) => {
                        visit_binary!(Bitvector32Term::BitwiseOr, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseXor(left, right) => {
                        visit_binary!(Bitvector32Term::BitwiseXor, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseNot(value) => {
                        visit_unary!(Bitvector32Term::BitwiseNot, value, tasks)
                    }
                    Bitvector32Term::Int64From32(value) => {
                        visit_unary!(Bitvector32Term::Int64From32, value, tasks)
                    }
                    Bitvector32Term::Int64FromUInt32(value) => {
                        visit_unary!(Bitvector32Term::Int64FromUInt32, value, tasks)
                    }
                    Bitvector32Term::UInt64From32(value) => {
                        visit_unary!(Bitvector32Term::UInt64From32, value, tasks)
                    }
                    Bitvector32Term::UInt64FromInt32(value) => {
                        visit_unary!(Bitvector32Term::UInt64FromInt32, value, tasks)
                    }
                    Bitvector32Term::UInt64FromInt64(value) => {
                        visit_unary!(Bitvector32Term::UInt64FromInt64, value, tasks)
                    }
                    Bitvector32Term::Int64BitwiseNot(value) => {
                        visit_unary!(Bitvector32Term::Int64BitwiseNot, value, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseNot(value) => {
                        visit_unary!(Bitvector32Term::UInt64BitwiseNot, value, tasks)
                    }
                    Bitvector32Term::Int64Add(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Add, left, right, tasks)
                    }
                    Bitvector32Term::Int64Subtract(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Subtract, left, right, tasks)
                    }
                    Bitvector32Term::Int64Multiply(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Multiply, left, right, tasks)
                    }
                    Bitvector32Term::Int64Divide(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Divide, left, right, tasks)
                    }
                    Bitvector32Term::Int64Remainder(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Remainder, left, right, tasks)
                    }
                    Bitvector32Term::Int64ShiftLeft(left, right) => {
                        visit_binary!(Bitvector32Term::Int64ShiftLeft, left, right, tasks)
                    }
                    Bitvector32Term::Int64ArithmeticShiftRight(left, right) => visit_binary!(
                        Bitvector32Term::Int64ArithmeticShiftRight,
                        left,
                        right,
                        tasks
                    ),
                    Bitvector32Term::Int64BitwiseAnd(left, right) => {
                        visit_binary!(Bitvector32Term::Int64BitwiseAnd, left, right, tasks)
                    }
                    Bitvector32Term::Int64BitwiseOr(left, right) => {
                        visit_binary!(Bitvector32Term::Int64BitwiseOr, left, right, tasks)
                    }
                    Bitvector32Term::Int64BitwiseXor(left, right) => {
                        visit_binary!(Bitvector32Term::Int64BitwiseXor, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Add(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Add, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Subtract(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Subtract, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Multiply(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Multiply, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Divide(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Divide, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Remainder(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Remainder, left, right, tasks)
                    }
                    Bitvector32Term::UInt64ShiftLeft(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64ShiftLeft, left, right, tasks)
                    }
                    Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64LogicalShiftRight, left, right, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseAnd(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64BitwiseAnd, left, right, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseOr(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64BitwiseOr, left, right, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseXor(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64BitwiseXor, left, right, tasks)
                    }
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildIf);
                        tasks.push(AtomicCanonicalizationTask::Visit(else_term));
                        tasks.push(AtomicCanonicalizationTask::Visit(then_term));
                        tasks.push(AtomicCanonicalizationTask::VisitCondition(condition));
                    }
                    Bitvector32Term::RangeFold {
                        start,
                        end,
                        initial,
                        accumulator,
                        item,
                        body,
                    } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildRangeFold {
                            accumulator: *accumulator,
                            item: *item,
                        });
                        tasks.push(AtomicCanonicalizationTask::Visit(body));
                        tasks.push(AtomicCanonicalizationTask::Visit(initial));
                        tasks.push(AtomicCanonicalizationTask::Visit(end));
                        tasks.push(AtomicCanonicalizationTask::Visit(start));
                    }
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildPureFunction {
                            name: name.clone(),
                            argument_count: arguments.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(AtomicCanonicalizationTask::Visit(argument));
                        }
                    }
                }
            }
            AtomicCanonicalizationTask::VisitCondition(condition) => match condition {
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedLessThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedLessEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedGreaterThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedGreaterEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32Equal(left, right) => {
                    visit_condition_binary!(ConditionTerm::Bitvector32Equal, left, right, tasks)
                }
                ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedAddOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedSubtractOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedMultiplyOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedDivideOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedShiftLeftOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedLessThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedLessThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedLessEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedGreaterThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedGreaterEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedLessThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedLessEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedGreaterThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedGreaterEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64Equal(left, right) => {
                    visit_condition_binary!(ConditionTerm::Bitvector64Equal, left, right, tasks)
                }
                ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedAddOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedSubtractOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedMultiplyOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedDivideOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedShiftLeftOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildPointerOffsetEqual);
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(right));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(left));
                }
                ConditionTerm::PointerEqual(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildPointerEqual {
                        left_block: left.block.clone(),
                        right_block: right.block.clone(),
                    });
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(&right.offset));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(&left.offset));
                }
            },
            AtomicCanonicalizationTask::VisitOffset(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    offset_results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildOffsetAdd);
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(right));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(left));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    tasks.push(AtomicCanonicalizationTask::RebuildInt32Scaled(*byte_width));
                    tasks.push(AtomicCanonicalizationTask::Visit(value));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    tasks.push(AtomicCanonicalizationTask::RebuildInt64Scaled {
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    });
                    tasks.push(AtomicCanonicalizationTask::Visit(value));
                }
            },
            AtomicCanonicalizationTask::RebuildBinary(constructor) => {
                let right = results.pop().expect("visited right term");
                let left = results.pop().expect("visited left term");
                results.push(constructor(Box::new(left), Box::new(right)));
            }
            AtomicCanonicalizationTask::RebuildUnary(constructor) => {
                let value = results.pop().expect("visited unary term");
                results.push(constructor(Box::new(value)));
            }
            AtomicCanonicalizationTask::RebuildConditionBinary(constructor) => {
                let right = results.pop().expect("visited right condition operand");
                let left = results.pop().expect("visited left condition operand");
                condition_results.push(constructor(Box::new(left), Box::new(right)));
            }
            AtomicCanonicalizationTask::RebuildPointerOffsetEqual => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerOffsetEqual(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            AtomicCanonicalizationTask::RebuildPointerEqual {
                left_block,
                right_block,
            } => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerEqual(
                    Box::new(Pointer {
                        block: left_block,
                        offset: left,
                    }),
                    Box::new(Pointer {
                        block: right_block,
                        offset: right,
                    }),
                ));
            }
            AtomicCanonicalizationTask::RebuildOffsetAdd => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                offset_results.push(PointerOffsetTerm::add(left, right));
            }
            AtomicCanonicalizationTask::RebuildInt32Scaled(byte_width) => {
                let value = results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int32(value, byte_width));
            }
            AtomicCanonicalizationTask::RebuildInt64Scaled {
                byte_width,
                unsigned,
            } => {
                let value = results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int64(value, byte_width, unsigned));
            }
            AtomicCanonicalizationTask::RebuildIf => {
                let else_term = results.pop().expect("visited else term");
                let then_term = results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                results.push(Bitvector32Term::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
            AtomicCanonicalizationTask::RebuildRangeFold { accumulator, item } => {
                let body = results.pop().expect("visited fold body");
                let initial = results.pop().expect("visited fold initial value");
                let end = results.pop().expect("visited fold end");
                let start = results.pop().expect("visited fold start");
                results.push(Bitvector32Term::RangeFold {
                    start: Box::new(start),
                    end: Box::new(end),
                    initial: Box::new(initial),
                    accumulator,
                    item,
                    body: Box::new(body),
                });
            }
            AtomicCanonicalizationTask::RebuildPureFunction {
                name,
                argument_count,
            } => {
                let first = results.len() - argument_count;
                let arguments = results.split_off(first);
                results.push(Bitvector32Term::PureFunctionApplication { name, arguments });
            }
        }
    }
    assert_eq!(results.len(), 1, "canonicalization produces one term");
    assert!(condition_results.is_empty());
    assert!(offset_results.is_empty());
    results.pop().unwrap()
}

/// Canonicalizes the loads inside a pointer's offset.
pub(super) fn canonicalize_pointer_loads(pointer: &Pointer) -> Pointer {
    enum OffsetTask<'a> {
        Visit(&'a PointerOffsetTerm),
        RebuildAdd,
    }
    let mut tasks = vec![OffsetTask::Visit(&pointer.offset)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            OffsetTask::Visit(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(OffsetTask::RebuildAdd);
                    tasks.push(OffsetTask::Visit(right));
                    tasks.push(OffsetTask::Visit(left));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    results.push(PointerOffsetTerm::scale_int32(
                        canonicalize_atomic_loads_deep(value),
                        *byte_width,
                    ));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => results.push(PointerOffsetTerm::scale_int64(
                    canonicalize_atomic_loads_deep(value),
                    *byte_width,
                    *unsigned,
                )),
            },
            OffsetTask::RebuildAdd => {
                let right = results.pop().expect("visited right offset");
                let left = results.pop().expect("visited left offset");
                results.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    Pointer {
        block: pointer.block.clone(),
        offset: results.pop().expect("canonicalization produces one offset"),
    }
}

/// Compares two condition facts operandwise under memory-resolution
/// equality, so forms that differ only in provably-irrelevant cached
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
/// value. These are execution-certified equations usable by check.
pub(crate) fn certified_store_equations(facts: &[ExecutionPureFact]) -> Vec<Proposition> {
    facts
        .iter()
        .filter_map(|fact| {
            let store = fact.certified_store_data()?;
            let value = match &store.value {
                CValue::Int16(term)
                | CValue::Int32(term)
                | CValue::UInt8(term)
                | CValue::UInt16(term)
                | CValue::UInt32(term)
                | CValue::Int64(term)
                | CValue::UInt64(term) => term.clone(),
                CValue::Void | CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => {
                    return None;
                }
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
                CValue::Int16(_) | CValue::UInt16(_) => 2,
                CValue::Int32(_) | CValue::UInt32(_) => 4,
                CValue::Int64(_) | CValue::UInt64(_) => 8,
                CValue::Pointer(_) => 4,
                CValue::Float32(_) => 4,
                CValue::Float64(_) => 8,
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
            | Bitvector32Term::UnsignedDivide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::UnsignedRemainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::LogicalShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                bitvector_has_memory(left) || bitvector_has_memory(right)
            }
            Bitvector32Term::BitwiseNot(term)
            | Bitvector32Term::Int64BitwiseNot(term)
            | Bitvector32Term::UInt64BitwiseNot(term) => bitvector_has_memory(term),
            Bitvector32Term::Int64From32(term)
            | Bitvector32Term::UInt64From32(term)
            | Bitvector32Term::Int64FromUInt32(term)
            | Bitvector32Term::UInt64FromInt32(term)
            | Bitvector32Term::UInt64FromInt64(term) => bitvector_has_memory(term),
            Bitvector32Term::Int64Add(left, right)
            | Bitvector32Term::Int64Subtract(left, right)
            | Bitvector32Term::Int64Multiply(left, right)
            | Bitvector32Term::Int64Divide(left, right)
            | Bitvector32Term::Int64Remainder(left, right)
            | Bitvector32Term::Int64ShiftLeft(left, right)
            | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
            | Bitvector32Term::Int64BitwiseAnd(left, right)
            | Bitvector32Term::Int64BitwiseOr(left, right)
            | Bitvector32Term::Int64BitwiseXor(left, right)
            | Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64Multiply(left, right)
            | Bitvector32Term::UInt64Divide(left, right)
            | Bitvector32Term::UInt64Remainder(left, right)
            | Bitvector32Term::UInt64ShiftLeft(left, right)
            | Bitvector32Term::UInt64LogicalShiftRight(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right)
            | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                bitvector_has_memory(left) || bitvector_has_memory(right)
            }
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
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::Variable(_) => false,
        }
    }
    fn offset_has_memory(offset: &PointerOffsetTerm) -> bool {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                offset_has_memory(left) || offset_has_memory(right)
            }
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => bitvector_has_memory(value),
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
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
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
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
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
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_memories(value, memories)
        }
    }
}

fn collect_bitvector_memories(term: &Bitvector32Term, memories: &mut Vec<SharedCMemory>) {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(memory, _) => {
            if !memories.contains(memory) {
                memories.push(memory.clone());
            }
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right)
        | Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            collect_bitvector_memories(left, memories);
            collect_bitvector_memories(right, memories);
        }
        Bitvector32Term::BitwiseNot(term)
        | Bitvector32Term::Int64BitwiseNot(term)
        | Bitvector32Term::UInt64BitwiseNot(term)
        | Bitvector32Term::Int64From32(term)
        | Bitvector32Term::UInt64From32(term)
        | Bitvector32Term::Int64FromUInt32(term)
        | Bitvector32Term::UInt64FromInt32(term)
        | Bitvector32Term::UInt64FromInt64(term) => collect_bitvector_memories(term, memories),
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
        ConditionTerm::Bitvector64SignedLessThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_less_than(left, right)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_less_equal(left, right)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_greater_than(left, right)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_greater_equal(left, right)
        }
        ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::uint64_less_than(left, right)
        }
        ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::uint64_less_equal(left, right)
        }
        ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::uint64_greater_than(left, right)
        }
        ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::uint64_greater_equal(left, right)
        }
        ConditionTerm::Bitvector64Equal(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_equal(left, right)
        }
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_add_overflows(left, right)
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_subtract_overflows(left, right)
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_multiply_overflows(left, right)
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_divide_overflows(left, right)
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::int64_signed_shift_left_overflows(left, right)
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
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => PointerOffsetTerm::scale_int64(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
            *byte_width,
            *unsigned,
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
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        Some((
            transport_framed_atomic_bitvector(left, after, assumptions)?,
            transport_framed_atomic_bitvector(right, after, assumptions)?,
        ))
    };
    Some(match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_) => term.clone(),
        Bitvector32Term::Variable(variable) => {
            // A load variable transports as the load it represents:
            // when frame evidence rewrites that load to the post-effect
            // snapshot, the fact is rewritten with the post-point load
            // variable. Content-addressed construction gives the same variable
            // to any later lowering at that snapshot. A defining equation
            // in the ambient assumptions carries the mint-time form,
            // whose live snapshot the frame checks can actually relate to
            // `after`; the registry's canonicalized form is the
            // fallback.
            // The registry's origin is the first live snapshot the variable
            // was minted from: DAG-connected and cell-comparable to `after`,
            // which is what the frame checks below relate.
            let named_load = crate::kernel::eval::registered_load_origin_for_variable(variable)
                .map(|(memory, pointer)| Bitvector32Term::MemoryLoad(memory, Box::new(pointer)));
            if let Some(load) = named_load {
                let transported = transport_framed_atomic_bitvector(&load, after, assumptions)?;
                if transported != load
                    && let Some((renamed, _)) =
                        crate::kernel::eval::load_variable_for_term(&transported)
                {
                    Bitvector32Term::Variable(renamed)
                } else {
                    term.clone()
                }
            } else {
                term.clone()
            }
        }
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
        Bitvector32Term::Int64From32(value) => Bitvector32Term::int64_from_32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
        Bitvector32Term::UInt64From32(value) => Bitvector32Term::uint64_from_32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
        Bitvector32Term::Int64FromUInt32(value) => Bitvector32Term::int64_from_uint32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
        Bitvector32Term::UInt64FromInt32(value) => Bitvector32Term::uint64_from_int32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
        Bitvector32Term::UInt64FromInt64(value) => Bitvector32Term::uint64_from_int64(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
        Bitvector32Term::Int64Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_add(left, right)
        }
        Bitvector32Term::Int64Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_subtract(left, right)
        }
        Bitvector32Term::Int64Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_multiply(left, right)
        }
        Bitvector32Term::Int64Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_divide(left, right)
        }
        Bitvector32Term::Int64Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_remainder(left, right)
        }
        Bitvector32Term::Int64ShiftLeft(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_shift_left(left, right)
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_arithmetic_shift_right(left, right)
        }
        Bitvector32Term::Int64BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_bitwise_and(left, right)
        }
        Bitvector32Term::Int64BitwiseOr(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_bitwise_or(left, right)
        }
        Bitvector32Term::Int64BitwiseXor(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::int64_bitwise_xor(left, right)
        }
        Bitvector32Term::Int64BitwiseNot(value) => Bitvector32Term::int64_bitwise_not(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
        Bitvector32Term::UInt64Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_add(left, right)
        }
        Bitvector32Term::UInt64Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_subtract(left, right)
        }
        Bitvector32Term::UInt64Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_multiply(left, right)
        }
        Bitvector32Term::UInt64Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_divide(left, right)
        }
        Bitvector32Term::UInt64Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_remainder(left, right)
        }
        Bitvector32Term::UInt64ShiftLeft(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_shift_left(left, right)
        }
        Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_logical_shift_right(left, right)
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_bitwise_and(left, right)
        }
        Bitvector32Term::UInt64BitwiseOr(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_bitwise_or(left, right)
        }
        Bitvector32Term::UInt64BitwiseXor(left, right) => {
            let (left, right) = binary(left, right)?;
            Bitvector32Term::uint64_bitwise_xor(left, right)
        }
        Bitvector32Term::UInt64BitwiseNot(value) => Bitvector32Term::uint64_bitwise_not(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
        ),
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
        Bitvector32Term::UnsignedDivide(left, right) => Bitvector32Term::UnsignedDivide(
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
        Bitvector32Term::UnsignedRemainder(left, right) => Bitvector32Term::UnsignedRemainder(
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
        Bitvector32Term::LogicalShiftRight(left, right) => Bitvector32Term::LogicalShiftRight(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
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
    let left = normalize_exact_memory_loads_in_pointer_offset(left, assumptions);
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    let right = normalize_exact_memory_loads_in_pointer_offset(right, assumptions);
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
) -> PointerOffsetTerm {
    enum Task {
        Visit(PointerOffsetTerm),
        RebuildAdd,
    }

    let mut tasks = vec![Task::Visit(offset.clone())];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(offset) => {
                crate::instrumentation::record_deterministic_work(1);
                if crate::instrumentation::deadline_exceeded() {
                    results.push(offset);
                    continue;
                }
                match offset {
                    PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                        results.push(offset)
                    }
                    PointerOffsetTerm::Add(left, right) => {
                        tasks.push(Task::RebuildAdd);
                        tasks.push(Task::Visit(*right));
                        tasks.push(Task::Visit(*left));
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                        results.push(PointerOffsetTerm::scale_int32(
                            normalize_exact_memory_loads_in_bitvector(&value, assumptions),
                            byte_width,
                        ));
                    }
                    PointerOffsetTerm::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => {
                        results.push(PointerOffsetTerm::scale_int64(
                            normalize_exact_memory_loads_in_bitvector(&value, assumptions),
                            byte_width,
                            unsigned,
                        ));
                    }
                }
            }
            Task::RebuildAdd => {
                let right = results.pop().expect("visited right pointer offset");
                let left = results.pop().expect("visited left pointer offset");
                results.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    results
        .pop()
        .expect("normalization produces one pointer offset")
}

#[derive(Clone, Copy)]
enum ExactLoadBinary {
    Add,
    Subtract,
    Multiply,
    Divide,
    UnsignedDivide,
    Remainder,
    UnsignedRemainder,
    ShiftLeft,
    ArithmeticShiftRight,
    LogicalShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    Int64Add,
    Int64Subtract,
    Int64Multiply,
    Int64Divide,
    Int64Remainder,
    Int64ShiftLeft,
    Int64ArithmeticShiftRight,
    Int64BitwiseAnd,
    Int64BitwiseOr,
    Int64BitwiseXor,
    UInt64Add,
    UInt64Subtract,
    UInt64Multiply,
    UInt64Divide,
    UInt64Remainder,
    UInt64ShiftLeft,
    UInt64LogicalShiftRight,
    UInt64BitwiseAnd,
    UInt64BitwiseOr,
    UInt64BitwiseXor,
}

#[derive(Clone, Copy)]
enum ExactLoadUnary {
    BitwiseNot,
    Int64From32,
    UInt64From32,
    Int64FromUInt32,
    UInt64FromInt32,
    UInt64FromInt64,
    Int64BitwiseNot,
    UInt64BitwiseNot,
}

enum ExactLoadNormalizationTask {
    Visit(Bitvector32Term),
    RebuildBinary(ExactLoadBinary),
    RebuildUnary(ExactLoadUnary),
    RebuildIf(ConditionTerm),
    RebuildPureFunction { name: String, argument_count: usize },
    LeaveLoad(Bitvector32Term),
}

fn normalize_exact_memory_loads_in_bitvector_iterative(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Bitvector32Term {
    fn rebuild_binary(
        operator: ExactLoadBinary,
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Bitvector32Term {
        match operator {
            ExactLoadBinary::Add => Bitvector32Term::add(left, right),
            ExactLoadBinary::Subtract => Bitvector32Term::subtract(left, right),
            ExactLoadBinary::Multiply => Bitvector32Term::multiply(left, right),
            ExactLoadBinary::Divide => Bitvector32Term::divide(left, right),
            ExactLoadBinary::UnsignedDivide => Bitvector32Term::unsigned_divide(left, right),
            ExactLoadBinary::Remainder => Bitvector32Term::remainder(left, right),
            ExactLoadBinary::UnsignedRemainder => Bitvector32Term::unsigned_remainder(left, right),
            ExactLoadBinary::ShiftLeft => Bitvector32Term::shift_left(left, right),
            ExactLoadBinary::ArithmeticShiftRight => {
                Bitvector32Term::arithmetic_shift_right(left, right)
            }
            ExactLoadBinary::LogicalShiftRight => Bitvector32Term::logical_shift_right(left, right),
            ExactLoadBinary::BitwiseAnd => Bitvector32Term::bitwise_and(left, right),
            ExactLoadBinary::BitwiseOr => Bitvector32Term::bitwise_or(left, right),
            ExactLoadBinary::BitwiseXor => Bitvector32Term::bitwise_xor(left, right),
            ExactLoadBinary::Int64Add => Bitvector32Term::int64_add(left, right),
            ExactLoadBinary::Int64Subtract => Bitvector32Term::int64_subtract(left, right),
            ExactLoadBinary::Int64Multiply => Bitvector32Term::int64_multiply(left, right),
            ExactLoadBinary::Int64Divide => Bitvector32Term::int64_divide(left, right),
            ExactLoadBinary::Int64Remainder => Bitvector32Term::int64_remainder(left, right),
            ExactLoadBinary::Int64ShiftLeft => Bitvector32Term::int64_shift_left(left, right),
            ExactLoadBinary::Int64ArithmeticShiftRight => {
                Bitvector32Term::int64_arithmetic_shift_right(left, right)
            }
            ExactLoadBinary::Int64BitwiseAnd => Bitvector32Term::int64_bitwise_and(left, right),
            ExactLoadBinary::Int64BitwiseOr => Bitvector32Term::int64_bitwise_or(left, right),
            ExactLoadBinary::Int64BitwiseXor => Bitvector32Term::int64_bitwise_xor(left, right),
            ExactLoadBinary::UInt64Add => Bitvector32Term::uint64_add(left, right),
            ExactLoadBinary::UInt64Subtract => Bitvector32Term::uint64_subtract(left, right),
            ExactLoadBinary::UInt64Multiply => Bitvector32Term::uint64_multiply(left, right),
            ExactLoadBinary::UInt64Divide => Bitvector32Term::uint64_divide(left, right),
            ExactLoadBinary::UInt64Remainder => Bitvector32Term::uint64_remainder(left, right),
            ExactLoadBinary::UInt64ShiftLeft => Bitvector32Term::uint64_shift_left(left, right),
            ExactLoadBinary::UInt64LogicalShiftRight => {
                Bitvector32Term::uint64_logical_shift_right(left, right)
            }
            ExactLoadBinary::UInt64BitwiseAnd => Bitvector32Term::uint64_bitwise_and(left, right),
            ExactLoadBinary::UInt64BitwiseOr => Bitvector32Term::uint64_bitwise_or(left, right),
            ExactLoadBinary::UInt64BitwiseXor => Bitvector32Term::uint64_bitwise_xor(left, right),
        }
    }

    fn rebuild_unary(operator: ExactLoadUnary, value: Bitvector32Term) -> Bitvector32Term {
        match operator {
            ExactLoadUnary::BitwiseNot => Bitvector32Term::bitwise_not(value),
            ExactLoadUnary::Int64From32 => Bitvector32Term::int64_from_32(value),
            ExactLoadUnary::UInt64From32 => Bitvector32Term::uint64_from_32(value),
            ExactLoadUnary::Int64FromUInt32 => Bitvector32Term::int64_from_uint32(value),
            ExactLoadUnary::UInt64FromInt32 => Bitvector32Term::uint64_from_int32(value),
            ExactLoadUnary::UInt64FromInt64 => Bitvector32Term::uint64_from_int64(value),
            ExactLoadUnary::Int64BitwiseNot => Bitvector32Term::int64_bitwise_not(value),
            ExactLoadUnary::UInt64BitwiseNot => Bitvector32Term::uint64_bitwise_not(value),
        }
    }

    fn push_binary(
        tasks: &mut Vec<ExactLoadNormalizationTask>,
        operator: ExactLoadBinary,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    ) {
        tasks.push(ExactLoadNormalizationTask::RebuildBinary(operator));
        tasks.push(ExactLoadNormalizationTask::Visit(*right));
        tasks.push(ExactLoadNormalizationTask::Visit(*left));
    }

    fn push_unary(
        tasks: &mut Vec<ExactLoadNormalizationTask>,
        operator: ExactLoadUnary,
        value: Box<Bitvector32Term>,
    ) {
        tasks.push(ExactLoadNormalizationTask::RebuildUnary(operator));
        tasks.push(ExactLoadNormalizationTask::Visit(*value));
    }

    let mut tasks = vec![ExactLoadNormalizationTask::Visit(term.clone())];
    let mut results = Vec::new();
    let mut active_loads = std::collections::HashSet::new();
    while let Some(task) = tasks.pop() {
        match task {
            ExactLoadNormalizationTask::Visit(term) => {
                crate::instrumentation::record_deterministic_work(1);
                if crate::instrumentation::deadline_exceeded() {
                    results.push(term);
                    continue;
                }
                match term {
                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
                    | Bitvector32Term::Variable(_) => results.push(term),
                    Bitvector32Term::Add(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Add, left, right)
                    }
                    Bitvector32Term::Subtract(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Subtract, left, right)
                    }
                    Bitvector32Term::Multiply(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Multiply, left, right)
                    }
                    Bitvector32Term::Divide(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Divide, left, right)
                    }
                    Bitvector32Term::UnsignedDivide(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UnsignedDivide, left, right)
                    }
                    Bitvector32Term::Remainder(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Remainder, left, right)
                    }
                    Bitvector32Term::UnsignedRemainder(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UnsignedRemainder, left, right)
                    }
                    Bitvector32Term::ShiftLeft(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::ShiftLeft, left, right)
                    }
                    Bitvector32Term::ArithmeticShiftRight(left, right) => push_binary(
                        &mut tasks,
                        ExactLoadBinary::ArithmeticShiftRight,
                        left,
                        right,
                    ),
                    Bitvector32Term::LogicalShiftRight(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::LogicalShiftRight, left, right)
                    }
                    Bitvector32Term::BitwiseAnd(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::BitwiseAnd, left, right)
                    }
                    Bitvector32Term::BitwiseOr(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::BitwiseOr, left, right)
                    }
                    Bitvector32Term::BitwiseXor(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::BitwiseXor, left, right)
                    }
                    Bitvector32Term::Int64Add(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64Add, left, right)
                    }
                    Bitvector32Term::Int64Subtract(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64Subtract, left, right)
                    }
                    Bitvector32Term::Int64Multiply(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64Multiply, left, right)
                    }
                    Bitvector32Term::Int64Divide(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64Divide, left, right)
                    }
                    Bitvector32Term::Int64Remainder(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64Remainder, left, right)
                    }
                    Bitvector32Term::Int64ShiftLeft(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64ShiftLeft, left, right)
                    }
                    Bitvector32Term::Int64ArithmeticShiftRight(left, right) => push_binary(
                        &mut tasks,
                        ExactLoadBinary::Int64ArithmeticShiftRight,
                        left,
                        right,
                    ),
                    Bitvector32Term::Int64BitwiseAnd(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64BitwiseAnd, left, right)
                    }
                    Bitvector32Term::Int64BitwiseOr(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64BitwiseOr, left, right)
                    }
                    Bitvector32Term::Int64BitwiseXor(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::Int64BitwiseXor, left, right)
                    }
                    Bitvector32Term::UInt64Add(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64Add, left, right)
                    }
                    Bitvector32Term::UInt64Subtract(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64Subtract, left, right)
                    }
                    Bitvector32Term::UInt64Multiply(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64Multiply, left, right)
                    }
                    Bitvector32Term::UInt64Divide(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64Divide, left, right)
                    }
                    Bitvector32Term::UInt64Remainder(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64Remainder, left, right)
                    }
                    Bitvector32Term::UInt64ShiftLeft(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64ShiftLeft, left, right)
                    }
                    Bitvector32Term::UInt64LogicalShiftRight(left, right) => push_binary(
                        &mut tasks,
                        ExactLoadBinary::UInt64LogicalShiftRight,
                        left,
                        right,
                    ),
                    Bitvector32Term::UInt64BitwiseAnd(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64BitwiseAnd, left, right)
                    }
                    Bitvector32Term::UInt64BitwiseOr(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64BitwiseOr, left, right)
                    }
                    Bitvector32Term::UInt64BitwiseXor(left, right) => {
                        push_binary(&mut tasks, ExactLoadBinary::UInt64BitwiseXor, left, right)
                    }
                    Bitvector32Term::BitwiseNot(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::BitwiseNot, value)
                    }
                    Bitvector32Term::Int64From32(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::Int64From32, value)
                    }
                    Bitvector32Term::UInt64From32(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::UInt64From32, value)
                    }
                    Bitvector32Term::Int64FromUInt32(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::Int64FromUInt32, value)
                    }
                    Bitvector32Term::UInt64FromInt32(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::UInt64FromInt32, value)
                    }
                    Bitvector32Term::UInt64FromInt64(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::UInt64FromInt64, value)
                    }
                    Bitvector32Term::Int64BitwiseNot(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::Int64BitwiseNot, value)
                    }
                    Bitvector32Term::UInt64BitwiseNot(value) => {
                        push_unary(&mut tasks, ExactLoadUnary::UInt64BitwiseNot, value)
                    }
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(ExactLoadNormalizationTask::RebuildIf(*condition));
                        tasks.push(ExactLoadNormalizationTask::Visit(*else_term));
                        tasks.push(ExactLoadNormalizationTask::Visit(*then_term));
                    }
                    Bitvector32Term::RangeFold { .. } => results.push(term),
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
                        let argument_count = arguments.len();
                        tasks.push(ExactLoadNormalizationTask::RebuildPureFunction {
                            name,
                            argument_count,
                        });
                        for argument in arguments.into_iter().rev() {
                            tasks.push(ExactLoadNormalizationTask::Visit(argument));
                        }
                    }
                    load @ Bitvector32Term::MemoryLoad(_, _) => {
                        if !active_loads.insert(load.clone()) {
                            results.push(load);
                            continue;
                        }
                        let Bitvector32Term::MemoryLoad(memory, pointer) = &load else {
                            unreachable!()
                        };
                        let resolved = match memory.known_value(pointer) {
                            Some(CValue::Int32(value)) if value != load => Some(value),
                            _ => assumptions.resolve_memory_load_term(&load),
                        };
                        let Some(resolved) = resolved else {
                            active_loads.remove(&load);
                            results.push(load);
                            continue;
                        };
                        tasks.push(ExactLoadNormalizationTask::LeaveLoad(load));
                        tasks.push(ExactLoadNormalizationTask::Visit(resolved));
                    }
                }
            }
            ExactLoadNormalizationTask::RebuildBinary(operator) => {
                let right = results.pop().expect("visited right bitvector term");
                let left = results.pop().expect("visited left bitvector term");
                results.push(rebuild_binary(operator, left, right));
            }
            ExactLoadNormalizationTask::RebuildUnary(operator) => {
                let value = results.pop().expect("visited unary bitvector term");
                results.push(rebuild_unary(operator, value));
            }
            ExactLoadNormalizationTask::RebuildIf(condition) => {
                let else_term = results.pop().expect("visited else term");
                let then_term = results.pop().expect("visited then term");
                results.push(Bitvector32Term::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
            ExactLoadNormalizationTask::RebuildPureFunction {
                name,
                argument_count,
            } => {
                let first = results.len() - argument_count;
                let arguments = results.split_off(first);
                results.push(Bitvector32Term::PureFunctionApplication { name, arguments });
            }
            ExactLoadNormalizationTask::LeaveLoad(load) => {
                active_loads.remove(&load);
            }
        }
    }
    results
        .pop()
        .expect("normalization produces one bitvector term")
}

pub(super) fn normalize_exact_memory_loads_in_bitvector(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Bitvector32Term {
    normalize_exact_memory_loads_in_bitvector_iterative(term, assumptions)
}

fn normalize_exact_memory_loads_in_bitvector_recursive(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
    depth: usize,
) -> Bitvector32Term {
    if depth >= 64 || crate::instrumentation::deadline_exceeded() {
        return term.clone();
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            normalize_exact_memory_loads_in_bitvector_recursive(left, assumptions, depth + 1),
            normalize_exact_memory_loads_in_bitvector_recursive(right, assumptions, depth + 1),
        )
    };
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Variable(_) => term.clone(),
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
        Bitvector32Term::UnsignedDivide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::unsigned_divide(left, right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::remainder(left, right)
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::unsigned_remainder(left, right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::shift_left(left, right)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::arithmetic_shift_right(left, right)
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::logical_shift_right(left, right)
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
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::Int64From32(value) => Bitvector32Term::int64_from_32(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::UInt64From32(value) => Bitvector32Term::uint64_from_32(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::Int64FromUInt32(value) => Bitvector32Term::int64_from_uint32(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::UInt64FromInt32(value) => Bitvector32Term::uint64_from_int32(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::UInt64FromInt64(value) => Bitvector32Term::uint64_from_int64(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::Int64Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_add(left, right)
        }
        Bitvector32Term::Int64Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_subtract(left, right)
        }
        Bitvector32Term::Int64Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_multiply(left, right)
        }
        Bitvector32Term::Int64Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_divide(left, right)
        }
        Bitvector32Term::Int64Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_remainder(left, right)
        }
        Bitvector32Term::Int64ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_shift_left(left, right)
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_arithmetic_shift_right(left, right)
        }
        Bitvector32Term::Int64BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_bitwise_and(left, right)
        }
        Bitvector32Term::Int64BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_bitwise_or(left, right)
        }
        Bitvector32Term::Int64BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::int64_bitwise_xor(left, right)
        }
        Bitvector32Term::Int64BitwiseNot(value) => Bitvector32Term::int64_bitwise_not(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::UInt64Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_add(left, right)
        }
        Bitvector32Term::UInt64Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_subtract(left, right)
        }
        Bitvector32Term::UInt64Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_multiply(left, right)
        }
        Bitvector32Term::UInt64Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_divide(left, right)
        }
        Bitvector32Term::UInt64Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_remainder(left, right)
        }
        Bitvector32Term::UInt64ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_shift_left(left, right)
        }
        Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_logical_shift_right(left, right)
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_bitwise_and(left, right)
        }
        Bitvector32Term::UInt64BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_bitwise_or(left, right)
        }
        Bitvector32Term::UInt64BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::uint64_bitwise_xor(left, right)
        }
        Bitvector32Term::UInt64BitwiseNot(value) => Bitvector32Term::uint64_bitwise_not(
            normalize_exact_memory_loads_in_bitvector_recursive(value, assumptions, depth + 1),
        ),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: condition.clone(),
            then_term: Box::new(normalize_exact_memory_loads_in_bitvector_recursive(
                then_term,
                assumptions,
                depth + 1,
            )),
            else_term: Box::new(normalize_exact_memory_loads_in_bitvector_recursive(
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
                        normalize_exact_memory_loads_in_bitvector_recursive(
                            argument,
                            assumptions,
                            depth + 1,
                        )
                    })
                    .collect(),
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            if let Some(CValue::Int32(value)) = memory.known_value(pointer)
                && &value != term
            {
                return normalize_exact_memory_loads_in_bitvector_recursive(
                    &value,
                    assumptions,
                    depth + 1,
                );
            }
            let Some(value) = assumptions.resolve_memory_load_term(term) else {
                return term.clone();
            };
            normalize_exact_memory_loads_in_bitvector_recursive(&value, assumptions, depth + 1)
        }
    }
}

#[cfg(test)]
mod exact_load_normalization_tests {
    use super::*;

    fn load_chain(length: usize, tail: u32) -> Bitvector32Term {
        let pointer = Pointer {
            block: "normalization-load-chain".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        (0..length).fold(Bitvector32Term::Constant(tail), |value, _| {
            let memory = CMemory::new().store(pointer.clone(), CValue::Int32(value));
            Bitvector32Term::MemoryLoad(intern_c_memory(memory), Box::new(pointer.clone()))
        })
    }

    fn nested_add(length: usize, tail: Bitvector32Term) -> Bitvector32Term {
        (0..length).fold(tail, |term, _| {
            Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(0)), Box::new(term))
        })
    }

    #[test]
    fn exact_load_normalization_is_complete_past_the_old_depth_limit() {
        let term = nested_add(80, load_chain(80, 29));
        assert_eq!(
            normalize_exact_memory_loads_in_bitvector(&term, &PureFactContext::new()),
            Bitvector32Term::Constant(29)
        );

        let offset = (0..80).fold(
            PointerOffsetTerm::Int32Scaled {
                value: Box::new(load_chain(80, 7)),
                byte_width: 4,
            },
            |offset, _| {
                PointerOffsetTerm::Add(Box::new(PointerOffsetTerm::Constant(0)), Box::new(offset))
            },
        );
        assert_eq!(
            normalize_exact_memory_loads_in_pointer_offset(&offset, &PureFactContext::new()),
            PointerOffsetTerm::Constant(28)
        );
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

/// A lookup already in progress for a cell refuses re-entry without
/// unregistering the outer lookup: the guard is built only when its key is
/// new, so the refused path drops nothing.
#[cfg(test)]
#[test]
fn cell_lookup_guard_refuses_reentry_and_keeps_the_outer_lookup() {
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let pointer = Pointer {
        block: "cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let outer = CellLookupGuard::enter(&memory, &pointer).expect("the first lookup registers");
    assert!(!memory_dag_cell_lookup_depth_is_zero());
    assert!(
        CellLookupGuard::enter(&memory, &pointer).is_none(),
        "re-entering the cell is a cycle"
    );
    assert!(
        !memory_dag_cell_lookup_depth_is_zero(),
        "the refused re-entry leaves the outer lookup registered"
    );
    drop(outer);
    assert!(memory_dag_cell_lookup_depth_is_zero());
}

/// Canonicalizes the loads inside a binary condition so forms differing
/// only in redundant cached cells compare and prove identically.
pub(super) fn condition_with_canonicalized_loads(
    condition: &ConditionTerm,
) -> Option<ConditionTerm> {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(canonicalize_atomic_loads_deep(left)),
            Box::new(canonicalize_atomic_loads_deep(right)),
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

/// Returns a condition fact with its loads in canonical form. Forms that
/// differ only in redundant cached cells canonicalize identically.
pub(crate) fn c_condition_fact_with_canonicalized_loads(fact: &Proposition) -> Proposition {
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    match condition_with_canonicalized_loads(condition) {
        Some(canonical) => Proposition::ConditionIs(canonical, *value),
        None => fact.clone(),
    }
}

/// Never-inlined endpoint matcher for the effect arms: the direct-unchanged
/// check participates in transport recursion where added frame bytes
/// overflow the stack. The fact's snapshot handles may differ from the
/// effect's endpoints by bookkeeping (materialized cells, recorded locals);
/// what the chain needs is agreement on the loaded cell, which the
/// directly-match check decides per pointer with havoc-marker parity.
#[inline(never)]
fn directly_matched_effect_endpoint(
    effect_side: &CMemory,
    side: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    memories_directly_match_for_pointer_load(effect_side, side, pointer, assumptions)
}
