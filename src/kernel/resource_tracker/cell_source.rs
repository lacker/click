//! How the tracker reads one memory cell's recorded history: the cell walk
//! and the retained hop evidence it produces.
//!
//! The walk answers two different questions with one traversal. The tracker
//! asks "is this cell the same at these two program points", and takes only
//! the node the walk stopped at. Memory-load reasoning asks "are these two
//! loads equal", and takes the whole path as retained evidence. Both live
//! here because they read the same recorded edges under the same rules; see
//! `docs/internals/resource-tracker.md` and `docs/internals/memory-dag.md`.

use crate::kernel::memory_provenance::*;
use crate::kernel::primitives::*;
use crate::kernel::reasoning::*;

/// Where the memory DAG says the cell at a pointer came from: the
/// select-over-store answer to "what does this cell hold after these
/// stores", read off the write history execution recorded rather than
/// reconstructed by canonicalizing and deep-comparing snapshot values.
///
/// Both variants name the node the walk stopped at, and both denote the same
/// thing — the value of loading the pointer *in that node*. That is what
/// makes two lookups comparable by node identity alone.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MemoryDagCell {
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

/// Why a cell walk stopped where it did.
///
/// The node a walk stops at answers "what does this load read"; this answers
/// the separate question of what the walk *knows* about the step it did not
/// cross, and the three reasons are not interchangeable. A walk that ran out
/// of history proved nothing either way. A walk that could not show a step
/// separate proved nothing either way, and some other route may still
/// separate that step. A walk stopped by a step that provably writes, creates
/// or retires bytes this access reads has established a positive fact: the
/// cell one step older is a *different version* of this cell, and two loads
/// either side of that step are not one value by any structural route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum CellWalkStop {
    /// The walk reached a snapshot with no recorded derivation: the oldest
    /// point the recorded history reaches.
    OldestRecorded,
    /// The step the walk stopped at provably acts on this access's bytes.
    Affected,
    /// The step the walk stopped at could not be shown separate from the
    /// access, and was not shown to act on it either.
    NotShownSeparate,
}

/// One exact edge traversed while resolving a cell through the named memory
/// DAG. Retaining the edge is only the first half of a proof object: callers
/// that expose this walk as a certificate must additionally retain the typed
/// derivation that justified crossing assumption-dependent edges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MemoryDagHop {
    pub(in crate::kernel) derived: SharedCMemory,
    pub(in crate::kernel) derivation: std::sync::Arc<CMemoryDerivation>,
    pub(in crate::kernel) justification: MemoryDagHopJustification,
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
pub(in crate::kernel) enum MemoryDagHopJustification {
    StoreDistinctBlocks,
    StoreCommonBaseUnequalConstants {
        condition: ConditionTerm,
    },
    StoreCommonBaseExactInequality {
        condition: ConditionTerm,
    },
    StoreCommonBaseSignedOrder {
        condition: ConditionTerm,
        path: Vec<SignedOrderDerivationStep>,
        reversed: bool,
    },
    StoreSeparatedRanges {
        authority: StoreSeparatedRangesAuthority,
        left: CMemoryRange,
        right: CMemoryRange,
        orientation: StoreSeparatedRangeOrientation,
        write_membership: PointerInRangeEvidence,
        load_membership: PointerInRangeEvidence,
    },
    IntrinsicNoWrite,
    AllocationOfOtherBlock,
    LocalLifetimeEndedOfOtherBlock,
    HeapFreeOfDistinctBlock,
    /// A `ContractAllocationRetired` edge whose retired allocation lies
    /// inside the write set of the call that retired it
    /// ([`retirement_inside_its_call_havoc`]). The edge writes no byte, and
    /// every byte it could have released was already rewritten by that
    /// call's `CallHavoc`, which is the next edge the walk meets for it.
    RetirementInsideItsCallHavoc,
    CallHavocRanges {
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    LoopHavocRanges {
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    AssumptionDependent(MemoryDagAssumptionKind),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum MemoryDagAssumptionKind {
    StoreCommonBaseDistinctness,
    StoreExplicitRange,
    StoreGeneralDistinctness,
    HeapFreeResourceSeparation,
    CallHavocRangeSeparation,
    /// A cell held by memory the caller kept owning across the call
    /// (`CMemoryDerivation::CallHavoc::kept_by_caller`).
    CallHavocKeptByCaller,
    LoopHavocRangeSeparation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum StoreSeparatedRangesAuthority {
    ExactProposition(Proposition),
    ResourceComposition(ResourceContext),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum StoreSeparatedRangeOrientation {
    WriteLeftLoadRight,
    WriteRightLoadLeft,
}

/// Either an assumption-free structural membership or a pointer's exact
/// element index with the two retained signed bounds that place it inside one
/// range. Symbolic construction may search indexed order facts, but checking
/// touches only this index and the named bound premises.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PointerInRangeEvidence {
    /// Existing structural constant/affine membership. Retaining this cheap
    /// form keeps ordinary store edges out of the symbolic bound producer.
    Shallow,
    Indexed {
        index: Bitvector32Term,
        lower: RangeBoundEvidence,
        upper: RangeBoundEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum RangeBoundEvidence {
    Intrinsic,
    SignedOrderPath(Vec<SignedOrderDerivationStep>),
    /// `left < base + 1` and `base < right` imply `left < right` over
    /// signed int32. The second strict bound also proves that `base + 1`
    /// does not wrap.
    StrictUpperViaSuccessor {
        to_successor: SignedOrderDerivationStep,
        successor_base_to_upper: Vec<SignedOrderDerivationStep>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum RangeDisjointFromPointerEvidence {
    DistinctBlocks,
    ExactSeparationFact(Proposition),
    DirectConstantOutside {
        index: i64,
        /// The access width the index was judged against. A range is a byte
        /// footprint, so an access wider than one element has to clear every
        /// element it reaches, and checking cannot re-derive that from
        /// the index alone.
        bytes: u32,
        start: i64,
        end: i64,
    },
    ForwardOffset {
        offset: Bitvector32Term,
        positive: PositiveTermEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PositiveTermEvidence {
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
    ///
    /// `bytes` is the access width the hop was recorded for. A hop is a claim
    /// that a step missed *these* bytes, so checking it against a different
    /// access is not the same claim.
    pub(in crate::kernel) fn checks(
        &self,
        derivation: &CMemoryDerivation,
        pointer: &Pointer,
        bytes: u32,
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
            Self::StoreCommonBaseSignedOrder {
                condition,
                path,
                reversed,
            } => {
                let CMemoryDerivation::Store { pointer: write, .. } = derivation else {
                    return false;
                };
                let Some(ConditionTerm::Bitvector32Equal(left, right)) =
                    pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                else {
                    return false;
                };
                if condition != &ConditionTerm::Bitvector32Equal(left.clone(), right.clone()) {
                    return false;
                }
                let (lower, upper) = if *reversed {
                    (right.as_ref(), left.as_ref())
                } else {
                    (left.as_ref(), right.as_ref())
                };
                assumptions.checks_exact_signed_order_path(path, lower, upper, true)
            }
            Self::StoreSeparatedRanges {
                authority,
                left,
                right,
                orientation,
                write_membership,
                load_membership,
            } => {
                let CMemoryDerivation::Store { pointer: write, .. } = derivation else {
                    return false;
                };
                let authority_checks = match authority {
                    StoreSeparatedRangesAuthority::ExactProposition(proposition) => {
                        assumptions.prop_facts.contains(proposition)
                            && matches!(
                                proposition,
                                Proposition::CResourceSeparate {
                                    left: CResource::Memory(fact_left),
                                    right: CResource::Memory(fact_right),
                                } if fact_left == left && fact_right == right
                            )
                    }
                    StoreSeparatedRangesAuthority::ResourceComposition(resources) => {
                        assumptions.resource_compositions.contains(resources)
                            && resources.proves_owned_memory_ranges_separate_shallow(left, right)
                    }
                };
                authority_checks
                    && !assumptions.memory_ranges_overlap_after_base_equality(left, right)
                    && !crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                        write,
                        pointer,
                        assumptions,
                    )
                    && match orientation {
                        StoreSeparatedRangeOrientation::WriteLeftLoadRight => {
                            write_membership.checks(write, left, assumptions)
                                && load_membership.checks(pointer, right, assumptions)
                        }
                        StoreSeparatedRangeOrientation::WriteRightLoadLeft => {
                            write_membership.checks(write, right, assumptions)
                                && load_membership.checks(pointer, left, assumptions)
                        }
                    }
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
            Self::LocalLifetimeEndedOfOtherBlock => matches!(
                derivation,
                CMemoryDerivation::LocalLifetimeEnded { block, .. }
                    if pointer.block != *block
                        && pointers_proven_distinct_for_memory_resolution(
                            &Pointer {
                                block: block.clone(),
                                offset: PointerOffsetTerm::Constant(0),
                            },
                            pointer,
                            assumptions,
                        )
            ),
            Self::HeapFreeOfDistinctBlock => matches!(
                derivation,
                CMemoryDerivation::HeapFreed {
                    allocation_base, ..
                }
                | CMemoryDerivation::ContractAllocationRetired {
                    allocation_base, ..
                } if allocation_base.blocks_proven_distinct(pointer)
            ),
            Self::RetirementInsideItsCallHavoc => retirement_inside_its_call_havoc(derivation),
            Self::CallHavocRanges { ranges } => {
                let CMemoryDerivation::CallHavoc { mutable_ranges, .. } = derivation else {
                    return false;
                };
                ranges.len() == mutable_ranges.len()
                    && ranges.iter().zip(mutable_ranges).all(|(evidence, range)| {
                        evidence.checks(range, pointer, bytes, assumptions)
                    })
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
                    && ranges.iter().zip(mutable_ranges).all(|(evidence, range)| {
                        evidence.checks(range, pointer, bytes, assumptions)
                    })
            }
            Self::AssumptionDependent(_) => false,
        }
    }
}

impl PositiveTermEvidence {
    pub(in crate::kernel) fn for_term(
        term: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
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
    /// `bytes` is the access width being checked, and it must be the one the
    /// producer judged: a route that only clears one element is not a proof
    /// about a wider access.
    pub(in crate::kernel) fn checks(
        &self,
        range: &CMemoryRange,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::DistinctBlocks => range.base.blocks_proven_distinct(pointer),
            Self::ExactSeparationFact(fact) => {
                assumptions.prop_facts.contains(fact)
                    && exact_separation_fact_covers_range_and_pointer(
                        fact,
                        range,
                        pointer,
                        assumptions,
                    )
            }
            Self::DirectConstantOutside {
                index,
                bytes: judged_bytes,
                start,
                end,
            } => {
                // Re-derive in the range's own element unit, exactly as the
                // producer did: checking this in a different unit is how
                // smart execution and certificate checking would drift apart
                // while both looked healthy. The recorded width must also be
                // the one being checked, or the certificate is a proof about
                // some other access.
                let element_width = range.element_width();
                *judged_bytes == bytes
                    && direct_constant_element_index(pointer, range.base(), element_width)
                        == Some(*index)
                    && signed_bitvector_constant(range.start()) == Some(*start)
                    && signed_bitvector_constant(range.end()) == Some(*end)
                    && access_element_span(bytes, element_width).is_some_and(|span| {
                        index.checked_add(span).is_some_and(|last| last <= *start) || *end <= *index
                    })
            }
            Self::ForwardOffset { offset, positive } => {
                bytes <= range.element_width()
                    && forward_range_offset_from_pointer(range, pointer) == Some(offset.clone())
                    && positive.checks(
                        &Bitvector32Term::add(offset.clone(), range.start.clone()),
                        assumptions,
                    )
            }
        }
    }
}

impl MemoryDagCell {
    pub(in crate::kernel) fn node(&self) -> &SharedCMemory {
        match self {
            Self::Stored { node, .. } | Self::Unwritten { node, .. } => node,
        }
    }

    /// The concrete value the lookup pins down, when it pins one down.
    pub(in crate::kernel) fn resolved_value(&self, pointer: &Pointer) -> Option<CValue> {
        match self {
            Self::Stored { value, .. } => Some(value.clone()),
            Self::Unwritten { node, .. } => node.known_value(pointer),
        }
    }

    pub(in crate::kernel) fn checks_walk_from(
        &self,
        memory: &SharedCMemory,
        pointer: &Pointer,
        bytes: u32,
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
                    .checks(hop.derivation.as_ref(), pointer, bytes, assumptions)
            {
                return false;
            }
            current = hop.derivation.base().clone();
        }
        &current == self.node()
    }

    pub(in crate::kernel) fn has_only_typed_hops(&self) -> bool {
        match self {
            Self::Stored { path, .. } | Self::Unwritten { path, .. } => {
                path.iter().all(|hop| hop.justification.is_typed())
            }
        }
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
    > = const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
}

pub(in crate::kernel) struct CellLookupGuard {
    key: ((u32, u32), Pointer),
}

impl CellLookupGuard {
    pub(in crate::kernel) fn enter(memory: &SharedCMemory, pointer: &Pointer) -> Option<Self> {
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

/// True outside any memory-DAG cell lookup. Answers computed inside a
/// lookup may have met an in-progress cell and are weaker than a top-level
/// answer, so they must not be memoized under a lookup-free key.
pub(in crate::kernel) fn memory_dag_cell_lookup_depth_is_zero() -> bool {
    CELL_LOOKUPS_IN_PROGRESS.with(|lookups| lookups.borrow().is_empty())
}

/// A fingerprint of the memory-DAG cell lookups in progress: a nested
/// answer is a function of this set (a lookup of an in-progress cell has no
/// answer), so a memo that remembers nested answers keys them by it. Work is
/// the set's size, the lookup nesting depth.
pub(in crate::kernel) fn memory_dag_cell_lookups_fingerprint() -> u64 {
    use std::hash::{Hash, Hasher};
    CELL_LOOKUPS_IN_PROGRESS.with(|lookups| {
        let lookups = lookups.borrow();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        lookups.len().hash(&mut hasher);
        for lookup in lookups.iter() {
            crate::instrumentation::record_deterministic_work(1);
            lookup.hash(&mut hasher);
        }
        hasher.finish()
    })
}

impl RangeBoundEvidence {
    fn for_true_condition(
        condition: &ConditionTerm,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if condition == &ConditionTerm::Constant(true) {
            return Some(Self::Intrinsic);
        }
        let (left, right, strict) = condition_as_order_fact(condition, true)?;
        if let Some(step) = assumptions.exact_direct_order_step(&left, &right, strict) {
            return Some(Self::SignedOrderPath(vec![step]));
        }
        if strict {
            let successor = assumptions.signed_order_bound_entries(&left).find_map(
                |(fact_endpoint, successor, strict, forward)| {
                    if !strict || !forward || fact_endpoint != left {
                        return None;
                    }
                    let successor_base = successor.add_const_base(1)?;
                    let to_successor =
                        assumptions.exact_direct_order_step(&fact_endpoint, &successor, true)?;
                    let successor_base_to_upper = assumptions
                        .exact_direct_order_step(&successor_base, &right, true)
                        .map(|step| vec![step])
                        .or_else(|| {
                            assumptions.exact_signed_order_path_evidence(
                                &successor_base,
                                &right,
                                true,
                            )
                        })?;
                    Some(Self::StrictUpperViaSuccessor {
                        to_successor,
                        successor_base_to_upper,
                    })
                },
            );
            if successor.is_some() {
                return successor;
            }
        }
        assumptions
            .exact_signed_order_path_evidence(&left, &right, strict)
            .map(Self::SignedOrderPath)
    }

    fn checks(&self, condition: &ConditionTerm, assumptions: &PureFactContext) -> bool {
        match self {
            Self::Intrinsic => condition == &ConditionTerm::Constant(true),
            Self::SignedOrderPath(path) => {
                condition_as_order_fact(condition, true).is_some_and(|(left, right, strict)| {
                    assumptions.checks_exact_signed_order_path(path, &left, &right, strict)
                })
            }
            Self::StrictUpperViaSuccessor {
                to_successor,
                successor_base_to_upper,
            } => {
                let ConditionTerm::Bitvector32SignedLessThan(left, right) = condition else {
                    return false;
                };
                if to_successor.lower != **left || !to_successor.strict {
                    return false;
                }
                let Some(successor_base) = to_successor.upper.add_const_base(1) else {
                    return false;
                };
                assumptions.checks_exact_order_step(to_successor)
                    && assumptions.checks_exact_signed_order_path(
                        successor_base_to_upper,
                        &successor_base,
                        right,
                        true,
                    )
            }
        }
    }
}

impl PointerInRangeEvidence {
    pub(in crate::kernel) fn for_pointer(
        pointer: &Pointer,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
            pointer,
            range,
            assumptions,
        ) {
            return Some(Self::Shallow);
        }
        let index =
            pointer.element_index_from_base_with_width(range.base(), range.element_width())?;
        let lower_condition =
            ConditionTerm::signed_less_equal(range.start().clone(), index.clone());
        let upper_condition = ConditionTerm::signed_less_than(index.clone(), range.end().clone());
        Some(Self::Indexed {
            index,
            lower: RangeBoundEvidence::for_true_condition(&lower_condition, assumptions)?,
            upper: RangeBoundEvidence::for_true_condition(&upper_condition, assumptions)?,
        })
    }

    fn checks(
        &self,
        pointer: &Pointer,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> bool {
        let Self::Indexed {
            index: retained_index,
            lower,
            upper,
        } = self
        else {
            return crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
                pointer,
                range,
                assumptions,
            );
        };
        let Some(index) =
            pointer.element_index_from_base_with_width(range.base(), range.element_width())
        else {
            return false;
        };
        if index != *retained_index {
            return false;
        }
        lower.checks(
            &ConditionTerm::signed_less_equal(range.start().clone(), index.clone()),
            assumptions,
        ) && upper.checks(
            &ConditionTerm::signed_less_than(index, range.end().clone()),
            assumptions,
        )
    }
}

/// Whether `step` retires an allocation that the call retiring it had
/// already put inside its own write set: the edge is a
/// `ContractAllocationRetired` whose base, past any other retirements the
/// same call recorded, is a `CallHavoc` with a mutable range that covers every
/// byte of the allocation by structure.
///
/// Such an edge is transparent to a cell's value. It writes no byte; the only
/// reason a retirement ever stops a cell is that the callee may have freed the
/// allocation and let a later owner reuse its addresses, so a load after the
/// edge must not be named by a value from *before the call*. A byte of this
/// allocation cannot reach one: the havoc just below is inside the same call,
/// every such byte lies in one of its ranges, and a walk crosses a havoc only
/// on a proof that the cell misses every range. So the walk stops at the havoc
/// at the latest, and the name it gives is the call's post-call value, which is
/// exactly what the load reads. A byte outside the allocation is untouched by
/// the retirement in the first place.
///
/// Coverage is structural and assumption-free (the range starts at the
/// allocation's base pointer, and its byte count is the allocation's size or a
/// constant at least as large), so the answer is a property of the recorded
/// edges alone and may serve the naming walk. The work is one unit per edge
/// looked through, bounded by the retirements of one call.
pub(in crate::kernel) fn retirement_inside_its_call_havoc(step: &CMemoryDerivation) -> bool {
    let CMemoryDerivation::ContractAllocationRetired {
        base,
        allocation_base,
        bytes,
    } = step
    else {
        return false;
    };
    retired_allocation_inside_call_havoc(base, allocation_base, bytes)
}

/// Whether a retirement of `allocation_base[0..bytes]` taken from `base` may
/// keep `base`'s forget mark rather than marking itself forgotten from
/// `base` ([`CMemory::mark_forgotten_from`]).
///
/// The mark exists so a snapshot that dropped knowledge cannot re-intern as
/// the one it forgot from, or as anything older. A retirement inside its
/// call's havoc ([`retirement_inside_its_call_havoc`]) is, for every cell
/// value, the same memory as that havoc's snapshot: the dropped cells of the
/// allocation hold the havoc's post-call values, and the other dropped cells
/// are untouched. Keeping the havoc's mark is what makes the
/// content-addressed load names (the projections
/// `canonical_memory_for_pointer_load` interns, which carry the mark) agree
/// with the memory-DAG walk, which crosses such a retirement to the havoc.
///
/// Re-interning is still ruled out. The result carries the havoc's marker
/// block, whose identity is the call's fresh variable, so it cannot equal any
/// snapshot from before the call. It can equal the havoc snapshot itself only
/// when the retirement dropped nothing, and then the dropped edge lost
/// nothing either: the havoc, the next edge down, stops every cell and every
/// block question the retirement would have stopped for this allocation.
pub(in crate::kernel) fn retirement_keeps_its_call_havocs_forget_mark(
    base: &SharedCMemory,
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    retired_allocation_inside_call_havoc(base, allocation_base, bytes)
}

fn retired_allocation_inside_call_havoc(
    base: &SharedCMemory,
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    let mut current = base.clone();
    loop {
        crate::instrumentation::record_deterministic_work(1);
        let Some(derivation) = current.derivation() else {
            return false;
        };
        match derivation.as_ref() {
            CMemoryDerivation::ContractAllocationRetired { base, .. } => current = base.clone(),
            CMemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                return mutable_ranges.iter().any(|range| {
                    range_structurally_covers_allocation(range, allocation_base, bytes)
                });
            }
            _ => return false,
        }
    }
}

fn range_structurally_covers_allocation(
    range: &CMemoryRange,
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    if range.base() != allocation_base || range.start() != &Bitvector32Term::Constant(0) {
        return false;
    }
    let covered = memory_range_byte_count(
        range.start().clone(),
        range.end().clone(),
        range.element_width(),
    );
    if &covered == bytes {
        return true;
    }
    // Both extents constant: the range covers the allocation when it spans at
    // least as many bytes. A count that does not fit a non-negative `i32` is
    // not read as an extent.
    match (
        signed_bitvector_constant(&covered),
        signed_bitvector_constant(bytes),
    ) {
        (Some(covered), Some(bytes)) => bytes >= 0 && covered >= bytes,
        _ => false,
    }
}

pub(in crate::kernel) fn memory_dag_cell_source(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
) -> Option<MemoryDagCell> {
    memory_dag_cell_source_with_stop(memory, pointer, bytes, assumptions, cross_loop_havoc)
        .map(|(cell, _)| cell)
}

/// [`memory_dag_cell_source`] with the reason the walk stopped, for the one
/// caller that asks the history whether two loads can be one value at all.
/// It is the same single traversal; only the second half of its answer is
/// kept.
pub(in crate::kernel) fn memory_dag_cell_source_with_stop(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
) -> Option<(MemoryDagCell, CellWalkStop)> {
    // A lookup of a cell already being looked up is a cycle and has no
    // answer; see `CELL_LOOKUPS_IN_PROGRESS`.
    let _lookup = CellLookupGuard::enter(memory, pointer)?;
    Some(memory_dag_cell_source_walk(
        memory,
        pointer,
        bytes,
        assumptions,
        cross_loop_havoc,
    ))
}

fn memory_dag_cell_source_walk(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
) -> (MemoryDagCell, CellWalkStop) {
    let evidence = super::step_effect::Evidence {
        assumptions,
        cross_loop_havoc,
    };
    let mut current = memory.clone();
    let mut path = Vec::new();
    // The walk ends at a snapshot with no derivation: ids strictly
    // decrease along `base`, so every chain is finite.
    loop {
        // Each hop is one unit of deterministic work, so a scaling
        // regression sees a walk that grows with the proof.
        crate::instrumentation::record_deterministic_work(1);
        let Some(derivation) = current.derivation() else {
            return (
                MemoryDagCell::Unwritten {
                    node: current,
                    path,
                },
                CellWalkStop::OldestRecorded,
            );
        };
        // One rule decides every step for every resource; this walk's part is
        // to keep the hop it justified, and to read the written value off the
        // edge when the step turns out to be the write itself.
        let justification = match super::step_effect::affects(
            derivation.as_ref(),
            &current,
            super::Resource::Cell { pointer, bytes },
            &evidence,
        ) {
            super::step_effect::StepEffect::Affected => {
                if let CMemoryDerivation::Store { value, .. } = derivation.as_ref() {
                    return (
                        MemoryDagCell::Stored {
                            node: current,
                            value: value.clone(),
                            path,
                        },
                        CellWalkStop::Affected,
                    );
                }
                return (
                    MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    },
                    CellWalkStop::Affected,
                );
            }
            super::step_effect::StepEffect::NotShownSeparate(_) => {
                return (
                    MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    },
                    CellWalkStop::NotShownSeparate,
                );
            }
            super::step_effect::StepEffect::Separate(super::step_effect::Separation::Cell(
                justification,
            )) => justification,
            // Another resource's separation cannot be the answer to a cell
            // question, and if one ever were, stopping is the fail-closed
            // reading.
            super::step_effect::StepEffect::Separate(
                super::step_effect::Separation::Block(_)
                | super::step_effect::Separation::Footprint(_),
            ) => {
                return (
                    MemoryDagCell::Unwritten {
                        node: current,
                        path,
                    },
                    CellWalkStop::NotShownSeparate,
                );
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
