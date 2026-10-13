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
    /// one and whose value is exactly as wide as the read, so the load reads
    /// `value` ([`write_supplies_read`]). A store that only *reaches* the
    /// read's bytes — part of them, or more than them — stops the walk as
    /// [`Self::Unwritten`] at the node it produced: no extraction rule turns
    /// its value into the bytes the read returns.
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
    /// The store's full address equals `write` in this checking context;
    /// exact byte geometry at that spelling misses the complete read.
    StoreAliasedByteSeparation {
        write: Pointer,
    },
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
        write_membership: AccessInRangeEvidence,
        load_membership: AccessInRangeEvidence,
    },
    IntrinsicNoWrite,
    AllocationOfOtherBlock,
    LocalLifetimeEndedOfOtherBlock,
    /// The complete retired automatic object and this read occupy separate
    /// ranges, with the exact authority and memberships retained for checking.
    LocalLifetimeEndedSeparatedRanges {
        authority: StoreSeparatedRangesAuthority,
        left: CMemoryRange,
        right: CMemoryRange,
        orientation: StoreSeparatedRangeOrientation,
        write_membership: AccessInRangeEvidence,
        load_membership: AccessInRangeEvidence,
    },
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
    CallHavocKeptRange {
        range: CMemoryRange,
        first: PointerInRangeEvidence,
        last: PointerInRangeEvidence,
    },
    JoinReadAgreement {
        arms: Vec<(MemoryDagCell, MemoryDagCell)>,
    },
    LoopHavocRanges {
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    /// A `CellsSeeded` edge crossed: one justification per store it stands
    /// for, newest first ([`CMemoryDerivation::seeded_stores`]).
    SeededStores {
        hops: Vec<MemoryDagHopJustification>,
    },
    /// A `CellsSeeded` edge crossed because its run's block is proven
    /// distinct from the cell's: every one of its stores is.
    SeededStoresDistinctBlock,
    /// The run caches byte-preserving scalar loads of its immediate base.
    SeededLoadsOfBase,
    /// A `CellsSeeded` edge crossed because the cell has the run base's atoms
    /// and a constant shift whose bytes meet no store of the run: each store
    /// is at an unequal constant shift with a gap its bytes clear.
    SeededStoresMissedByShift,
    AssumptionDependent(MemoryDagAssumptionKind),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum MemoryDagAssumptionKind {
    StoreCommonBaseDistinctness,
    StoreGeneralDistinctness,
    HeapFreeResourceSeparation,
    /// A cell held by memory the caller kept owning across the call
    /// (`CMemoryDerivation::CallHavoc::kept_by_caller`).
    CallHavocKeptByCaller,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum StoreSeparatedRangesAuthority {
    ExactProposition(Proposition),
    ResourceComposition(ResourceContext),
    BorrowPartition(ResourceContext),
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
    /// One spelling at the selected range's base, justified by the current
    /// maintained graph. Checking never searches other aliases or history.
    GraphAlias {
        alias: Pointer,
        membership: Box<PointerInRangeEvidence>,
    },
    ExactAlias {
        alias: Pointer,
        condition: ConditionTerm,
        membership: Box<PointerInRangeEvidence>,
    },
    ShiftedExactAlias {
        base: Pointer,
        alias: Pointer,
        bytes: u32,
        membership: Box<PointerInRangeEvidence>,
    },
    /// An indexed access whose additive base is equal to the selected range's
    /// base, including loads from snapshots joined by checked memory history.
    /// The displacement is exact pointer arithmetic, not a modular index sum.
    EquivalentBase {
        base: Pointer,
        displacement: PointerOffsetTerm,
        membership: Box<PointerInRangeEvidence>,
    },
    /// Existing structural constant/affine membership. Retaining this cheap
    /// form keeps ordinary store edges out of the symbolic bound producer.
    Shallow,
    /// An exact signed delta against relative endpoints. Re-derivation
    /// checks the delta's non-wrap requirements before affine membership.
    ExactRelative { delta: ExactElementDelta },
    Indexed {
        index: Bitvector32Term,
        lower: RangeBoundEvidence,
        upper: RangeBoundEvidence,
    },
}

/// A complete access stays in one range when its first and last addressed
/// elements are in that range. Both memberships retain their own premises.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct AccessInRangeEvidence {
    first: PointerInRangeEvidence,
    last: Option<PointerInRangeEvidence>,
}

impl AccessInRangeEvidence {
    pub(in crate::kernel) fn for_access(
        pointer: &Pointer,
        bytes: u32,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let last_offset = Self::last_offset(bytes, range)?;
        Some(Self {
            first: PointerInRangeEvidence::for_pointer(pointer, range, assumptions)?,
            last: if last_offset == 0 {
                None
            } else {
                Some(PointerInRangeEvidence::for_pointer(
                    &pointer.offset_by_bytes(last_offset),
                    range,
                    assumptions,
                )?)
            },
        })
    }

    fn last_offset(bytes: u32, range: &CMemoryRange) -> Option<u32> {
        let width = range.element_width();
        (bytes != 0 && width != 0).then(|| ((bytes - 1) / width) * width)
    }

    fn checks(
        &self,
        pointer: &Pointer,
        bytes: u32,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(last_offset) = Self::last_offset(bytes, range) else {
            return false;
        };
        self.first.checks(pointer, range, assumptions)
            && match (last_offset, &self.last) {
                (0, None) => true,
                (offset, Some(last)) if offset != 0 => {
                    last.checks(&pointer.offset_by_bytes(offset), range, assumptions)
                }
                _ => false,
            }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum RangeBoundEvidence {
    Intrinsic,
    PinnedConstants(Box<PinnedRangeBound>),
    SignedOrderPath(Vec<SignedOrderDerivationStep>),
    EndpointEdge(SignedOrderDerivationStep),
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
    SeparatedRanges {
        authority: StoreSeparatedRangesAuthority,
        range_member: CMemoryRange,
        access_member: CMemoryRange,
        range_membership: RangeInRangeEvidence,
        membership: AccessInRangeEvidence,
    },
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
    /// An exact element delta at or after the nonwrapping range end. The
    /// access may be wider than one element because every byte goes forward.
    AfterEnd {
        delta: ExactElementDelta,
        start_nonnegative: RangeBoundEvidence,
        ordered_end: RangeBoundEvidence,
        after_end: RangeBoundEvidence,
    },
    ForwardOffset {
        offset: Bitvector32Term,
        positive: PositiveTermEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum RangeInRangeEvidence {
    ExactArithmetic,
    OrderedSameBase {
        bounds: [RangeBoundEvidence; 4],
        parent_extent_guard: Option<Proposition>,
    },
    BoundedAccess(AccessInRangeEvidence),
}

impl RangeInRangeEvidence {
    fn ordered_parent_extent_guard(parent: &CMemoryRange) -> Option<Option<Proposition>> {
        match memory_range_byte_count_extent(
            parent.start().clone(),
            parent.end().clone(),
            parent.element_width(),
        ) {
            MemoryRangeExtent::ConstantValid => Some(None),
            MemoryRangeExtent::ConstantInvalid { .. } => None,
            MemoryRangeExtent::Guards(guards) => {
                // The ordered subset bounds establish the forward condition.
                // Retain the separate byte-fit premise to exclude scaled wrap.
                let [_, fits]: [Proposition; 2] = guards.try_into().ok()?;
                Some(Some(fits))
            }
        }
    }

    fn ordered_conditions(
        range: &CMemoryRange,
        parent: &CMemoryRange,
    ) -> Option<[ConditionTerm; 4]> {
        if range.base() != parent.base()
            || range.element_width() == 0
            || range.element_width() != parent.element_width()
            || range.int32_bounds().is_none()
            || parent.int32_bounds().is_none()
        {
            return None;
        }
        Some([
            ConditionTerm::signed_less_equal(0u32.into(), parent.start().clone()),
            ConditionTerm::signed_less_equal(parent.start().clone(), range.start().clone()),
            ConditionTerm::signed_less_equal(range.start().clone(), range.end().clone()),
            ConditionTerm::signed_less_equal(range.end().clone(), parent.end().clone()),
        ])
    }

    fn for_ordered_range(
        range: &CMemoryRange,
        parent: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let [nonnegative, starts_inside, ordered, ends_inside] =
            Self::ordered_conditions(range, parent)?.map(|condition| {
                RangeBoundEvidence::for_selected_condition(&condition, assumptions)
            });
        let bounds = [nonnegative?, starts_inside?, ordered?, ends_inside?];
        let parent_extent_guard = Self::ordered_parent_extent_guard(parent)?;
        if let Some(guard) = &parent_extent_guard {
            if !assumptions.contains_assumed_exact(guard) {
                return None;
            }
            if crate::kernel::assumptions::implicit_reasoning_provenance_capturing() {
                crate::kernel::record_implicit_reasoning_provenance(assumptions, guard);
            }
        }
        for bound in &bounds {
            bound.record_provenance(assumptions);
        }
        Some(Self::OrderedSameBase {
            bounds,
            parent_extent_guard,
        })
    }

    fn bounded_access(range: &CMemoryRange) -> Option<(Pointer, u32)> {
        range.int32_bounds()?;
        // This fallback covers a concrete write footprint. A modular affine
        // endpoint difference alone does not establish an ordered extent.
        let start = range.signed_constant_start()?;
        let end = range.signed_constant_end()?;
        let count = end.checked_sub(start)?;
        let bytes = u32::try_from(count)
            .ok()?
            .checked_mul(range.element_width())?;
        (bytes != 0).then(|| {
            (
                range
                    .base()
                    .offset_by_elements(range.start().clone(), range.element_width()),
                bytes,
            )
        })
    }

    pub(in crate::kernel) fn for_range(
        range: &CMemoryRange,
        parent: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
            range,
            parent,
            assumptions,
        ) {
            return Some(Self::ExactArithmetic);
        }
        if let Some(proof) = Self::for_ordered_range(range, parent, assumptions) {
            return Some(proof);
        }
        let (first, bytes) = Self::bounded_access(range)?;
        AccessInRangeEvidence::for_access(&first, bytes, parent, assumptions)
            .map(Self::BoundedAccess)
    }

    fn checks(
        &self,
        range: &CMemoryRange,
        parent: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::ExactArithmetic => {
                crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                    range,
                    parent,
                    assumptions,
                )
            }
            Self::OrderedSameBase {
                bounds,
                parent_extent_guard,
            } => {
                Self::ordered_conditions(range, parent).is_some_and(|conditions| {
                    bounds
                        .iter()
                        .zip(conditions)
                        .all(|(bound, condition)| bound.checks(&condition, assumptions))
                }) && Self::ordered_parent_extent_guard(parent).is_some_and(|expected| {
                    &expected == parent_extent_guard
                        && expected
                            .as_ref()
                            .is_none_or(|guard| assumptions.contains_assumed_exact(guard))
                })
            }
            Self::BoundedAccess(membership) => {
                Self::bounded_access(range).is_some_and(|(first, bytes)| {
                    membership.checks(&first, bytes, parent, assumptions)
                })
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PositiveTermEvidence {
    Constant,
    ExactCondition(ConditionTerm),
    OneLowerBound(ConditionTerm),
}

impl MemoryDagHopJustification {
    pub(in crate::kernel) fn is_typed(&self) -> bool {
        match self {
            Self::AssumptionDependent(_) => false,
            Self::SeededStores { hops } => hops.iter().all(Self::is_typed),
            Self::JoinReadAgreement { arms } => arms
                .iter()
                .all(|(left, right)| left.has_only_typed_hops() && right.has_only_typed_hops()),
            _ => true,
        }
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
            Self::StoreAliasedByteSeparation { write: aligned } => {
                let CMemoryDerivation::Store {
                    pointer: write,
                    value,
                    ..
                } = derivation
                else {
                    return false;
                };
                !write.blocks_proven_distinct(aligned)
                    && assumptions.pointers_known_equal(write, aligned)
                    && crate::kernel::reasoning::exact_access_byte_overlap(
                        aligned,
                        value.byte_width(),
                        pointer,
                        bytes,
                    ) == Some(crate::kernel::reasoning::AccessByteOverlap::Separate)
            }
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
            }
            | Self::LocalLifetimeEndedSeparatedRanges {
                authority,
                left,
                right,
                orientation,
                write_membership,
                load_membership,
            } => {
                let retired;
                let (write, write_bytes) = match (self, derivation) {
                    (
                        Self::StoreSeparatedRanges { .. },
                        CMemoryDerivation::Store { pointer, value, .. },
                    ) => (pointer, value.byte_width()),
                    (
                        Self::LocalLifetimeEndedSeparatedRanges { .. },
                        CMemoryDerivation::LocalLifetimeEnded { base, block },
                    ) => {
                        if !block.starts_with("local:") || pointer.block == *block {
                            return false;
                        }
                        let Some(extent) = base.block_size(block).and_then(|size| size.as_const())
                        else {
                            return false;
                        };
                        retired = Pointer {
                            block: block.clone(),
                            offset: PointerOffsetTerm::Constant(0),
                        };
                        (&retired, extent)
                    }
                    _ => return false,
                };
                let authority_checks = match authority {
                    StoreSeparatedRangesAuthority::ExactProposition(proposition) => {
                        assumptions.prop_facts.contains(proposition)
                            && proposition.memory_separation().is_some_and(
                                |(fact_left, fact_right)| fact_left == left && fact_right == right,
                            )
                    }
                    StoreSeparatedRangesAuthority::BorrowPartition(resources) => {
                        assumptions.resource_compositions.contains(resources)
                            && resources.proves_borrow_partition_separate(left, right)
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
                            write_membership.checks(write, write_bytes, left, assumptions)
                                && load_membership.checks(pointer, bytes, right, assumptions)
                        }
                        StoreSeparatedRangeOrientation::WriteRightLoadLeft => {
                            write_membership.checks(write, write_bytes, right, assumptions)
                                && load_membership.checks(pointer, bytes, left, assumptions)
                        }
                    }
            }
            Self::IntrinsicNoWrite => matches!(
                derivation,
                CMemoryDerivation::BlockDeclared { .. }
                    | CMemoryDerivation::HeapAllocationPending { .. }
                    | CMemoryDerivation::HeapAllocationFailed { .. }
                    | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
                    | CMemoryDerivation::ObjectInitializationRecorded { .. }
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
                        && pointers_in_distinct_objects_for_memory_resolution(
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
            Self::CallHavocKeptRange { range, first, last } => {
                let CMemoryDerivation::CallHavoc {
                    kept_by_caller: Some(kept),
                    ..
                } = derivation
                else {
                    return false;
                };
                let width = range.element_width();
                width != 0
                    && bytes != 0
                    && bytes.is_multiple_of(width)
                    && kept.contains_range(range)
                    && first.checks(pointer, range, assumptions)
                    && last.checks(
                        &pointer.offset_by_elements(
                            Bitvector32Term::Constant(bytes / width - 1),
                            width,
                        ),
                        range,
                        assumptions,
                    )
            }
            Self::JoinReadAgreement { arms } => {
                let CMemoryDerivation::BranchJoin { base, incoming } = derivation else {
                    return false;
                };
                arms.len() == incoming.len()
                    && arms.iter().zip(incoming).all(|((left, right), memory)| {
                        left.node() == right.node()
                            && left.checks_walk_from(base, pointer, bytes, assumptions)
                            && right.checks_walk_from(memory, pointer, bytes, assumptions)
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
            Self::SeededLoadsOfBase => super::step_effect::seeded_loads_preserve_base(derivation),
            Self::SeededStoresDistinctBlock => matches!(
                derivation,
                CMemoryDerivation::CellsSeeded { run, .. }
                    if run.base().blocks_proven_distinct(pointer)
            ),
            Self::SeededStoresMissedByShift => {
                let CMemoryDerivation::CellsSeeded { run, .. } = derivation else {
                    return false;
                };
                let crate::kernel::reasoning::memory_resolution::RunAccess::Shift(shift) =
                    crate::kernel::reasoning::memory_resolution::run_access(run, pointer)
                else {
                    return false;
                };
                let (low, high) = crate::kernel::reasoning::memory_resolution::run_elements_meeting(
                    run,
                    shift,
                    i64::from(bytes),
                );
                (low..high).all(|index| run.holes().contains(index))
            }
            Self::SeededStores { hops } => {
                let Some(stores) = derivation.seeded_stores() else {
                    return false;
                };
                hops.len() == stores.len()
                    && hops.iter().zip(stores).all(|(hop, (write, value))| {
                        hop.checks(
                            &CMemoryDerivation::Store {
                                base: derivation.base().clone(),
                                pointer: write,
                                value,
                            },
                            pointer,
                            bytes,
                            assumptions,
                        )
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
    pub(in crate::kernel) fn for_after_end(
        range: &CMemoryRange,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if bytes == 0 || range.int32_bounds().is_none() {
            return None;
        }
        let delta = pointer.exact_element_delta_from_base(
            range.base(),
            range.element_width(),
            Some(assumptions),
        )?;
        let index = delta.as_index_term()?;
        let proof = Self::AfterEnd {
            delta,
            start_nonnegative: RangeBoundEvidence::for_selected_condition(
                &ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    range.start().clone(),
                ),
                assumptions,
            )?,
            ordered_end: RangeBoundEvidence::for_selected_condition(
                &ConditionTerm::signed_less_equal(range.start().clone(), range.end().clone()),
                assumptions,
            )?,
            after_end: RangeBoundEvidence::for_selected_condition(
                &ConditionTerm::signed_less_equal(range.end().clone(), index),
                assumptions,
            )?,
        };
        if let Self::AfterEnd {
            start_nonnegative,
            ordered_end,
            after_end,
            ..
        } = &proof
        {
            start_nonnegative.record_provenance(assumptions);
            ordered_end.record_provenance(assumptions);
            after_end.record_provenance(assumptions);
        }
        Some(proof)
    }

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
            Self::SeparatedRanges {
                authority,
                range_member,
                access_member,
                range_membership,
                membership,
            } => {
                let authority_checks = match authority {
                    StoreSeparatedRangesAuthority::ExactProposition(fact) => {
                        assumptions.prop_facts.contains(fact)
                            && fact.memory_separation().is_some_and(|(left, right)| {
                                left == range_member && right == access_member
                                    || right == range_member && left == access_member
                            })
                    }
                    StoreSeparatedRangesAuthority::ResourceComposition(resources) => {
                        assumptions.resource_compositions.contains(resources)
                            && resources.proves_owned_memory_ranges_separate_shallow(
                                range_member,
                                access_member,
                            )
                    }
                    StoreSeparatedRangesAuthority::BorrowPartition(resources) => {
                        assumptions.resource_compositions.contains(resources)
                            && resources
                                .proves_borrow_partition_separate(range_member, access_member)
                    }
                };
                authority_checks
                    && !assumptions
                        .memory_ranges_overlap_after_base_equality(range_member, access_member)
                    && range_membership.checks(range, range_member, assumptions)
                    && membership.checks(pointer, bytes, access_member, assumptions)
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
                    && range.signed_constant_start() == Some(*start)
                    && range.signed_constant_end() == Some(*end)
                    && access_element_span(bytes, element_width).is_some_and(|span| {
                        index.checked_add(span).is_some_and(|last| last <= *start) || *end <= *index
                    })
            }
            Self::ForwardOffset { offset, positive } => {
                range.int32_bounds().is_some()
                    && bytes <= range.element_width()
                    && forward_range_offset_from_pointer(range, pointer) == Some(offset.clone())
                    && positive.checks(
                        &Bitvector32Term::add(offset.clone(), range.start().clone()),
                        assumptions,
                    )
            }
            Self::AfterEnd {
                delta,
                start_nonnegative,
                ordered_end,
                after_end,
            } => {
                bytes != 0
                    && range.int32_bounds().is_some()
                    && pointer
                        .exact_element_delta_from_base(
                            range.base(),
                            range.element_width(),
                            Some(assumptions),
                        )
                        .as_ref()
                        == Some(delta)
                    && start_nonnegative.checks(
                        &ConditionTerm::signed_less_equal(
                            Bitvector32Term::Constant(0),
                            range.start().clone(),
                        ),
                        assumptions,
                    )
                    && ordered_end.checks(
                        &ConditionTerm::signed_less_equal(
                            range.start().clone(),
                            range.end().clone(),
                        ),
                        assumptions,
                    )
                    && delta.as_index_term().is_some_and(|index| {
                        after_end.checks(
                            &ConditionTerm::signed_less_equal(range.end().clone(), index),
                            assumptions,
                        )
                    })
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

    /// The concrete value the lookup pins down for a `kind` read at
    /// `pointer`, when it pins one down.
    ///
    /// A stored value starts at the read's address by construction
    /// ([`write_supplies_read`]); it, and a cell the stopping snapshot
    /// materialized at this exact address, answer only when the read of
    /// `kind` returns exactly that value ([`LoadKind::reads_value`]). A value
    /// of another width holds other bytes than the read returns, and one of
    /// the read's width but the other signedness is another number.
    pub(in crate::kernel) fn resolved_value(
        &self,
        pointer: &Pointer,
        kind: LoadKind,
    ) -> Option<CValue> {
        match self {
            Self::Stored { value, .. } => kind.read_cell(value),
            Self::Unwritten { node, .. } => kind.read_cell(&node.known_value(pointer)?),
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
    static CELL_LOOKUP_REFUSALS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many cell lookups have been refused because the same lookup was in
/// progress. The set of lookups in progress changes an answer only through
/// such a refusal, so an answer computed while this count stayed put is the
/// one any set of lookups in progress would allow, or stronger.
pub(in crate::kernel) fn memory_dag_cell_lookup_refusals() -> u64 {
    CELL_LOOKUP_REFUSALS.with(std::cell::Cell::get)
}

pub(in crate::kernel) struct CellLookupGuard {
    key: ((u32, u32), Pointer),
}

impl CellLookupGuard {
    pub(in crate::kernel) fn enter(memory: &SharedCMemory, pointer: &Pointer) -> Option<Self> {
        let key = (memory.arena_id(), pointer.clone());
        // `then`, not `then_some`: a guard built eagerly and discarded on
        // the cycle path would run `drop` and unregister the outer lookup.
        let entered =
            CELL_LOOKUPS_IN_PROGRESS.with(|lookups| lookups.borrow_mut().insert(key.clone()));
        if !entered {
            CELL_LOOKUP_REFUSALS.with(|refusals| refusals.set(refusals.get() + 1));
        }
        entered.then(|| Self { key })
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct PinnedRangeBound {
    left_value: i32,
    right_value: i32,
    left_equality: DirectBitvectorEqualityEvidence,
    right_equality: DirectBitvectorEqualityEvidence,
}

impl RangeBoundEvidence {
    // The retained proof is also the exact dependency list for transport
    // certificates. Checking with a captured context must keep its bounds.
    fn record_provenance(&self, assumptions: &PureFactContext) {
        if !crate::kernel::assumptions::implicit_reasoning_provenance_capturing() {
            return;
        }
        let record = |step: &SignedOrderDerivationStep| {
            crate::kernel::record_implicit_reasoning_provenance(assumptions, &step.premise);
        };
        match self {
            Self::Intrinsic => {}
            Self::PinnedConstants(bound) => {
                for equality in [&bound.left_equality, &bound.right_equality] {
                    for premise in equality.context_premises() {
                        crate::kernel::record_implicit_reasoning_provenance(assumptions, &premise);
                    }
                }
            }
            Self::EndpointEdge(step) => record(step),
            Self::SignedOrderPath(path) => path.iter().for_each(record),
            Self::StrictUpperViaSuccessor {
                to_successor,
                successor_base_to_upper,
            } => {
                record(to_successor);
                successor_base_to_upper.iter().for_each(record);
            }
        }
    }

    fn intrinsically_true(condition: &ConditionTerm) -> bool {
        condition == &ConditionTerm::Constant(true)
            || matches!(condition, ConditionTerm::Bitvector32SignedLessEqual(left, right) if left == right)
    }

    fn intrinsic_connection(from: &Bitvector32Term, to: &Bitvector32Term) -> Option<bool> {
        if from == to {
            Some(false)
        } else {
            signed_bitvector_constant(from)
                .zip(signed_bitvector_constant(to))
                .and_then(|(from, to)| (from <= to).then_some(from < to))
        }
    }

    // An endpoint-local route for hot framing queries. A selected order edge
    // may connect through constants, but no unrelated facts are enumerated.
    fn for_selected_condition(
        condition: &ConditionTerm,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if Self::intrinsically_true(condition) {
            return Some(Self::Intrinsic);
        }
        let (left, right, strict) = condition_as_order_fact(condition, true)?;
        if let Some(step) = assumptions.exact_direct_order_step(&left, &right, strict) {
            return Some(Self::SignedOrderPath(vec![step]));
        }
        if let Some(bound) = Self::pinned_constants(&left, &right, strict, assumptions) {
            return Some(bound);
        }
        assumptions
            .signed_order_bound_entries(&left)
            .chain(assumptions.signed_order_bound_entries(&right))
            .find_map(|(endpoint, other, edge_strict, forward)| {
                let (lower, upper) = if forward {
                    (endpoint, other)
                } else {
                    (other, endpoint)
                };
                let before = Self::intrinsic_connection(&left, &lower)?;
                let after = Self::intrinsic_connection(&upper, &right)?;
                if strict && !edge_strict && !before && !after {
                    return None;
                }
                assumptions
                    .exact_direct_order_step(&lower, &upper, edge_strict)
                    .map(Self::EndpointEdge)
            })
    }

    fn pinned_constants(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict: bool,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let pinned = |term: &Bitvector32Term| {
            let (value, equality) = if let Some(value) = signed_bitvector_constant(term) {
                (
                    value,
                    DirectBitvectorEqualityEvidence::EqualSignedConstants {
                        value,
                        left: SignedConstantEvidence::Constant,
                        right: SignedConstantEvidence::Constant,
                    },
                )
            } else {
                let Bitvector32Term::Variable(variable) = term else {
                    return None;
                };
                assumptions.singleton_constant_equality_evidence(*variable)?
            };
            Some((i32::try_from(value).ok()?, equality))
        };
        let (left_value, left_equality) = pinned(left)?;
        let (right_value, right_equality) = pinned(right)?;
        (if strict {
            left_value < right_value
        } else {
            left_value <= right_value
        })
        .then(|| {
            Self::PinnedConstants(Box::new(PinnedRangeBound {
                left_value,
                right_value,
                left_equality,
                right_equality,
            }))
        })
    }

    fn for_true_condition(
        condition: &ConditionTerm,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if let Some(selected) = Self::for_selected_condition(condition, assumptions) {
            return Some(selected);
        }
        let (left, right, strict) = condition_as_order_fact(condition, true)?;
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
            Self::Intrinsic => Self::intrinsically_true(condition),
            Self::PinnedConstants(bound) => {
                condition_as_order_fact(condition, true).is_some_and(|(left, right, strict)| {
                    (if strict {
                        bound.left_value < bound.right_value
                    } else {
                        bound.left_value <= bound.right_value
                    }) && bound.left_equality.checks(
                        &left,
                        &(bound.left_value as u32).into(),
                        assumptions,
                    ) && bound.right_equality.checks(
                        &right,
                        &(bound.right_value as u32).into(),
                        assumptions,
                    )
                })
            }
            Self::EndpointEdge(step) => {
                condition_as_order_fact(condition, true).is_some_and(|(left, right, strict)| {
                    Self::intrinsic_connection(&left, &step.lower)
                        .zip(Self::intrinsic_connection(&step.upper, &right))
                        .is_some_and(|(before, after)| {
                            (!strict || before || step.strict || after)
                                && assumptions.checks_exact_order_step(step)
                        })
                })
            }
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
        Self::for_pointer_direct(pointer, range, assumptions)
            .or_else(|| {
                assumptions
                    .exact_pointer_aliases(pointer)
                    .find_map(|alias| {
                        let membership = Self::for_pointer_direct(alias, range, assumptions)?;
                        let condition =
                            ConditionTerm::pointer_equal(pointer.clone(), alias.clone());
                        crate::kernel::record_implicit_reasoning_provenance(
                            assumptions,
                            &Proposition::ConditionIs(condition.clone(), true),
                        );
                        Some(Self::ExactAlias {
                            alias: alias.clone(),
                            condition,
                            membership: Box::new(membership),
                        })
                    })
            })
            .or_else(|| {
                assumptions
                    .exact_pointer_aliases(range.base())
                    .find_map(|base| {
                        let bytes = pointer
                            .element_index_from_base_with_width(base, 1)?
                            .as_const()?;
                        if *pointer != base.offset_by_bytes(bytes) {
                            return None;
                        }
                        let shifted = range.base().offset_by_bytes(bytes);
                        let membership = Self::for_pointer_direct(&shifted, range, assumptions)?;
                        crate::kernel::record_implicit_reasoning_provenance(
                            assumptions,
                            &Proposition::ConditionIs(
                                ConditionTerm::pointer_equal(base.clone(), range.base().clone()),
                                true,
                            ),
                        );
                        Some(Self::ShiftedExactAlias {
                            base: base.clone(),
                            alias: range.base().clone(),
                            bytes,
                            membership: Box::new(membership),
                        })
                    })
            })
            .or_else(|| {
                // A named-call read and its model identity can be joined
                // through a third pointer. Ask the graph for one spelling;
                // keep membership and full address equality as separate checks.
                let alias = assumptions.pointer_at_known_constant_base(pointer, range.base())?;
                let membership = Self::for_pointer_direct(&alias, range, assumptions)?;
                if pointer.blocks_proven_distinct(&alias)
                    || !assumptions.pointers_known_equal(pointer, &alias)
                {
                    return None;
                }
                Some(Self::GraphAlias {
                    alias,
                    membership: Box::new(membership),
                })
            })
            .or_else(|| Self::for_equivalent_base(pointer, range, assumptions))
    }

    fn for_equivalent_base(
        pointer: &Pointer,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if pointer.block != range.base().block {
            return None;
        }
        let PointerOffsetTerm::Add(left, right) = &pointer.offset else {
            return None;
        };
        [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ]
        .into_iter()
        .find_map(|(base_offset, displacement)| {
            let base = Pointer {
                block: pointer.block.clone(),
                offset: base_offset.clone(),
            };
            if base == *range.base() {
                return None;
            }
            let alias = Pointer {
                block: range.base().block.clone(),
                offset: PointerOffsetTerm::add(range.base().offset.clone(), displacement.clone()),
            };
            let membership = Self::for_pointer_direct(&alias, range, assumptions);
            let membership = membership?;
            // An equal base helps only when this displacement
            // supplies a checked member of the selected range.
            // Do not resolve load histories for failed members.
            if !pointers_proven_equal_for_memory_resolution(&base, range.base(), assumptions) {
                return None;
            }
            Some(Self::EquivalentBase {
                base,
                displacement: displacement.clone(),
                membership: Box::new(membership),
            })
        })
    }

    fn for_pointer_direct(
        pointer: &Pointer,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        // Try exact selected bounds before the broader shallow rule,
        // which may consult offset equality and memory history. The
        // exact delta refuses an index obtained only by modular folding.
        let delta = range
            .wide_bounds()
            .is_none()
            .then(|| {
                pointer.exact_element_delta_from_base(
                    range.base(),
                    range.element_width(),
                    Some(assumptions),
                )
            })
            .flatten();
        if let Some(index) = delta.as_ref().and_then(ExactElementDelta::as_index_term)
            && let (Some(lower), Some(upper)) = (
                RangeBoundEvidence::for_selected_condition(
                    &ConditionTerm::signed_less_equal(range.start().clone(), index.clone()),
                    assumptions,
                ),
                RangeBoundEvidence::for_selected_condition(
                    &ConditionTerm::signed_less_than(index.clone(), range.end().clone()),
                    assumptions,
                ),
            )
        {
            lower.record_provenance(assumptions);
            upper.record_provenance(assumptions);
            return Some(Self::Indexed {
                index,
                lower,
                upper,
            });
        }
        if let Some(delta) = delta
            && crate::kernel::assumptions::element_delta_in_range_by_affine_arithmetic(
                &delta,
                range.start(),
                range.end(),
                assumptions,
            )
        {
            return Some(Self::ExactRelative { delta });
        }
        if crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
            pointer,
            range,
            assumptions,
        ) {
            return Some(Self::Shallow);
        }
        if range.wide_bounds().is_some() {
            return None;
        }
        let index = pointer
            .exact_element_delta_from_base(range.base(), range.element_width(), Some(assumptions))?
            .as_index_term()?;
        let lower_condition =
            ConditionTerm::signed_less_equal(range.start().clone(), index.clone());
        let upper_condition = ConditionTerm::signed_less_than(index.clone(), range.end().clone());
        let lower = RangeBoundEvidence::for_true_condition(&lower_condition, assumptions);
        let upper = RangeBoundEvidence::for_true_condition(&upper_condition, assumptions);
        let lower = lower?;
        let upper = upper?;
        lower.record_provenance(assumptions);
        upper.record_provenance(assumptions);
        Some(Self::Indexed {
            lower,
            upper,
            index,
        })
    }

    pub(in crate::kernel) fn checks(
        &self,
        pointer: &Pointer,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> bool {
        if let Self::EquivalentBase {
            base,
            displacement,
            membership,
        } = self
        {
            let original = Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::add(base.offset.clone(), displacement.clone()),
            };
            let alias = Pointer {
                block: range.base().block.clone(),
                offset: PointerOffsetTerm::add(range.base().offset.clone(), displacement.clone()),
            };
            let reversed = Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::add(displacement.clone(), base.offset.clone()),
            };
            return (*pointer == original || *pointer == reversed)
                && base.block == range.base().block
                && pointers_proven_equal_for_memory_resolution(base, range.base(), assumptions)
                && matches!(
                    membership.as_ref(),
                    Self::Shallow | Self::ExactRelative { .. } | Self::Indexed { .. }
                )
                && membership.checks(&alias, range, assumptions);
        }
        if let Self::GraphAlias { alias, membership } = self {
            return !pointer.blocks_proven_distinct(alias)
                && assumptions.pointers_known_equal(pointer, alias)
                && matches!(
                    membership.as_ref(),
                    Self::Shallow | Self::ExactRelative { .. } | Self::Indexed { .. }
                )
                && membership.checks(alias, range, assumptions);
        }
        if let Self::ShiftedExactAlias {
            base,
            alias,
            bytes,
            membership,
        } = self
        {
            return *pointer == base.offset_by_bytes(*bytes)
                && assumptions.exact_condition_value(&ConditionTerm::pointer_equal(
                    base.clone(),
                    alias.clone(),
                )) == Some(true)
                && matches!(
                    membership.as_ref(),
                    Self::Shallow | Self::ExactRelative { .. } | Self::Indexed { .. }
                )
                && membership.checks(&alias.offset_by_bytes(*bytes), range, assumptions);
        }
        if let Self::ExactAlias {
            alias,
            condition,
            membership,
        } = self
        {
            return *condition == ConditionTerm::pointer_equal(pointer.clone(), alias.clone())
                && assumptions.exact_condition_value(condition) == Some(true)
                && matches!(
                    membership.as_ref(),
                    Self::Shallow | Self::ExactRelative { .. } | Self::Indexed { .. }
                )
                && membership.checks(alias, range, assumptions);
        }
        if let Self::ExactRelative { delta } = self {
            return range.wide_bounds().is_none()
                && pointer
                    .exact_element_delta_from_base(
                        range.base(),
                        range.element_width(),
                        Some(assumptions),
                    )
                    .as_ref()
                    == Some(delta)
                && crate::kernel::assumptions::element_delta_in_range_by_affine_arithmetic(
                    delta,
                    range.start(),
                    range.end(),
                    assumptions,
                );
        }
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
        // Signed indexed evidence cannot check a wide range.
        if range.int32_bounds().is_none() {
            return false;
        }
        let Some(index) = pointer
            .exact_element_delta_from_base(range.base(), range.element_width(), Some(assumptions))
            .and_then(|delta| delta.as_index_term())
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
    // This arithmetic rule uses signed 32-bit indices; wide ranges are undecided.
    if range.wide_bounds().is_some() {
        return false;
    }
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

/// Whether a write of `value` at `write` supplies exactly the value a
/// `bytes`-byte read at `pointer` returns: it starts at the read's address
/// and is exactly as wide.
///
/// This is the one check every route that reads a value off the recorded
/// history spends. A write the walk stops at only *reaches* the read when the
/// two share a byte, and that is how a two-byte store's value was once read
/// back as a four-byte load inside which it landed. The kernel has no rule
/// that extracts a narrower read from a wider write or assembles a wider read
/// from a narrower one, so anything other than an exact match pins nothing;
/// the read is then whatever the produced snapshot holds there.
///
/// The walk is asked about an access width, the recorded one at the read's
/// address, and this check decides on that width alone. The read's own kind,
/// which a load term carries, is the second half and is
/// [`MemoryDagCell::resolved_value`]'s: a write of the read's width but the
/// other signedness stops the walk here and supplies nothing, because an
/// `int8` value's term is sign-extended where a `uint8` read's is not.
pub(in crate::kernel) fn write_supplies_read(
    write: &Pointer,
    value: &CValue,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    value.byte_width() == bytes
        && (super::step_effect::write_is_at_read_address(write, pointer, assumptions)
            || write.block == pointer.block
                && crate::kernel::reasoning::memory_resolution::constant_byte_shift(write, pointer)
                    == Some(0))
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
        None,
    ))
}

/// A locally bounded read-value query. Reaching the limit preserves only the
/// stopping snapshot's own cell; it never assumes that an unchecked hop frames
/// the read. This prevents a simple normalization from scanning a whole path.
pub(in crate::kernel) fn memory_dag_cell_source_with_hop_limit(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    max_hops: usize,
) -> Option<MemoryDagCell> {
    let _lookup = CellLookupGuard::enter(memory, pointer)?;
    Some(memory_dag_cell_source_walk(memory, pointer, bytes, assumptions, true, Some(max_hops)).0)
}

fn memory_dag_cell_source_walk(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
    max_hops: Option<usize>,
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
        if max_hops.is_some_and(|limit| path.len() >= limit) {
            return (
                MemoryDagCell::Unwritten {
                    node: current,
                    path,
                },
                CellWalkStop::NotShownSeparate,
            );
        }
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
                let seeded = matches!(derivation.as_ref(), CMemoryDerivation::CellsSeeded { .. })
                    .then(|| {
                        super::step_effect::seeded_cell_effect(
                            derivation.as_ref(),
                            pointer,
                            bytes,
                            &evidence,
                        )
                    });
                let written = match (seeded, derivation.as_ref()) {
                    (Some(super::step_effect::SeededCellEffect::Written(write, value)), _) => {
                        Some((write, value))
                    }
                    (
                        None,
                        CMemoryDerivation::Store {
                            pointer: write,
                            value,
                            ..
                        },
                    ) => Some((write.clone(), value.clone())),
                    _ => None,
                };
                if let Some((write, value)) = written
                    && write_supplies_read(&write, &value, pointer, bytes, assumptions)
                {
                    return (
                        MemoryDagCell::Stored {
                            node: current,
                            value,
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

/// Compare just the two paths back to their nearest common snapshot. Arena
/// ids decrease on every edge, so walking the newer endpoint finds that
/// common ancestor without inspecting its history. Every hop carries the
/// same local typed certificate as an ordinary read-preservation query.
pub(super) fn join_read_agreement(
    base: &SharedCMemory,
    incoming: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    evidence: &super::step_effect::Evidence<'_>,
) -> Option<(MemoryDagCell, MemoryDagCell)> {
    let mut left = base.clone();
    let mut right = incoming.clone();
    let mut left_path = Vec::new();
    let mut right_path = Vec::new();
    while left != right {
        crate::instrumentation::record_deterministic_work(1);
        let (current, path) = if left.arena_id() > right.arena_id() {
            (&mut left, &mut left_path)
        } else {
            (&mut right, &mut right_path)
        };
        let _lookup = CellLookupGuard::enter(current, pointer)?;
        let derivation = current.derivation()?;
        let super::step_effect::StepEffect::Separate(super::step_effect::Separation::Cell(
            justification,
        )) = super::step_effect::affects(
            &derivation,
            current,
            super::Resource::Cell { pointer, bytes },
            evidence,
        )
        else {
            return None;
        };
        if !justification.is_typed() {
            return None;
        }
        path.push(MemoryDagHop {
            derived: current.clone(),
            derivation: derivation.clone(),
            justification,
        });
        *current = derivation.base().clone();
    }
    Some((
        MemoryDagCell::Unwritten {
            node: left,
            path: left_path,
        },
        MemoryDagCell::Unwritten {
            node: right,
            path: right_path,
        },
    ))
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // A signed certificate is not reusable against a native range, even when
    // its base and the low words of its bounds agree.
    #[test]
    fn wide_ranges_refuse_signed_allocation_and_index_certificates() {
        let base = Pointer::symbolic(Variable(984_300));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let facts = PureFactContext::new();
        assert!(!range_structurally_covers_allocation(
            &wide,
            &base,
            &Bitvector32Term::Constant(4)
        ));
        let indexed = PointerInRangeEvidence::Indexed {
            index: 0u32.into(),
            lower: RangeBoundEvidence::Intrinsic,
            upper: RangeBoundEvidence::Intrinsic,
        };
        assert!(!indexed.checks(&base, &wide, &facts));
        let forward = RangeDisjointFromPointerEvidence::ForwardOffset {
            offset: 1u32.into(),
            positive: PositiveTermEvidence::Constant,
        };
        assert!(!forward.checks(&wide, &base, 4, &facts));
    }
}

#[cfg(test)]
mod equivalent_base_membership_tests {
    use super::*;

    #[test]
    fn equivalent_base_membership_checks_displacement_before_load_histories() {
        let mut samples = Vec::new();
        for count in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let at = |id| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(id)),
            };
            let mut memory = CMemory::new();
            for i in 0..count {
                memory = memory.store(at(9_896_000 + i), CValue::Int32((i as u32).into()));
            }
            let snapshot = intern_c_memory(memory);
            let loaded_base = |id| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int64(
                    Bitvector32Term::MemoryLoad(
                        snapshot.clone(),
                        Box::new(at(id)),
                        crate::kernel::LoadKind::Bits64,
                    ),
                    4,
                    true,
                ),
            };
            let base = loaded_base(9_895_001);
            let selected = loaded_base(9_895_002).offset_by_bytes(64);
            let range = CMemoryRange::new_with_element_width(base, 0u32.into(), 2u32.into(), 4);
            // The general producer also tries other aliases, whose load histories
            // may be relevant. This measures only the selected EquivalentBase
            // candidate, which must reject displacement before resolving its base.
            // Sixteen elements cannot fit [0..2); the reversed Add arm has a
            // native64 displacement without a signed32 membership index. Neither
            // failed candidate needs equality between its history-derived bases.
            let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
                PointerInRangeEvidence::for_equivalent_base(
                    &selected,
                    &range,
                    &PureFactContext::new(),
                )
            });
            assert!(proof.is_none());
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "failed equivalent-base displacement resolved load histories: {samples:?}"
        );
    }
}

#[cfg(test)]
mod ordered_range_tests {
    use super::*;

    #[test]
    fn symbolic_same_base_containment_retains_exact_ordered_extents() {
        let mut samples = Vec::new();
        for unrelated in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(9_896_000));
            let length = Bitvector32Term::Variable(Variable(9_896_001));
            let capacity = Bitvector32Term::Variable(Variable(9_896_002));
            let child = CMemoryRange::new(base.clone(), 0u32.into(), length.clone());
            let parent = CMemoryRange::new(base.clone(), 0u32.into(), capacity.clone());
            let lower = Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(0u32.into(), length.clone()),
                true,
            );
            let upper = Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(length.clone(), capacity.clone()),
                true,
            );
            let fits = Proposition::ConditionIs(
                ConditionTerm::unsigned_less_equal(capacity.clone(), 1_073_741_823u32.into()),
                true,
            );
            let mut assumptions = PureFactContext::new()
                .assume_proposition(lower.clone())
                .assume_proposition(upper.clone())
                .assume_proposition(fits.clone());
            for id in 0..unrelated {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(9_896_100 + id * 2)),
                        Bitvector32Term::Variable(Variable(9_896_101 + id * 2)),
                    ),
                    true,
                );
            }
            let ((proof, premises), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::collect_reasoning_provenance(|| {
                        crate::kernel::capture_implicit_reasoning_provenance(|| {
                            RangeInRangeEvidence::for_range(&child, &parent, &assumptions)
                        })
                    })
                });
            let proof = proof.expect("selected length bounds cover the complete symbolic range");
            assert!(matches!(
                &proof,
                RangeInRangeEvidence::OrderedSameBase { .. }
            ));
            assert!(premises.contains(&lower));
            assert!(premises.contains(&upper));
            assert!(premises.contains(&fits));
            let captured = premises
                .into_iter()
                .fold(PureFactContext::new(), PureFactContext::assume_proposition);
            assert!(proof.checks(&child, &parent, &captured));
            for bound in [&lower, &upper, &fits] {
                let missing = captured.without_exact_fact(bound);
                assert!(!proof.checks(&child, &parent, &missing));
                assert!(
                    RangeInRangeEvidence::for_ordered_range(&child, &parent, &missing).is_none()
                );
            }
            let overflowing_parent =
                CMemoryRange::new(base.clone(), 0u32.into(), 1_073_741_825u32.into());
            let overflowing_context = captured.clone().assume_condition(
                ConditionTerm::signed_less_equal(length.clone(), 1_073_741_825u32.into()),
                true,
            );
            assert!(!proof.checks(&child, &overflowing_parent, &overflowing_context));
            assert!(
                RangeInRangeEvidence::for_ordered_range(
                    &child,
                    &overflowing_parent,
                    &overflowing_context,
                )
                .is_none()
            );
            let reversed = CMemoryRange::new(base.clone(), length.clone(), 0u32.into());
            let negative = CMemoryRange::new(base.clone(), u32::MAX.into(), length.clone());
            let wide = CMemoryRange::new_wide(
                base.clone(),
                Bitvector32Term::UInt64Constant(0),
                Bitvector32Term::UInt64Constant(1),
                4,
            );
            let other_base = CMemoryRange::new(
                Pointer::symbolic(Variable(9_896_003)),
                0u32.into(),
                length.clone(),
            );
            let other_stride = CMemoryRange::new_with_element_width(base, 0u32.into(), length, 8);
            for changed in [reversed, negative, wide, other_base, other_stride] {
                assert!(!proof.checks(&changed, &parent, &captured));
                assert!(
                    RangeInRangeEvidence::for_ordered_range(&changed, &parent, &captured).is_none()
                );
            }
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "selected extent evidence visited unrelated bounds: {samples:?}"
        );
    }
}

#[cfg(test)]
mod pinned_range_bound_tests {
    use super::*;

    #[test]
    fn indexed_access_pinned_to_zero_retains_its_equality_and_complete_width() {
        let mut samples = Vec::new();
        for unrelated in [16u64, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(crate::kernel::Variable(9_899_000));
            let index = Bitvector32Term::Variable(crate::kernel::Variable(9_899_001));
            let pointer = base.offset_by_elements(index.clone(), 4);
            let range = CMemoryRange::new(base, 0u32.into(), 1u32.into());
            let equality = Proposition::ConditionIs(ConditionTerm::equal(index, 0u32.into()), true);
            let mut context = PureFactContext::new().assume_proposition(equality.clone());
            for i in 0..unrelated {
                context = context.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(crate::kernel::Variable(9_900_000 + i)),
                        7u32.into(),
                    ),
                    true,
                );
            }
            let ((proof, premises), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::collect_reasoning_provenance(|| {
                        crate::kernel::capture_implicit_reasoning_provenance(|| {
                            AccessInRangeEvidence::for_access(&pointer, 4, &range, &context)
                        })
                    })
                });
            let proof = proof.expect("zero index belongs to one complete int32 element");
            assert!(premises.contains(&equality));
            assert!(proof.checks(&pointer, 4, &range, &context));
            assert!(!proof.checks(&pointer, 4, &range, &context.without_exact_fact(&equality)));
            assert!(AccessInRangeEvidence::for_access(&pointer, 8, &range, &context).is_none());
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "unrelated equalities changed work: {samples:?}"
        );
    }

    #[test]
    fn pinned_index_outside_the_range_is_not_membership() {
        let base = Pointer::symbolic(crate::kernel::Variable(9_899_100));
        let index = Bitvector32Term::Variable(crate::kernel::Variable(9_899_101));
        let pointer = base.offset_by_elements(index.clone(), 4);
        let range = CMemoryRange::new(base, 0u32.into(), 1u32.into());
        for value in [1u32, u32::MAX] {
            let context = PureFactContext::new()
                .assume_condition(ConditionTerm::equal(index.clone(), value.into()), true);
            assert!(AccessInRangeEvidence::for_access(&pointer, 4, &range, &context).is_none());
        }
    }
}
