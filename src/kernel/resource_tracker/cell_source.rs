//! How the tracker reads one memory cell's recorded history: the cell walk
//! and the retained hop evidence it produces.
//!
//! The walk answers two different questions with one traversal. The tracker
//! asks "is this cell the same at these two program points", and takes only
//! the node the walk stopped at. Memory-load reasoning asks "are these two
//! loads equal", and takes the whole path as retained evidence. Both live
//! here because they read the same recorded edges under the same rules; see
//! `docs/internals/resource-tracker.md` and `docs/internals/memory-dag.md`.

#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::memory_provenance::*;
use crate::kernel::primitives::*;
use crate::kernel::reasoning::*;
use crate::kernel::{CompareRelation, MachineIntegerType, StoredMemoryValue};

/// Where the memory DAG says the cell at a pointer came from: the
/// select-over-store answer to "what does this cell hold after these
/// stores", read off the write history execution recorded rather than
/// reconstructed by canonicalizing and deep-comparing state values.
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
        node: SharedMemory,
        value: StoredMemoryValue,
        path: Vec<MemoryDagHop>,
    },
    /// The walk reached `node` without crossing any edge that could have
    /// written the cell, and stopped: `node` carries no derivation, its
    /// derivation is undecidable against this pointer, or the hop cap ran
    /// out. The load therefore reads whatever `node` holds at the pointer.
    Unwritten {
        node: SharedMemory,
        path: Vec<MemoryDagHop>,
    },
}

/// Why a cell walk stopped where it did.
///
/// The node a walk stops at answers "what does this load read"; this answers
/// the separate question of why the walk stopped, and the reasons are not
/// interchangeable. A walk that ran out
/// of history proved nothing either way. A walk that could not show a step
/// separate proved nothing either way, and some other route may still
/// separate that step. A walk stopped by a step that provably writes, creates
/// or retires bytes this access reads has established a positive fact: the
/// cell one step older is a *different version* of this cell, and two loads
/// either side of that step are not one value by any structural route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum CellWalkStop {
    /// The paired walks met at the same state; its older history is irrelevant.
    CommonState,
    /// A cache-only forgetting edge retains the queried typed value in its input.
    RetainedValue,
    /// The walk reached a state with no recorded derivation: the oldest
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
    pub(in crate::kernel) derived: SharedMemory,
    pub(in crate::kernel) derivation: std::sync::Arc<MemoryDerivation>,
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
    /// Full byte geometry in the maintained numeric-address classes.
    StoreAddressByteSeparation,
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
        path: Vec<OrderDerivationStep>,
        reversed: bool,
    },
    StoreSeparatedRanges {
        authority: StoreSeparatedRangesAuthority,
        left: MemoryRange,
        right: MemoryRange,
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
        left: MemoryRange,
        right: MemoryRange,
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
        range: MemoryRange,
        first: PointerInRangeEvidence,
        last: PointerInRangeEvidence,
    },
    JoinReadAgreement {
        arms: Vec<(MemoryDagCell, MemoryDagCell)>,
    },
    LoopHavocRanges {
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    /// Every range a loop declared it may write lies in an object proven
    /// distinct from the read's.
    LoopHavocWriteSetInDistinctObjects,
    LoopHavocKeptRange {
        range: MemoryRange,
        first: PointerInRangeEvidence,
        last: PointerInRangeEvidence,
    },
    /// A `CellsSeeded` edge crossed: one justification per store it stands
    /// for, newest first ([`MemoryDerivation::seeded_stores`]).
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
    StoreExplicitRange,
    StoreGeneralDistinctness,
    HeapFreeResourceSeparation,
    CallHavocRangeSeparation,
    /// A cell held by memory the caller kept owning across the call
    /// (`MemoryDerivation::CallHavoc::kept_by_caller`).
    CallHavocKeptByCaller,
    LoopHavocRangeSeparation,
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
    /// Existing structural constant/affine membership. Retaining this cheap
    /// form keeps ordinary store edges out of the symbolic bound producer.
    Shallow,
    Indexed {
        index: SharedMachineIntegerTerm,
        lower: RangeBoundEvidence,
        upper: RangeBoundEvidence,
    },
    /// An unsigned 64-bit element index of a 32-bit-bounded range: the read
    /// is the range's own base plus `index` whole elements, the range starts
    /// at a constant no greater than zero (an unsigned index is never
    /// below it), and `upper` — an exact fact of the context — keeps the
    /// index below the range's constant end ([`unsigned_index_in_range`]).
    UnsignedIndexed {
        index: SharedMachineIntegerTerm,
        upper: ConditionTerm,
    },
}

/// The unsigned 64-bit element index of `pointer` in a 32-bit-bounded
/// `range`, and the exact order facts any one of which keeps it below the
/// range's end: `index < end`, its mirror, and `index <= end - 1`.
///
/// The pointer must add one unsigned 64-bit scaled index, at the range's
/// element width, to exactly the range's base (structural identity, so one
/// object's elements at one origin); numeric address equality never
/// qualifies. The range must start at a constant at most zero and end at a
/// non-negative constant. The answer is built from the terms in hand; a
/// caller asks the context for each candidate by exact lookup.
pub(in crate::kernel) fn unsigned_index_in_range(
    pointer: &Pointer,
    range: &MemoryRange,
) -> Option<(SharedMachineIntegerTerm, Vec<ConditionTerm>)> {
    crate::instrumentation::record_deterministic_work(1);
    let (start, end) = range.int32_bounds()?;
    let start = i64::from(start.as_const()? as i32);
    let end = i64::from(end.as_const()? as i32);
    if start > 0 || end <= 0 {
        return None;
    }
    let (index_offset, base_rest) =
        crate::kernel::reasoning::common_base_index_offsets(pointer, range.base())?;
    if base_rest != PointerOffsetTerm::Constant(0) {
        return None;
    }
    let PointerOffsetTerm::Int64Scaled {
        value,
        byte_width,
        unsigned: true,
    } = index_offset
    else {
        return None;
    };
    if byte_width != i64::from(range.element_width()) {
        return None;
    }
    let index = value.clone();
    let end_term = MachineTerm::uint64_constant(end as u64);
    let last = MachineTerm::uint64_constant((end - 1) as u64);
    let compare = |relation, bound: &MachineTerm, reverse| {
        let atom = index.operand_view().literal().or_else(|| {
            index
                .operand_view()
                .variable()
                .copied()
                .map(MachineTerm::Variable)
        });
        if let Some(atom) = atom {
            let (left, right) = if reverse {
                (bound.clone(), atom)
            } else {
                (atom, bound.clone())
            };
            return ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        let mut operands = [
            index.operand_view(),
            crate::kernel::MachineOperandView::Legacy(bound),
        ];
        if reverse {
            operands.swap(0, 1);
        }
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            MachineIntegerType::UInt64,
            relation,
            operands,
        )
    };
    let guards = vec![
        compare(CompareRelation::LessThan, &end_term, false),
        compare(CompareRelation::GreaterThan, &end_term, true),
        compare(CompareRelation::LessEqual, &last, false),
        compare(CompareRelation::GreaterEqual, &last, true),
    ];
    Some((index, guards))
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
        range: &MemoryRange,
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

    fn last_offset(bytes: u32, range: &MemoryRange) -> Option<u32> {
        let width = range.element_width();
        (bytes != 0 && width != 0).then(|| ((bytes - 1) / width) * width)
    }

    fn checks(
        &self,
        pointer: &Pointer,
        bytes: u32,
        range: &MemoryRange,
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
    SignedOrderPath(Vec<OrderDerivationStep>),
    /// `left < base + 1` and `base < right` imply `left < right` over
    /// signed int32. The second strict bound also proves that `base + 1`
    /// does not wrap.
    StrictUpperViaSuccessor {
        to_successor: OrderDerivationStep,
        successor_base_to_upper: Vec<OrderDerivationStep>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum RangeDisjointFromPointerEvidence {
    /// Identical endpoints describe no bytes, independent of the base.
    Empty,
    DistinctBlocks,
    BorrowPartition(Box<BorrowPartitionRangeEvidence>),
    ExactSeparationFact(Box<SeparatedRangeEvidence>),
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
        offset: SharedMachineIntegerTerm,
        positive: PositiveTermEvidence,
    },
}

/// A selected explicit separation, complete mutable footprint, and full read.
/// The selected members are retained input, rather than rediscovered by checking.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct SeparatedRangeEvidence {
    pub(in crate::kernel) fact: Proposition,
    pub(in crate::kernel) range_member: MemoryRange,
    pub(in crate::kernel) access_member: MemoryRange,
    pub(in crate::kernel) membership: AccessInRangeEvidence,
}

impl SeparatedRangeEvidence {
    fn checks(
        &self,
        range: &MemoryRange,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        assumptions.prop_facts.contains(&self.fact)
            && self.fact.memory_separation().is_some_and(|(left, right)| {
                left == &self.range_member && right == &self.access_member
                    || right == &self.range_member && left == &self.access_member
            })
            && !assumptions
                .memory_ranges_overlap_after_base_equality(&self.range_member, &self.access_member)
            && crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                range,
                &self.range_member,
                assumptions,
            )
            && self
                .membership
                .checks(pointer, bytes, &self.access_member, assumptions)
    }
}

/// A complete mutable footprint and read selected from one live borrowed
/// view/owner partition. The selected members are explicit certificate input;
/// checking never rediscovers them among unrelated resources.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct BorrowPartitionRangeEvidence {
    pub(in crate::kernel) resources: ResourceContext,
    pub(in crate::kernel) range_member: MemoryRange,
    pub(in crate::kernel) access_member: MemoryRange,
    pub(in crate::kernel) membership: AccessInRangeEvidence,
}

impl BorrowPartitionRangeEvidence {
    fn checks(
        &self,
        range: &MemoryRange,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        assumptions.resource_compositions.contains(&self.resources)
            && self
                .resources
                .proves_borrow_partition_separate(&self.range_member, &self.access_member)
            && !assumptions
                .memory_ranges_overlap_after_base_equality(&self.range_member, &self.access_member)
            && crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                range,
                &self.range_member,
                assumptions,
            )
            && self
                .membership
                .checks(pointer, bytes, &self.access_member, assumptions)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PositiveTermEvidence {
    Constant,
    ExactCondition(ConditionTerm),
    OneLowerBound(ConditionTerm),
}

impl MemoryDagHopJustification {
    fn is_typed(&self) -> bool {
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
        derivation: &MemoryDerivation,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::StoreDistinctBlocks => matches!(
                derivation,
                MemoryDerivation::Store { pointer: write, .. }
                    if write.blocks_proven_distinct(pointer)
            ),
            Self::StoreAddressByteSeparation => {
                let MemoryDerivation::Store {
                    pointer: write,
                    value,
                    ..
                } = derivation
                else {
                    return false;
                };
                assumptions
                    .numeric_access_byte_overlap(write, value.byte_width(), pointer, bytes)
                    .or_else(|| {
                        (write.block == pointer.block)
                            .then(|| {
                                crate::kernel::reasoning::exact_access_byte_overlap(
                                    write,
                                    value.byte_width(),
                                    pointer,
                                    bytes,
                                )
                            })
                            .flatten()
                    })
                    == Some(crate::kernel::reasoning::AccessByteOverlap::Separate)
            }
            Self::StoreAliasedByteSeparation { write: aligned } => {
                let MemoryDerivation::Store {
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
                let MemoryDerivation::Store { pointer: write, .. } = derivation else {
                    return false;
                };
                pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                    == Some(condition.clone())
                    && condition == &ConditionTerm::Constant(false)
            }
            Self::StoreCommonBaseExactInequality { condition } => {
                let MemoryDerivation::Store { pointer: write, .. } = derivation else {
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
                let MemoryDerivation::Store { pointer: write, .. } = derivation else {
                    return false;
                };
                let Some(ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                }) = pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                else {
                    return false;
                };
                if *condition
                    != (ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: left.clone(),
                        right: right.clone(),
                    })
                {
                    return false;
                }
                let (lower, upper) = if *reversed {
                    (right.as_ref(), left.as_ref())
                } else {
                    (left.as_ref(), right.as_ref())
                };
                assumptions.checks_exact_signed_order_source_path(
                    path,
                    MachineOperandView::Legacy(lower),
                    MachineOperandView::Legacy(upper),
                    true,
                )
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
                        MemoryDerivation::Store { pointer, value, .. },
                    ) => (pointer, value.byte_width()),
                    (
                        Self::LocalLifetimeEndedSeparatedRanges { .. },
                        MemoryDerivation::LocalLifetimeEnded { base, block },
                    ) => {
                        if !block.is_local_block() || pointer.block == *block {
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
                MemoryDerivation::BlockDeclared { .. }
                    | MemoryDerivation::HeapAllocationPending { .. }
                    | MemoryDerivation::HeapAllocationFailed { .. }
                    | MemoryDerivation::ContractAllocationClaimsChanged { .. }
                    | MemoryDerivation::ObjectInitializationRecorded { .. }
                    | MemoryDerivation::CellObserved { .. }
                    | MemoryDerivation::CellsForgotten { .. }
            ),
            Self::AllocationOfOtherBlock => matches!(
                derivation,
                MemoryDerivation::HeapAllocated { block, .. } if pointer.block != *block
            ),
            Self::LocalLifetimeEndedOfOtherBlock => matches!(
                derivation,
                MemoryDerivation::LocalLifetimeEnded { block, .. }
                    if pointer.blocks_proven_distinct(&Pointer {
                        block: block.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    })
            ),
            Self::HeapFreeOfDistinctBlock => matches!(
                derivation,
                MemoryDerivation::HeapFreed {
                    allocation_base, ..
                }
                | MemoryDerivation::ContractAllocationRetired {
                    allocation_base, ..
                } if allocation_base.blocks_proven_distinct(pointer)
            ),
            Self::RetirementInsideItsCallHavoc => retirement_inside_its_call_havoc(derivation),
            Self::CallHavocRanges { ranges } => {
                let MemoryDerivation::CallHavoc { mutable_ranges, .. } = derivation else {
                    return false;
                };
                ranges.len() == mutable_ranges.len()
                    && ranges.iter().zip(mutable_ranges).all(|(evidence, range)| {
                        evidence.checks(range, pointer, bytes, assumptions)
                    })
            }
            Self::CallHavocKeptRange { range, first, last }
            | Self::LoopHavocKeptRange { range, first, last } => {
                let kept = match (self, derivation) {
                    (
                        Self::CallHavocKeptRange { .. },
                        MemoryDerivation::CallHavoc {
                            kept_by_caller: Some(kept),
                            ..
                        },
                    )
                    | (
                        Self::LoopHavocKeptRange { .. },
                        MemoryDerivation::LoopHavoc {
                            kept_by_function: Some(kept),
                            ..
                        },
                    ) => kept,
                    _ => return false,
                };
                let width = range.element_width();
                width != 0
                    && bytes != 0
                    && bytes.is_multiple_of(width)
                    && kept.contains_range(range)
                    && first.checks(pointer, range, assumptions)
                    && last.checks(
                        &pointer
                            .offset_by_elements(MachineTerm::constant(bytes / width - 1), width),
                        range,
                        assumptions,
                    )
            }
            Self::JoinReadAgreement { arms } => {
                let MemoryDerivation::BranchJoin { base, incoming } = derivation else {
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
                let MemoryDerivation::LoopHavoc {
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
            Self::LoopHavocWriteSetInDistinctObjects => matches!(
                derivation,
                MemoryDerivation::LoopHavoc {
                    mutable_ranges: Some(mutable_ranges),
                    ..
                } if mutable_ranges
                    .iter()
                    .all(|range| range.base().block.proven_distinct(&pointer.block))
            ),
            Self::SeededLoadsOfBase => super::step_effect::seeded_loads_preserve_base(derivation),
            Self::SeededStoresDistinctBlock => matches!(
                derivation,
                MemoryDerivation::CellsSeeded { run, .. }
                    if run.base().blocks_proven_distinct(pointer)
            ),
            Self::SeededStoresMissedByShift => {
                let MemoryDerivation::CellsSeeded { run, .. } = derivation else {
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
                            &MemoryDerivation::Store {
                                base: derivation.base().clone(),
                                pointer: write,
                                value: value.into(),
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
    pub(in crate::kernel) fn for_view(
        term: MachineOperandView<'_>,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if crate::kernel::assumptions::signed_index_constant(term).is_some_and(|value| value > 0) {
            return Some(Self::Constant);
        }
        let exact = crate::kernel::assumptions::index_comparison(
            CompareRelation::LessThan,
            MachineOperandView::Legacy(&MachineTerm::constant(0)),
            term,
        );
        if assumptions.selected_comparison_value(&exact) == Some(true) {
            return Some(Self::ExactCondition(exact));
        }
        let lower_bound = crate::kernel::assumptions::index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&MachineTerm::constant(1)),
            term,
        );
        (assumptions.selected_comparison_value(&lower_bound) == Some(true))
            .then_some(Self::OneLowerBound(lower_bound))
    }

    fn checks_view(&self, term: MachineOperandView<'_>, assumptions: &PureFactContext) -> bool {
        match self {
            Self::Constant => crate::kernel::assumptions::signed_index_constant(term)
                .is_some_and(|value| value > 0),
            Self::ExactCondition(condition) => {
                condition
                    == &crate::kernel::assumptions::index_comparison(
                        CompareRelation::LessThan,
                        MachineOperandView::Legacy(&MachineTerm::constant(0)),
                        term,
                    )
                    && assumptions.selected_comparison_value(condition) == Some(true)
            }
            Self::OneLowerBound(condition) => {
                condition
                    == &crate::kernel::assumptions::index_comparison(
                        CompareRelation::LessEqual,
                        MachineOperandView::Legacy(&MachineTerm::constant(1)),
                        term,
                    )
                    && assumptions.selected_comparison_value(condition) == Some(true)
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
        range: &MemoryRange,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::Empty => {
                let (start, end) = range.bound_terms();
                start == end
            }
            Self::DistinctBlocks => range.base.blocks_proven_distinct(pointer),
            Self::BorrowPartition(evidence) => evidence.checks(range, pointer, bytes, assumptions),
            Self::ExactSeparationFact(evidence) => {
                evidence.checks(range, pointer, bytes, assumptions)
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
                    && positive.checks_view(
                        crate::kernel::assumptions::index_binary(
                            MachineBinaryOp::Add,
                            offset.operand_view(),
                            MachineOperandView::Legacy(range.start()),
                        )
                        .operand_view(),
                        assumptions,
                    )
            }
        }
    }
}

impl MemoryDagCell {
    pub(in crate::kernel) fn node(&self) -> &SharedMemory {
        match self {
            Self::Stored { node, .. } | Self::Unwritten { node, .. } => node,
        }
    }

    /// The concrete value the lookup pins down for a `kind` read at
    /// `pointer`, when it pins one down.
    ///
    /// A stored value starts at the read's address by construction
    /// ([`write_supplies_read`]); it, and a cell the stopping state
    /// materialized at this exact address, answer only when the read of
    /// `kind` returns exactly that value ([`LoadKind::reads_value`]). A value
    /// of another width holds other bytes than the read returns, and one of
    /// the read's width but the other signedness is another number.
    pub(in crate::kernel) fn resolved_value(
        &self,
        pointer: &Pointer,
        kind: LoadKind,
    ) -> Option<ProgramValue> {
        match self {
            Self::Stored { value, .. } => kind.read_cell(value.native()),
            Self::Unwritten { node, .. } => kind.read_cell(&node.known_value(pointer)?),
        }
    }

    pub(in crate::kernel) fn checks_walk_from(
        &self,
        memory: &SharedMemory,
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
    pub(in crate::kernel) fn enter(memory: &SharedMemory, pointer: &Pointer) -> Option<Self> {
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

impl RangeBoundEvidence {
    fn for_true_condition(
        condition: &ConditionTerm,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        use crate::kernel::assumptions::{
            checked_scalar_facts::ScalarOperandKey as Key, order_view_at_format,
        };
        use crate::kernel::machine_integer::Relation;
        if condition == &ConditionTerm::Constant(true) {
            return Some(Self::Intrinsic);
        }
        let view = order_view_at_format(condition, true, MachineIntegerType::Int32)?;
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let strict = view.relation == Relation::Less;
        if let Some(step) = assumptions.exact_direct_order_source_step(left, right, strict) {
            return Some(Self::SignedOrderPath(vec![step]));
        }
        if strict {
            let successor = assumptions.signed_order_bound_views(left).find_map(
                |(endpoint, successor, strict, forward)| {
                    if !strict || !forward || Key::new(endpoint) != Key::new(left) {
                        return None;
                    }
                    let base = successor.int32_add_const_base(1)?;
                    let to_successor =
                        assumptions.exact_direct_order_source_step(endpoint, successor, true)?;
                    let successor_base_to_upper = assumptions
                        .exact_direct_order_source_step(base, right, true)
                        .map(|step| vec![step])
                        .or_else(|| {
                            assumptions.exact_signed_order_source_path(base, right, true)
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
            .exact_signed_order_source_path(left, right, strict)
            .map(Self::SignedOrderPath)
    }

    fn checks(&self, condition: &ConditionTerm, assumptions: &PureFactContext) -> bool {
        use crate::kernel::assumptions::{
            checked_scalar_facts::ScalarOperandKey as Key, order_view_at_format,
        };
        use crate::kernel::machine_integer::Relation;
        if matches!(self, Self::Intrinsic) {
            return condition == &ConditionTerm::Constant(true);
        }
        let Some(goal) = order_view_at_format(condition, true, MachineIntegerType::Int32) else {
            return false;
        };
        let [left, right] = goal
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let strict = goal.relation == Relation::Less;
        match self {
            Self::Intrinsic => unreachable!(),
            Self::SignedOrderPath(path) => {
                assumptions.checks_exact_signed_order_source_path(path, left, right, strict)
            }
            Self::StrictUpperViaSuccessor {
                to_successor,
                successor_base_to_upper,
            } => {
                let Proposition::ConditionIs(condition, truth) = &to_successor.premise else {
                    return false;
                };
                let Some(edge) = order_view_at_format(condition, *truth, MachineIntegerType::Int32)
                else {
                    return false;
                };
                let [lower, upper] = edge
                    .operands
                    .each_ref()
                    .map(|operand| operand.operand_view());
                if !strict
                    || edge.relation != Relation::Less
                    || Key::new(lower) != Key::new(left)
                    || assumptions.exact_condition_value(condition) != Some(*truth)
                {
                    return false;
                }
                let Some(base) = upper.int32_add_const_base(1) else {
                    return false;
                };
                assumptions.checks_exact_signed_order_source_path(
                    successor_base_to_upper,
                    base,
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
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        Self::for_model_start_alias(pointer, range, assumptions)
            .or_else(|| Self::for_pointer_direct(pointer, range, assumptions))
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
                            .shared_element_index_from_base_with_width(base, 1)?
                            .operand_view()
                            .word32_constant()?;
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
    }

    fn for_model_start_alias(
        pointer: &Pointer,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        // A resource's model start can name the loaded start used by
        // the program's index. Keep the existing bound spelling and
        // align only this selected access through checked address
        // equality; the spelling supplies no range authority.
        let (start, _) = range.int32_bounds()?;
        let index = pointer
            .shared_element_index_from_base_with_width(range.base(), range.element_width())?;
        let Some((MachineIntegerType::Int32, MachineBinaryOp::Add, [left, right])) =
            index.operand_view().binary()
        else {
            return None;
        };
        let start = MachineOperandView::Legacy(start);
        let candidates = [[start, right], [left, start]].map(|operands| {
            MachineOperandView::Shared(&crate::kernel::KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                operands.map(|v| {
                    crate::kernel::KernelTerm::retained_machine_operand(
                        MachineIntegerType::Int32,
                        v,
                    )
                }),
            ))
            .retain(MachineIntegerType::Int32)
        });
        for candidate in candidates {
            if candidate == index {
                continue;
            }
            let alias = range
                .base()
                .offset_by_shared_elements(candidate, range.element_width());
            if pointer.blocks_proven_distinct(&alias)
                || !assumptions.pointers_known_equal(pointer, &alias)
            {
                continue;
            }
            if let Some(membership) = Self::for_pointer_direct(&alias, range, assumptions) {
                return Some(Self::GraphAlias {
                    alias,
                    membership: Box::new(membership),
                });
            }
        }
        None
    }

    fn for_pointer_direct(
        pointer: &Pointer,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
            pointer,
            range,
            assumptions,
        ) {
            return Some(Self::Shallow);
        }
        // A wide range has the one membership rule the shallow check just
        // applied; the signed 32-bit index evidence below does not read it.
        if range.wide_bounds().is_some() {
            return None;
        }
        if let Some((index, guards)) = unsigned_index_in_range(pointer, range) {
            return guards
                .into_iter()
                .find(|guard| assumptions.exact_condition_value(guard) == Some(true))
                .map(|upper| Self::UnsignedIndexed { index, upper });
        }
        let index = pointer
            .shared_element_index_from_base_with_width(range.base(), range.element_width())?;
        let lower_condition = crate::kernel::assumptions::index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&range.start()),
            index.operand_view(),
        );
        let upper_condition = crate::kernel::assumptions::index_comparison(
            CompareRelation::LessThan,
            index.operand_view(),
            MachineOperandView::Legacy(&range.end()),
        );
        Some(Self::Indexed {
            index,
            lower: RangeBoundEvidence::for_true_condition(&lower_condition, assumptions)?,
            upper: RangeBoundEvidence::for_true_condition(&upper_condition, assumptions)?,
        })
    }

    pub(in crate::kernel) fn checks(
        &self,
        pointer: &Pointer,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> bool {
        if let Self::GraphAlias { alias, membership } = self {
            return !pointer.blocks_proven_distinct(alias)
                && assumptions.pointers_known_equal(pointer, alias)
                && matches!(
                    membership.as_ref(),
                    Self::Shallow | Self::Indexed { .. } | Self::UnsignedIndexed { .. }
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
                    Self::Shallow | Self::Indexed { .. } | Self::UnsignedIndexed { .. }
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
                    Self::Shallow | Self::Indexed { .. } | Self::UnsignedIndexed { .. }
                )
                && membership.checks(alias, range, assumptions);
        }
        if let Self::UnsignedIndexed { index, upper } = self {
            return unsigned_index_in_range(pointer, range).is_some_and(|(found, guards)| {
                (found == *index
                    || crate::kernel::memory_provenance::pointer_index_syntax_equal(&found, index))
                    && guards.iter().any(|guard| {
                        if guard == upper {
                            return true;
                        }
                        crate::kernel::proof::propositions_are_alpha_equal(
                            &Proposition::ConditionIs(guard.clone(), true),
                            &Proposition::ConditionIs(upper.clone(), true),
                        )
                    })
            }) && assumptions.exact_condition_value(upper) == Some(true);
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
        let Some(index) =
            pointer.shared_element_index_from_base_with_width(range.base(), range.element_width())
        else {
            return false;
        };
        if index != *retained_index {
            return false;
        }
        lower.checks(
            &crate::kernel::assumptions::index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&range.start()),
                index.operand_view(),
            ),
            assumptions,
        ) && upper.checks(
            &crate::kernel::assumptions::index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(&range.end()),
            ),
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
pub(in crate::kernel) fn retirement_inside_its_call_havoc(step: &MemoryDerivation) -> bool {
    let MemoryDerivation::ContractAllocationRetired {
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
/// `base` ([`Memory::mark_forgotten_from`]).
///
/// The mark exists so a state that dropped knowledge cannot re-intern as
/// the one it forgot from, or as anything older. A retirement inside its
/// call's havoc ([`retirement_inside_its_call_havoc`]) is, for every cell
/// value, the same memory as that havoc's state: the dropped cells of the
/// allocation hold the havoc's post-call values, and the other dropped cells
/// are untouched. Keeping the havoc's mark is what makes the
/// content-addressed load names (the projections
/// `canonical_memory_for_pointer_load` interns, which carry the mark) agree
/// with the memory-DAG walk, which crosses such a retirement to the havoc.
///
/// Re-interning is still ruled out. The result carries the havoc's marker
/// block, whose identity is the call's fresh variable, so it cannot equal any
/// state from before the call. It can equal the havoc state itself only
/// when the retirement dropped nothing, and then the dropped edge lost
/// nothing either: the havoc, the next edge down, stops every cell and every
/// block question the retirement would have stopped for this allocation.
pub(in crate::kernel) fn retirement_keeps_its_call_havocs_forget_mark(
    base: &SharedMemory,
    allocation_base: &Pointer,
    bytes: &MachineTerm,
) -> bool {
    retired_allocation_inside_call_havoc(base, allocation_base, bytes)
}

fn retired_allocation_inside_call_havoc(
    base: &SharedMemory,
    allocation_base: &Pointer,
    bytes: &MachineTerm,
) -> bool {
    let mut current = base.clone();
    loop {
        crate::instrumentation::record_deterministic_work(1);
        let Some(derivation) = current.derivation() else {
            return false;
        };
        match derivation.as_ref() {
            MemoryDerivation::ContractAllocationRetired { base, .. } => current = base.clone(),
            MemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                return mutable_ranges.iter().any(|range| {
                    range_structurally_covers_allocation(range, allocation_base, bytes)
                });
            }
            _ => return false,
        }
    }
}

fn range_structurally_covers_allocation(
    range: &MemoryRange,
    allocation_base: &Pointer,
    bytes: &MachineTerm,
) -> bool {
    // This arithmetic rule uses signed 32-bit indices; wide ranges are undecided.
    if range.wide_bounds().is_some() {
        return false;
    }
    if range.base() != allocation_base || range.start() != &MachineTerm::constant(0) {
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
/// the read is then whatever the produced state holds there.
///
/// The walk is asked about an access width, the recorded one at the read's
/// address, and this check decides on that width alone. The read's own kind,
/// which a load term carries, is the second half and is
/// [`MemoryDagCell::resolved_value`]'s: a write of the read's width but the
/// other signedness stops the walk here and supplies nothing, because an
/// `int8` value's term is sign-extended where a `uint8` read's is not.
pub(in crate::kernel) fn write_supplies_read(
    write: &Pointer,
    value: &ProgramValue,
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
    memory: &SharedMemory,
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
/// Like the ordinary lookup, it inspects at most one immediate transition.
/// Reaching that limit is inconclusive, not evidence of preservation across
/// any earlier transition.
pub(in crate::kernel) fn memory_dag_cell_source_with_stop(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
) -> Option<(MemoryDagCell, CellWalkStop)> {
    // Inspect the selected state and one immediate transition only.
    // Longer preservation arguments must be written as certificate links.
    let _lookup = CellLookupGuard::enter(memory, pointer)?;
    Some(memory_dag_cell_source_walk(
        memory,
        pointer,
        bytes,
        assumptions,
        cross_loop_havoc,
        1,
    ))
}

/// A locally bounded read-value query. Reaching the limit preserves only the
/// stopping state's own cell; it never assumes that an unchecked hop frames
/// the read. This prevents a simple normalization from scanning a whole path.
pub(in crate::kernel) fn memory_dag_cell_source_with_hop_limit(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    max_hops: usize,
) -> Option<MemoryDagCell> {
    memory_dag_cell_source_with_hop_limit_and_stop(memory, pointer, bytes, assumptions, max_hops)
        .map(|(cell, _)| cell)
}

pub(in crate::kernel) fn memory_dag_cell_source_with_hop_limit_and_stop(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    max_hops: usize,
) -> Option<(MemoryDagCell, CellWalkStop)> {
    let _lookup = CellLookupGuard::enter(memory, pointer)?;
    Some(memory_dag_cell_source_walk(
        memory,
        pointer,
        bytes,
        assumptions,
        true,
        max_hops,
    ))
}

fn memory_dag_cell_source_walk(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
    max_hops: usize,
) -> (MemoryDagCell, CellWalkStop) {
    let result = memory_dag_cell_source_walk_inner(
        memory,
        pointer,
        bytes,
        assumptions,
        cross_loop_havoc,
        max_hops,
    );
    record_transport_cell_walk(memory, pointer, bytes, &result.0, result.1, Some(max_hops));
    result
}

fn memory_dag_cell_source_walk_inner(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    cross_loop_havoc: bool,
    max_hops: usize,
) -> (MemoryDagCell, CellWalkStop) {
    let evidence = super::step_effect::Evidence {
        assumptions,
        cross_loop_havoc,
    };
    let mut current = memory.clone();
    let mut path = Vec::new();
    // The walk ends at a state with no derivation: ids strictly
    // decrease along `base`, so every chain is finite.
    loop {
        // Forgetting cached cells changes knowledge, not bytes. An exact
        // value in that edge's input is already a checked observation; do
        // not jump past it and demand a frame across an older loop havoc.
        // This reads one named predecessor and one exact address, never a
        // cache bucket or an alternate pointer spelling.
        if crate::kernel::memory_provenance::extended_dag_bridging_active()
            && path.len() < max_hops
            && let Some(derivation) = current.derivation()
            && let MemoryDerivation::CellsForgotten { base } = derivation.as_ref()
            && base.cells.concrete().get(pointer).is_some_and(|value| {
                matches!(value.native(), crate::kernel::integer32_c_value!(_))
                    && value.byte_width() == bytes
            })
        {
            crate::instrumentation::record_deterministic_work(1);
            let node = base.clone();
            path.push(MemoryDagHop {
                derived: current,
                derivation,
                justification: MemoryDagHopJustification::IntrinsicNoWrite,
            });
            return (
                MemoryDagCell::Unwritten { node, path },
                CellWalkStop::RetainedValue,
            );
        }
        // The bound counts actual transitions, independently of whether a
        // search previously cached a longer preservation result.
        if path.len() >= max_hops {
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
            super::TrackedResource::Cell { pointer, bytes },
            &evidence,
        ) {
            super::step_effect::StepEffect::Affected => {
                let seeded = matches!(derivation.as_ref(), MemoryDerivation::CellsSeeded { .. })
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
                        Some((write, StoredMemoryValue::from(value)))
                    }
                    (
                        None,
                        MemoryDerivation::Store {
                            pointer: write,
                            value,
                            ..
                        },
                    ) => Some((write.clone(), value.clone())),
                    _ => None,
                };
                if let Some((write, value)) = written
                    && write_supplies_read(&write, value.native(), pointer, bytes, assumptions)
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

/// Compare just the two paths back to their nearest common state. Arena
/// ids decrease on every edge, so walking the newer endpoint finds that
/// common ancestor without inspecting its history. Every hop carries the
/// same local typed certificate as an ordinary read-preservation query.
pub(in crate::kernel) fn join_read_agreement(
    base: &SharedMemory,
    incoming: &SharedMemory,
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
            super::TrackedResource::Cell { pointer, bytes },
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
        let wide = MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1 << 33),
            4,
        );
        let facts = PureFactContext::new();
        let signed_index = binary_node!(
            Int32,
            Add,
            Box::new(MachineTerm::Variable(Variable(984_301))),
            Box::new(MachineTerm::Variable(Variable(984_302))),
        );
        let signed_access = base.offset_by_elements(signed_index, 4);
        assert!(PointerInRangeEvidence::for_pointer(&signed_access, &wide, &facts).is_none());
        assert!(!range_structurally_covers_allocation(
            &wide,
            &base,
            &MachineTerm::constant(4)
        ));
        let indexed = PointerInRangeEvidence::Indexed {
            index: MachineOperandView::Legacy(&MachineTerm::constant(0))
                .retain(MachineIntegerType::Int32),
            lower: RangeBoundEvidence::Intrinsic,
            upper: RangeBoundEvidence::Intrinsic,
        };
        assert!(!indexed.checks(&base, &wide, &facts));
        let forward = RangeDisjointFromPointerEvidence::ForwardOffset {
            offset: MachineOperandView::Legacy(&MachineTerm::constant(1))
                .retain(MachineIntegerType::Int32),
            positive: PositiveTermEvidence::Constant,
        };
        assert!(!forward.checks(&wide, &base, 4, &facts));
    }
}

#[cfg(test)]
mod borrowed_range_frame_tests {
    use super::*;
    use crate::kernel::loans::{LoanLedger, LoanViewBinding};
    use crate::kernel::{Proposition, PureFactContext, Variable};

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/resource_tracker/cell_source/borrowed_range_frame_tests.rs"
        );
    }
}

#[cfg(test)]
mod separated_range_frame_tests {
    use super::*;
    use crate::kernel::{Proposition, PureFactContext, Variable};

    fn model_start_frame() -> (
        Pointer,
        Pointer,
        Pointer,
        SharedMemory,
        PureFactContext,
        Vec<Proposition>,
    ) {
        let word = |id| MachineTerm::Variable(Variable(id));
        let start = word(9_941_001);
        let loaded_start = word(9_941_002);
        let end = word(9_941_003);
        let index = word(9_941_004);
        let model_index =
            binary_node!(Int32, Add, Box::new(start.clone()), Box::new(index.clone()));
        let actual_index =
            binary_node!(Int32, Add, Box::new(loaded_start.clone()), Box::new(index));
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let data = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scaled_int32_node(word(9_941_005), 4),
        };
        let backing = MemoryRange::new(data.clone(), start.clone(), end.clone());
        let descriptor = MemoryRange::new(field.clone(), 0u32.into(), 4u32.into());
        let facts = vec![
            Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(backing)),
                right: Box::new(Resource::Memory(descriptor)),
            },
            Proposition::ConditionIs(ConditionTerm::equal(loaded_start, start.clone()), true),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(start.clone(), model_index.clone()),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_than(model_index, end.clone()),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_less_equal(0u32.into(), start), true),
            Proposition::ConditionIs(ConditionTerm::signed_less_equal(end, 1024u32.into()), true),
        ];
        let context = facts
            .iter()
            .cloned()
            .fold(PureFactContext::new(), PureFactContext::assume_proposition);
        let initial = Memory::new();
        let before = crate::kernel::intern_memory_ref(&initial);
        let after = crate::kernel::intern_memory(initial.store(
            data.offset_by_elements(actual_index, 4),
            ProgramValue::Int32(1u32.into()),
        ));
        (
            Pointer::loaded_value(&before, &field),
            Pointer::loaded_value(&after, &field),
            field,
            before,
            context,
            facts,
        )
    }

    #[test]
    fn model_start_alias_frames_a_complete_pointer_read_only_with_its_premises() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, after, field, memory, context, facts) = model_start_frame();
        assert!(
            crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                &before, &after, &context
            )
        );
        for missing in &facts[..4] {
            let without = facts
                .iter()
                .filter(|fact| *fact != missing)
                .cloned()
                .fold(PureFactContext::new(), PureFactContext::assume_proposition);
            assert!(
                !crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                    &before, &after, &without
                ),
                "without {missing:?}"
            );
        }
        let partial = crate::kernel::intern_memory(
            memory
                .memory()
                .clone()
                .store(field.offset_by_bytes(4), ProgramValue::Int32(2u32.into())),
        );
        let overwritten = Pointer::loaded_value(&partial, &field);
        assert!(
            !crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                &before,
                &overwritten,
                &context
            ),
            "a four-byte store into the upper pointer half cannot preserve an eight-byte read"
        );
    }

    #[test]
    fn separated_read_start_does_not_frame_an_overlapping_wide_read() {
        let field = Pointer {
            block: "separated-frame".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let backing = MemoryRange::new(field.offset_by_bytes(8), 0u32.into(), 1u32.into());
        let descriptor = MemoryRange::new(field.clone(), 0u32.into(), 2u32.into());
        let context = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(backing.clone())),
            right: Box::new(Resource::Memory(descriptor)),
        });
        let read = field.offset_by_bytes(4);
        let proof = typed_range_disjoint_from_pointer_evidence(&backing, &read, 4, &context)
            .expect("read [4, 8) is separated from mutable bytes [8, 12)");
        assert!(matches!(
            &proof,
            RangeDisjointFromPointerEvidence::ExactSeparationFact(_)
        ));
        assert!(proof.checks(&backing, &read, 4, &context));
        // The start still belongs to the descriptor, but [4, 12) actually
        // overlaps the mutable footprint. Point membership cannot frame it.
        assert!(!proof.checks(&backing, &read, 8, &context));
        assert!(typed_range_disjoint_from_pointer_evidence(&backing, &read, 8, &context).is_none());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/resource_tracker/cell_source/separated_range_frame_tests.rs"
        );
    }
}

#[cfg(test)]
mod unsigned_index_membership_tests {
    use super::*;
    use crate::kernel::{PureFactContext, Variable};

    /// `base[k]` for an unsigned 64-bit `k`, one byte per element.
    fn byte_at(base: &Pointer, index: Variable) -> Pointer {
        Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scaled_int64_node(MachineTerm::Variable(index), 1, true),
        }
    }

    fn below(index: Variable, end: u64) -> ConditionTerm {
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: Box::new(MachineTerm::Variable(index)),
            right: Box::new(MachineTerm::uint64_constant(end)),
        }
    }

    fn bytes(base: &Pointer, end: u32) -> MemoryRange {
        MemoryRange::new_with_element_width(base.clone(), 0u32.into(), end.into(), 1)
    }

    #[test]
    fn a_guarded_unsigned_index_is_inside_the_range() {
        let base = Pointer::symbolic(Variable(984_400));
        let k = Variable(984_401);
        let read = byte_at(&base, k);
        let range = bytes(&base, 4);
        let context = PureFactContext::new().assume_condition(below(k, 4), true);
        let membership = PointerInRangeEvidence::for_pointer(&read, &range, &context)
            .expect("k < 4 places base[k] in base[0..4]");
        assert!(matches!(
            membership,
            PointerInRangeEvidence::UnsignedIndexed { .. }
        ));
        assert!(membership.checks(&read, &range, &context));
        // The evidence is the exact fact: without it, checking refuses.
        assert!(!membership.checks(&read, &range, &PureFactContext::new()));
        // `k <= 3` is the same bound written inclusively.
        let inclusive = PureFactContext::new().assume_condition(
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::Variable(k)),
                right: Box::new(MachineTerm::uint64_constant(3)),
            },
            true,
        );
        assert!(PointerInRangeEvidence::for_pointer(&read, &range, &inclusive).is_some());
    }

    #[test]
    fn an_index_bounded_past_the_end_is_refused() {
        let base = Pointer::symbolic(Variable(984_410));
        let k = Variable(984_411);
        let read = byte_at(&base, k);
        let range = bytes(&base, 4);
        // `k < 5` allows `k == 4`, one past the range.
        let context = PureFactContext::new().assume_condition(below(k, 5), true);
        assert!(PointerInRangeEvidence::for_pointer(&read, &range, &context).is_none());
        let retained = PointerInRangeEvidence::UnsignedIndexed {
            index: SharedMachineIntegerTerm::index(
                MachineIntegerType::UInt64,
                MachineTerm::Variable(k),
            ),
            upper: below(k, 5),
        };
        assert!(!retained.checks(&read, &range, &context));
    }

    #[test]
    fn an_index_on_another_base_is_refused() {
        let base = Pointer::symbolic(Variable(984_420));
        let other = Pointer::symbolic(Variable(984_421));
        let k = Variable(984_422);
        let range = bytes(&base, 4);
        let context = PureFactContext::new().assume_condition(below(k, 4), true);
        // `other[k]` is not `base[k]` however `k` is bounded.
        let elsewhere = byte_at(&other, k);
        assert!(PointerInRangeEvidence::for_pointer(&elsewhere, &range, &context).is_none());
        let membership = PointerInRangeEvidence::for_pointer(&byte_at(&base, k), &range, &context)
            .expect("base[k] is inside");
        assert!(!membership.checks(&elsewhere, &range, &context));
        // One block at another origin is another base too: `base + 8 + k`.
        let shifted_base = base.offset_by_bytes(8);
        let shifted = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Add(
                Box::new(shifted_base.offset.clone()),
                Box::new(byte_at(&base, k).offset),
            ),
        };
        assert!(PointerInRangeEvidence::for_pointer(&shifted, &range, &context).is_none());
    }

    #[test]
    fn a_signed_or_wider_element_index_is_refused() {
        let base = Pointer::symbolic(Variable(984_430));
        let k = Variable(984_431);
        let range = bytes(&base, 4);
        let context = PureFactContext::new().assume_condition(below(k, 4), true);
        let signed = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scaled_int64_node(MachineTerm::Variable(k), 1, false),
        };
        assert!(unsigned_index_in_range(&signed, &range).is_none());
        // Four-byte elements of a one-byte range: the scale is not the
        // range's element width.
        let wide = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scaled_int64_node(MachineTerm::Variable(k), 4, true),
        };
        assert!(unsigned_index_in_range(&wide, &range).is_none());
        assert!(PointerInRangeEvidence::for_pointer(&wide, &range, &context).is_none());
    }

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/resource_tracker/cell_source/unsigned_index_membership_tests.rs"
        );
    }
}

#[cfg(test)]
mod empty_range_frame_tests {
    use super::*;

    #[test]
    fn empty_frames_cover_every_access_width_but_not_nonempty_ranges() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(9_951_000));
        let bound = MachineTerm::Variable(Variable(9_951_001));
        let context = PureFactContext::new();
        let ranges = [
            MemoryRange::new(base.clone(), bound.clone(), bound.clone()),
            MemoryRange::new_wide(base.clone(), bound.clone(), bound, 4),
        ];
        let nonempty = [
            MemoryRange::new(base.clone(), 0u32.into(), 1u32.into()),
            MemoryRange::new_wide(
                base.clone(),
                MachineTerm::uint64_constant(0),
                MachineTerm::uint64_constant(1),
                4,
            ),
        ];
        for (empty, changed) in ranges.iter().zip(&nonempty) {
            for bytes in [1, 4, 8, 16] {
                let proof =
                    typed_range_disjoint_from_pointer_evidence(empty, &base, bytes, &context)
                        .expect("an empty footprint cannot change any bytes");
                assert!(matches!(proof, RangeDisjointFromPointerEvidence::Empty));
                assert!(proof.checks(empty, &base, bytes, &context));
                assert!(!proof.checks(changed, &base, bytes, &context));
                assert!(
                    typed_range_disjoint_from_pointer_evidence(changed, &base, bytes, &context,)
                        .is_none()
                );
            }
        }
    }

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/resource_tracker/cell_source/empty_range_frame_tests.rs"
        );
    }
}

#[cfg(test)]
mod cache_independence_tests {
    use super::*;

    #[test]
    fn bounded_cell_source_is_independent_of_history_cache() {
        for stores in [2, 8, 32] {
            let _session = crate::kernel::VerificationSession::enter();
            let address = Pointer {
                block: "bounded-cache-independence".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let before = crate::kernel::intern_memory(
                Memory::new().store(address.clone(), crate::kernel::int32(7)),
            );
            let mut memory = before.memory().clone();
            for index in 0..stores {
                memory = memory.store(
                    address.offset_by_bytes(16 + index * 4),
                    crate::kernel::int32(9),
                );
            }
            let after = crate::kernel::intern_memory(memory);
            let context = PureFactContext::new();
            let query =
                || memory_dag_cell_source_with_stop(&after, &address, 4, &context, false).unwrap();
            let (cold, cold_stop) = query();
            assert_ne!(
                cold.node(),
                &before,
                "one transition must not cross the whole history"
            );
            assert_eq!(
                super::super::cell_last_same_version_point(&after, &address, 4),
                Some(before.clone())
            );
            let (warm, warm_stop) = query();
            assert_eq!(
                warm.node(),
                cold.node(),
                "warming history changed a bounded check at size {stores}"
            );
            assert_eq!(warm_stop, cold_stop);
        }
    }
}

#[cfg(test)]
mod shared_range_bound_evidence_tests {
    use super::*;

    #[test]
    fn range_bounds_retain_shared_sources_and_checked_successor_links() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable =
            |n| KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(n));
        let product = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Multiply,
            [variable(994101), variable(994102)],
        );
        let next = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Add,
            [
                product.clone(),
                KernelTermImport::default().machine(format, &MachineTerm::constant(1)),
            ],
        );
        let observed = SharedMachineIntegerTerm::from_shared(format, product.clone()).unwrap();
        let compare = |a, b| {
            ConditionTerm::integer_less_than(
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, a).unwrap()),
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, b).unwrap()),
            )
        };
        let goal = compare(variable(994103), variable(994104));
        for successor in [false, true] {
            let first = Proposition::ConditionIs(
                compare(
                    variable(994103),
                    if successor {
                        next.clone()
                    } else {
                        product.clone()
                    },
                ),
                true,
            );
            let second = Proposition::ConditionIs(compare(product.clone(), variable(994104)), true);
            let exports = KernelTermExport::machine_export_count();
            let facts = PureFactContext::new()
                .assume_proposition(first.clone())
                .assume_proposition(second.clone());
            let evidence =
                RangeBoundEvidence::for_true_condition(&goal, &facts).expect("shared range path");
            assert_eq!(
                matches!(evidence, RangeBoundEvidence::StrictUpperViaSuccessor { .. }),
                successor
            );
            assert!(evidence.checks(&goal, &facts));
            for source in [first, second] {
                assert!(
                    !evidence.checks(&goal, &PureFactContext::new().assume_proposition(source))
                );
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!observed.has_boxed_operand());
        }
    }
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/resource_tracker/cell_source/shared_range_bound_evidence_tests.rs"
        );
    }
}
