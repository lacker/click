//! The one question both walks ask: **does this recorded step affect this
//! resource?**
//!
//! There used to be two answers at every step kind — one the cell walk gave
//! and one the block walk gave — and a table of the differences between them
//! in `docs/internals/resource-tracker.md`. [`affects`] is now the only place
//! either walk decides, so the table is an answer table rather than a list of
//! inconsistencies, and a new step kind is answered once.
//!
//! The two resources still differ in what they may *spend* on an answer, and
//! that difference is structural here: the cell arm is handed the querying
//! context's facts, because its answer is re-derived per query and retained as
//! a checkable hop; the block arm is handed nothing but the edge, because its
//! answer is embedded in an array argument's name and memoized per
//! `(snapshot, block)`, where one path's assumptions must never reach
//! (`docs/internals/memory-dag.md`).

use super::cell_source::{MemoryDagAssumptionKind, MemoryDagHopJustification};
use super::{Resource, SeparationCheck};
use crate::kernel::memory_provenance::*;
use crate::kernel::primitives::*;
use crate::kernel::reasoning::*;

/// What one recorded step does to one resource.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum StepEffect {
    /// The step acted on the resource itself: the store wrote this cell, the
    /// declaration created this object, the free retired it.
    Affected,
    /// The step is separate from the resource, and this is what justified it.
    /// A walk that keeps evidence keeps this.
    Separate(Separation),
    /// The step's own footprint could not be shown separate from the
    /// resource. The resource may well be unchanged; nothing states it. The
    /// check that would have had to succeed is the repair's target.
    NotShownSeparate(SeparationCheck),
}

/// Why a step was known not to touch a resource.
///
/// The two arms are the two resources' evidence languages, and which arm a
/// caller may receive is decided by which resource it asked about.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum Separation {
    /// One cell, justified by one local hop proof — the form retained
    /// evidence keeps and re-checks.
    Cell(MemoryDagHopJustification),
    /// A whole block, justified by structure alone.
    Block(BlockSeparation),
    /// A stated byte footprint, justified by the step's own write set being
    /// outside every range of it.
    Footprint(FootprintSeparation),
}

/// Why a step was known not to touch the byte ranges a resource fact was
/// derived from.
///
/// This is the evidence language of a footprint, and it is deliberately the
/// narrowest of the three: the answer is spent invalidating resource
/// projections, which no premise records, so it consults no fact context and
/// no ownership. Every variant that names another object is
/// [`PointerBlock::proven_distinct`] plus, where both sides are constant,
/// interval arithmetic inside one object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum FootprintSeparation {
    /// The step writes no byte and moves no claim a range read consults, so
    /// no footprint can be stale because of it.
    WritesNothing,
    /// The written address lies outside every range of the footprint.
    StoreOutsideRanges,
    /// Every range the call or loop declared it may write lies outside every
    /// range of the footprint.
    WriteSetOutsideRanges,
    /// The released allocation lies outside every range of the footprint.
    ReleaseOutsideRanges,
    /// The retired automatic-storage object is proven distinct from the object
    /// every range of the footprint is in.
    ReleaseOfDistinctObject,
}

/// Why a step was known not to touch anything a pure function can observe
/// through a pointer into one block.
///
/// Every variant that names another object is a claim about *objects*, decided
/// by [`PointerBlock::proven_distinct`], never about spellings: a file-scope
/// `global:g` and a parameter's `ExternalArgument` memory are two known,
/// differing spellings that the caller is free to make one object, and every
/// array parameter of one function shares `ExternalArgument`. The one variant
/// that names no object instead rests on the step recording nothing a read can
/// consult, which is a stronger claim, not a weaker one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum BlockSeparation {
    /// The written address is in an object the kernel proves is not this one,
    /// so the one cell it writes, and the one union overlay it drops, are
    /// both outside this block.
    StoreInDistinctBlock,
    /// The object that entered the memory model is proven distinct from this
    /// one, so it has its own `blocks` key and this block's extent entry is
    /// untouched.
    DeclarationOfDistinctBlock,
    /// The object that became live is proven distinct from this one, so its
    /// extent and its fresh-allocation status are its own.
    AllocationOfDistinctBlock,
    /// A pending allocation request was registered or failed. Neither step
    /// changes existing storage; successful allocation is judged separately.
    PendingAllocationMetadata,
    /// The automatic-storage object retired, or the heap allocation released,
    /// is proven distinct from this one, so this block keeps its contents,
    /// extent, liveness and heap status.
    ReleaseOfDistinctBlock,
    /// Every range the call or loop declared it may write lies in an object
    /// proven distinct from this one, and so does everything else the step
    /// forgets on that account.
    WriteSetInDistinctObjects,
}

/// What the querying context offers a walk towards an answer.
///
/// Only the cell arm is given this. The `cross_loop_havoc` flag is the
/// caller's, not the edge's: the naming walk never crosses a loop havoc,
/// while memory-load reasoning may under its own gates.
pub(in crate::kernel) struct Evidence<'a> {
    pub(in crate::kernel) assumptions: &'a PureFactContext,
    pub(in crate::kernel) cross_loop_havoc: bool,
}

/// Whether `step` — the derivation of `produced` — can have changed
/// `resource`, and what justifies the answer.
///
/// The answers, by step kind:
///
/// | Recorded step | A cell | A block, as an array argument |
/// | --- | --- | --- |
/// | `Store` | separate on proven-distinct blocks, a common-base offset inequality, typed `separate(..)` evidence, an explicit range, general distinctness, or two owned members of one composition; affected when the written address is provably the loaded one | separate **only** on `PointerBlock::proven_distinct` |
/// | `BlockDeclared` | separate: it writes nothing | separate when the declared object is proven distinct; affected for this block's own declaration |
/// | `HeapAllocated` | separate when the block differs | separate when the fresh object is proven distinct; affected for this one |
/// | `HeapAllocationPending` / `HeapAllocationFailed` | separate: it writes nothing | separate: no read of any block consults a pending request |
/// | `ContractAllocationClaimsChanged` | separate: it writes nothing | **not shown separate** |
/// | `ContractAllocationRetired` | separate when the possibly released allocation misses the cell, or when the retiring call's own havoc covers the whole allocation | separate only for a proven-distinct object |
/// | `CellsForgotten` | separate: the state is the same | **not shown separate** |
/// | `LocalLifetimeEnded` | separate on proven distinctness | separate when the retired object is proven distinct; affected for this one |
/// | `HeapFreed` | separate on two separation ladders | separate when the released allocation's object is proven distinct; affected when it is this one |
/// | `CallHavoc` | separate on range disjointness, or when a range the caller kept owning holds the cell | separate when every declared range's object is proven distinct |
/// | `LoopHavoc(Some)` | separate under the extended-bridging and explicit-check gates, and never on the naming path | separate when every declared range's object is proven distinct |
/// | `LoopHavoc(None)` | never separate | never separate |
///
/// Two kinds still refuse a block outright, and both for want of a name on the
/// edge: `ContractAllocationClaimsChanged` names no allocation and
/// `CellsForgotten` names no cell, so neither can be shown to leave this
/// block's claims or known values alone.
///
/// The difference that remains by design is *what evidence a resource may
/// spend*: a block may use only the kernel's structural separation, because its
/// answer is shared across proof paths. Where the cell column reads a stated
/// `separate(..)`, an offset inequality or a resource composition, the block
/// column reads only `PointerBlock::proven_distinct` and the write set the edge
/// itself carries.
pub(in crate::kernel) fn affects(
    step: &CMemoryDerivation,
    produced: &SharedCMemory,
    resource: Resource<'_>,
    evidence: &Evidence<'_>,
) -> StepEffect {
    match resource {
        Resource::Cell { pointer, bytes } => cell_effect(step, produced, pointer, bytes, evidence),
        // The block arm is handed no evidence, which is how "assumption-free"
        // is enforced rather than remembered: it has no parameter a fact
        // could arrive through.
        Resource::Block(block) => block_effect(step, block),
        // A footprint's answer is spent dropping resource projections, which
        // record no premise, so it is handed no evidence either.
        Resource::Ranges(ranges) => footprint_effect(step, Some(ranges)),
        Resource::AnyMemory => footprint_effect(step, None),
        // A recorded memory edge says nothing about a model field or a
        // population: they are not memory, and their versions are values in
        // saved states rather than points on this history. Answering
        // `Affected` for every step would be wrong (a store does not replace a
        // model) and `Separate` would be a claim no edge supports, so the one
        // rule has nothing to decide here and these kinds never reach a walk.
        // `resource_tracker::same_at_states` is their whole interface.
        Resource::ModelField { .. } | Resource::Population { .. } => {
            unreachable!("a saved-state resource is answered by `same_at_states`, not by a walk")
        }
    }
}

/// The check that had to succeed for a walk to carry this resource across
/// this step — and so, what a repair has to establish.
///
/// Every `NotShownSeparate` answer below is built from this, and so is the
/// classification of a stop a diagnostic reports, so the check the walk wanted
/// and the check the refusal names are one thing.
pub(in crate::kernel) fn separation_check(
    step: &CMemoryDerivation,
    resource: Resource<'_>,
) -> SeparationCheck {
    match resource {
        Resource::Cell { .. } => match step {
            CMemoryDerivation::CallHavoc { .. }
            | CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(_),
                ..
            } => SeparationCheck::RangeDisjointness,
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            } => SeparationCheck::NoCheckedWriteSet,
            CMemoryDerivation::HeapFreed { .. }
            | CMemoryDerivation::ContractAllocationRetired { .. } => {
                SeparationCheck::HeapAllocationSeparation
            }
            CMemoryDerivation::Store { .. }
            | CMemoryDerivation::CellsSeeded { .. }
            | CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::HeapAllocationFailed { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. }
            | CMemoryDerivation::LocalLifetimeEnded { .. } => SeparationCheck::PointerDistinctness,
        },
        // A block's footprint is everything the object contains, so one check
        // covers its extent, liveness and heap status as well as its cells;
        // only a store has a single address to be distinct from.
        Resource::Block(_) => match step {
            CMemoryDerivation::Store { .. } | CMemoryDerivation::CellsSeeded { .. } => {
                SeparationCheck::PointerDistinctness
            }
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::HeapAllocationFailed { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. }
            | CMemoryDerivation::LocalLifetimeEnded { .. }
            | CMemoryDerivation::HeapFreed { .. }
            | CMemoryDerivation::ContractAllocationRetired { .. }
            | CMemoryDerivation::CallHavoc { .. }
            | CMemoryDerivation::LoopHavoc { .. } => SeparationCheck::WholeBlockAgreement,
        },
        // A footprint is a list of byte ranges, so the check is always "is the
        // step's own write set outside all of them"; only the two kinds that
        // name no write set at all answer otherwise.
        Resource::Ranges(_) | Resource::AnyMemory => match step {
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            } => SeparationCheck::NoCheckedWriteSet,
            CMemoryDerivation::HeapFreed { .. }
            | CMemoryDerivation::ContractAllocationRetired { .. } => {
                SeparationCheck::HeapAllocationSeparation
            }
            CMemoryDerivation::Store { .. }
            | CMemoryDerivation::CellsSeeded { .. }
            | CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::HeapAllocationFailed { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. }
            | CMemoryDerivation::LocalLifetimeEnded { .. }
            | CMemoryDerivation::CallHavoc { .. }
            | CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(_),
                ..
            } => SeparationCheck::RangeDisjointness,
        },
        // No separation check carries a model field or a population across a
        // memory edge, because no memory edge is between them; see `affects`.
        Resource::ModelField { .. } | Resource::Population { .. } => {
            unreachable!("a saved-state resource is answered by `same_at_states`, not by a walk")
        }
    }
}

/// One cell's answer: exactly the walk that named every load variable in the
/// repository before there was a rule, ladder for ladder.
///
/// Each arm answers in one order — a separation ladder first, then "this step
/// is about this very cell", then the check that failed — so that a caller
/// that crosses and a caller that only classifies a stop reach the same
/// verdict from the same premises.
fn cell_effect(
    step: &CMemoryDerivation,
    produced: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    evidence: &Evidence<'_>,
) -> StepEffect {
    let assumptions = evidence.assumptions;
    let hop = |justification| StepEffect::Separate(Separation::Cell(justification));
    let unknown =
        || StepEffect::NotShownSeparate(separation_check(step, Resource::Cell { pointer, bytes }));
    match step {
        CMemoryDerivation::Store {
            pointer: write,
            value,
            ..
        } => store_cell_effect(step, write, value, pointer, bytes, evidence),
        CMemoryDerivation::CellsSeeded { .. } => {
            match seeded_cell_effect(step, pointer, bytes, evidence) {
                SeededCellEffect::Written(..) => StepEffect::Affected,
                SeededCellEffect::Separate(mut hops)
                    if hops.len() == 1
                        && matches!(
                            hops[0],
                            MemoryDagHopJustification::SeededStoresDistinctBlock
                                | MemoryDagHopJustification::SeededStoresMissedByShift
                        ) =>
                {
                    hop(hops.pop().expect("one hop"))
                }
                SeededCellEffect::Separate(hops) => {
                    hop(MemoryDagHopJustification::SeededStores { hops })
                }
                SeededCellEffect::NotShownSeparate => unknown(),
            }
        }
        // Declaring a block, registering unresolved allocation metadata,
        // importing contract allocation claims, or forgetting cached cells
        // writes nothing, so every load is untouched — but only the
        // extended-bridging scope may exploit that: elsewhere these edges
        // must look like the pre-arc absence of an edge.
        CMemoryDerivation::BlockDeclared { .. }
        | CMemoryDerivation::HeapAllocationPending { .. }
        | CMemoryDerivation::HeapAllocationFailed { .. }
        | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
        | CMemoryDerivation::CellsForgotten { .. } => {
            if extended_dag_bridging_active() {
                hop(MemoryDagHopJustification::IntrinsicNoWrite)
            } else {
                unknown()
            }
        }
        CMemoryDerivation::HeapAllocated { block, .. } => {
            if pointer.block != *block && extended_dag_bridging_active() {
                hop(MemoryDagHopJustification::AllocationOfOtherBlock)
            } else if pointer.block == *block {
                StepEffect::Affected
            } else {
                unknown()
            }
        }
        CMemoryDerivation::LocalLifetimeEnded { block, .. } => {
            if pointer.block != *block
                && extended_dag_bridging_active()
                && pointers_proven_distinct_for_memory_resolution(
                    &Pointer {
                        block: block.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    pointer,
                    assumptions,
                )
            {
                hop(MemoryDagHopJustification::LocalLifetimeEndedOfOtherBlock)
            } else if pointer.block == *block {
                StepEffect::Affected
            } else {
                unknown()
            }
        }
        CMemoryDerivation::HeapFreed {
            allocation_base,
            bytes,
            ..
        }
        | CMemoryDerivation::ContractAllocationRetired {
            allocation_base,
            bytes,
            ..
        } => {
            if !extended_dag_bridging_active() {
                // Outside the scope that may read these edges at all, the
                // answer still has to say whether this very cell died with
                // the allocation.
                return if allocation_base.block == pointer.block {
                    StepEffect::Affected
                } else {
                    unknown()
                };
            }
            // A free ends the whole allocation, so what has to miss this
            // cell is the allocation's *extent*, not its base address. The
            // rung that asked `pointers_proven_distinct_for_memory_resolution`
            // about `allocation_base` asked whether the cell is the first
            // element, and answered "this free did not touch it" for
            // `p[3]` — every cell of the block but one. Distinct *blocks*
            // still decide above, and the extent question is the rung below,
            // which is the same predicate the state routes spend
            // (`heap_allocation_proven_separate_from_pointer`).
            if allocation_base.blocks_proven_distinct(pointer) {
                hop(MemoryDagHopJustification::HeapFreeOfDistinctBlock)
            } else if super::cell_source::retirement_inside_its_call_havoc(step) {
                // A contract retirement recorded right after its call's havoc,
                // whose write set covers the whole allocation: no byte of the
                // allocation can be named past that havoc, so the edge itself
                // changes no value (`retirement_inside_its_call_havoc`).
                hop(MemoryDagHopJustification::RetirementInsideItsCallHavoc)
            } else if heap_allocation_proven_separate_from_pointer(
                allocation_base,
                bytes,
                pointer,
                assumptions,
            ) {
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::HeapFreeResourceSeparation,
                ))
            } else if allocation_base.block == pointer.block {
                StepEffect::Affected
            } else {
                unknown()
            }
        }
        CMemoryDerivation::CallHavoc {
            mutable_ranges,
            kept_by_caller,
            ..
        } => {
            if let Some(ranges) = typed_ranges_disjoint_from_pointer_evidence(
                mutable_ranges,
                pointer,
                bytes,
                assumptions,
            ) {
                hop(MemoryDagHopJustification::CallHavocRanges { ranges })
            } else if assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                mutable_ranges,
                pointer,
                produced.memory(),
            ) {
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::CallHavocRangeSeparation,
                ))
            } else if kept_by_caller
                .as_ref()
                .is_some_and(|kept| kept.holds_access(pointer, bytes, assumptions))
            {
                // Memory the caller kept owning outside the transfer: the
                // callee owns none of it, so it wrote none of it. The ranges
                // are the edge's own, spelled in its write-set marker, and
                // placing the access inside one is decided here, in the
                // querying context, as the producer decided it.
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::CallHavocKeptByCaller,
                ))
            } else {
                unknown()
            }
        }
        CMemoryDerivation::LoopHavoc {
            mutable_ranges: Some(mutable_ranges),
            ..
        } => {
            if !evidence.cross_loop_havoc
                || !extended_dag_bridging_active()
                || !explicit_dag_check_active()
            {
                return unknown();
            }
            if let Some(ranges) = typed_ranges_disjoint_from_pointer_evidence(
                mutable_ranges,
                pointer,
                bytes,
                assumptions,
            ) {
                hop(MemoryDagHopJustification::LoopHavocRanges { ranges })
            } else if assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                mutable_ranges,
                pointer,
                produced.memory(),
            ) {
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::LoopHavocRangeSeparation,
                ))
            } else {
                unknown()
            }
        }
        CMemoryDerivation::LoopHavoc {
            mutable_ranges: None,
            ..
        } => unknown(),
    }
}

/// The `Store` arm of [`cell_effect`], for one write. A `CellsSeeded` edge is
/// the same question asked of each store it stands for.
fn store_cell_effect(
    step: &CMemoryDerivation,
    write: &Pointer,
    value: &CValue,
    pointer: &Pointer,
    bytes: u32,
    evidence: &Evidence<'_>,
) -> StepEffect {
    let assumptions = evidence.assumptions;
    let hop = |justification| StepEffect::Separate(Separation::Cell(justification));
    let unknown =
        || StepEffect::NotShownSeparate(separation_check(step, Resource::Cell { pointer, bytes }));
    if write == pointer
        || explicit_dag_check_active()
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
        return StepEffect::Affected;
    }
    // The ladders below prove the two ADDRESSES are different. That
    // is not the question: the question is whether the store writes
    // any of this cell's bytes, and `write + 4` is a different
    // address from `write` while still overwriting the upper half of
    // an eight-byte cell there.
    //
    // A known constant gap between the addresses answers the byte
    // question outright, so take that answer first: overlapping
    // bytes mean the store wrote this cell, whatever the addresses
    // are called.
    let overlap = access_byte_overlap(write, value.byte_width(), pointer, bytes, assumptions);
    if overlap == AccessByteOverlap::Overlaps {
        return StepEffect::Affected;
    }
    // Otherwise the ladders may speak, but the two that rest on
    // address inequality alone may only stand in for byte separation
    // when the gap they establish is at least as wide as the wider
    // access. Where it is not, they are skipped rather than
    // contradicted: the answer becomes "not shown separate", which
    // is both the truth and the refusal that explains itself.
    let address_inequality_separates_bytes = overlap == AccessByteOverlap::Separate;
    // The recorded-range fallback covers writes into a
    // proven-separate region (a buffer store crossed while resolving
    // a struct field); extended-bridging scope only, and under its
    // own capped budget so this advisory walk can never drain the
    // enclosing query's fuel.
    if write.blocks_proven_distinct(pointer) {
        hop(MemoryDagHopJustification::StoreDistinctBlocks)
    } else if address_inequality_separates_bytes
        && pointer_offsets_with_common_base_proven_distinct(write, pointer, assumptions)
    {
        let condition = pointer_offsets_with_common_base_distinctness_condition(write, pointer)
            .expect("a successful common-base check has a cancellation condition");
        let unequal_constants = condition == ConditionTerm::Constant(false);
        if unequal_constants {
            hop(MemoryDagHopJustification::StoreCommonBaseUnequalConstants { condition })
        } else if assumptions.exact_condition_value(&condition) == Some(false) {
            hop(MemoryDagHopJustification::StoreCommonBaseExactInequality { condition })
        } else if let ConditionTerm::Bitvector32Equal(left, right) = &condition
            && let Some(path) = assumptions.exact_signed_order_path_evidence(left, right, true)
        {
            hop(MemoryDagHopJustification::StoreCommonBaseSignedOrder {
                condition,
                path,
                reversed: false,
            })
        } else if let ConditionTerm::Bitvector32Equal(left, right) = &condition
            && let Some(path) = assumptions.exact_signed_order_path_evidence(right, left, true)
        {
            hop(MemoryDagHopJustification::StoreCommonBaseSignedOrder {
                condition,
                path,
                reversed: true,
            })
        } else {
            hop(MemoryDagHopJustification::AssumptionDependent(
                MemoryDagAssumptionKind::StoreCommonBaseDistinctness,
            ))
        }
    } else if explicit_dag_check_active()
        && let Some(justification) =
            typed_store_separated_ranges_evidence(write, pointer, assumptions)
    {
        hop(justification)
    } else if explicit_dag_check_active()
        && assumptions.pointers_proven_disjoint_by_shallow_explicit_range(write, pointer)
    {
        hop(MemoryDagHopJustification::AssumptionDependent(
            MemoryDagAssumptionKind::StoreExplicitRange,
        ))
    } else if extended_dag_bridging_active()
        && address_inequality_separates_bytes
        && pointers_proven_distinct_for_memory_resolution(write, pointer, assumptions)
    {
        hop(MemoryDagHopJustification::AssumptionDependent(
            MemoryDagAssumptionKind::StoreGeneralDistinctness,
        ))
    } else if let Some(justification) =
        owned_composition_store_separated_evidence(write, pointer, assumptions)
    {
        // Last, after every cheaper check: one composition in the
        // context owns the written address and the read address
        // through two different members, so the partition invariant
        // separates them. The evidence names the composition and each
        // side's membership, and the naming walks cannot reach it:
        // they are handed no facts at all, and this reads nothing but
        // facts.
        hop(justification)
    } else {
        unknown()
    }
}

/// What a `CellsSeeded` edge does to one cell.
#[derive(Debug)]
pub(in crate::kernel) enum SeededCellEffect {
    /// One of its stores writes the cell: the store's pointer, and the value
    /// the walk reads.
    Written(Pointer, CValue),
    /// Every store it stands for is separate from the cell, in the order a
    /// walk meets them.
    Separate(Vec<MemoryDagHopJustification>),
    NotShownSeparate,
}

/// The stores of a `CellsSeeded` edge, newest first, asked one by one exactly
/// as a walk over the stores themselves would ask them: the first that writes
/// the cell answers, and the edge is crossed only when every store is
/// separate.
pub(in crate::kernel) fn seeded_cell_effect(
    step: &CMemoryDerivation,
    pointer: &Pointer,
    bytes: u32,
    evidence: &Evidence<'_>,
) -> SeededCellEffect {
    let CMemoryDerivation::CellsSeeded { run, .. } = step else {
        unreachable!("seeded_cell_effect is asked about a CellsSeeded edge");
    };
    crate::instrumentation::record_deterministic_work(1);
    match crate::kernel::reasoning::memory_resolution::run_access(run, pointer) {
        // Every store is in the run's block, which is proven distinct from
        // this one: each is separate by `StoreDistinctBlocks`.
        crate::kernel::reasoning::memory_resolution::RunAccess::DistinctBlock => {
            SeededCellEffect::Separate(vec![MemoryDagHopJustification::SeededStoresDistinctBlock])
        }
        // Common atoms: every store at an unequal constant shift whose bytes
        // miss the access is separate by `StoreCommonBaseUnequalConstants`,
        // and the newest store whose bytes meet it writes the cell.
        crate::kernel::reasoning::memory_resolution::RunAccess::Shift(shift) => {
            let (low, high) = crate::kernel::reasoning::memory_resolution::run_elements_meeting(
                run,
                shift,
                i64::from(bytes),
            );
            match (low..high)
                .rev()
                .find(|index| !run.holes().contains(*index))
            {
                Some(index) => SeededCellEffect::Written(run.slot_pointer(index), run.value(index)),
                None => SeededCellEffect::Separate(vec![
                    MemoryDagHopJustification::SeededStoresMissedByShift,
                ]),
            }
        }
        crate::kernel::reasoning::memory_resolution::RunAccess::Scaled { .. }
        | crate::kernel::reasoning::memory_resolution::RunAccess::Other => {
            seeded_cell_effect_store_by_store(step, run, pointer, bytes, evidence)
        }
    }
}

/// The stores of a `CellsSeeded` edge asked one by one, newest first.
fn seeded_cell_effect_store_by_store(
    step: &CMemoryDerivation,
    run: &crate::kernel::primitives::CellRun,
    pointer: &Pointer,
    bytes: u32,
    evidence: &Evidence<'_>,
) -> SeededCellEffect {
    let mut hops = Vec::new();
    for index in run.live_indexes_newest_first() {
        crate::instrumentation::record_deterministic_work(1);
        let write = run.slot_pointer(index);
        let value = run.value(index);
        match store_cell_effect(step, &write, &value, pointer, bytes, evidence) {
            StepEffect::Affected => return SeededCellEffect::Written(write, value),
            StepEffect::Separate(Separation::Cell(justification)) => hops.push(justification),
            StepEffect::Separate(_) | StepEffect::NotShownSeparate(_) => {
                return SeededCellEffect::NotShownSeparate;
            }
        }
    }
    SeededCellEffect::Separate(hops)
}

/// One whole block's answer: separate means separate from **everything the
/// block contains**, decided from the edge alone.
///
/// A pure function reading through a pointer into `block` is opaque, so it may
/// read any cell of the block, and an `unfold` states its defining equation
/// with the fold lowered at the live state while the application keeps the
/// argument it was built with. Two program points may therefore share one
/// argument only when they agree on everything such a body can observe
/// through the pointer: the contents of every cell of the block, the union
/// overlays in it, its own entry in `blocks` (the extent a read is checked
/// against), its liveness (the ended-local set and the heap's live, freed and
/// pending status for it), and the zeroed status that decides what an
/// unwritten byte reads as.
///
/// The per-kind argument, against the producers in
/// `src/kernel/primitives/memory_state.rs`:
///
/// * `Store` into an object proven distinct from this one writes exactly one
///   cell and drops union overlays only at that same pointer, both outside
///   this block; it touches `blocks`, the ended-local set and the heap not at
///   all. A merely different spelling is not enough, and a `Symbolic` block on
///   either side separates from nothing:
///   `mdtests/global_may_alias_an_array_argument.md` is the caller that makes
///   a global and an array parameter one object, and carrying a fact across
///   the store to `g[0]` there would hold `g[0] == 5` and `g[0] == 1` at one
///   point.
/// * `BlockDeclared` inserts one entry in `blocks` under the declared block's
///   own key and changes nothing else — no cell, no overlay, no ended-local
///   entry, no heap status. An object proven distinct from this one therefore
///   has a different key, so this block's own extent entry is the same entry it
///   was, and everything a body reads through the pointer is untouched. This is
///   why `int32 t;` now carries a fact about `a` as a whole, as it has always
///   carried `a[0] == 5`.
/// * `HeapAllocated` inserts the fresh object's extent under its own key and
///   marks that one base live and uninitialized-or-zeroed. An object proven
///   distinct from this block therefore leaves this block's extent, contents,
///   liveness and zeroed status alone. A `Heap` block is a fresh object, which
///   is the `proven_distinct` arm this rides.
/// * `HeapAllocationPending` records a requested allocation that has no
///   address yet: `pending_allocations`, and `zeroed_pending_allocations` for a
///   `calloc`. Nothing that decides what a read of a block sees consults
///   either map — not its extent, not its cells, not its liveness, not its
///   zeroed status — so this step is separate from every block, with no
///   distinctness claim needed. That is also why the cell arm crosses it. The
///   moment the request resolves is a `HeapAllocated` edge, judged on its own,
///   and a pending *reallocation* records no edge at all, so a walk stops at
///   it for want of a derivation.
/// * `ContractAllocationRetired` leaves deallocation undecided but forgets
///   cached content and status for the consumed allocation. Its affected
///   footprint is judged with the same separation bounds as `HeapFreed`;
///   unlike a definite free, it creates no deallocation tombstone.
/// * `HeapFreed` moves one allocation from live to deallocated, drops its
///   uninitialized and zeroed status, removes its extent, and drops the cells
///   that allocation may contain — which `heap_allocation_may_contain_pointer`
///   confines to that allocation's own block. `LocalLifetimeEnded` removes the
///   retired block's extent, its cells and its overlays, and adds it to the
///   ended-local set, all under that block's key. An object proven distinct
///   from this block keeps everything this block contains. Neither is a
///   spelling test: a contract-imported allocation can be a subrange of
///   `ExternalArgument` memory, so freeing it is not separate from an array
///   parameter, and every array parameter of one function shares that block.
/// * `CallHavoc` and `LoopHavoc` with a checked write set are the two steps
///   that stand for code this rule cannot see, so what they *do* to the
///   snapshot has to be enumerated rather than assumed. A call havoc forgets
///   every cell that is neither in a `local:` block nor proven disjoint from
///   the declared ranges, drops the zeroed reading of every allocation those
///   ranges may reach, and inserts its two marker blocks. A loop havoc forgets
///   every cell outside the preserved scalar-local blocks and the
///   loan-protected ones, and inserts its marker block; it changes no extent,
///   no ended-local entry and no heap status at all. When every declared range
///   lies in an object proven distinct from this block:
///     * its cells keep their values across a call havoc, because block
///       distinctness is the first thing `range_proven_disjoint_from_pointer`
///       decides, so the retention test holds for every one of them;
///     * its zeroed status survives, because
///       `heap_allocation_may_contain_pointer` needs equal blocks before it
///       will call an allocation written;
///     * the marker blocks are fresh keys, so this block's extent entry is
///       untouched;
///     * and a loop havoc does drop this block's cached values, which is a
///       change of *form* only. The argument names the older snapshot, and its
///       known values stay true of the real object precisely because the
///       declared write set excludes that object; forgetting what the newer
///       snapshot knew removes knowledge from the newer state rather than
///       changing the object.
///
///   The declared write set is the same thing a cell fact already trusts to be
///   the complete footprint of the code behind the edge; a block trusts it no
///   further. Because the write set is checked and path-independent it may be
///   read off the interned edge, which is what separates it from a stated
///   `separate(..)`.
/// * `ContractAllocationClaimsChanged` and `CellsForgotten` still stop the
///   walk, and for the same reason as each other: the edge names no object.
///   The first moves live, uninitialized and zeroed-prefix claims for *some*
///   allocation, and a contract claim may cover a subrange of
///   `ExternalArgument` memory — the very object an array parameter points
///   into. The second is a form change with the same state, but nothing on the
///   edge says which cells it dropped. Recording what they concern is what
///   would settle either.
/// * `LoopHavoc` without a write set never crosses: a body that may write
///   anything it can reach has no footprint to be separate from.
///
/// No arm consults a fact, a stated `separate(..)` or ownership, because this
/// answer is memoized per `(snapshot, block)` and an interned edge is shared
/// by paths with different assumptions.
fn block_effect(step: &CMemoryDerivation, block: &PointerBlock) -> StepEffect {
    let unknown = || StepEffect::NotShownSeparate(separation_check(step, Resource::Block(block)));
    // An arm that names one object answers in one order: proven distinct from
    // this block, else this very block, else the check that failed.
    let one_object = |changed: &PointerBlock, separation| {
        if changed.proven_distinct(block) {
            StepEffect::Separate(Separation::Block(separation))
        } else if changed == block {
            StepEffect::Affected
        } else {
            unknown()
        }
    };
    // A kind whose answer is still "stop", whatever it names. Naming this
    // block is still `Affected`, so a refusal keeps saying "changed" rather
    // than "may have changed" about the block's own declaration or release.
    let stops = |named: Option<&PointerBlock>| {
        if named == Some(block) {
            StepEffect::Affected
        } else {
            unknown()
        }
    };
    match step {
        CMemoryDerivation::Store { pointer, .. } => {
            one_object(&pointer.block, BlockSeparation::StoreInDistinctBlock)
        }
        // Every store of a run writes the run's own block.
        CMemoryDerivation::CellsSeeded { run, .. } => {
            one_object(&run.base().block, BlockSeparation::StoreInDistinctBlock)
        }
        CMemoryDerivation::BlockDeclared {
            block: declared, ..
        } => one_object(declared, BlockSeparation::DeclarationOfDistinctBlock),
        CMemoryDerivation::HeapAllocated {
            block: allocated, ..
        } => one_object(allocated, BlockSeparation::AllocationOfDistinctBlock),
        CMemoryDerivation::HeapAllocationPending { .. }
        | CMemoryDerivation::HeapAllocationFailed { .. } => StepEffect::Separate(
            Separation::Block(BlockSeparation::PendingAllocationMetadata),
        ),
        CMemoryDerivation::HeapFreed {
            allocation_base, ..
        }
        | CMemoryDerivation::ContractAllocationRetired {
            allocation_base, ..
        } => one_object(
            &allocation_base.block,
            BlockSeparation::ReleaseOfDistinctBlock,
        ),
        CMemoryDerivation::LocalLifetimeEnded { block: retired, .. } => {
            one_object(retired, BlockSeparation::ReleaseOfDistinctBlock)
        }
        // It writes no bytes, but the claims it moves are what authorize a
        // read, and the edge names no allocation they could belong to.
        CMemoryDerivation::ContractAllocationClaimsChanged { .. } => stops(None),
        // The state is the same but the cell map is not, and the edge names no
        // cell, so nothing says the dropped values were not this block's.
        CMemoryDerivation::CellsForgotten { .. } => stops(None),
        CMemoryDerivation::CallHavoc { mutable_ranges, .. }
        | CMemoryDerivation::LoopHavoc {
            mutable_ranges: Some(mutable_ranges),
            ..
        } => {
            if mutable_ranges
                .iter()
                .all(|range| range.base().block.proven_distinct(block))
            {
                StepEffect::Separate(Separation::Block(
                    BlockSeparation::WriteSetInDistinctObjects,
                ))
            } else {
                unknown()
            }
        }
        // Without a checked write set the edge is an unconditional barrier:
        // nothing can be shown separate from a body that may write anything it
        // can reach.
        CMemoryDerivation::LoopHavoc {
            mutable_ranges: None,
            ..
        } => stops(None),
    }
}

/// One stated byte footprint's answer: separate means the step's own write set
/// is outside every range of it, decided from the edge alone.
///
/// `ranges` is `None` for a footprint the kernel could not name
/// ([`Resource::AnyMemory`]), and then only the kinds that write no byte are
/// separate — nothing bounds what such a footprint covers, so there is no
/// range to be outside of.
///
/// The per-kind argument is the cell arm's, restricted to what a footprint may
/// spend. Like the block arm this reads no fact context, but for a different
/// reason: the answer is not embedded in a name, it is spent *removing* a
/// resource fact, and removing one is only ever sound to do more often. So the
/// arm is free to be coarser than the cell arm and is: it treats a write
/// through a block that may be any object
/// ([`crate::kernel::primitives::resource_algebra::memory_block_may_alias`]) as
/// affecting every footprint, rather than asking a range whether that block is
/// proven distinct from it.
///
/// * `Store` is separate when the written bytes miss every range of the
///   footprint, which
///   [`crate::kernel::primitives::resource_algebra::memory_range_overlaps_pointer`]
///   decides by block distinctness first and then by constant byte intervals.
/// * `CallHavoc` and `LoopHavoc` with a checked write set are separate when
///   every declared range misses every range of the footprint. The declared
///   write set is the complete footprint of the code behind the edge, which is
///   what a cell fact already trusts it to be.
/// * `HeapFreed` is separate when the released bytes miss every range. A
///   symbolic byte count is read as the whole address space, so it misses
///   nothing.
/// * `LocalLifetimeEnded` is separate when the retired object is proven
///   distinct from the object every range is in. It drops that block's cells
///   and extent and nothing else.
/// * `BlockDeclared`, `HeapAllocated`, `HeapAllocationPending`,
///   `ContractAllocationClaimsChanged` and `CellsForgotten` write no byte of
///   any pre-existing object, so no stated footprint can be stale because of
///   them. `HeapAllocated` belongs here because a projection's footprint is
///   stated over objects that already existed; the fresh object's own bytes
///   are in no range of it.
/// * `LoopHavoc` without a write set is an unconditional barrier.
fn footprint_effect(step: &CMemoryDerivation, ranges: Option<&[CMemoryRange]>) -> StepEffect {
    let resource = match ranges {
        Some(ranges) => Resource::Ranges(ranges),
        None => Resource::AnyMemory,
    };
    let unknown = || StepEffect::NotShownSeparate(separation_check(step, resource));
    let separate = |separation| StepEffect::Separate(Separation::Footprint(separation));
    // A step that writes no byte and moves no claim is separate from every
    // footprint, named or not.
    if matches!(
        step,
        CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::HeapAllocationFailed { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. }
    ) {
        return separate(FootprintSeparation::WritesNothing);
    }
    // Nothing bounds an unnamed footprint, so every other kind may reach it.
    let Some(ranges) = ranges else {
        return unknown();
    };
    match step {
        CMemoryDerivation::Store { pointer, value, .. } => {
            if !memory_block_may_alias(&pointer.block)
                && !ranges
                    .iter()
                    .any(|range| memory_range_overlaps_pointer(range, pointer, value.byte_width()))
            {
                separate(FootprintSeparation::StoreOutsideRanges)
            } else {
                unknown()
            }
        }
        CMemoryDerivation::CellsSeeded { .. } => {
            let stores = step.seeded_stores().expect("a CellsSeeded edge");
            if stores.iter().all(|(pointer, value)| {
                !memory_block_may_alias(&pointer.block)
                    && !ranges.iter().any(|range| {
                        memory_range_overlaps_pointer(range, pointer, value.byte_width())
                    })
            }) {
                separate(FootprintSeparation::StoreOutsideRanges)
            } else {
                unknown()
            }
        }
        CMemoryDerivation::CallHavoc { mutable_ranges, .. }
        | CMemoryDerivation::LoopHavoc {
            mutable_ranges: Some(mutable_ranges),
            ..
        } => {
            if !mutable_ranges
                .iter()
                .any(|written| memory_block_may_alias(&written.base().block))
                && !ranges.iter().any(|footprint| {
                    mutable_ranges
                        .iter()
                        .any(|written| memory_ranges_overlap(footprint, written))
                })
            {
                separate(FootprintSeparation::WriteSetOutsideRanges)
            } else {
                unknown()
            }
        }
        CMemoryDerivation::HeapFreed {
            allocation_base,
            bytes,
            ..
        }
        | CMemoryDerivation::ContractAllocationRetired {
            allocation_base,
            bytes,
            ..
        } => {
            if !memory_block_may_alias(&allocation_base.block)
                && !ranges.iter().any(|range| {
                    memory_range_overlaps_pointer(
                        range,
                        allocation_base,
                        bytes.as_const().unwrap_or(u32::MAX),
                    )
                })
            {
                separate(FootprintSeparation::ReleaseOutsideRanges)
            } else {
                unknown()
            }
        }
        CMemoryDerivation::LocalLifetimeEnded { block, .. } => {
            let retired = Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            if ranges
                .iter()
                .all(|range| range.base().blocks_proven_distinct(&retired))
            {
                separate(FootprintSeparation::ReleaseOfDistinctObject)
            } else {
                unknown()
            }
        }
        CMemoryDerivation::LoopHavoc {
            mutable_ranges: None,
            ..
        } => unknown(),
        // Answered above, before the footprint had to be named.
        CMemoryDerivation::BlockDeclared { .. }
        | CMemoryDerivation::HeapAllocated { .. }
        | CMemoryDerivation::HeapAllocationPending { .. }
        | CMemoryDerivation::HeapAllocationFailed { .. }
        | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
        | CMemoryDerivation::CellsForgotten { .. } => separate(FootprintSeparation::WritesNothing),
    }
}
