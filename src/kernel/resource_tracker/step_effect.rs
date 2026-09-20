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
}

/// Why a step was known not to touch anything a pure function can observe
/// through a pointer into one block.
///
/// Every variant is a claim about *objects*, decided by
/// [`PointerBlock::proven_distinct`], never about spellings: a file-scope
/// `global:g` and a parameter's `ExternalArgument` memory are two known,
/// differing spellings that the caller is free to make one object, and every
/// array parameter of one function shares `ExternalArgument`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum BlockSeparation {
    /// The written address is in an object the kernel proves is not this one,
    /// so the one cell it writes, and the one union overlay it drops, are
    /// both outside this block.
    StoreInDistinctBlock,
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
/// | `Store` | separate on proven-distinct blocks, a common-base offset inequality, typed `separate(..)` evidence, an explicit range, or general distinctness; affected when the written address is provably the loaded one | separate **only** on `PointerBlock::proven_distinct` |
/// | `BlockDeclared` | separate: it writes nothing | **not shown separate** |
/// | `HeapAllocated` | separate when the block differs | **not shown separate** |
/// | `HeapAllocationPending` | separate: it writes nothing | **not shown separate** |
/// | `ContractAllocationClaimsChanged` | separate: it writes nothing | **not shown separate** |
/// | `CellsForgotten` | separate: the state is the same | **not shown separate** |
/// | `LocalLifetimeEnded` | separate on proven distinctness | **not shown separate** |
/// | `HeapFreed` | separate on three separation ladders | **not shown separate** |
/// | `CallHavoc` | separate on range disjointness | **not shown separate** |
/// | `LoopHavoc(Some)` | separate under the extended-bridging and explicit-check gates, and never on the naming path | **not shown separate** |
/// | `LoopHavoc(None)` | never separate | never separate |
///
/// The block column's blanket refusals are the two walks' remaining
/// differences, carried over unchanged from when they were two separate sets
/// of hard-coded answers. Each one is a finding to settle on its own now that
/// there is one place to settle it in.
///
/// The difference that will remain is *what evidence a resource may spend*: a
/// block may use only the kernel's structural separation, because its answer
/// is shared across proof paths.
pub(in crate::kernel) fn affects(
    step: &CMemoryDerivation,
    produced: &SharedCMemory,
    resource: Resource<'_>,
    evidence: &Evidence<'_>,
) -> StepEffect {
    match resource {
        Resource::Cell(pointer) => cell_effect(step, produced, pointer, evidence),
        // The block arm is handed no evidence, which is how "assumption-free"
        // is enforced rather than remembered: it has no parameter a fact
        // could arrive through.
        Resource::Block(block) => block_effect(step, block),
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
        Resource::Cell(_) => match step {
            CMemoryDerivation::CallHavoc { .. }
            | CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(_),
                ..
            } => SeparationCheck::RangeDisjointness,
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            } => SeparationCheck::NoCheckedWriteSet,
            CMemoryDerivation::HeapFreed { .. } => SeparationCheck::HeapAllocationSeparation,
            CMemoryDerivation::Store { .. }
            | CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. }
            | CMemoryDerivation::LocalLifetimeEnded { .. } => SeparationCheck::PointerDistinctness,
        },
        // A block's footprint is everything the object contains, so one check
        // covers its extent, liveness and heap status as well as its cells;
        // only a store has a single address to be distinct from.
        Resource::Block(_) => match step {
            CMemoryDerivation::Store { .. } => SeparationCheck::PointerDistinctness,
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. }
            | CMemoryDerivation::LocalLifetimeEnded { .. }
            | CMemoryDerivation::HeapFreed { .. }
            | CMemoryDerivation::CallHavoc { .. }
            | CMemoryDerivation::LoopHavoc { .. } => SeparationCheck::WholeBlockAgreement,
        },
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
    evidence: &Evidence<'_>,
) -> StepEffect {
    let assumptions = evidence.assumptions;
    let hop = |justification| StepEffect::Separate(Separation::Cell(justification));
    let unknown = || StepEffect::NotShownSeparate(separation_check(step, Resource::Cell(pointer)));
    match step {
        CMemoryDerivation::Store { pointer: write, .. } => {
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
            // The recorded-range fallback covers writes into a
            // proven-separate region (a buffer store crossed while resolving
            // a struct field); extended-bridging scope only, and under its
            // own capped budget so this advisory walk can never drain the
            // enclosing query's fuel.
            if write.blocks_proven_distinct(pointer) {
                hop(MemoryDagHopJustification::StoreDistinctBlocks)
            } else if pointer_offsets_with_common_base_proven_distinct(write, pointer, assumptions)
            {
                let condition =
                    pointer_offsets_with_common_base_distinctness_condition(write, pointer)
                        .expect("a successful common-base check has a cancellation condition");
                let unequal_constants = condition == ConditionTerm::Constant(false);
                if unequal_constants {
                    hop(MemoryDagHopJustification::StoreCommonBaseUnequalConstants { condition })
                } else if assumptions.exact_condition_value(&condition) == Some(false) {
                    hop(MemoryDagHopJustification::StoreCommonBaseExactInequality { condition })
                } else if let ConditionTerm::Bitvector32Equal(left, right) = &condition
                    && let Some(path) =
                        assumptions.exact_signed_order_path_evidence(left, right, true)
                {
                    hop(MemoryDagHopJustification::StoreCommonBaseSignedOrder {
                        condition,
                        path,
                        reversed: false,
                    })
                } else if let ConditionTerm::Bitvector32Equal(left, right) = &condition
                    && let Some(path) =
                        assumptions.exact_signed_order_path_evidence(right, left, true)
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
                && pointers_proven_distinct_for_memory_resolution(write, pointer, assumptions)
            {
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::StoreGeneralDistinctness,
                ))
            } else {
                unknown()
            }
        }
        // Declaring a block, registering unresolved allocation metadata,
        // moving contract allocation claims, or forgetting cached cells
        // writes nothing, so every load is untouched — but only the
        // extended-bridging scope may exploit that: elsewhere these edges
        // must look like the pre-arc absence of an edge.
        CMemoryDerivation::BlockDeclared { .. }
        | CMemoryDerivation::HeapAllocationPending { .. }
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
            if allocation_base.blocks_proven_distinct(pointer) {
                hop(MemoryDagHopJustification::HeapFreeOfDistinctBlock)
            } else if pointers_proven_distinct_for_memory_resolution(
                allocation_base,
                pointer,
                assumptions,
            ) {
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::HeapFreeGeneralDistinctness,
                ))
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
        CMemoryDerivation::CallHavoc { mutable_ranges, .. } => {
            if let Some(ranges) =
                typed_ranges_disjoint_from_pointer_evidence(mutable_ranges, pointer, assumptions)
            {
                hop(MemoryDagHopJustification::CallHavocRanges { ranges })
            } else if assumptions.ranges_proven_disjoint_from_pointer_for_frame(
                mutable_ranges,
                pointer,
                produced.memory(),
            ) {
                hop(MemoryDagHopJustification::AssumptionDependent(
                    MemoryDagAssumptionKind::CallHavocRangeSeparation,
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
            if let Some(ranges) =
                typed_ranges_disjoint_from_pointer_evidence(mutable_ranges, pointer, assumptions)
            {
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
/// * Every other kind stops the walk, exactly as it did before there was one
///   rule. Each blanket refusal below is a finding to settle on its own.
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
        // It changes the `blocks` map, which decides the extent a read of
        // this block is checked against.
        CMemoryDerivation::BlockDeclared {
            block: declared, ..
        } => stops(Some(declared)),
        // They change heap status, which decides whether a read is defined,
        // is zeroed, or has a pending reallocation.
        CMemoryDerivation::HeapAllocated {
            block: allocated, ..
        } => stops(Some(allocated)),
        CMemoryDerivation::HeapAllocationPending {
            allocation_base, ..
        } => stops(Some(&allocation_base.block)),
        CMemoryDerivation::HeapFreed {
            allocation_base, ..
        } => stops(Some(&allocation_base.block)),
        // It retires an object every alias to which must stop reading, and
        // this rule decides no aliases.
        CMemoryDerivation::LocalLifetimeEnded { block: retired, .. } => stops(Some(retired)),
        // It writes no bytes, but the claims it moves are what authorize a
        // read.
        CMemoryDerivation::ContractAllocationClaimsChanged { .. } => stops(None),
        // The state is the same but the cell map is not, so a read that
        // resolves concretely at one end resolves symbolically at the other.
        CMemoryDerivation::CellsForgotten { .. } => stops(None),
        // Both are exactly the barriers whose write sets have to be justified
        // in a querying context, which this rule does not have.
        CMemoryDerivation::CallHavoc { .. } | CMemoryDerivation::LoopHavoc { .. } => stops(None),
    }
}
