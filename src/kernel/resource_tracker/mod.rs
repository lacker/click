//! The resource tracker: the one place in the kernel that knows **which
//! resources are known to be the same at which program points**.
//!
//! A *resource* is a piece of mutable state, or part of one: today a memory
//! cell, or a memory block as a pure function reads it through an array
//! argument. A *program point* is a point on the current proof path,
//! identified by the memory snapshot the kernel had reached there. The
//! tracker answers two questions about them:
//!
//! * [`last_same`] — walking back from a point, where was this resource last
//!   known to be the same, and what stopped the walk there;
//! * [`same`] — are these two points known to hold the same version of this
//!   resource, and if not, was it **changed** (a step wrote it) or is it
//!   merely **unknown** (a step could not be shown separate from it).
//!
//! Everything else is built on those. Naming a term that reads memory embeds
//! the oldest point its resource is the same as, so equal names mean equal
//! terms; that is [`last_same_point`], and it is the only form on the hot
//! path. [`explain`] adds nothing to the answer — it names the step that
//! broke the chain so a refusal can say what went wrong.
//!
//! **What the tracker is not.** It has no ownership rules: it never decides
//! who may read or write a resource, and it has no overlap logic of its own —
//! it asks the resource and assumption layers whether two footprints are
//! separate. It never looks inside a proposition: a term matters to it only
//! through the resources the term reads. And it does not search. Each
//! question is a bounded walk over recorded history with exact lookups, so it
//! gives the same answer wherever it is asked.
//!
//! **The soundness corridor.** The tracker reads `CMemoryDerivation` edges,
//! which are interned first-wins: one edge can be shared by proof paths with
//! different assumptions, so an edge may carry only what is true on *every*
//! path that could produce that snapshot. A write set qualifies; a
//! path-dependent separation does not. That is why the naming walks below are
//! assumption-free — an answer that is embedded in a name and memoized per
//! snapshot must not depend on one path's facts — and why the crossing
//! evidence is re-derived in the querying context instead of being recorded
//! (`docs/internals/memory-dag.md`, `docs/internals/resource-tracker.md`).
//!
//! **Known inconsistencies between the two walks** are tabulated in
//! `docs/internals/resource-tracker.md`; they are deliberately preserved
//! here, not unified.

pub(in crate::kernel) mod cell_source;

use crate::kernel::memory_provenance::with_extended_dag_bridging;
use crate::kernel::primitives::*;
use cell_source::{MemoryDagCell, memory_dag_cell_source};

/// A point on the current proof path, named by the memory snapshot the
/// kernel had reached there: `entry`, a `mark`ed label, or "here".
///
/// Program points are compared by interned snapshot identity, so two points
/// that the execution reached by different routes to the same state are one
/// point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProgramPoint(SharedCMemory);

impl ProgramPoint {
    pub(crate) fn at(snapshot: &SharedCMemory) -> Self {
        Self(snapshot.clone())
    }

    /// The point a `CMemory` value stands at, interning it first. Callers
    /// that already hold an interned snapshot use [`ProgramPoint::at`].
    pub(crate) fn of_memory(memory: &CMemory) -> Self {
        Self(crate::kernel::intern_c_memory(memory.clone()))
    }

    pub(crate) fn snapshot(&self) -> &SharedCMemory {
        &self.0
    }

    pub(crate) fn memory(&self) -> &CMemory {
        self.0.memory()
    }

    /// True when this point is later in the recorded history than `other`.
    /// Snapshot ids strictly increase along derivation edges, so comparing
    /// them orders two points of one arena without walking.
    fn is_later_than(&self, other: &Self) -> bool {
        let (arena, id) = self.0.arena_id();
        let (other_arena, other_id) = other.0.arena_id();
        arena == other_arena && id > other_id
    }
}

/// A resource the tracker can answer about, borrowed from the caller so that
/// asking costs nothing on the naming path.
///
/// New kinds — a byte range, a struct extent, a composite instance, a local —
/// are added as variants here and in [`OwnedResource`]; callers that only
/// build and pass a resource do not change.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Resource<'a> {
    /// One memory cell, at this address.
    Cell(&'a Pointer),
    /// A whole memory block, as a pure function reads it through an array
    /// argument: the footprint is every cell reachable through the pointer.
    Block(&'a PointerBlock),
}

impl Resource<'_> {
    pub(crate) fn to_owned(self) -> OwnedResource {
        match self {
            Self::Cell(pointer) => OwnedResource::Cell(pointer.clone()),
            Self::Block(block) => OwnedResource::Block(block.clone()),
        }
    }
}

/// [`Resource`] owned, for the answers a diagnostic keeps past the question.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OwnedResource {
    Cell(Pointer),
    Block(PointerBlock),
}

impl OwnedResource {
    pub(crate) fn as_resource(&self) -> Resource<'_> {
        match self {
            Self::Cell(pointer) => Resource::Cell(pointer),
            Self::Block(block) => Resource::Block(block),
        }
    }

    /// The address to spell this resource by in a diagnostic.
    pub(crate) fn pointer(&self) -> Option<&Pointer> {
        match self {
            Self::Cell(pointer) => Some(pointer),
            Self::Block(_) => None,
        }
    }

    pub(crate) fn block(&self) -> &PointerBlock {
        match self {
            Self::Cell(pointer) => &pointer.block,
            Self::Block(block) => block,
        }
    }
}

/// Where a resource was last known to be the same, walking back from a
/// point, and what stopped the walk there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LastSame {
    pub(crate) point: ProgramPoint,
    pub(crate) stopped_by: Stop,
}

/// What happened at the point a walk stopped at, and why it stopped there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Stop {
    pub(crate) change: Change,
    pub(crate) reason: StopReason,
}

impl Stop {
    /// Reads the stop off the point the walk stopped at: the step below a
    /// point is the edge the walk did not cross. Computing this is what a
    /// diagnostic asks for and the naming path never pays for.
    fn at_point(point: &ProgramPoint, resource: Resource<'_>, wrote_it: bool) -> Self {
        let Some(derivation) = point.snapshot().derivation() else {
            return Self {
                change: Change::BeginningOfHistory,
                reason: StopReason::HistoryEnds,
            };
        };
        let change = Change::of_derivation(derivation.as_ref());
        let reason = if wrote_it || change.affects_directly(resource) {
            StopReason::Affected
        } else {
            StopReason::NotShownSeparate(SeparationCheck::for_step(&change, resource))
        };
        Self { change, reason }
    }
}

/// The state-changing step recorded at a program point, in the tracker's
/// terms rather than the DAG's.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Change {
    /// One address was assigned.
    Store { pointer: Pointer },
    /// A call may have written the ranges it declared.
    Call { ranges: Vec<CMemoryRange> },
    /// A loop may have written the ranges its checked effect summary
    /// declared, or anything at all when it declared none.
    Loop { ranges: Option<Vec<CMemoryRange>> },
    /// One heap allocation's lifetime ended.
    Free { allocation: Pointer },
    /// A fresh heap block became live.
    Allocation { block: PointerBlock },
    /// An allocation request has no resolved address yet.
    AllocationPending,
    /// Allocation claims moved across a contract boundary.
    ContractAllocationClaims,
    /// A block entered the memory model.
    Declaration { block: PointerBlock },
    /// An automatic-storage object was retired.
    LifetimeEnd { block: PointerBlock },
    /// Cached cell values were dropped; the state is the same, the form is
    /// not.
    CellsForgotten,
    /// Nothing: the recorded history starts here.
    BeginningOfHistory,
}

impl Change {
    fn of_derivation(derivation: &CMemoryDerivation) -> Self {
        match derivation {
            CMemoryDerivation::Store { pointer, .. } => Self::Store {
                pointer: pointer.clone(),
            },
            CMemoryDerivation::CallHavoc { mutable_ranges, .. } => Self::Call {
                ranges: mutable_ranges.clone(),
            },
            CMemoryDerivation::LoopHavoc { mutable_ranges, .. } => Self::Loop {
                ranges: mutable_ranges.clone(),
            },
            CMemoryDerivation::HeapFreed {
                allocation_base, ..
            } => Self::Free {
                allocation: allocation_base.clone(),
            },
            CMemoryDerivation::HeapAllocated { block, .. } => Self::Allocation {
                block: block.clone(),
            },
            CMemoryDerivation::HeapAllocationPending { .. } => Self::AllocationPending,
            CMemoryDerivation::ContractAllocationClaimsChanged { .. } => {
                Self::ContractAllocationClaims
            }
            CMemoryDerivation::BlockDeclared { block, .. } => Self::Declaration {
                block: block.clone(),
            },
            CMemoryDerivation::LocalLifetimeEnded { block, .. } => Self::LifetimeEnd {
                block: block.clone(),
            },
            CMemoryDerivation::CellsForgotten { .. } => Self::CellsForgotten,
        }
    }

    /// True when the step is about this very resource rather than about
    /// something the tracker failed to separate from it: a store inside the
    /// resource's own block, or a lifetime event on that block.
    fn affects_directly(&self, resource: Resource<'_>) -> bool {
        let block = match resource {
            Resource::Cell(pointer) => &pointer.block,
            Resource::Block(block) => block,
        };
        match self {
            // A cell's own address is decided by the walk, which pins the
            // value; reaching here means only the blocks agree, and for one
            // cell that is not yet a claim that this cell was written.
            Self::Store { pointer } => {
                matches!(resource, Resource::Block(_)) && &pointer.block == block
            }
            Self::Allocation {
                block: changed_block,
            }
            | Self::Declaration {
                block: changed_block,
            }
            | Self::LifetimeEnd {
                block: changed_block,
            } => changed_block == block,
            Self::Free { allocation } => &allocation.block == block,
            Self::Call { .. }
            | Self::Loop { .. }
            | Self::AllocationPending
            | Self::ContractAllocationClaims
            | Self::CellsForgotten
            | Self::BeginningOfHistory => false,
        }
    }
}

/// Why a walk stopped where it did.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StopReason {
    /// The step acted on this resource itself: the store wrote this cell, the
    /// allocation created this object, the lifetime end retired it.
    Affected,
    /// The step's own footprint could not be shown separate from the
    /// resource, by this check.
    NotShownSeparate(SeparationCheck),
    /// Nothing earlier is recorded.
    HistoryEnds,
}

/// The check that would have had to succeed for the walk to carry the
/// resource across the step — and so, what a repair has to establish.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SeparationCheck {
    /// The written address had to be proven to address a different object,
    /// or a different offset in the same one.
    PointerDistinctness,
    /// Every range the step may write had to be proven disjoint from the
    /// resource.
    RangeDisjointness,
    /// The freed allocation had to be proven separate from the resource.
    HeapAllocationSeparation,
    /// The step carries no checked write set at all, so nothing can be shown
    /// separate from it.
    NoCheckedWriteSet,
    /// A fact about a block as a whole is only carried across a step that
    /// leaves the block's cells, overlays, extent, liveness and heap status
    /// all untouched, which only a store the kernel proves is in another
    /// object does. Stated separations are not consulted, because this
    /// answer is embedded in a name and memoized per snapshot.
    WholeBlockAgreement,
}

impl SeparationCheck {
    fn for_step(change: &Change, resource: Resource<'_>) -> Self {
        if matches!(resource, Resource::Block(_)) {
            return match change {
                Change::Store { .. } => Self::PointerDistinctness,
                _ => Self::WholeBlockAgreement,
            };
        }
        match change {
            Change::Store { .. } => Self::PointerDistinctness,
            Change::Call { .. } => Self::RangeDisjointness,
            Change::Loop { ranges } => {
                if ranges.is_some() {
                    Self::RangeDisjointness
                } else {
                    Self::NoCheckedWriteSet
                }
            }
            Change::Free { .. } => Self::HeapAllocationSeparation,
            Change::Allocation { .. }
            | Change::Declaration { .. }
            | Change::LifetimeEnd { .. }
            | Change::AllocationPending
            | Change::ContractAllocationClaims
            | Change::CellsForgotten
            | Change::BeginningOfHistory => Self::PointerDistinctness,
        }
    }
}

/// Whether one resource is known to hold the same version at two points.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Sameness {
    Same,
    /// A step between the two points wrote the resource.
    Changed {
        at: ProgramPoint,
        by: Stop,
    },
    /// A step between the two points could not be shown to leave the
    /// resource alone. The resource may well be unchanged; nothing states it.
    Unknown {
        at: ProgramPoint,
        why: Stop,
    },
}

impl Sameness {
    /// The step that broke the chain, for the two answers that have one.
    pub(crate) fn blocking_step(&self) -> Option<(&ProgramPoint, &Stop)> {
        match self {
            Self::Same => None,
            Self::Changed { at, by } => Some((at, by)),
            Self::Unknown { at, why } => Some((at, why)),
        }
    }
}

/// How many steps a bounded report walks before it stops counting.
const MAX_REPORTED_STEPS: usize = 64;

/// One resource's history between two program points, reduced to what a
/// refusal may say: the resource, the answer, and how many recorded steps
/// the tracker crossed after the blocking one. Never the memory itself.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Explanation {
    pub(crate) resource: OwnedResource,
    pub(crate) here: ProgramPoint,
    /// The other point, when the question had one.
    pub(crate) there: Option<ProgramPoint>,
    pub(crate) outcome: Sameness,
    /// Recorded steps between the blocking step and `here`, capped at
    /// [`MAX_REPORTED_STEPS`]. The tracker crossed all of them, so a
    /// renderer may say they do not touch the resource.
    pub(crate) crossed_after: usize,
}

/// The point a resource read at `at` is named by: the oldest point it is
/// known to be the same at. This is the naming path — memoized, and the only
/// tracker call on the hot path.
pub(crate) fn last_same_point(resource: Resource<'_>, at: &ProgramPoint) -> Option<ProgramPoint> {
    match resource {
        Resource::Cell(pointer) => cell_last_same_point(at.snapshot(), pointer).map(ProgramPoint),
        Resource::Block(block) => Some(ProgramPoint(block_last_same_point(at.snapshot(), block))),
    }
}

/// [`last_same_point`] with the stop information the naming path discards.
///
/// The walk itself is the same one; only the classification of where it
/// stopped is new, and it is computed here rather than recorded, so that the
/// naming path does no extra work.
pub(crate) fn last_same(resource: Resource<'_>, at: &ProgramPoint) -> Option<LastSame> {
    match resource {
        Resource::Cell(pointer) => {
            let cell = cell_source_for_naming(at.snapshot(), pointer)?;
            let point = ProgramPoint(cell.node().clone());
            let wrote_it = matches!(cell, MemoryDagCell::Stored { .. });
            let stopped_by = Stop::at_point(&point, resource, wrote_it);
            Some(LastSame { point, stopped_by })
        }
        Resource::Block(block) => {
            let point = ProgramPoint(block_last_same_point(at.snapshot(), block));
            let stopped_by = Stop::at_point(&point, resource, false);
            Some(LastSame { point, stopped_by })
        }
    }
}

/// Whether the resource is known to hold the same version at both points.
///
/// Two points agree exactly when they name the same version, which is what
/// the naming path already decides. When they do not, the later of the two
/// stopped first, and the step below its answer is the one that broke the
/// chain.
pub(crate) fn same(resource: Resource<'_>, left: &ProgramPoint, right: &ProgramPoint) -> Sameness {
    if left == right {
        return Sameness::Same;
    }
    let (Some(left_same), Some(right_same)) =
        (last_same(resource, left), last_same(resource, right))
    else {
        return Sameness::Unknown {
            at: left.clone(),
            why: Stop {
                change: Change::BeginningOfHistory,
                reason: StopReason::HistoryEnds,
            },
        };
    };
    if left_same.point == right_same.point {
        return Sameness::Same;
    }
    let blocking = if left_same.point.is_later_than(&right_same.point) {
        left_same
    } else {
        right_same
    };
    match blocking.stopped_by.reason {
        StopReason::Affected => Sameness::Changed {
            at: blocking.point,
            by: blocking.stopped_by,
        },
        StopReason::NotShownSeparate(_) | StopReason::HistoryEnds => Sameness::Unknown {
            at: blocking.point,
            why: blocking.stopped_by,
        },
    }
}

/// [`same`], with the bounded context a refusal prints.
pub(crate) fn explain(
    resource: Resource<'_>,
    here: &ProgramPoint,
    there: &ProgramPoint,
) -> Explanation {
    let outcome = same(resource, here, there);
    explanation_for(resource, here, Some(there.clone()), outcome)
}

/// What the resource's version at one point rests on, with no second point
/// to compare against: the step that ended the last stretch of agreement.
/// A resource nothing has touched since the beginning of the history
/// answers [`Sameness::Same`].
pub(crate) fn explain_last_same(resource: Resource<'_>, here: &ProgramPoint) -> Explanation {
    let outcome = match last_same(resource, here) {
        Some(last) => match last.stopped_by.reason {
            StopReason::HistoryEnds => Sameness::Same,
            StopReason::Affected => Sameness::Changed {
                at: last.point,
                by: last.stopped_by,
            },
            StopReason::NotShownSeparate(_) => Sameness::Unknown {
                at: last.point,
                why: last.stopped_by,
            },
        },
        None => Sameness::Same,
    };
    explanation_for(resource, here, None, outcome)
}

fn explanation_for(
    resource: Resource<'_>,
    here: &ProgramPoint,
    there: Option<ProgramPoint>,
    outcome: Sameness,
) -> Explanation {
    let crossed_after = outcome
        .blocking_step()
        .map(|(at, _)| recorded_steps_between(here, at))
        .unwrap_or_default();
    Explanation {
        resource: resource.to_owned(),
        here: here.clone(),
        there,
        outcome,
        crossed_after,
    }
}

/// Recorded steps from `from` back to `to`, bounded. Zero when `to` is not
/// an ancestor of `from`, which is what the two answers that report no step
/// already say.
fn recorded_steps_between(from: &ProgramPoint, to: &ProgramPoint) -> usize {
    let mut current = from.snapshot().clone();
    for crossed in 0..MAX_REPORTED_STEPS {
        if &current == to.snapshot() {
            return crossed;
        }
        let Some(derivation) = current.derivation() else {
            return 0;
        };
        current = derivation.base().clone();
    }
    MAX_REPORTED_STEPS
}

/// The tracker's memo tables, cleared with the other per-verification
/// canonical-form caches (`VerificationSession`).
pub(crate) fn clear_version_memos() {
    CELL_EPOCH_MEMO.with(|memo| memo.borrow_mut().clear());
    BLOCK_EPOCH_MEMO.with(|memo| memo.borrow_mut().clear());
}

/// The snapshot a pure function's array argument names: the latest one that
/// still agrees with `memory` about everything such a function can observe
/// through a pointer into `block`.
///
/// An `Integer` function over an array carries its snapshot in the argument
/// itself, and that argument is compared structurally, so a fact about
/// `icount(array-ref(S, p), ..)` matches a goal about
/// `icount(array-ref(S', p), ..)` only when `S` and `S'` are the same
/// snapshot. Every step of the program makes a new snapshot, so without a
/// canonical form such a fact dies at the next statement even when that
/// statement cannot touch the array. This is the array-argument counterpart
/// of [`cell_last_same_point`], which is why a plain `a[k] == 5` survives the
/// same step today.
///
/// **What the epoch must guarantee.** The function is opaque, so it may read
/// any cell reachable through `p`, and an `unfold` states its defining
/// equation with the fold lowered at the *live* state while the application
/// keeps this argument. The epoch is therefore only sound when `memory` and
/// the returned snapshot agree on everything the body can see through `p`:
/// the contents of every cell of `block`, the union overlays in `block`, the
/// block's own extent and liveness, and the heap status that decides whether
/// a read of `block` is defined at all.
///
/// **How that is obtained.** By crossing one edge kind and stopping at every
/// other. A `Store` into a block *proven distinct* from `block` writes exactly
/// one cell, in another object, and drops union overlays only at that same
/// pointer; it therefore changes nothing about `block`, its overlays, the
/// `blocks` map, the ended-local set, or the heap. Crossing only that edge
/// makes the agreement above hold by construction, with no snapshot
/// comparison and no fact context — which is also what lets the answer be
/// memoized per interned snapshot and block.
///
/// **Why the separation has to be proven, not spelled.** This walk is
/// assumption-free: it has no `PureFactContext` to read a `separate(..)`
/// clause or a pointer disequality out of, so the only separation available to
/// it is the kernel's structural one, [`PointerBlock::proven_distinct`].
/// Anything weaker is unsound here. "Both identities are known and they are
/// written differently" is weaker: a parameter's `ExternalArgument` memory and
/// a file-scope `global:g` are two known, differing spellings that the caller
/// is free to make one object, and
/// `mdtests/global_may_alias_an_array_argument.md` is the caller that does.
/// Carrying an array fact across the store to `g[0]` there would hold
/// `g[0] == 5` and `g[0] == 1` at one point.
///
/// The arms of `proven_distinct` that an array argument actually reaches are
/// each a claim about objects rather than names. A `local:` block is storage
/// this function declared, so memory reached through a parameter cannot be it
/// — this is the arm `array_fact_survives_a_store_to_a_local` rides. A `Heap`
/// block was allocated in this function's own view, so it is a fresh object
/// distinct from everything already named. Two different `Concrete` blocks are
/// two distinct declared objects, so a store to one global does not disturb a
/// fact about another. A `Symbolic` block is a logic variable later facts may
/// constrain to any address, so it separates from nothing and stops the walk
/// on either side, which also makes an entry gate on the subject unnecessary:
/// a subject this walk cannot separate from anything simply never crosses.
///
/// Every `CMemoryDerivation` variant and its decision:
///
/// * `Store` — cross **only** when the written pointer's block is proven
///   distinct from `block`. Merely differing spellings, and a symbolic block on
///   either side, stop the walk.
/// * `BlockDeclared` — stops. It changes the `blocks` map, which decides the
///   extent a read of `block` is checked against.
/// * `HeapAllocated`, `HeapAllocationPending`, `HeapFreed` — stop. They
///   change heap status, which decides whether a read is defined, is zeroed,
///   or has a pending reallocation.
/// * `ContractAllocationClaimsChanged` — stops. It writes no bytes, but the
///   claims it moves are what authorize a read.
/// * `CellsForgotten` — stops. The state is the same but the cell map is not,
///   so a read that resolves concretely at one end resolves symbolically at
///   the other, and the two argument snapshots would name forms this rule
///   has no business equating.
/// * `LocalLifetimeEnded` — stops. It retires an object every alias to which
///   must stop reading, and this walk decides no aliases.
/// * `LoopHavoc`, `CallHavoc` — stop. Both are exactly the barriers whose
///   write sets must be justified in a querying context, which this walk
///   does not have.
///
/// The walk is assumption-free and terminates: snapshot ids strictly decrease
/// along `base`. It always reports an epoch, because a subject it can separate
/// from nothing crosses nothing and so answers `memory` itself.
fn block_last_same_point(memory: &SharedCMemory, block: &PointerBlock) -> SharedCMemory {
    let recorded = |key: &(crate::kernel::SharedCMemory, PointerBlock)| {
        BLOCK_EPOCH_MEMO.with(|memo| memo.borrow().get(key).cloned())
    };
    let key = (memory.clone(), block.clone());
    if let Some(hit) = recorded(&key) {
        return hit;
    }
    // Every snapshot on the way to the epoch has the same epoch, so each one
    // is recorded when the walk ends. Without that, a proof that uses one
    // array fact after each of N steps walks the whole chain N times and
    // costs N^2 hops; with it, a walk from a new snapshot meets a recorded
    // answer after one hop, so the whole proof costs one hop per snapshot.
    // `an_array_fact_carried_across_local_stores_scales_linearly` is the
    // regression that tells those apart.
    let mut path = Vec::new();
    let epoch = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "array-ref block epoch walk",
        || {
            let mut current = memory.clone();
            loop {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(hit) = recorded(&(current.clone(), block.clone())) {
                    return hit;
                }
                let Some(derivation) = current.derivation() else {
                    return current;
                };
                let crossable = match derivation.as_ref() {
                    CMemoryDerivation::Store { pointer, .. } => {
                        pointer.block.proven_distinct(block)
                    }
                    CMemoryDerivation::BlockDeclared { .. }
                    | CMemoryDerivation::HeapAllocated { .. }
                    | CMemoryDerivation::HeapAllocationPending { .. }
                    | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
                    | CMemoryDerivation::HeapFreed { .. }
                    | CMemoryDerivation::CellsForgotten { .. }
                    | CMemoryDerivation::LocalLifetimeEnded { .. }
                    | CMemoryDerivation::LoopHavoc { .. }
                    | CMemoryDerivation::CallHavoc { .. } => false,
                };
                if !crossable {
                    return current;
                }
                path.push(current.clone());
                current = derivation.base().clone();
            }
        },
    );
    BLOCK_EPOCH_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len().saturating_add(path.len()) >= 100_000 {
            memo.clear();
        }
        for node in path {
            memo.insert((node, block.clone()), epoch.clone());
        }
        memo.insert(key, epoch.clone());
    });
    epoch
}

thread_local! {
    static BLOCK_EPOCH_MEMO: std::cell::RefCell<
        std::collections::HashMap<
            (crate::kernel::SharedCMemory, PointerBlock),
            crate::kernel::SharedCMemory,
        >,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

#[cfg(test)]
pub(crate) fn block_epoch_memo_len() -> usize {
    BLOCK_EPOCH_MEMO.with(|memo| memo.borrow().len())
}

/// The point one cell's load variable is named by: the snapshot at which the
/// loaded cell was last written or entered the world, walked assumption-free
/// over recorded edges. Snapshots that differ only by effects the recorded
/// history proves disjoint from the cell share a point, so load variables
/// stay stable across them.
fn cell_last_same_point(memory: &SharedCMemory, pointer: &Pointer) -> Option<SharedCMemory> {
    // Assumption-free and a function of the interned snapshot, the pointer,
    // and the recorded edges, so the answer is memoized per query.
    let key = (memory.clone(), pointer.clone());
    if let Some(hit) = CELL_EPOCH_MEMO.with(|memo| memo.borrow().get(&key).cloned()) {
        return hit;
    }
    let epoch = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "cell epoch walk",
        || cell_source_for_naming(memory, pointer).map(|cell| cell.node().clone()),
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

/// The cell walk exactly as naming runs it: no ambient facts, and loop havoc
/// never crossed. Declaring a block, forgetting cached cells, or allocating
/// another block writes nothing; a name must not change across them, so the
/// naming walk crosses those edges unconditionally.
///
/// Every tracker answer about a cell goes through here, so a diagnostic
/// explains the name the term actually got rather than a walk run under
/// different flags.
fn cell_source_for_naming(memory: &SharedCMemory, pointer: &Pointer) -> Option<MemoryDagCell> {
    with_extended_dag_bridging(|| {
        memory_dag_cell_source(memory, pointer, &PureFactContext::new(), false)
    })
}

thread_local! {
    static CELL_EPOCH_MEMO: std::cell::RefCell<
        std::collections::HashMap<(crate::kernel::SharedCMemory, Pointer), Option<crate::kernel::SharedCMemory>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// One read of a resource by a term: which resource, and the program point
/// the term reads it at.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ResourceRead {
    pub(crate) resource: OwnedResource,
    pub(crate) point: ProgramPoint,
}

/// The resources a proposition reads, in traversal order.
///
/// This is a diagnostic-only traversal of the shapes a memory-reading fact
/// takes. A shape it does not know contributes no read, so a refusal built on
/// it simply has nothing to say — it never says something false.
pub(crate) fn reads_of_proposition(fact: &Proposition) -> Vec<ResourceRead> {
    let mut reads = Vec::new();
    collect_proposition_reads(fact, &mut reads);
    reads
}

fn collect_proposition_reads(fact: &Proposition, reads: &mut Vec<ResourceRead>) {
    match fact {
        Proposition::ConditionIs(condition, _) => collect_condition_reads(condition, reads),
        Proposition::Equal(left, right) => {
            collect_term_reads(left, reads);
            collect_term_reads(right, reads);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_reads(left, reads);
            collect_proposition_reads(right, reads);
        }
        Proposition::Not(inner) => collect_proposition_reads(inner, reads),
        Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
            collect_proposition_reads(body, reads);
        }
        _ => {}
    }
}

fn collect_term_reads(term: &Term, reads: &mut Vec<ResourceRead>) {
    match term {
        Term::Condition(condition) => collect_condition_reads(condition, reads),
        Term::Bitvector32(term) => collect_bitvector_reads(term, reads),
        Term::Integer(term) => collect_integer_term_reads(term, reads),
        Term::PointerOffset(offset) => collect_offset_reads(offset, reads),
        Term::Algebraic(term) => {
            term.for_each_bitvector_term(|term| collect_bitvector_reads(term, reads));
        }
        Term::CValue(value) => collect_value_reads(value, reads),
        _ => {}
    }
}

/// The resource two propositions read at different program points, when the
/// only difference between them is which version they read.
///
/// Both sides must read the same resources in the same order; a pair that
/// differs in anything else is a different proposition, not another version
/// of this one.
pub(crate) fn version_mismatch(
    left: &Proposition,
    right: &Proposition,
) -> Option<(OwnedResource, ProgramPoint, ProgramPoint)> {
    let left_reads = reads_of_proposition(left);
    let right_reads = reads_of_proposition(right);
    if left_reads.is_empty() || left_reads.len() != right_reads.len() {
        return None;
    }
    if left_reads
        .iter()
        .zip(&right_reads)
        .any(|(left, right)| left.resource != right.resource)
    {
        return None;
    }
    left_reads
        .into_iter()
        .zip(right_reads)
        .find(|(left, right)| left.point != right.point)
        .map(|(left, right)| (left.resource, left.point, right.point))
}

/// Whether a proposition reads any resource at all. A fact that reads none
/// has no version to differ about, which is what lets a diagnostic rule out
/// this whole class before looking at anything else.
pub(crate) fn reads_any_resource(fact: &Proposition) -> bool {
    !reads_of_proposition(fact).is_empty()
}

/// The resource one proposition reads at two different program points — the
/// shape an equation between a term and its own earlier value takes.
pub(crate) fn internal_version_mismatch(
    fact: &Proposition,
) -> Option<(OwnedResource, ProgramPoint, ProgramPoint)> {
    let reads = reads_of_proposition(fact);
    reads.iter().enumerate().find_map(|(index, read)| {
        reads[index + 1..]
            .iter()
            .find(|later| later.resource == read.resource && later.point != read.point)
            .map(|later| {
                (
                    read.resource.clone(),
                    read.point.clone(),
                    later.point.clone(),
                )
            })
    })
}

fn push_read(reads: &mut Vec<ResourceRead>, resource: OwnedResource, point: ProgramPoint) {
    let read = ResourceRead { resource, point };
    if !reads.contains(&read) {
        reads.push(read);
    }
}

fn collect_condition_reads(condition: &ConditionTerm, reads: &mut Vec<ResourceRead>) {
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_bitvector_term(|term| collect_bitvector_reads(term, reads));
            right.for_each_bitvector_term(|term| collect_bitvector_reads(term, reads));
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            collect_integer_reads(left, reads);
            collect_integer_reads(right, reads);
        }
        ConditionTerm::Float32(float) | ConditionTerm::Float64(float) => {
            float.for_each_bitvector_term(|term| collect_bitvector_reads(term, reads));
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_offset_reads(left, reads);
            collect_offset_reads(right, reads);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_offset_reads(&left.offset, reads);
            collect_offset_reads(&right.offset, reads);
        }
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
            collect_bitvector_reads(left, reads);
            collect_bitvector_reads(right, reads);
        }
    }
}

fn collect_offset_reads(offset: &PointerOffsetTerm, reads: &mut Vec<ResourceRead>) {
    for value in offset.scaled_values() {
        collect_bitvector_reads(value, reads);
    }
}

fn collect_value_reads(value: &CValue, reads: &mut Vec<ResourceRead>) {
    match value {
        CValue::Pointer(pointer) => collect_offset_reads(&pointer.pointer().offset, reads),
        _ => {
            if let Some(term) = crate::kernel::spec::c_value_bitvector_term(value) {
                collect_bitvector_reads(&term, reads);
            }
        }
    }
}

fn collect_integer_reads(term: &SharedIntegerTerm, reads: &mut Vec<ResourceRead>) {
    collect_integer_term_reads(term.as_ref(), reads);
}

fn collect_integer_term_reads(term: &IntegerTerm, reads: &mut Vec<ResourceRead>) {
    match term {
        IntegerTerm::Machine(machine) => {
            collect_bitvector_reads(machine.value(), reads);
        }
        IntegerTerm::Negate(inner) => collect_integer_reads(inner, reads),
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_integer_reads(left, reads);
            collect_integer_reads(right, reads);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_argument_reads(argument, reads);
            }
        }
        IntegerTerm::RangeFold { initial, body, .. } => {
            collect_integer_reads(initial, reads);
            collect_integer_reads(body, reads);
        }
        IntegerTerm::Constant(_)
        | IntegerTerm::Variable(_)
        | IntegerTerm::AlgebraicMatch { .. } => {}
    }
}

fn collect_argument_reads(argument: &PureFunctionArgument, reads: &mut Vec<ResourceRead>) {
    match argument {
        PureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            if let CValue::Pointer(pointer) = pointer {
                push_read(
                    reads,
                    OwnedResource::Block(pointer.pointer().block.clone()),
                    ProgramPoint::of_memory(memory),
                );
            }
        }
        PureFunctionArgument::Integer(term) => collect_integer_reads(term, reads),
        PureFunctionArgument::Algebraic(term) => {
            term.for_each_bitvector_term(|term| collect_bitvector_reads(term, reads));
        }
        PureFunctionArgument::Value(value) => collect_value_reads(value, reads),
    }
}

fn collect_bitvector_reads(term: &Bitvector32Term, reads: &mut Vec<ResourceRead>) {
    match term {
        Bitvector32Term::MemoryLoad(memory, pointer) => push_read(
            reads,
            OwnedResource::Cell(pointer.as_ref().clone()),
            ProgramPoint::at(memory),
        ),
        // A load variable reads the cell it was minted for, at the point its
        // name embeds.
        Bitvector32Term::Variable(variable) => {
            if let Some((memory, pointer)) =
                crate::kernel::registered_load_origin_for_variable(variable)
            {
                push_read(
                    reads,
                    OwnedResource::Cell(pointer),
                    ProgramPoint::at(&memory),
                );
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
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_bitvector_reads(left, reads);
            collect_bitvector_reads(right, reads);
        }
        Bitvector32Term::BitwiseNot(inner)
        | Bitvector32Term::Int64From32(inner)
        | Bitvector32Term::UInt64From32(inner)
        | Bitvector32Term::UInt32From64(inner)
        | Bitvector32Term::Int64FromUInt32(inner)
        | Bitvector32Term::UInt64FromInt32(inner)
        | Bitvector32Term::UInt64FromInt64(inner) => collect_bitvector_reads(inner, reads),
        Bitvector32Term::If {
            then_term,
            else_term,
            ..
        } => {
            collect_bitvector_reads(then_term, reads);
            collect_bitvector_reads(else_term, reads);
        }
        // Every other shape either reads no memory or reaches it only
        // through a form this bounded traversal does not enter.
        _ => {}
    }
}

#[cfg(test)]
mod tests;
