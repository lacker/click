//! The resource tracker: the one place in the kernel that knows **which
//! resources are known to be the same at which program points**.
//!
//! A *resource* is a piece of mutable state: a memory cell, an observed
//! memory block, or a model field. A surface *program point* is a code
//! location or proof mark used by `at(point, expression)`. It selects a
//! recorded symbolic execution state on the current proof path.
//!
//! Memory reasoning uses a *version point*, [`VersionPoint`], identified by
//! an interned memory state. The assumption-free naming walk selects the
//! earliest version point it can prove unchanged for the chosen resource.
//! Distinct program points may select the same version point for one cell.
//! The tracker answers two questions about version points:
//!
//! * [`last_same`] — walking back from a point, where was this resource last
//!   known to be the same, and what stopped the walk there;
//! * [`same`] — are these two points known to hold the same version of this
//!   resource, and if not, was it **changed** (a step wrote it) or is it
//!   merely **unknown** (a step could not be shown separate from it).
//!
//! A C read whose cell no cached value answers also asks
//! [`cell_value_on_path`], the one question answered under one path's facts;
//! it names nothing, so its answer never enters a term shared across paths.
//!
//! Everything else is built on those. Naming a term that reads memory embeds
//! the oldest point its resource is the same as, so equal names mean equal
//! terms; that is [`last_same_version_point`], and it is the only form on the hot
//! path. [`explain`] adds nothing to the answer — it names the step that
//! broke the chain so a refusal can say what went wrong.
//!
//! **Two kinds of point, because there are two kinds of version.** A memory
//! resource's version is named by its version point, where an operation
//! changed it or prevented the assumption-free walk from crossing. A read
//! term can embed that version point. A model field's version is the
//! **value stored in the instance**, so its points are whole saved states — [`StatePoint`], a
//! handle to the state the kernel already keeps at `entry`, at a `mark` or at
//! an iteration, never a copy. That kind has no naming walk and no recorded
//! edge to walk; [`same_at_states`] is its whole interface, and it is two
//! keyed lookups and one term comparison.
//!
//! **What the tracker is not.** It has no ownership rules: it never decides
//! who may read or write a resource, and it has no overlap logic of its own —
//! it asks the resource and assumption layers whether two footprints are
//! separate. It never looks inside a proposition: a term matters to it only
//! through the resources the term reads. And it does not search. Each
//! question is a bounded walk over recorded history with exact lookups, so it
//! gives the same answer wherever it is asked.
//!
//! **The soundness corridor.** The tracker reads `MemoryDerivation` edges,
//! which are interned first-wins: one edge can be shared by proof paths with
//! different assumptions, so an edge may carry only what is true on *every*
//! path that could produce that state. A write set qualifies; a
//! path-dependent separation does not. That is why the naming walks below are
//! assumption-free — an answer that is embedded in a name and memoized per
//! state must not depend on one path's facts — and why the crossing
//! evidence is re-derived in the querying context instead of being recorded
//! (`docs/internals/memory-dag.md`, `docs/internals/resource-tracker.md`).
//!
//! **One rule decides every step.** Both walks ask
//! [`step_effect::affects`] — "does this recorded step affect this resource?"
//! — so a step kind has one answer per resource rather than one per walk. The
//! answer table is in that rule's doc comment and in
//! `docs/internals/resource-tracker.md`.

pub(in crate::kernel) mod cell_source;
pub(in crate::kernel) mod step_effect;

use crate::kernel::memory_provenance::with_extended_dag_bridging;
use crate::kernel::primitives::*;
use crate::kernel::unary_term;
use crate::kernel::{MachineCastSpelling, cast_term};

/// A position in memory history, identified by an interned memory state.
/// The naming walk selects a resource's version point from these positions.
///
/// This is not the surface program point passed to `at`: two distinct
/// program points can select the same version point for a cell. Equality
/// here compares interned memory states, not source locations or all values
/// at a location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VersionPoint(SharedMemory);

impl VersionPoint {
    pub(crate) fn at(memory: &SharedMemory) -> Self {
        Self(memory.clone())
    }

    /// The point a `Memory` value stands at, interning it first. Callers
    /// that already hold an interned state use [`VersionPoint::at`].
    pub(crate) fn of_memory(memory: &Memory) -> Self {
        Self(crate::kernel::intern_memory(memory.clone()))
    }

    pub(crate) fn shared_memory(&self) -> &SharedMemory {
        &self.0
    }

    pub(crate) fn memory(&self) -> &Memory {
        self.0.memory()
    }

    /// True when this point is later in the recorded history than `other`.
    /// Memory state ids strictly increase along derivation edges, so comparing
    /// them orders two points of one arena without walking.
    pub(crate) fn is_later_than(&self, other: &Self) -> bool {
        let (arena, id) = self.0.arena_id();
        let (other_arena, other_id) = other.0.arena_id();
        arena == other_arena && id > other_id
    }
}

/// A state point for a resource that does not live in memory: a borrowed
/// handle to the whole execution state the kernel already holds there — the
/// contract's entry state, a `mark`ed state out of `RecordedStates`, a
/// loop's iteration state, or the live one.
///
/// It is a handle, never a copy. The tracker reads one keyed entry out of the
/// state and nothing else, and two points are one point when they are one
/// state: nothing compares two states' contents, because a resource context's
/// `PartialEq` walks its facts and no tracker answer may cost that.
///
/// Memory keeps [`VersionPoint`] instead, whose identity is one interned
/// state id. That is what the naming path needs and what a load variable's
/// name embeds; a whole state is neither interned nor ordered, so it could not
/// serve there.
#[derive(Clone, Copy)]
pub(crate) struct StatePoint<'a> {
    state: &'a ExecutionState,
}

impl<'a> StatePoint<'a> {
    pub(crate) fn at(state: &'a ExecutionState) -> Self {
        Self { state }
    }

    pub(crate) fn state(self) -> &'a ExecutionState {
        self.state
    }

    /// True when the two handles are the same state. Pointer identity only:
    /// a `Same` answer this gives is exact, and where it says nothing the
    /// two keyed lookups below decide.
    fn is_one_state(self, other: Self) -> bool {
        std::ptr::eq(self.state, other.state)
    }
}

impl std::fmt::Debug for StatePoint<'_> {
    /// A state's own `Debug` is the whole symbolic state. A point is a
    /// handle, and a diagnostic that printed one would be the repeated raw
    /// memory state the tooling rules forbid.
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("StatePoint(<saved state>)")
    }
}

/// A resource the tracker can answer about, borrowed from the caller so that
/// asking costs nothing on the naming path.
///
/// New kinds — a byte range, a struct extent, a composite instance, a local —
/// are added as variants here and in [`OwnedResource`]; callers that only
/// build and pass a resource do not change.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TrackedResource<'a> {
    /// One memory cell: this many bytes, starting at this address.
    ///
    /// The width is part of the resource because separation is a question
    /// about bytes, not addresses. A store at `p + 4` is a different
    /// *address* from `p` by every address test there is, and it still
    /// overwrites the upper half of an eight-byte cell at `p`. A cell asked
    /// about without its width would be separated from that store and keep
    /// its old value across it.
    ///
    /// Read descriptors use their recorded access width, or their kind's
    /// conservative width when unobserved. Callers holding only an address
    /// pass [`MAX_SCALAR_ACCESS_BYTES`]. Over-stating a width can only shrink
    /// the separated set, never grow it.
    Cell { pointer: &'a Pointer, bytes: u32 },
    /// A whole memory block, as a pure function reads it through an array
    /// argument: the footprint is every cell reachable through the pointer.
    Block(&'a PointerBlock),
    /// The byte ranges a resource fact was derived from: the footprint a
    /// projection's support states, as a list of ranges.
    Ranges(&'a [MemoryRange]),
    /// A memory footprint the kernel cannot name — a composite core, or a
    /// projection whose address is itself read from memory through a shape the
    /// footprint walk does not enter. Every step that can write memory affects
    /// it, because nothing bounds what it covers.
    AnyMemory,
    /// One model field of one resource instance: which instance, by the
    /// identity a contract's binder names, and which field of its schema.
    ///
    /// A field's **version is the value stored in the instance**. There is no
    /// generation counter and no new per-instance state: an instance that
    /// survived a call keeps its identity and gets fresh field variables, so
    /// the stored value already distinguishes the versions.
    ModelField {
        identity: Variable,
        children: &'a [String],
        field_index: usize,
    },
}

/// The width a cell resource stands in when its caller cannot name one.
///
/// A load term carries its own read's kind, but a cell resource stands for
/// every read of its address, and a caller holding only the address must
/// assume the widest scalar the kernel can load. Over-stating the width only
/// shrinks the separated set, so this is the fail-closed reading of a width
/// the caller cannot name.
pub(crate) fn widest_scalar_access_bytes() -> u32 {
    u32::try_from(crate::kernel::MAX_SCALAR_ACCESS_BYTES)
        .expect("the widest scalar access is a small positive byte count")
}

impl TrackedResource<'_> {
    pub(crate) fn to_owned(self) -> OwnedResource {
        match self {
            Self::Cell { pointer, bytes } => OwnedResource::Cell {
                pointer: pointer.clone(),
                bytes,
            },
            Self::Block(block) => OwnedResource::Block(block.clone()),
            Self::Ranges(ranges) => OwnedResource::Ranges(ranges.to_vec()),
            Self::AnyMemory => OwnedResource::AnyMemory,
            Self::ModelField {
                identity,
                children,
                field_index,
            } => OwnedResource::ModelField {
                identity,
                children: children.to_vec(),
                field_index,
            },
        }
    }

    /// Whether this resource's versions are values in a saved state rather
    /// than points on the memory history. Those kinds have no naming path and
    /// no recorded edge; [`same_at_states`] is their whole interface.
    pub(crate) fn lives_in_a_saved_state(self) -> bool {
        matches!(self, Self::ModelField { .. })
    }
}

/// [`TrackedResource`] owned, for the answers a diagnostic keeps past the question.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OwnedResource {
    Cell {
        pointer: Pointer,
        bytes: u32,
    },
    Block(PointerBlock),
    Ranges(Vec<MemoryRange>),
    AnyMemory,
    ModelField {
        identity: Variable,
        children: Vec<String>,
        field_index: usize,
    },
}

impl OwnedResource {
    pub(crate) fn as_resource(&self) -> TrackedResource<'_> {
        match self {
            Self::Cell { pointer, bytes } => TrackedResource::Cell {
                pointer,
                bytes: *bytes,
            },
            Self::Block(block) => TrackedResource::Block(block),
            Self::Ranges(ranges) => TrackedResource::Ranges(ranges),
            Self::AnyMemory => TrackedResource::AnyMemory,
            Self::ModelField {
                identity,
                children,
                field_index,
            } => TrackedResource::ModelField {
                identity: *identity,
                children,
                field_index: *field_index,
            },
        }
    }
}

/// Where a resource was last known to be the same, walking back from a
/// point, and what stopped the walk there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LastSame {
    pub(crate) point: VersionPoint,
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
    ///
    /// The classification comes from [`step_effect::affects`], the same rule
    /// the walk itself asked, run with the same evidence the naming walk has —
    /// none — so a refusal explains the answer the term actually got rather
    /// than a second opinion about it.
    fn at_point(point: &VersionPoint, resource: TrackedResource<'_>) -> Self {
        let Some(derivation) = point.shared_memory().derivation() else {
            return Self {
                change: Change::BeginningOfHistory,
                reason: StopReason::HistoryEnds,
            };
        };
        let change = Change::of_derivation(derivation.as_ref());
        let reason =
            match step_effect::affects(
                derivation.as_ref(),
                point.shared_memory(),
                resource,
                &step_effect::Evidence {
                    assumptions: &naming_context(),
                    cross_loop_havoc: false,
                },
            ) {
                step_effect::StepEffect::Affected => StopReason::Affected,
                // A walk that stopped here found the step neither separate nor
                // about the resource itself, so it wanted this check to succeed —
                // and that is what a repair has to establish.
                step_effect::StepEffect::Separate(_)
                | step_effect::StepEffect::NotShownSeparate(_) => StopReason::NotShownSeparate(
                    step_effect::separation_check(derivation.as_ref(), resource),
                ),
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
    /// A compact range of cell values was recorded. The edge does not
    /// distinguish input materialization from a source-level range write.
    CellsSeeded { pointer: Pointer },
    /// A call may have written the ranges it declared.
    Call { ranges: Vec<MemoryRange> },
    /// A loop may have written the ranges its checked effect summary
    /// declared, or anything at all when it declared none.
    Loop { ranges: Option<Vec<MemoryRange>> },
    /// One heap allocation's lifetime ended.
    Free { allocation: Pointer },
    /// A fresh heap block became live.
    Allocation { block: PointerBlock },
    /// An allocation request has no resolved address yet.
    AllocationPending,
    /// Allocation claims moved across a contract boundary.
    ContractAllocationClaims,
    /// A contract consumed an allocation and did not guarantee continuity.
    ContractRetirement { allocation: Pointer },
    /// A block entered the memory model.
    Declaration { block: PointerBlock },
    /// An automatic-storage object was retired.
    LifetimeEnd { block: PointerBlock },
    /// Cached cell values were dropped; the state is the same, the form is
    /// not.
    CellsForgotten,
    /// A read observation was added to the cache without changing bytes.
    CellObserved,
    /// Incoming branch memories are joined; a read needs agreement in every arm.
    BranchJoin,
    /// An object's initialized-byte metadata was extended.
    ObjectInitializationRecorded,
    /// Nothing: the recorded history starts here.
    BeginningOfHistory,
    /// One instance's model was replaced: its identity survived and its field
    /// values did not.
    ///
    /// No recorded memory edge carries this, because a model field is not
    /// memory. `by` is the step the **mint** of the new value recorded, which
    /// is the only place that knows why it minted one; `None` where neither
    /// side's value was minted as an arbitrary model, and then the text says
    /// only what it can see.
    ModelReplaced {
        by: Option<crate::kernel::model_fields::ModelMint>,
    },
    /// A saved state does not hold the resource at all: the instance was
    /// consumed, or it was never there.
    ///
    /// Which of the two points it is missing at decides what a repair can say,
    /// so both are reported: a value only the *first* point has lost can still
    /// be named at the second, and one neither holds can be named nowhere.
    NotHeld {
        missing_here: bool,
        missing_there: bool,
    },
}

impl Change {
    fn of_derivation(derivation: &MemoryDerivation) -> Self {
        match derivation {
            MemoryDerivation::Store { pointer, .. } => Self::Store {
                pointer: pointer.clone(),
            },
            // The first element names the recorded range, without attributing
            // the input materialization to a source store.
            MemoryDerivation::CellsSeeded { run, .. } => Self::CellsSeeded {
                pointer: run.base().clone(),
            },
            MemoryDerivation::CallHavoc { mutable_ranges, .. } => Self::Call {
                ranges: mutable_ranges.clone(),
            },
            MemoryDerivation::LoopHavoc { mutable_ranges, .. } => Self::Loop {
                ranges: mutable_ranges.clone(),
            },
            MemoryDerivation::HeapFreed {
                allocation_base, ..
            } => Self::Free {
                allocation: allocation_base.clone(),
            },
            MemoryDerivation::HeapAllocated { block, .. } => Self::Allocation {
                block: block.clone(),
            },
            MemoryDerivation::HeapAllocationPending { .. }
            | MemoryDerivation::HeapAllocationFailed { .. } => Self::AllocationPending,
            MemoryDerivation::ContractAllocationClaimsChanged { .. } => {
                Self::ContractAllocationClaims
            }
            MemoryDerivation::ContractAllocationRetired {
                allocation_base, ..
            } => Self::ContractRetirement {
                allocation: allocation_base.clone(),
            },
            MemoryDerivation::BlockDeclared { block, .. } => Self::Declaration {
                block: block.clone(),
            },
            MemoryDerivation::LocalLifetimeEnded { block, .. } => Self::LifetimeEnd {
                block: block.clone(),
            },
            MemoryDerivation::ObjectInitializationRecorded { .. } => {
                Self::ObjectInitializationRecorded
            }
            MemoryDerivation::CellObserved { .. } => Self::CellObserved,
            MemoryDerivation::CellsForgotten { .. } => Self::CellsForgotten,
            MemoryDerivation::BranchJoin { .. } => Self::BranchJoin,
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
    /// The two saved states hold different values at the one key that was
    /// asked about. Deliberately not [`StopReason::Affected`]: nothing
    /// recorded says a step wrote it, and a tracker that claimed one would
    /// print a step the reader never took.
    DifferentVersion,
    /// One of the two saved states does not hold the resource at all — the
    /// instance was consumed, or the state never had
    /// it. This is the fail-closed answer: a version that cannot be found is
    /// never reported the same.
    NotHeld,
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
    /// all untouched, which the step the walk stopped at was not shown to do.
    /// Stated separations are not consulted, because this answer is embedded
    /// in a name and memoized per state.
    WholeBlockAgreement,
}

/// Whether one resource is known to hold the same version at two points.
///
/// `at` is the memory point the blocking step sits below. It is absent for a
/// resource whose versions are values in two saved states: no recorded edge
/// carries the change, so there is no point to name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Sameness {
    Same,
    /// A step between the two points wrote the resource.
    Changed {
        at: Option<VersionPoint>,
        by: Stop,
    },
    /// A step between the two points could not be shown to leave the
    /// resource alone. The resource may well be unchanged; nothing states it.
    Unknown {
        at: Option<VersionPoint>,
        why: Stop,
    },
}

impl Sameness {
    /// The step that broke the chain, for the two answers that have one.
    pub(crate) fn blocking_step(&self) -> Option<(Option<&VersionPoint>, &Stop)> {
        match self {
            Self::Same => None,
            Self::Changed { at, by } => Some((at.as_ref(), by)),
            Self::Unknown { at, why } => Some((at.as_ref(), why)),
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
    /// The point the question was asked at, for a resource that has one.
    /// Absent for the kinds whose points are saved states: a state is neither
    /// interned nor ordered, so it cannot be one of these.
    pub(crate) here: Option<VersionPoint>,
    /// The other point, when the question had one.
    pub(crate) there: Option<VersionPoint>,
    pub(crate) outcome: Sameness,
    /// Recorded steps between the blocking step and `here`, capped at
    /// [`MAX_REPORTED_STEPS`]. The tracker crossed all of them, so a
    /// renderer may say they do not touch the resource.
    pub(crate) crossed_after: usize,
}

impl Explanation {
    /// True when `there` is the earlier of the two points, which is the one a
    /// refusal says the resource may have changed *since*. False when the
    /// question had a single point, or when the two are not comparable.
    pub(crate) fn there_is_earlier(&self) -> bool {
        match (&self.here, &self.there) {
            (Some(here), Some(there)) => here.is_later_than(there),
            _ => false,
        }
    }
}

/// The point a resource read at `at` is named by: the oldest point it is
/// known to be the same at. This is the naming path — memoized, and the only
/// tracker call on the hot path.
pub(crate) fn last_same_version_point(
    resource: TrackedResource<'_>,
    at: &VersionPoint,
) -> Option<VersionPoint> {
    match resource {
        TrackedResource::Cell { pointer, bytes } => {
            cell_last_same_version_point(at.shared_memory(), pointer, bytes).map(VersionPoint)
        }
        TrackedResource::Block(block) => Some(VersionPoint(block_last_same_version_point(
            at.shared_memory(),
            block,
        ))),
        // No term names a memory footprint, so a footprint has no naming path
        // to be the oldest point of. Its one caller knows both ends of the
        // interval it cares about and asks [`step_effect::affects`] at every
        // step in between, which is the same rule this walk would run.
        //
        // A model field has no naming path either, for a different reason:
        // its versions are values in saved states rather than points on the
        // memory history, so there is no oldest point to be.
        // [`same_at_states`] is its whole interface.
        TrackedResource::Ranges(_)
        | TrackedResource::AnyMemory
        | TrackedResource::ModelField { .. } => None,
    }
}

/// [`last_same_version_point`] with the reason the resource walk stopped.
/// Cell naming retains that decision alongside its endpoint; querying it
/// must not re-run the effect check that produced it.
pub(crate) fn last_same(resource: TrackedResource<'_>, at: &VersionPoint) -> Option<LastSame> {
    match resource {
        TrackedResource::Cell { pointer, bytes } => last_same_named_cell(pointer, bytes, at),
        TrackedResource::Block(block) => {
            let point = VersionPoint(block_last_same_version_point(at.shared_memory(), block));
            let stopped_by = Stop::at_point(&point, resource);
            Some(LastSame { point, stopped_by })
        }
        TrackedResource::Ranges(_)
        | TrackedResource::AnyMemory
        | TrackedResource::ModelField { .. } => None,
    }
}

/// [`last_same`] for a cell, from the memoized naming walk
/// ([`last_same_version_point`]): the point a read there is named at, and why the
/// walk stopped there. A caller asking about a cell a read was just named
/// for pays no second walk.
pub(crate) fn last_same_named_cell(
    pointer: &Pointer,
    bytes: u32,
    at: &VersionPoint,
) -> Option<LastSame> {
    let version = cell_last_same_version(at.shared_memory(), pointer, bytes)?;
    let change = version
        .memory
        .derivation()
        .map_or(Change::BeginningOfHistory, |edge| {
            Change::of_derivation(&edge)
        });
    Some(LastSame {
        point: VersionPoint(version.memory),
        stopped_by: Stop {
            change,
            reason: version.reason,
        },
    })
}

/// Whether the resource is known to hold the same version at both points.
///
/// Two points agree exactly when they name the same version, which is what
/// the naming path already decides. When they do not, the later of the two
/// stopped first, and the step below its answer is the one that broke the
/// chain.
pub(crate) fn same(
    resource: TrackedResource<'_>,
    left: &VersionPoint,
    right: &VersionPoint,
) -> Sameness {
    if left == right {
        return Sameness::Same;
    }
    let (Some(left_same), Some(right_same)) =
        (last_same(resource, left), last_same(resource, right))
    else {
        return Sameness::Unknown {
            at: Some(left.clone()),
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
            at: Some(blocking.point),
            by: blocking.stopped_by,
        },
        StopReason::NotShownSeparate(_)
        | StopReason::HistoryEnds
        | StopReason::DifferentVersion
        | StopReason::NotHeld => Sameness::Unknown {
            at: Some(blocking.point),
            why: blocking.stopped_by,
        },
    }
}

/// Whether a resource whose version is a **value in a saved state** holds one
/// version at two such states.
///
/// This is the whole interface for [`TrackedResource::ModelField`], and it is a
/// two-point value comparison rather
/// than a walk. There is no recorded history to walk: the memory DAG records
/// one write set per state, and nothing records "field *k* of this instance
/// was replaced". A field that survived a call kept
/// its identity and got fresh field variables, so the two stored values are
/// already the two versions — which is why this needs no generation counter
/// and no new per-instance state.
///
/// **Cost.** One keyed lookup in each state — `instances` by identity — and
/// one term
/// comparison at the single key asked about. Nothing enumerates a resource
/// context, nothing compares two states, and nothing is memoized: the answer
/// reads path state, which may not be cached by content across verifications.
/// Like the memory cases, it is asked **only while building a refusal**.
///
/// **Fail closed.** `Same` needs both lookups to succeed and the two values to
/// be syntactically equal. Anything else is `Unknown`: a field a contract did
/// not promise must never be reported the same, because a caller that believed
/// it would hold a false theorem.
///
/// **Never `Changed`.** No recorded edge says a step replaced the value, so the
/// answer is never the `Changed` a memory write earns. The step is still named
/// where one is known: the site that minted the new value recorded why it did
/// (`crate::kernel::model_fields`), and the two values this already fetched are
/// where that is read from.
pub(crate) fn same_at_states(
    resource: TrackedResource<'_>,
    left: StatePoint<'_>,
    right: StatePoint<'_>,
) -> Sameness {
    debug_assert!(
        resource.lives_in_a_saved_state(),
        "a memory resource is answered by `same` over program points"
    );
    if left.is_one_state(right) {
        return Sameness::Same;
    }
    let (left_held, right_held) = (
        version_at_state(resource, left),
        version_at_state(resource, right),
    );
    let (Some(left_version), Some(right_version)) = (left_held.as_ref(), right_held.as_ref())
    else {
        return Sameness::Unknown {
            at: None,
            why: Stop {
                change: Change::NotHeld {
                    missing_here: left_held.is_none(),
                    missing_there: right_held.is_none(),
                },
                reason: StopReason::NotHeld,
            },
        };
    };
    if left_version == right_version {
        return Sameness::Same;
    }
    Sameness::Unknown {
        at: None,
        why: Stop {
            change: replacing_change(left_version, right_version),
            reason: StopReason::DifferentVersion,
        },
    }
}

/// What replaced the version, from the two values already in hand.
///
/// A field value the contract's entry minted is the **old** version, so the
/// other side's mint is the step that replaced it. Where neither side was
/// minted as an arbitrary model — a folded constant, a value an `ensures`
/// relates — nothing is claimed.
fn replacing_change(left: &Version, right: &Version) -> Change {
    let (Version::Field(left), Version::Field(right)) = (left, right);
    let mint = |value: &AlgebraicValue| {
        crate::kernel::model_fields::algebraic_value_variable(value)
            .and_then(crate::kernel::model_fields::registered_model_field_origin)
            .map(|origin| origin.minted_by)
    };
    let replaced = [mint(left), mint(right)]
        .into_iter()
        .flatten()
        .find(|mint| *mint != crate::kernel::model_fields::ModelMint::ContractEntry);
    Change::ModelReplaced { by: replaced }
}

/// [`same_at_states`], with the bounded context a refusal prints.
pub(crate) fn explain_at_states(
    resource: TrackedResource<'_>,
    here: StatePoint<'_>,
    there: StatePoint<'_>,
) -> Explanation {
    Explanation {
        resource: resource.to_owned(),
        here: None,
        there: None,
        outcome: same_at_states(resource, here, there),
        crossed_after: 0,
    }
}

/// One version of a saved-state resource: exactly what the state stores at the
/// one key asked about, kept in its own form so the mint of a field value can
/// still be read off it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Version {
    /// One model field's stored value.
    Field(AlgebraicValue),
}

/// The version by one keyed lookup. The comparison is syntactic: two spellings
/// of one value answer `Unknown`, which is the safe direction.
///
/// The one unit recorded here is the whole cost model: a question costs two,
/// whatever the states hold. `a_saved_state_version_costs_one_lookup_per_point`
/// is the regression, and it is what would fail if this ever enumerated a
/// resource context instead of indexing it.
fn version_at_state(resource: TrackedResource<'_>, point: StatePoint<'_>) -> Option<Version> {
    crate::instrumentation::record_deterministic_work(1);
    match resource {
        TrackedResource::ModelField {
            identity,
            children,
            field_index,
        } => point
            .state()
            .resource_instance_at_path(identity, children)
            .and_then(|instance| instance.fields().get(field_index))
            .cloned()
            .map(Version::Field),
        // A memory resource's version is a program point, not a value.
        TrackedResource::Cell { .. }
        | TrackedResource::Block(_)
        | TrackedResource::Ranges(_)
        | TrackedResource::AnyMemory => None,
    }
}

/// [`same`], with the bounded context a refusal prints.
pub(crate) fn explain(
    resource: TrackedResource<'_>,
    here: &VersionPoint,
    there: &VersionPoint,
) -> Explanation {
    let outcome = same(resource, here, there);
    explanation_for(resource, here, Some(there.clone()), outcome)
}

/// What the resource's version at one point rests on, with no second point
/// to compare against: the step that ended the last stretch of agreement.
/// A resource nothing has touched since the beginning of the history
/// answers [`Sameness::Same`].
pub(crate) fn explain_last_same(resource: TrackedResource<'_>, here: &VersionPoint) -> Explanation {
    let outcome = match last_same(resource, here) {
        Some(last) => match last.stopped_by.reason {
            StopReason::HistoryEnds => Sameness::Same,
            StopReason::Affected => Sameness::Changed {
                at: Some(last.point),
                by: last.stopped_by,
            },
            StopReason::NotShownSeparate(_)
            | StopReason::DifferentVersion
            | StopReason::NotHeld => Sameness::Unknown {
                at: Some(last.point),
                why: last.stopped_by,
            },
        },
        None => Sameness::Same,
    };
    explanation_for(resource, here, None, outcome)
}

fn explanation_for(
    resource: TrackedResource<'_>,
    here: &VersionPoint,
    there: Option<VersionPoint>,
    outcome: Sameness,
) -> Explanation {
    let crossed_after = outcome
        .blocking_step()
        .and_then(|(at, _)| at)
        .map(|at| recorded_steps_between(here, at))
        .unwrap_or_default();
    Explanation {
        resource: resource.to_owned(),
        here: Some(here.clone()),
        there,
        outcome,
        crossed_after,
    }
}

/// Recorded steps from `from` back to `to`, bounded. Zero when `to` is not
/// an ancestor of `from`, which is what the two answers that report no step
/// already say.
fn recorded_steps_between(from: &VersionPoint, to: &VersionPoint) -> usize {
    let mut current = from.shared_memory().clone();
    for crossed in 0..MAX_REPORTED_STEPS {
        if &current == to.shared_memory() {
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
    CELL_VERSION_MEMO.with(|memo| memo.borrow_mut().clear());
    BLOCK_VERSION_MEMO.with(|memo| memo.borrow_mut().clear());
    NAMING_CONTEXT.with(|context| context.borrow_mut().take());
}

/// The empty fact context every naming walk asks its questions in.
///
/// A naming walk is assumption-free, but answering an alias question still
/// registers the queried terms, and the reads their addresses depend on, in
/// the context's equality graph. A fresh empty context per walk re-registered
/// the same terms for every walk that met them, so a step that named a few
/// dozen cells paid for the whole dependency chain of each again. One empty
/// context per verification session registers each term once. It holds no
/// fact: its graph carries only the producer-recorded read definitions that
/// any context registers on demand. It does not derive stored-value
/// equations, whose authority requires this naming walk to have finished.
/// It is rebuilt whenever the thread's read table is replaced.
fn naming_context() -> std::rc::Rc<PureFactContext> {
    NAMING_CONTEXT.with(|context| {
        let mut context = context.borrow_mut();
        if let Some(current) = context.as_ref()
            && current.equality_graph.reads_current_logical_reads()
        {
            return current.clone();
        }
        let mut fresh = PureFactContext::new();
        fresh.equality_graph = crate::kernel::equality_graph::EqualityGraph::for_naming();
        let fresh = std::rc::Rc::new(fresh);
        *context = Some(fresh.clone());
        fresh
    })
}

thread_local! {
    static NAMING_CONTEXT: std::cell::RefCell<Option<std::rc::Rc<PureFactContext>>> =
        const { std::cell::RefCell::new(None) };
}

/// The state a pure function's array argument names: the latest one that
/// still agrees with `memory` about everything such a function can observe
/// through a pointer into `block`.
///
/// An `Integer` function over an array carries its state in the argument
/// itself, and that argument is compared structurally, so a fact about
/// `icount(array-ref(S, p), ..)` matches a goal about
/// `icount(array-ref(S', p), ..)` only when `S` and `S'` are the same
/// state. Every step of the program makes a new state, so without a
/// canonical form such a fact dies at the next statement even when that
/// statement cannot touch the array. This is the array-argument counterpart
/// of [`cell_last_same_version_point`], which is why a plain `a[k] == 5` survives the
/// same step today.
///
/// **What the version must guarantee.** The function is opaque, so it may read
/// any cell reachable through `p`, and an `unfold` states its defining
/// equation with the fold lowered at the *live* state while the application
/// keeps this argument. The version is therefore only sound when `memory` and
/// the returned state agree on everything the body can see through `p`:
/// the contents of every cell of `block`, the union overlays in `block`, the
/// block's own extent and liveness, and the heap status that decides whether
/// a read of `block` is defined at all.
///
/// **How that is obtained.** By asking [`step_effect::affects`] about
/// `TrackedResource::Block` at every recorded edge and stopping at the first one it
/// does not answer `Separate`. That rule's `TrackedResource::Block` arm is where the
/// per-step argument lives, kind by kind; it is handed no fact context at all,
/// which is what lets this answer be memoized per interned state and block.
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
/// The walk is assumption-free and terminates: state ids strictly decrease
/// along `base`. It always reports a version, because a subject it can separate
/// from nothing crosses nothing and so answers `memory` itself.
fn block_last_same_version_point(memory: &SharedMemory, block: &PointerBlock) -> SharedMemory {
    let recorded = |key: &(crate::kernel::SharedMemory, PointerBlock)| {
        BLOCK_VERSION_MEMO.with(|memo| memo.borrow().get(key).cloned())
    };
    let key = (memory.clone(), block.clone());
    if let Some(hit) = recorded(&key) {
        return hit;
    }
    // Every state on the way to the version has the same version, so each one
    // is recorded when the walk ends. Without that, a proof that uses one
    // array fact after each of N steps walks the whole chain N times and
    // costs N^2 hops; with it, a walk from a new state meets a recorded
    // answer after one hop, so the whole proof costs one hop per state.
    // `an_array_fact_carried_across_local_stores_scales_linearly` is the
    // regression that tells those apart.
    let mut path = Vec::new();
    let version = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "array-ref block version walk",
        || {
            // A block's answer is shared across proof paths, so this walk
            // offers the rule nothing to spend; the `TrackedResource::Block` arm
            // reads none of it. Built once, because a walk is one question.
            let evidence = step_effect::Evidence {
                assumptions: &PureFactContext::new(),
                cross_loop_havoc: false,
            };
            let mut current = memory.clone();
            loop {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(hit) = recorded(&(current.clone(), block.clone())) {
                    return hit;
                }
                let Some(derivation) = current.derivation() else {
                    return current;
                };
                let crossable = matches!(
                    step_effect::affects(
                        derivation.as_ref(),
                        &current,
                        TrackedResource::Block(block),
                        &evidence,
                    ),
                    // A cell hop cannot be the answer to a block question, and
                    // if one ever were, stopping is the fail-closed reading.
                    step_effect::StepEffect::Separate(step_effect::Separation::Block(_))
                );
                if !crossable {
                    return current;
                }
                path.push(current.clone());
                current = derivation.base().clone();
            }
        },
    );
    BLOCK_VERSION_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len().saturating_add(path.len()) >= 100_000 {
            memo.clear();
        }
        for node in path {
            memo.insert((node, block.clone()), version.clone());
        }
        memo.insert(key, version.clone());
    });
    version
}

thread_local! {
    static BLOCK_VERSION_MEMO: std::cell::RefCell<
        std::collections::HashMap<
            (crate::kernel::SharedMemory, PointerBlock),
            crate::kernel::SharedMemory,
        >,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

#[cfg(test)]
pub(crate) fn block_version_memo_len() -> usize {
    BLOCK_VERSION_MEMO.with(|memo| memo.borrow().len())
}

#[derive(Clone)]
struct NamedCellVersion {
    memory: SharedMemory,
    reason: StopReason,
}

pub(super) fn cell_last_same_version_point(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
) -> Option<SharedMemory> {
    cell_last_same_version(memory, pointer, bytes).map(|version| version.memory)
}

fn cell_last_same_version(
    memory: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
) -> Option<NamedCellVersion> {
    // Assumption-free and a function of the interned state, the pointer,
    // the access width and the recorded edges, so the answer is memoized per
    // query. The width is part of the key because it is part of the
    // question: a wider access stops at stores a narrower one crosses.
    // Cache observations retain a direct byte-source identity. Jump over
    // that entire prefix before naming a new cell, rather than walking the
    // same unchanged observations separately for every address.
    let memory = memory.unchanged_bytes_source();
    let key = (memory.clone(), pointer.clone(), bytes);
    if let Some(hit) = CELL_VERSION_MEMO.with(|memo| memo.borrow().get(&key).cloned()) {
        return hit;
    }
    // Retain the endpoint and the decision that stopped this walk, not its
    // path. Consumers must not re-run that decision: read registration can
    // already hold the naming context's equality graph lock. Reuse a cached
    // prefix so the next statement pays only for its own memory delta.
    crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "cell version walk",
        || {
            with_extended_dag_bridging(|| {
                let assumptions = naming_context();
                let evidence = step_effect::Evidence {
                    assumptions: &assumptions,
                    cross_loop_havoc: false,
                };
                // Whole-block separation applies to every address in the block.
                // Reuse its memoized prefix before the byte-specific walk so a
                // fresh offset does not retrace all unrelated stores. The block
                // rule is assumption-free and stronger than cell separation.
                let mut current =
                    block_last_same_version_point(&memory, &pointer.block).unchanged_bytes_source();
                let mut visited = if current != memory {
                    vec![key.clone()]
                } else {
                    Vec::new()
                };
                let refusals = cell_source::memory_dag_cell_lookup_refusals();
                let result = loop {
                    let current_key = (current.clone(), pointer.clone(), bytes);
                    if let Some(hit) =
                        CELL_VERSION_MEMO.with(|memo| memo.borrow().get(&current_key).cloned())
                    {
                        break hit;
                    }
                    crate::instrumentation::record_deterministic_work(1);
                    visited.push(current_key);
                    let Some(_lookup) = cell_source::CellLookupGuard::enter(&current, pointer)
                    else {
                        break None;
                    };
                    let Some(derivation) = current.derivation() else {
                        break Some(NamedCellVersion {
                            memory: current,
                            reason: StopReason::HistoryEnds,
                        });
                    };
                    match step_effect::affects(
                        &derivation,
                        &current,
                        TrackedResource::Cell { pointer, bytes },
                        &evidence,
                    ) {
                        step_effect::StepEffect::Separate(step_effect::Separation::Cell(_)) => {
                            current = derivation.base().unchanged_bytes_source()
                        }
                        step_effect::StepEffect::Affected => {
                            break Some(NamedCellVersion {
                                memory: current,
                                reason: StopReason::Affected,
                            });
                        }
                        step_effect::StepEffect::NotShownSeparate(reason) => {
                            break Some(NamedCellVersion {
                                memory: current,
                                reason: StopReason::NotShownSeparate(reason),
                            });
                        }
                        step_effect::StepEffect::Separate(_) => {
                            // A cell can cross only a cell separation.
                            let reason = step_effect::separation_check(
                                &derivation,
                                TrackedResource::Cell { pointer, bytes },
                            );
                            break Some(NamedCellVersion {
                                memory: current,
                                reason: StopReason::NotShownSeparate(reason),
                            });
                        }
                    }
                };
                CELL_VERSION_MEMO.with(|memo| {
                    let mut memo = memo.borrow_mut();
                    if memo.len() >= 100_000 {
                        memo.clear();
                    }
                    // An answer that met a lookup already in progress is
                    // weaker than the walk's own answer, so it is not kept
                    // (`memory_dag_cell_lookup_refusals`).
                    if result.is_some()
                        && cell_source::memory_dag_cell_lookup_refusals() == refusals
                    {
                        for key in visited {
                            memo.insert(key, result.clone());
                        }
                    }
                });
                result
            })
        },
    )
}

/// The value one cell holds at `at` on the querying path, when its recorded
/// history pins one down: the cached value at the point the cell was last the
/// same, where the steps the naming walk could not cross are crossed with the
/// path's own facts.
///
/// A store at a symbolic address — `buf[u] = 7` — drops the cached cells it
/// may write, so a later `buf[0]` finds no cell even on a path that knows
/// `u != 0`. The naming walk is assumption-free (its answer is embedded in a
/// name shared by every path), so it stops at that store. This read names
/// nothing: it answers for this path only, through the fact-aware cell walk
/// ([`cell_source::memory_dag_cell_source`]), which resumes the memoized
/// naming walk and applies `assumptions` only at the steps it stopped at.
/// The value is the store the walk reached, or the cell the state it
/// stopped at caches at exactly `pointer`; every step in between is proven
/// separate from the cell, so that is the cell's value at `at` wherever
/// `assumptions` hold.
pub(crate) fn cell_value_on_path(
    at: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<crate::kernel::ExecutionValue> {
    match cell_source::memory_dag_cell_source(at, pointer, bytes, assumptions, false)? {
        cell_source::MemoryDagCell::Stored { value, .. } => Some(value.into_value()),
        cell_source::MemoryDagCell::Unwritten { node, .. } => node.known_retained_value(pointer),
    }
}

/// The state a static-storage cell is read at on the querying path, when
/// that path's facts carry the cell unwritten from `at` back to the root
/// (`function.entry`) and nothing on the way caches its value. A store the
/// naming walk could not place, such as `g[u] = 7` on a path that knows
/// `u != 0`, leaves an untouched `g[0]` its entry value: the read is the load
/// at the root, as it is with no store at all. The path's facts cross the
/// steps the naming walk cannot (as in [`cell_value_on_path`]); from the
/// state they reach, the memoized naming walk must run to the root. The
/// state is returned, and a load there is named at the root.
pub(crate) fn static_cell_unwritten_since_entry_on_path(
    at: &SharedMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<SharedMemory> {
    if !pointer.block.is_static_storage_block() {
        return None;
    }
    match cell_source::memory_dag_cell_source(at, pointer, bytes, assumptions, false)? {
        cell_source::MemoryDagCell::Unwritten { node, .. }
            if node != *at
                && node.known_value(pointer).is_none()
                && cell_last_same_version(&node, pointer, bytes)
                    .is_some_and(|version| version.reason == StopReason::HistoryEnds) =>
        {
            Some(node)
        }
        _ => None,
    }
}

thread_local! {
    static CELL_VERSION_MEMO: std::cell::RefCell<
        std::collections::HashMap<
            (crate::kernel::SharedMemory, Pointer, u32),
            Option<NamedCellVersion>,
        >,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// One read of a resource by a term: which resource, and the program point
/// the term reads it at.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ResourceRead {
    pub(crate) resource: OwnedResource,
    pub(crate) point: VersionPoint,
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
            term.for_each_machine_operand(|term| collect_operand_reads(term, reads));
        }
        Term::ProgramValue(value) => collect_value_reads(value, reads),
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
) -> Option<(OwnedResource, VersionPoint, VersionPoint)> {
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
) -> Option<(OwnedResource, VersionPoint, VersionPoint)> {
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

fn push_read(reads: &mut Vec<ResourceRead>, resource: OwnedResource, point: VersionPoint) {
    let read = ResourceRead { resource, point };
    if !reads.contains(&read) {
        reads.push(read);
    }
}

fn collect_condition_operand_reads(
    condition: crate::kernel::BooleanOperandView<'_>,
    reads: &mut Vec<ResourceRead>,
) {
    condition.for_each_dependency_leaf(|leaf| {
        if let crate::kernel::BooleanOperandView::Shared(root) = leaf
            && matches!(
                root.node(),
                crate::kernel::KernelTermNode::BoolLiteral(_)
                    | crate::kernel::KernelTermNode::Variable(_)
                    | crate::kernel::KernelTermNode::Call { .. }
            )
        {
            return;
        }

        if let Some((_, operands)) = leaf.machine_arguments() {
            for operand in operands {
                collect_operand_reads(operand, reads);
            }
        } else if let Some(values) = leaf.pointer_values() {
            for value in values {
                for address in value.addresses() {
                    collect_pointer_block_reads(address.node().block.native_atom(), reads);
                    address.node().offset.visit_root_in_order(true, |node| {
                        if let Some(index) = node.index() {
                            collect_operand_reads(
                                crate::kernel::MachineOperandView::Shared(index),
                                reads,
                            );
                        }
                    });
                }
            }
        } else if let Some(addresses) = leaf.pointer_addresses() {
            for address in addresses {
                collect_pointer_block_reads(address.node().block.native_atom(), reads);
                address.node().offset.visit_root_in_order(true, |node| {
                    if let Some(index) = node.index() {
                        collect_operand_reads(
                            crate::kernel::MachineOperandView::Shared(index),
                            reads,
                        );
                    }
                });
            }
        } else if let Some(offsets) = leaf.pointer_offsets() {
            crate::kernel::SharedPointerOffset::visit_pair_in_order(&offsets, true, |node| {
                if let Some(index) = node.index() {
                    collect_operand_reads(crate::kernel::MachineOperandView::Shared(index), reads);
                }
            });
        } else {
            // Integer comparison leaves retain their existing integer reader;
            // calls and opaque conditions retain the native admission rules.
            collect_condition_reads(&leaf.native(), reads);
        }
    });
}

fn collect_condition_reads(condition: &ConditionTerm, reads: &mut Vec<ResourceRead>) {
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_reads(pointer, reads);
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_machine_operand(|term| collect_operand_reads(term, reads));
            right.for_each_machine_operand(|term| collect_operand_reads(term, reads));
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
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
            collect_pointer_reads(left, reads);
            collect_pointer_reads(right, reads);
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_reads(left, reads);
            collect_bitvector_reads(right, reads);
        }
        // As a word-valued Click application: not entered.
        ConditionTerm::BoolApplication(_) => {}
        ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
            for child in condition.bool_children() {
                collect_condition_reads(child, reads);
            }
        }
        // A `bool` cell is one byte.
        ConditionTerm::BoolLoad(memory, pointer) => push_read(
            reads,
            OwnedResource::Cell {
                pointer: pointer.as_ref().clone(),
                bytes: 1,
            },
            VersionPoint::at(memory),
        ),
    }
}

/// A loaded pointer reads the complete pointer cell its name was defined at,
/// at the point that name embeds, as an offset's load variable reads its cell.
fn collect_pointer_reads(pointer: &Pointer, reads: &mut Vec<ResourceRead>) {
    collect_pointer_block_reads(&pointer.block, reads);
    collect_offset_reads(&pointer.offset, reads);
}

fn collect_pointer_block_reads(block: &PointerBlock, reads: &mut Vec<ResourceRead>) {
    if let PointerBlock::LoadedPointer(identity) = *block
        && let Some((memory, address)) = crate::kernel::eval::registered_pointer_load(identity)
    {
        push_read(
            reads,
            OwnedResource::Cell {
                pointer: address,
                bytes: crate::kernel::C_POINTER_BYTE_WIDTH,
            },
            VersionPoint::at(&memory),
        );
    }
}

fn collect_offset_reads(offset: &PointerOffsetTerm, reads: &mut Vec<ResourceRead>) {
    let mut pending = vec![offset];
    while let Some(offset) = pending.pop() {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => {
                collect_operand_reads(value.operand_view(), reads)
            }
            _ => {}
        }
    }
}

fn collect_operand_reads(
    root: crate::kernel::MachineOperandView<'_>,
    reads: &mut Vec<ResourceRead>,
) {
    use crate::kernel::{MachineIntegerType as T, MachineOperandView as V, MachineUnaryOp as U};
    let mut pending = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(view) = pending.pop() {
        if let V::Shared(node) = view {
            if !seen.insert(node.id()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
        }
        if let Some(leaf) = view.read_source() {
            collect_bitvector_reads(&leaf, reads);
        } else if let Some((condition, arms)) = view.conditional_view() {
            collect_condition_operand_reads(condition, reads);
            pending.extend(arms.into_iter().rev());
        } else if let Some((T::Int32 | T::UInt32, _, operands)) = view.binary() {
            pending.extend(operands.into_iter().rev());
        } else if let Some((T::Int32 | T::UInt32, U::BitwiseNot, operand)) = view.unary() {
            pending.push(operand);
        } else if let Some((encoding, _, _, operand)) = view.cast() {
            if matches!(
                encoding,
                MachineCastSpelling::Generic
                    | MachineCastSpelling::Int64From32
                    | MachineCastSpelling::UInt64From32
                    | MachineCastSpelling::UInt32From64
                    | MachineCastSpelling::Int64FromUInt32
                    | MachineCastSpelling::UInt64FromInt32
                    | MachineCastSpelling::UInt64FromInt64
            ) {
                pending.push(operand);
            }
        }
    }
}

fn collect_value_reads(value: &ProgramValue, reads: &mut Vec<ResourceRead>) {
    match value {
        ProgramValue::Pointer(pointer) => collect_pointer_reads(pointer.pointer(), reads),
        _ => {
            if let Some(term) = crate::kernel::spec::program_value_bitvector_term(value) {
                collect_bitvector_reads(&term, reads);
            }
        }
    }
}

fn collect_integer_reads(term: &SharedIntegerTerm, reads: &mut Vec<ResourceRead>) {
    collect_integer_term_reads(term.as_ref(), reads);
}

fn collect_integer_term_reads(term: &IntegerTerm, reads: &mut Vec<ResourceRead>) {
    collect_integer_node_reads(term, reads, &mut std::collections::BTreeSet::new());
}

fn collect_shared_integer_reads(
    term: &SharedIntegerTerm,
    reads: &mut Vec<ResourceRead>,
    seen: &mut std::collections::BTreeSet<u64>,
) {
    if seen.insert(term.id()) {
        collect_integer_node_reads(term.as_ref(), reads, seen);
    }
}

fn collect_integer_node_reads(
    term: &IntegerTerm,
    reads: &mut Vec<ResourceRead>,
    seen: &mut std::collections::BTreeSet<u64>,
) {
    crate::instrumentation::record_deterministic_work(1);
    match term {
        IntegerTerm::Machine(machine) => {
            collect_operand_reads(machine.operand_view(), reads);
        }
        IntegerTerm::Negate(inner) => collect_shared_integer_reads(inner, reads, seen),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_shared_integer_reads(left, reads, seen);
            collect_shared_integer_reads(right, reads, seen);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                match argument {
                    PureFunctionArgument::Integer(term) => {
                        collect_shared_integer_reads(term, reads, seen)
                    }
                    _ => collect_argument_reads(argument, reads),
                }
            }
        }
        IntegerTerm::RangeFold { initial, body, .. } => {
            collect_shared_integer_reads(initial, reads, seen);
            collect_shared_integer_reads(body, reads, seen);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_reads(condition, reads);
            collect_shared_integer_reads(then_term, reads, seen);
            collect_shared_integer_reads(else_term, reads, seen);
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
            if let ProgramValue::Pointer(pointer) = pointer {
                push_read(
                    reads,
                    OwnedResource::Block(pointer.pointer().block.clone()),
                    VersionPoint::of_memory(memory),
                );
            }
        }
        PureFunctionArgument::Integer(term) => collect_integer_reads(term, reads),
        PureFunctionArgument::Algebraic(term) => {
            term.for_each_machine_operand(|term| collect_operand_reads(term, reads));
        }
        PureFunctionArgument::Value(value) => collect_value_reads(value, reads),
        PureFunctionArgument::SharedMachine(value) => {
            collect_operand_reads(value.operand_view(), reads)
        }
    }
}

fn collect_bitvector_reads(term: &MachineTerm, reads: &mut Vec<ResourceRead>) {
    match term {
        MachineTerm::MemoryLoad(..) | MachineTerm::Variable(_) => {
            if let Some(read) = crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Legacy(term),
            ) {
                push_read(
                    reads,
                    OwnedResource::Cell {
                        pointer: read.pointer,
                        bytes: read.bytes,
                    },
                    VersionPoint::at(&read.origin.unwrap_or(read.memory)),
                );
            }
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            collect_bitvector_reads(left, reads);
            collect_bitvector_reads(right, reads);
        }
        unary_term!(Bits32, BitwiseNot, inner)
        | cast_term!(Int64From32, inner)
        | MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: inner,
            ..
        }
        | cast_term!(UInt64From32, inner)
        | cast_term!(UInt32From64, inner)
        | cast_term!(Int64FromUInt32, inner)
        | cast_term!(UInt64FromInt32, inner)
        | cast_term!(UInt64FromInt64, inner) => collect_bitvector_reads(inner, reads),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_reads(condition, reads);
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
