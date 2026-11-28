//! The program point: a node a proof path reached.
//!
//! A [`ProgramPoint`] carries the memory state there and its place on the
//! path: an identity minted at each memory transition, linked to the point or
//! points it was reached from. SymbolicMemory states are interned by content, so two
//! paths that reach equal memory share one state; their points are still two.
//!
//! Surface records the name of each point it records a state at
//! (`RecordedStates::point_name`).

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Weak};

use crate::kernel::MachineIntegerType;
use crate::persistent::{PersistentMap, PersistentSet};

use super::cell_version_intervals::CellVersionIntervals;
use super::{
    Address, AddressBase, AddressOffset, LoadKind, MemoryDerivation, MemoryRange, OldMachineTerm,
    ProgramType, ProgramValue, SharedMemory, StoredMemoryValue, SymbolicMemory, intern_memory,
    intern_memory_ref,
};
use crate::kernel::{OffsetTree, OffsetView};

/// The identity of one point an execution path reached.
///
/// Identities are unique within a process and carry no order: no decision
/// may depend on comparing two of them other than for equality. Ordering is
/// provided solely for exact fact keys.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ProgramPointId(u64);

static NEXT_PROGRAM_POINT_ID: AtomicU64 = AtomicU64::new(1);

impl ProgramPointId {
    fn fresh() -> Self {
        Self(NEXT_PROGRAM_POINT_ID.fetch_add(1, Ordering::Relaxed))
    }
}

/// The steps a path took between two points, newest first: each recorded
/// memory step and the memory it produced.
///
/// A step is added where it is recorded ([`super::record_memory_derivation`])
/// to the log of the memory value the path is executing, so the log follows
/// the path that ran even when the arena shares the resulting content with
/// another path. The point a state reaches next takes the log.
pub(crate) struct StepLog {
    step: Arc<MemoryDerivation>,
    produced: SharedMemory,
    previous: Option<Arc<StepLog>>,
    named_cells_origin: Option<NamedCellsOrigin>,
    first_base: SharedMemory,
    contiguous: bool,
    preserves_external_storage: bool,
    preserves_external_arrays: bool,
}

/// The exact source of a suffix that only names existing cells. The log
/// retains the earlier steps, so their identity is available without walking.
#[derive(Clone)]
struct NamedCellsOrigin {
    memory: (u32, u32),
    previous: Option<Weak<StepLog>>,
}

impl NamedCellsOrigin {
    fn of(memory: &SharedMemory, steps: Option<&Arc<StepLog>>) -> Self {
        if let Some(steps) = steps
            && steps.produced.arena_id() == memory.arena_id()
            && let Some(origin) = &steps.named_cells_origin
        {
            return origin.clone();
        }
        Self {
            memory: memory.arena_id(),
            previous: steps.map(Arc::downgrade),
        }
    }
}

impl StepLog {
    /// `previous` with `step`, which produced `produced`, added as newest.
    pub(crate) fn push(
        previous: Option<Arc<Self>>,
        step: Arc<MemoryDerivation>,
        produced: SharedMemory,
        names_existing_cells: bool,
    ) -> Arc<Self> {
        let named_cells_origin =
            names_existing_cells.then(|| NamedCellsOrigin::of(step.base(), previous.as_ref()));
        let (first_base, contiguous) = previous.as_ref().map_or_else(
            || (step.base().clone(), true),
            |prefix| {
                (
                    prefix.first_base.clone(),
                    prefix.contiguous && prefix.produced.arena_id() == step.base().arena_id(),
                )
            },
        );
        let step_preserves_external_storage =
            step_preserves_external_storage(&step, names_existing_cells);
        let preserves_external_storage = step_preserves_external_storage
            && previous
                .as_ref()
                .is_none_or(|old| old.preserves_external_storage);
        let preserves_external_arrays = previous
            .as_ref()
            .is_none_or(|old| old.preserves_external_arrays)
            && (step_preserves_external_storage
                || matches!(step.as_ref(), MemoryDerivation::CallHavoc { mutable_ranges, .. }
                if mutable_ranges.iter().all(|range| {
                    crate::instrumentation::record_deterministic_work(1);
                    indexed_local(&range.base().base)
                })));
        Arc::new(Self {
            step,
            produced,
            previous,
            named_cells_origin,
            first_base,
            contiguous,
            preserves_external_storage,
            preserves_external_arrays,
        })
    }

    /// Whether the replacement extends this view with naming alone. Even a
    /// real store that restores the same contents has a different log prefix.
    pub(super) fn materializes_from(
        source: &SharedMemory,
        source_steps: Option<&Arc<Self>>,
        replacement: &SharedMemory,
        replacement_steps: Option<&Arc<Self>>,
    ) -> bool {
        if source.arena_id() == replacement.arena_id()
            && source_steps.map(Arc::as_ptr) == replacement_steps.map(Arc::as_ptr)
        {
            return true;
        }
        let Some(steps) = replacement_steps else {
            return false;
        };
        let Some(origin) = &steps.named_cells_origin else {
            return false;
        };
        let before = NamedCellsOrigin::of(source, source_steps);
        steps.produced.arena_id() == replacement.arena_id()
            && origin.memory == before.memory
            && origin.previous.as_ref().map(Weak::as_ptr)
                == before.previous.as_ref().map(Weak::as_ptr)
    }

    /// The steps, newest first, each with the memory it produced.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn newest_first(&self) -> impl Iterator<Item = (&MemoryDerivation, &SharedMemory)> {
        std::iter::successors(Some(self), |log| log.previous.as_deref())
            .map(|log| (log.step.as_ref(), &log.produced))
    }
}

/// Whether one recorded step leaves all caller-supplied storage unchanged.
/// `names_existing_cells` says the step only named cells the view already
/// held.
fn step_preserves_external_storage(step: &MemoryDerivation, names_existing_cells: bool) -> bool {
    match step {
        MemoryDerivation::Store { pointer, .. }
        | MemoryDerivation::RepresentationWrite { pointer, .. } => indexed_local(&pointer.base),
        // A declaration makes fresh storage: a local, or the
        // temporary a call result is built in.
        MemoryDerivation::BlockDeclared { block, .. } => {
            indexed_local(block) || matches!(block, AddressBase::Temporary(_))
        }
        MemoryDerivation::LocalLifetimeEnded { block, .. } => indexed_local(block),
        // Pending and resolved fresh allocations leave existing objects alone.
        MemoryDerivation::HeapAllocationPending { .. }
        | MemoryDerivation::HeapAllocationFailed { .. }
        | MemoryDerivation::HeapAllocated { .. } => true,
        // The call's write effect is recorded separately. The return
        // clause supplies initialization evidence for the typed cell.
        MemoryDerivation::ObjectInitializationRecorded { .. } => true,
        MemoryDerivation::LoopHavoc {
            mutable_ranges: Some(ranges),
            ..
        } => ranges.iter().all(|range| {
            crate::instrumentation::record_deterministic_work(1);
            indexed_local(&range.base().base)
        }),
        _ => names_existing_cells,
    }
}

impl std::fmt::Debug for StepLog {
    /// A count, not the steps: a log can be long and its memories large.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let count = std::iter::successors(Some(self), |log| log.previous.as_deref()).count();
        write!(f, "StepLog({count} steps)")
    }
}

impl Drop for StepLog {
    /// Drop a long log one step at a time.
    fn drop(&mut self) {
        let mut previous = self.previous.take();
        while let Some(log) = previous {
            previous = match Arc::try_unwrap(log) {
                Ok(mut log) => log.previous.take(),
                Err(_) => None,
            };
        }
    }
}

type PointReadObjects = PersistentMap<AddressBase, PointReadObject>;
type PointReadCells = PersistentMap<i64, PointReadWrite>;

#[derive(Clone, Debug)]
struct PointReadIndex {
    /// A wholesale barrier ends the shared index lineage.
    generation: ProgramPointId,
    blocks: PointReadObjects,
}

impl PointReadIndex {
    fn empty(generation: ProgramPointId) -> Self {
        Self {
            generation,
            blocks: PointReadObjects::default(),
        }
    }
}

#[derive(Clone, Debug)]
struct PointReadObject {
    /// A whole-object removal can discard an arbitrarily large map. A later
    /// write creates a new lineage so the join need not diff those maps.
    generation: ProgramPointId,
    origin: Option<(AddressBase, AddressOffset)>,
    cells: PointReadCells,
}

impl PartialEq for PointReadObject {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation
            && self.origin == other.origin
            && self.cells.shares_root_with(&other.cells)
    }
}

#[derive(Clone, Debug)]
struct PointReadWrite {
    end: i64,
    version: Weak<PointNode>,
    source: Arc<MemoryDerivation>,
}

impl PartialEq for PointReadWrite {
    fn eq(&self, other: &Self) -> bool {
        self.end == other.end
            && Weak::ptr_eq(&self.version, &other.version)
            && Arc::ptr_eq(&self.source, &other.source)
    }
}

#[derive(Debug)]
pub(super) struct PointNode {
    id: ProgramPointId,
    /// The number of points before this one on its longest path from the
    /// path's start: one more than its deepest predecessor. A walk back
    /// toward an ancestor stops once it reaches the ancestor's depth.
    depth: u32,
    function_entry: bool,
    /// Whether this is a contract call's effect point
    /// ([`PointTransition::CallEffect`]).
    call_effect: bool,
    /// The memory state the path had here.
    memory: SharedMemory,
    /// The steps the path took from its predecessor to here, newest first;
    /// none when it reached here without a recorded step.
    steps: Option<Arc<StepLog>>,
    /// The points this one was reached from on its path: one after an
    /// ordinary transition, two after a branch join, none at the start.
    predecessors: Box<[PathLink]>,
    /// For a branch join, the point where its arms split.
    split: Option<PathLink>,
    /// Disjoint typed cells, keyed by storage and byte start. The
    /// predecessor chain owns the version points.
    point_read_index: PointReadIndex,
    /// Earliest recorded view in a suffix of effects disjoint from parameter
    /// storage. Read selection can start here.
    external_read_start: Option<ReadVersionPoint>,
    /// Array version carried across this point's checked call. The ordinary
    /// local suffix can reach this point without crossing the call for scalars.
    array_version_after_call: Option<ReadVersionPoint>,
    array_block_versions: Option<ArrayBlockVersions>,
    external_entry_writes: Option<ExternalEntryWrites>,
    /// At a loop's exit: what the loop's iterations wrote. A loop's head
    /// step stands for its iterations, and the iterations that run back to
    /// the head are on no exit's path, so their writes are recorded here
    /// once the body is checked.
    loop_iterations: Option<LoopIterations>,
}

/// The writes of a loop's iterations: every store, call and inner loop on
/// each path from the loop's head back to it.
pub(crate) struct LoopIterations {
    /// The head point whose step stands for these iterations.
    pub(crate) head: ProgramPointId,
    /// `None` when some path back to the head does not record its writes.
    ///
    /// Held behind a trait object: a point that holds writes that hold
    /// memories that hold points is a type whose thread-safety the compiler
    /// would otherwise prove by unbounded recursion.
    writes: Option<Arc<dyn std::any::Any + Send + Sync>>,
}

impl std::fmt::Debug for LoopIterations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LoopIterations")
            .field("head", &self.head)
            .field("writes", &self.writes())
            .finish()
    }
}

impl LoopIterations {
    pub(crate) fn new(
        head: ProgramPointId,
        writes: Option<Arc<crate::kernel::RecordedWrites>>,
    ) -> Self {
        Self {
            head,
            writes: writes.map(|writes| writes as Arc<dyn std::any::Any + Send + Sync>),
        }
    }

    /// What the iterations wrote, when every path back to the head
    /// recorded it.
    pub(crate) fn writes(&self) -> Option<&crate::kernel::RecordedWrites> {
        self.writes.as_deref().map(|writes| {
            writes
                .downcast_ref()
                .expect("loop iterations hold recorded writes")
        })
    }
}

#[derive(Clone, Debug)]
struct ReadVersionPoint {
    point: Weak<PointNode>,
    view: IndexedView,
    memory: SharedMemory,
}

impl ReadVersionPoint {
    fn read(&self, read: ReadSelection) -> Option<ProgramPoint> {
        Some(ProgramPoint {
            memory: self.memory.clone(),
            path: PathLink(Some(self.point.upgrade()?), self.view.clone()),
            read,
        })
    }
}

/// The bytes of caller-supplied storage written since function entry, when
/// every effect since entry either left that storage alone or wrote a
/// fixed-width cell at a fixed displacement from one parameter origin. A
/// read from that origin of bytes none of those writes reached still holds
/// its entry value, so it keeps the entry version whatever else was written.
#[derive(Clone, Debug)]
struct ExternalEntryWrites {
    entry: Weak<PointNode>,
    /// The view the first step after entry started from.
    entry_view: SharedMemory,
    /// The one origin all writes since entry used; none before the first.
    origin: Option<(AddressBase, AddressOffset)>,
    written: PersistentSet<i64>,
    /// The point whose effect last changed `written` or `origin`, or the
    /// entry. Two arms with one generation hold one record.
    generation: ProgramPointId,
}

impl ExternalEntryWrites {
    /// The record at `from`: its own, or a fresh one when `from` is the
    /// function entry. `source` is the view the next step starts from.
    fn at(from: &PathLink, source: &SharedMemory) -> Option<Self> {
        if !from.matches_indexed_view(source) {
            return None;
        }
        let node = from.0.as_ref()?;
        if node.function_entry {
            return Some(Self {
                entry: Arc::downgrade(node),
                entry_view: source.clone(),
                origin: None,
                written: PersistentSet::default(),
                generation: node.id,
            });
        }
        node.external_entry_writes.clone()
    }

    fn after(
        predecessors: &[PathLink],
        steps: Option<&StepLog>,
        memory: &SharedMemory,
        id: ProgramPointId,
        transition: PointTransition,
    ) -> Option<Self> {
        let [from] = predecessors else {
            return None;
        };
        let source = match steps {
            Some(log)
                if log.contiguous
                    && log.produced.arena_id() == memory.arena_id()
                    && (transition != PointTransition::Provisional || log.previous.is_none()) =>
            {
                &log.first_base
            }
            Some(_) => return None,
            None => memory,
        };
        let mut record = Self::at(from, source)?;
        if let Some(log) = steps {
            if log.previous.is_none() {
                record.record(log, id)?;
            } else {
                let effects = std::iter::successors(Some(log), |log| log.previous.as_deref())
                    .collect::<Vec<_>>();
                for effect in effects.into_iter().rev() {
                    record.record(effect, id)?;
                }
            }
        }
        Some(record)
    }

    fn record(&mut self, effect: &StepLog, id: ProgramPointId) -> Option<()> {
        crate::instrumentation::record_deterministic_work(1);
        let step = effect.step.as_ref();
        if step_preserves_external_storage(step, effect.named_cells_origin.is_some()) {
            return Some(());
        }
        let (MemoryDerivation::Store { pointer, .. }
        | MemoryDerivation::RepresentationWrite { pointer, .. }) = step
        else {
            return None;
        };
        if !external_storage(&pointer.base) {
            return None;
        }
        let width = i64::from(step.single_write_extent()?.1.bytes()?);
        if !(1..=super::MAX_SCALAR_ACCESS_BYTES).contains(&width) {
            return None;
        }
        let (anchor, start) = read_displacement(&pointer.offset)?;
        let origin = read_origin(pointer, anchor)?;
        match &self.origin {
            Some(known) if *known != origin => return None,
            Some(_) => {}
            None => self.origin = Some(origin),
        }
        for byte in start..start.checked_add(width)? {
            crate::instrumentation::record_deterministic_work(1);
            self.written = self.written.with_value(byte);
        }
        self.generation = id;
        Some(())
    }

    /// Keep the record only when every arm holds the same one.
    fn joining(points: &[ProgramPoint]) -> Option<Self> {
        let at = |point: &ProgramPoint| Self::at(&point.path, &point.memory);
        let (first, rest) = points.split_first()?;
        let record = at(first)?;
        for point in rest {
            crate::instrumentation::record_deterministic_work(1);
            let other = at(point)?;
            if !Weak::ptr_eq(&record.entry, &other.entry) || record.generation != other.generation {
                return None;
            }
        }
        Some(record)
    }

    /// The entry read of `bytes` at `pointer`, when no recorded write since
    /// entry reached them.
    fn unwritten_entry_read(
        &self,
        pointer: &Address,
        bytes: u32,
        allow_materialized_entry: bool,
    ) -> Option<ProgramPoint> {
        if !external_storage(&pointer.base) {
            return None;
        }
        let (anchor, start) = read_displacement(&pointer.offset)?;
        if self
            .origin
            .as_ref()
            .is_some_and(|origin| Some(origin) != read_origin(pointer, anchor).as_ref())
        {
            return None;
        }
        for byte in start..start.checked_add(i64::from(bytes))? {
            crate::instrumentation::record_deterministic_work(1);
            if self.written.contains(&byte) {
                return None;
            }
        }
        let entry = self.entry.upgrade()?;
        if entry.memory.memory() != &SymbolicMemory::default()
            || (!allow_materialized_entry && self.entry_view.memory() != &SymbolicMemory::default())
        {
            return None;
        }
        Some(ProgramPoint {
            memory: entry.memory.clone(),
            path: PathLink(Some(entry), IndexedView::Recorded),
            read: ReadSelection::Entry,
        })
    }
}

#[derive(Clone, Debug)]
struct ArrayBlockVersions {
    /// A fresh lineage after an unclassified effect prevents a join from
    /// diffing maps with no shared base.
    generation: ProgramPointId,
    static_entry: Option<ReadVersionPoint>,
    writes: PersistentMap<AddressBase, ArrayBlockWrite>,
}

#[derive(Clone, Debug)]
struct ArrayBlockWrite {
    point: Weak<PointNode>,
    /// Bytes written since the entry anchor. None means this block had an
    /// effect without a known footprint, or diverging branch versions.
    static_writes: Option<StaticPointWrites>,
}

#[derive(Clone, Debug, Default)]
struct StaticPointWrites {
    stores: PersistentSet<i64>,
    calls: CellVersionIntervals<()>,
}

impl PartialEq for ArrayBlockWrite {
    fn eq(&self, other: &Self) -> bool {
        Weak::ptr_eq(&self.point, &other.point)
    }
}

impl ArrayBlockVersions {
    fn at_verified_view(path: &PathLink, memory: &SharedMemory) -> Option<Self> {
        let node = path.0.as_ref()?;
        if !node.function_entry {
            return node.array_block_versions.clone();
        }
        Some(Self {
            generation: node.id,
            static_entry: Some(ReadVersionPoint {
                point: Arc::downgrade(node),
                view: path.1.clone(),
                memory: memory.clone(),
            }),
            writes: PersistentMap::default(),
        })
    }

    /// Walk only changed keys between maps with the same lineage. An array
    /// with different versions on different arms receives the join's version.
    fn joining(points: &[ProgramPoint], joined: &Weak<PointNode>) -> Option<Self> {
        let versions_at = |point: &ProgramPoint| {
            if !point.path.matches_indexed_view(&point.memory) {
                return None;
            }
            Self::at_verified_view(&point.path, &point.memory)
        };
        let (first, rest) = points.split_first()?;
        let base = versions_at(first)?;
        let mut result = base.clone();
        for point in rest {
            crate::instrumentation::record_deterministic_work(1);
            let other = versions_at(point)?;
            if other.generation != base.generation {
                return None;
            }
            for (block, left, right) in base.writes.diff(&other.writes) {
                if block.is_static_storage_block()
                    || (left.is_some() && right.is_some() && result.writes.get(block).is_some())
                {
                    result.writes.insert(
                        block.clone(),
                        ArrayBlockWrite {
                            point: joined.clone(),
                            static_writes: None,
                        },
                    );
                } else {
                    // An automatic or heap object must exist on every
                    // arm. Its entry cannot stand for another lifetime.
                    result.writes.remove(block);
                }
            }
        }
        Some(result)
    }

    fn after(
        predecessors: &[PathLink],
        steps: Option<&StepLog>,
        memory: &SharedMemory,
        point: &Weak<PointNode>,
        id: ProgramPointId,
        transition: PointTransition,
    ) -> Option<Self> {
        let [from] = predecessors else {
            return None;
        };
        let source = match steps {
            Some(log)
                if log.contiguous
                    && log.produced.arena_id() == memory.arena_id()
                    && (transition != PointTransition::Provisional || log.previous.is_none()) =>
            {
                &log.first_base
            }
            Some(_) => return None,
            None => memory,
        };
        if !from.matches_indexed_view(source) {
            return None;
        }
        let mut versions = Self::at_verified_view(from, source).unwrap_or_else(|| Self {
            generation: id,
            static_entry: None,
            writes: PersistentMap::default(),
        });
        if let Some(log) = steps {
            if log.previous.is_none() {
                versions.record(&log.step, point)?;
            } else {
                let effects =
                    std::iter::successors(steps, |log| log.previous.as_deref()).collect::<Vec<_>>();
                for effect in effects.into_iter().rev() {
                    versions.record(&effect.step, point)?;
                }
            }
        }
        (versions.static_entry.is_some() || !versions.writes.is_empty()).then_some(versions)
    }

    fn record(&mut self, step: &MemoryDerivation, point: &Weak<PointNode>) -> Option<()> {
        use crate::kernel::resource_tracker::step_effect::{
            BlockSeparation, BlockVersionEffect, block_version_effect,
        };

        crate::instrumentation::record_deterministic_work(1);
        let effect = block_version_effect(step);
        if let BlockVersionEffect::Object(block, BlockSeparation::ReleaseOfDistinctBlock) = effect
            && (indexed_local(block) || matches!(block, AddressBase::Heap(_)))
        {
            self.writes.remove(block);
            return Some(());
        }
        let mut record_object = |block: &AddressBase, range: Option<&MemoryRange>| {
            if indexed_array_object(block) {
                let static_writes = self.static_entry.as_ref().and_then(|_| {
                    let mut written = match self.writes.get(block) {
                        Some(prior) => prior.static_writes.clone()?,
                        None => StaticPointWrites::default(),
                    };
                    if let Some(range) = range {
                        if !matches!(step, MemoryDerivation::CallHavoc { .. }) {
                            return None;
                        }
                        let (span, _) = super::static_call_range(range)?;
                        written.calls.write(span, ());
                    } else {
                        let (pointer, extent) = step.single_write_extent()?;
                        let span = super::static_cell_byte_span(pointer, extent.bytes()?)?;
                        for byte in span {
                            crate::instrumentation::record_deterministic_work(1);
                            written.stores = written.stores.with_value(byte);
                        }
                    }
                    Some(written)
                });
                self.writes.insert(
                    block.clone(),
                    ArrayBlockWrite {
                        point: point.clone(),
                        static_writes,
                    },
                );
                true
            } else {
                matches!(block, AddressBase::Temporary(_))
            }
        };
        match effect {
            BlockVersionEffect::Object(block, _) if record_object(block, None) => Some(()),
            BlockVersionEffect::WriteSet(ranges)
                if ranges.iter().all(|range| {
                    crate::instrumentation::record_deterministic_work(1);
                    record_object(&range.base().base, Some(range))
                }) =>
            {
                Some(())
            }
            BlockVersionEffect::Unchanged => Some(()),
            _ => None,
        }
    }
}

impl Drop for PointNode {
    /// A long path is a long chain; dropping it one link at a time keeps the
    /// stack flat however many transitions the path made.
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.predecessors).into_vec();
        pending.extend(self.split.take());
        while let Some(PathLink(node, _)) = pending.pop() {
            if let Some(node) = node
                && let Ok(mut node) = Arc::try_unwrap(node)
            {
                pending.extend(std::mem::take(&mut node.predecessors).into_vec());
                pending.extend(node.split.take());
            }
        }
    }
}

/// Where on its path a point is: its identity and the points it was reached
/// from, or none for a point built from a bare memory or a state before its
/// first memory transition. An [`super::ExecutionState`] carries the one for
/// the point it stands at.
///
/// It is not part of a state's equality, hashing or order: two states are
/// equal when they hold the same things, wherever each was reached.
#[derive(Clone, Debug, Default)]
pub struct PathLink(Option<Arc<PointNode>>, IndexedView);

#[derive(Clone, Copy, PartialEq, Eq)]
enum PointTransition {
    FunctionEntry,
    Execution,
    /// The state of a contract call after its value effects, before the
    /// effects on initialization, liveness and allocation that reach its
    /// exit: `call(f, j).effect`, a migration measure until reads are named
    /// by the write that made their value.
    CallEffect,
    Provisional,
    LoopHead,
}

/// Which view may use the execution point's versions. Proof-local views may
/// differ between copies of a path, so this is held on the link, not the node.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
enum IndexedView {
    #[default]
    Recorded,
    Materialized((u32, u32)),
    Unverified,
}

/// One more than the deepest of `predecessors`, or zero at a path's start.
fn path_depth(predecessors: &[PathLink]) -> u32 {
    predecessors
        .iter()
        .filter_map(|link| link.0.as_ref())
        .map(|node| node.depth + 1)
        .max()
        .unwrap_or(0)
}

impl PathLink {
    /// Visits every recorded step on the path from `from` to this point,
    /// newest first, until `visit` returns false: the memory history between
    /// two points. `Some(true)` when every step was visited, `Some(false)`
    /// when `visit` stopped, and `None` when this point is not reached from
    /// `from` through single predecessors (another path, or a branch join).
    pub(crate) fn visit_steps_since(
        &self,
        from: &PathLink,
        mut visit: impl FnMut(&MemoryDerivation) -> bool,
    ) -> Option<bool> {
        let target = from.id()?;
        let target_depth = from.0.as_ref()?.depth;
        let mut link = self;
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if link.id() == Some(target) {
                return Some(true);
            }
            let node = link.0.as_ref()?;
            // An ancestor is never as deep as its descendant: past its depth
            // the walk cannot meet it.
            if node.depth <= target_depth {
                return None;
            }
            let [predecessor] = node.predecessors.as_ref() else {
                return None;
            };
            // The steps from the predecessor to this point: a log can carry
            // older steps before them, which end where the predecessor's
            // memory begins.
            let start = predecessor.0.as_ref().map(|node| node.memory.arena_id());
            let mut steps = node.steps.as_deref();
            while let Some(log) = steps {
                crate::instrumentation::record_deterministic_work(1);
                if !visit(&log.step) {
                    return Some(false);
                }
                if Some(log.step.base().arena_id()) == start {
                    break;
                }
                steps = log.previous.as_deref();
            }
            link = predecessor;
        }
    }

    /// Visits every recorded step on every path from `from` to this point,
    /// each point once: the memory history of a region whose paths may
    /// branch and join. Each step is visited with the point it reached, and
    /// a loop exit's record of its iterations with `iterations`. `None` when
    /// some path into this point does not start at `from`.
    pub(crate) fn visit_region_steps_since(
        &self,
        from: &PathLink,
        mut visit: impl FnMut(ProgramPointId, &MemoryDerivation),
        mut iterations: impl FnMut(&LoopIterations),
    ) -> Option<()> {
        let target = from.id()?;
        let target_depth = from.0.as_ref()?.depth;
        let mut seen = std::collections::HashSet::new();
        let mut pending = vec![self];
        while let Some(link) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if link.id() == Some(target) {
                continue;
            }
            let node = link.0.as_ref()?;
            if node.depth <= target_depth || node.predecessors.is_empty() {
                return None;
            }
            if !seen.insert(node.id) {
                continue;
            }
            if let Some(record) = &node.loop_iterations {
                iterations(record);
            }
            let starts: Vec<_> = node
                .predecessors
                .iter()
                .filter_map(|predecessor| predecessor.0.as_ref())
                .map(|node| node.memory.arena_id())
                .collect();
            let mut steps = node.steps.as_deref();
            while let Some(log) = steps {
                crate::instrumentation::record_deterministic_work(1);
                visit(node.id, &log.step);
                if starts.contains(&log.step.base().arena_id()) {
                    break;
                }
                steps = log.previous.as_deref();
            }
            pending.extend(node.predecessors.iter());
        }
        Some(())
    }

    pub(in crate::kernel) fn shares_point_and_view(&self, other: &Self) -> bool {
        self.id() == other.id() && self.1 == other.1
    }

    pub(in crate::kernel) fn matches_indexed_view(&self, memory: &SharedMemory) -> bool {
        match self.1 {
            IndexedView::Recorded => self
                .0
                .as_ref()
                .is_some_and(|node| node.memory.arena_id() == memory.arena_id()),
            IndexedView::Materialized(view) => view == memory.arena_id(),
            IndexedView::Unverified => false,
        }
    }

    /// Bind the memory view being constructed for an entry root. There are
    /// no preceding execution versions to carry into this view.
    pub(super) fn with_entry_view(mut self, view: &SharedMemory) -> Self {
        assert!(
            self.0
                .as_ref()
                .is_some_and(|point| { point.predecessors.is_empty() && point.steps.is_none() })
        );
        self.1 = IndexedView::Materialized(view.arena_id());
        self
    }

    pub(super) fn with_materialized_view(
        mut self,
        source: &SharedMemory,
        view: &SharedMemory,
        verified: bool,
    ) -> Self {
        if !verified || !self.matches_indexed_view(source) {
            self.1 = IndexedView::Unverified;
        } else if source.arena_id() != view.arena_id() {
            self.1 = IndexedView::Materialized(view.arena_id());
            // A verified materialization names more cells of the same
            // state: it is that point's state too.
            if let Some(node) = &self.0 {
                super::record_memory_occurrence(view, node);
            }
        }
        self
    }

    /// The point of a proposition built only to look a fact up by its
    /// memory: lookups compare no point, so it needs none. It goes when
    /// fact indexes are keyed by point.
    pub(crate) fn lookup_key() -> Self {
        Self::default()
    }

    pub(super) fn function_entry(memory: SharedMemory) -> Self {
        Self::reached_from(
            memory,
            None,
            Box::new([]),
            None,
            PointTransition::FunctionEntry,
            None,
        )
    }

    /// A new point reached from this one by `steps`, where the path has
    /// `memory`.
    ///
    /// A path that has no point yet begins where its first step began: a
    /// state set up by steps before it first stands at a point (an entry
    /// state whose precondition observed cells) gets a point at the memory
    /// before them, so a walk back can cross them as it crosses any step.
    pub(crate) fn after(&self, memory: SharedMemory, steps: Option<Arc<StepLog>>) -> Self {
        self.after_with_index(memory, steps, PointTransition::Execution)
    }

    /// [`Self::after`], as a contract call's effect point.
    pub(crate) fn after_call_effect(
        &self,
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
    ) -> Self {
        self.after_with_index(memory, steps, PointTransition::CallEffect)
    }

    /// Whether this is a contract call's effect point.
    pub(crate) fn is_call_effect(&self) -> bool {
        self.0.as_ref().is_some_and(|node| node.call_effect)
    }

    pub(super) fn after_loop_head(
        &self,
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
    ) -> Self {
        self.after_with_index(memory, steps, PointTransition::LoopHead)
    }

    fn after_with_index(
        &self,
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
        transition: PointTransition,
    ) -> Self {
        let from = match (&self.0, &steps) {
            (None, Some(log)) => Self::reached_from(
                log.first_base.clone(),
                None,
                Box::new([]),
                None,
                PointTransition::Provisional,
                None,
            ),
            _ => self.clone(),
        };
        Self::reached_from(memory, steps, Box::new([from]), None, transition, None)
    }

    /// The point after a loop whose iterations wrote `iterations`: the same
    /// memory, reached from this exit.
    pub(super) fn after_loop_iterations(&self, iterations: LoopIterations) -> Self {
        let Some(node) = &self.0 else {
            return self.clone();
        };
        Self::reached_from(
            node.memory.clone(),
            None,
            Box::new([self.clone()]),
            None,
            PointTransition::Execution,
            Some(iterations),
        )
    }

    /// The head point of the loop whose head step this point's log holds
    /// last, when it holds one: the point a loop's iterations return to.
    pub(crate) fn loop_head(&self) -> Option<ProgramPointId> {
        let node = self.0.as_ref()?;
        let log = node.steps.as_deref()?;
        matches!(*log.step, MemoryDerivation::LoopHavoc { .. }).then_some(node.id)
    }

    /// A new point where two arms that split at `split` rejoin with
    /// `memory`.
    pub(crate) fn joining(
        left: ProgramPoint,
        right: ProgramPoint,
        split: &Self,
        memory: SharedMemory,
    ) -> Self {
        Self::joining_points(&[left, right], Some(split), memory)
    }

    pub(super) fn joining_points(
        points: &[ProgramPoint],
        split: Option<&Self>,
        memory: SharedMemory,
    ) -> Self {
        let predecessors = points
            .iter()
            .map(|point| point.path.clone())
            .collect::<Box<[_]>>();
        let id = ProgramPointId::fresh();
        let point_read_index =
            join_point_read_indexes(points).unwrap_or_else(|| PointReadIndex::empty(id));
        let external_read_start = joined_external_entry(points).or_else(|| {
            // A single exit still has a successor point of its own. When it
            // carries the predecessor's certified view, the join adds no
            // effect that could change the version of caller storage.
            let [predecessor] = points else { return None };
            if predecessor.memory.arena_id() != memory.arena_id()
                || !predecessor.has_certified_read_view()
            {
                return None;
            }
            let anchor = predecessor.parameter_read_start(&AddressBase::ExternalArgument);
            Some(ReadVersionPoint {
                point: Arc::downgrade(anchor.path.0.as_ref()?),
                view: anchor.path.1.clone(),
                memory: anchor.memory,
            })
        });
        Self(
            Some(Arc::new_cyclic(|joined| PointNode {
                id,
                depth: path_depth(&predecessors),
                function_entry: false,
                call_effect: false,
                memory,
                steps: None,
                predecessors,
                split: split.filter(|point| point.0.is_some()).cloned(),
                point_read_index,
                external_read_start,
                array_version_after_call: None,
                array_block_versions: ArrayBlockVersions::joining(points, joined),
                external_entry_writes: ExternalEntryWrites::joining(points),
                loop_iterations: None,
            })),
            IndexedView::Recorded,
        )
    }

    fn reached_from(
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
        predecessors: Box<[PathLink]>,
        split: Option<PathLink>,
        transition: PointTransition,
        loop_iterations: Option<LoopIterations>,
    ) -> Self {
        let predecessors = predecessors
            .into_vec()
            .into_iter()
            .filter(|point| point.0.is_some())
            .collect::<Box<[_]>>();
        let external_read_start = external_read_start(&predecessors, steps.as_deref(), &memory);
        let array_version_after_call =
            array_version_across_call(&predecessors, steps.as_deref(), &memory);
        let node = Arc::new_cyclic(|version| {
            let id = ProgramPointId::fresh();
            let point_read_index = point_read_index(
                &predecessors,
                steps.as_deref(),
                &memory,
                version,
                id,
                transition,
            );
            let array_block_versions = ArrayBlockVersions::after(
                &predecessors,
                steps.as_deref(),
                &memory,
                version,
                id,
                transition,
            );
            let external_entry_writes = ExternalEntryWrites::after(
                &predecessors,
                steps.as_deref(),
                &memory,
                id,
                transition,
            );
            PointNode {
                id,
                depth: path_depth(&predecessors),
                function_entry: transition == PointTransition::FunctionEntry,
                call_effect: transition == PointTransition::CallEffect,
                memory,
                steps,
                predecessors,
                split: split.filter(|point| point.0.is_some()),
                point_read_index,
                external_read_start,
                array_version_after_call,
                array_block_versions,
                external_entry_writes,
                loop_iterations,
            }
        });
        super::record_memory_occurrence(&node.memory, &node);
        Self(Some(node), IndexedView::Recorded)
    }

    /// The steps the path took from its predecessor to this point.
    pub(crate) fn steps(&self) -> Option<&StepLog> {
        self.0.as_ref().and_then(|node| node.steps.as_deref())
    }

    /// For a branch join, the point where its arms split.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn split(&self) -> Option<&Self> {
        self.0.as_ref().and_then(|node| node.split.as_ref())
    }

    /// The memory state the path had at this point.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn memory(&self) -> Option<&SharedMemory> {
        self.0.as_ref().map(|node| &node.memory)
    }

    /// The points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessors(&self) -> &[Self] {
        self.0
            .as_ref()
            .map(|node| node.predecessors.as_ref())
            .unwrap_or(&[])
    }

    pub(crate) fn id(&self) -> Option<ProgramPointId> {
        self.0.as_ref().map(|node| node.id)
    }

    /// The identities of the points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessor_ids(&self) -> Vec<ProgramPointId> {
        self.0
            .as_ref()
            .map(|node| node.predecessors.iter().filter_map(Self::id).collect())
            .unwrap_or_default()
    }
}

// Two automatic blocks with different identities are structurally disjoint.
fn indexed_local(block: &AddressBase) -> bool {
    matches!(block, AddressBase::AutomaticLocal { .. })
        || matches!(block, AddressBase::Concrete(_) if block.is_local_block())
}

fn indexed_array_object(block: &AddressBase) -> bool {
    block.is_static_storage_block() || indexed_local(block) || matches!(block, AddressBase::Heap(_))
}

/// Parameter addresses can alias across differently written bases. Keep one
/// parameter base and one symbolic offset origin in the shared parameter bucket.
fn external_storage(block: &AddressBase) -> bool {
    matches!(
        block,
        AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
    )
}

fn read_bucket(block: &AddressBase) -> Option<&AddressBase> {
    if external_storage(block) {
        Some(&AddressBase::ExternalArgument)
    } else if indexed_local(block) || matches!(block, AddressBase::Heap(_)) {
        Some(block)
    } else {
        None
    }
}

/// The bounded address shape only. No arithmetic or alias fact is consulted.
/// Symbolic offsets share a bucket only while they use the same origin.
fn read_displacement(offset: &AddressOffset) -> Option<(Option<&AddressOffset>, i64)> {
    match offset.view() {
        OffsetView::Constant(start) => Some((None, start)),
        OffsetView::Add(origin, delta)
            if origin.is_shallow()
                && let OffsetView::Constant(delta) = delta.view() =>
        {
            Some((Some(origin), delta))
        }
        OffsetView::Add(delta, origin)
            if origin.is_shallow()
                && let OffsetView::Constant(delta) = delta.view() =>
        {
            Some((Some(origin), delta))
        }
        _ if offset.is_shallow() => Some((Some(offset), 0)),
        _ => None,
    }
}

fn read_origin(
    pointer: &Address,
    anchor: Option<&AddressOffset>,
) -> Option<(AddressBase, AddressOffset)> {
    if anchor.is_some() || external_storage(&pointer.base) {
        Some((
            pointer.base.clone(),
            anchor.cloned().unwrap_or(AddressOffset::constant(0)),
        ))
    } else {
        None
    }
}

/// Intersect the versions carried by each checked incoming point. Diff each
/// arm against the first arm, so an earlier removal is not revisited for
/// every later arm.
fn join_point_read_indexes(points: &[ProgramPoint]) -> Option<PointReadIndex> {
    fn index(point: &ProgramPoint) -> Option<&PointReadIndex> {
        let node = point.path.0.as_ref()?;
        point
            .path
            .matches_indexed_view(&point.memory)
            .then_some(&node.point_read_index)
    }

    let (first, rest) = points.split_first()?;
    let base = index(first)?;
    let mut result = base.clone();
    for point in rest {
        let other = index(point)?;
        if other.generation != base.generation {
            return None;
        }
        for (key, left, right) in base.blocks.diff(&other.blocks) {
            let (Some(left), Some(right), Some(mut kept)) =
                (left, right, result.blocks.get(key).cloned())
            else {
                result.blocks.remove(key);
                continue;
            };
            if left.generation != right.generation || left.origin != right.origin {
                result.blocks.remove(key);
                continue;
            }
            for (start, _, _) in left.cells.diff(&right.cells) {
                kept.cells.remove(start);
            }
            if kept.cells.is_empty() {
                result.blocks.remove(key);
            } else {
                result.blocks.insert(key.clone(), kept);
            }
        }
    }
    Some(result)
}

fn external_read_start(
    predecessors: &[PathLink],
    steps: Option<&StepLog>,
    memory: &SharedMemory,
) -> Option<ReadVersionPoint> {
    let [from @ PathLink(Some(point), view)] = predecessors else {
        return None;
    };
    let source = match steps {
        Some(log)
            if log.contiguous
                && log.preserves_external_storage
                && log.produced.arena_id() == memory.arena_id() =>
        {
            &log.first_base
        }
        Some(_) => return None,
        None => memory,
    };
    if !from.matches_indexed_view(source) {
        return None;
    }
    point.external_read_start.clone().or_else(|| {
        Some(ReadVersionPoint {
            point: Arc::downgrade(point),
            view: view.clone(),
            memory: source.clone(),
        })
    })
}

/// Every write in a checked call confined to automatic objects is disjoint
/// from arrays supplied by parameters. The log summarizes those calls and
/// local effects when it records them, including within a transition batch.
fn array_version_across_call(
    predecessors: &[PathLink],
    steps: Option<&StepLog>,
    memory: &SharedMemory,
) -> Option<ReadVersionPoint> {
    let [from] = predecessors else { return None };
    let log = steps?;
    if !log.contiguous
        || !log.preserves_external_arrays
        || log.preserves_external_storage
        || log.produced.arena_id() != memory.arena_id()
    {
        return None;
    }
    external_array_anchor(from, &log.first_base)
}

/// An external array can start at function entry or at a write into the
/// shared caller storage. A named external object can only use entry here.
fn is_external_array_origin(node: &PointNode) -> bool {
    node.function_entry
        || node.steps.as_ref().is_some_and(|log| {
            log.contiguous
                && log.produced.arena_id() == node.memory.arena_id()
                && matches!(
                    log.step.as_ref(),
                    MemoryDerivation::Store { pointer, .. }
                        if pointer.base == AddressBase::ExternalArgument
                )
        })
}

/// The local suffix can end at an origin or at a call that carries one.
fn external_array_anchor(path: &PathLink, memory: &SharedMemory) -> Option<ReadVersionPoint> {
    if !path.matches_indexed_view(memory) {
        return None;
    }
    let node = path.0.as_ref()?;
    if is_external_array_origin(node) {
        return Some(ReadVersionPoint {
            point: Arc::downgrade(node),
            view: path.1.clone(),
            memory: memory.clone(),
        });
    }
    if let Some(anchor) = &node.external_read_start {
        let origin = anchor.point.upgrade()?;
        return if is_external_array_origin(&origin) {
            Some(anchor.clone())
        } else {
            origin.array_version_after_call.clone()
        };
    }
    node.array_version_after_call.clone()
}

/// Retain the common entry only when every incoming path proves that it
/// preserved external storage. The incoming points already own the anchors.
fn joined_external_entry(points: &[ProgramPoint]) -> Option<ReadVersionPoint> {
    let (first, rest) = points.split_first()?;
    let entry = external_array_anchor(&first.path, &first.memory)?;
    if !entry.point.upgrade()?.function_entry {
        return None;
    }
    for point in rest {
        crate::instrumentation::record_deterministic_work(1);
        let other = external_array_anchor(&point.path, &point.memory)?;
        if !Weak::ptr_eq(&entry.point, &other.point)
            || entry.memory.arena_id() != other.memory.arena_id()
        {
            return None;
        }
    }
    Some(entry)
}

/// Apply the explicit effects once, when execution seals the point. A read
/// of a provisional point may index a single effect but never replays a batch.
fn point_read_index(
    predecessors: &[PathLink],
    steps: Option<&StepLog>,
    memory: &SharedMemory,
    version: &Weak<PointNode>,
    id: ProgramPointId,
    transition: PointTransition,
) -> PointReadIndex {
    let [from @ PathLink(Some(before), _)] = predecessors else {
        return PointReadIndex::empty(id);
    };
    let Some(step) = steps else {
        return if from.matches_indexed_view(memory) {
            before.point_read_index.clone()
        } else {
            PointReadIndex::empty(id)
        };
    };
    if (transition == PointTransition::Provisional && step.previous.is_some())
        || !step.contiguous
        || !from.matches_indexed_view(&step.first_base)
        || step.produced.arena_id() != memory.arena_id()
    {
        return PointReadIndex::empty(id);
    }
    let mut index = before.point_read_index.clone();
    let record_writes = transition != PointTransition::LoopHead;
    if step.previous.is_none() {
        record_point_read_effect(&mut index, &step.step, version, id, record_writes);
    } else {
        let effects =
            std::iter::successors(Some(step), |step| step.previous.as_deref()).collect::<Vec<_>>();
        for effect in effects.into_iter().rev() {
            record_point_read_effect(&mut index, &effect.step, version, id, record_writes);
        }
    }
    index
}

fn record_point_read_effect(
    index: &mut PointReadIndex,
    step: &Arc<MemoryDerivation>,
    version: &Weak<PointNode>,
    id: ProgramPointId,
    record_writes: bool,
) {
    crate::instrumentation::record_deterministic_work(1);
    match step.as_ref() {
        MemoryDerivation::Store { pointer, .. }
        | MemoryDerivation::RepresentationWrite { pointer, .. }
        | MemoryDerivation::ObjectInitializationRecorded {
            pointer,
            call_output: Some(_),
            ..
        } if read_bucket(&pointer.base).is_some() => {
            let bucket = read_bucket(&pointer.base).expect("indexed write bucket");
            // A symbolic-size write can overlap other fields of the object
            // even when its modeled carrier width does not.
            if indexed_local(&pointer.base)
                && step
                    .single_write_extent()
                    .is_some_and(|(_, extent)| extent.bytes().is_none())
            {
                index.blocks.remove(bucket);
            }
            let output_width = match step.as_ref() {
                MemoryDerivation::ObjectInitializationRecorded { bytes, .. } => Some(*bytes),
                _ => None,
            };
            let width = i64::from(
                output_width
                    .unwrap_or_else(|| step.single_write().expect("single checked write").1),
            );
            let Some((anchor, start)) = read_displacement(&pointer.offset) else {
                index.blocks.remove(bucket);
                return;
            };
            let Some(end) = start
                .checked_add(width)
                .filter(|_| (1..=super::MAX_SCALAR_ACCESS_BYTES).contains(&width))
            else {
                index.blocks.remove(bucket);
                return;
            };
            let origin = read_origin(pointer, anchor);
            let mut block = index
                .blocks
                .get(bucket)
                .filter(|block| block.origin == origin)
                .cloned()
                .unwrap_or_else(|| PointReadObject {
                    generation: id,
                    origin,
                    cells: PointReadCells::default(),
                });
            clear_overlapping_cells(&mut block.cells, start, end);
            if record_writes
                && (output_width.is_some()
                    || integer_store_bits(step).is_some()
                    || matches!(step.as_ref(), MemoryDerivation::Store { value, .. }
                        if matches!(value.native(), ProgramValue::Bool(_) | ProgramValue::Pointer(_))
                            || (indexed_local(&pointer.base) && matches!(value.native(), ProgramValue::Parameter(_)))))
            {
                block.cells.insert(
                    start,
                    PointReadWrite {
                        end,
                        version: version.clone(),
                        source: step.clone(),
                    },
                );
            }
            if block.cells.is_empty() {
                index.blocks.remove(bucket);
            } else {
                index.blocks.insert(bucket.clone(), block);
            }
        }
        MemoryDerivation::CellsForgotten { .. }
        | MemoryDerivation::CellObserved { .. }
        | MemoryDerivation::BlockDeclared { .. }
        | MemoryDerivation::HeapAllocated { .. }
        | MemoryDerivation::HeapAllocationPending { .. }
        | MemoryDerivation::HeapAllocationFailed { .. }
        | MemoryDerivation::ContractAllocationClaimsChanged { .. }
        | MemoryDerivation::ObjectInitializationRecorded { .. } => {}
        MemoryDerivation::CallHavoc { mutable_ranges, .. }
        | MemoryDerivation::LoopHavoc {
            mutable_ranges: Some(mutable_ranges),
            ..
        } => {
            retain_outside_named_write_objects(index, mutable_ranges, id);
        }
        MemoryDerivation::LocalLifetimeEnded { block, .. } if indexed_local(block) => {
            index.blocks.remove(block);
        }
        MemoryDerivation::HeapFreed {
            allocation_base, ..
        }
        | MemoryDerivation::ContractAllocationRetired {
            allocation_base, ..
        } if read_bucket(&allocation_base.base).is_some() => {
            index
                .blocks
                .remove(read_bucket(&allocation_base.base).expect("indexed lifetime bucket"));
        }
        _ => *index = PointReadIndex::empty(id),
    }
}

/// These object identities are structurally distinct from every indexed
/// automatic object except that exact object. A checked range in such an
/// object can conservatively retire its whole bucket without visiting cells.
fn retain_outside_named_write_objects(
    index: &mut PointReadIndex,
    ranges: &[MemoryRange],
    id: ProgramPointId,
) {
    for range in ranges {
        crate::instrumentation::record_deterministic_work(1);
        let block = &range.base().base;
        if let Some(bucket) = read_bucket(block) {
            index.blocks.remove(bucket);
            continue;
        }
        match block {
            AddressBase::Temporary(_) => {}
            AddressBase::Concrete(_) | AddressBase::StaticObject { .. } => {
                index.blocks.remove(&AddressBase::ExternalArgument);
            }
            _ => {
                *index = PointReadIndex::empty(id);
                return;
            }
        }
    }
}

/// Disjoint intervals have at most one earlier start overlapping the write.
/// Every other hit starts inside the write, so a scalar write removes at most
/// its byte width plus one entry, regardless of the object's size.
fn clear_overlapping_cells(cells: &mut PointReadCells, start: i64, end: i64) {
    if let Some((&earlier, write)) = cells.get_less_than(&start)
        && write.end > start
    {
        cells.remove(&earlier);
    }
    if cells.contains_key(&start) {
        cells.remove(&start);
    }
    while let Some((&later, _)) = cells.get_greater_than(&start)
        && later < end
    {
        cells.remove(&later);
    }
}

fn integer_store_bits(step: &MemoryDerivation) -> Option<(LoadKind, &OldMachineTerm)> {
    let MemoryDerivation::Store { value, .. } = step else {
        return None;
    };
    match value.native() {
        ProgramValue::Int8(bits) => Some((LoadKind::Int8, bits)),
        ProgramValue::UInt8(bits) => Some((LoadKind::UInt8, bits)),
        ProgramValue::Int16(bits) => Some((LoadKind::Int16, bits)),
        ProgramValue::UInt16(bits) => Some((LoadKind::UInt16, bits)),
        ProgramValue::Int32(bits) => Some((LoadKind::Int32, bits)),
        ProgramValue::UInt32(bits) => Some((LoadKind::UInt32, bits)),
        ProgramValue::Int64(bits) | ProgramValue::UInt64(bits) => Some((LoadKind::Bits64, bits)),
        ProgramValue::Int128(bits) => Some((LoadKind::Int128, bits)),
        ProgramValue::UInt128(bits) => Some((LoadKind::UInt128, bits)),
        _ => None,
    }
}

impl PartialEq for PathLink {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for PathLink {}

impl std::hash::Hash for PathLink {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl PartialOrd for PathLink {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PathLink {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

/// A program point: a node a proof path reached, which Surface names with
/// `at(point, ...)`. A memory read is lowered to its version point, the point
/// back to which the recorded steps show the cell unchanged, and holds that
/// point.
///
/// Exact reads and indexed reads include the point they name in the term key.
/// Legacy reads still use the interned memory as their key.
#[derive(Clone)]
pub struct ProgramPoint {
    memory: SharedMemory,
    path: PathLink,
    read: ReadSelection,
}

/// Where a memory-named point's memory belongs.
#[derive(Clone)]
enum LegacyPlace {
    /// On the point's own path, which it has.
    OwnPath,
    /// The memory is the state at this point, or a view of that state.
    /// The point alone, without a link's view, keeps every read term small.
    TrueAt(Arc<PointNode>),
    /// The legacy walk's memory for a read made at this point. It is the
    /// state of an earlier point the walk does not name, not this one's.
    WalkedFrom(Arc<PointNode>),
    /// Built from a bare memory ([`ProgramPoint::unplaced`]): no claim.
    Unplaced,
}

#[derive(Clone)]
enum ReadSelection {
    /// Named by its memory (`ReadKey::Memory`), with the point that memory
    /// belongs to ([`LegacyPlace`]). The place is no part of the point's
    /// identity.
    Legacy(LegacyPlace),
    Exact,
    Entry,
    CallOutput,
    IndexedCell,
    IndexedWrite(Arc<MemoryDerivation>),
}

impl std::fmt::Debug for ProgramPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut point = f.debug_struct("ProgramPoint");
        if let Some(version) = self.read_version_id() {
            point.field("version", &version);
        } else {
            point
                .field("memory", &self.memory)
                .field("path", &self.path);
        }
        point.finish()
    }
}

/// Identity of a read, separate from the memory view retained for checking.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(in crate::kernel) enum ReadKey {
    Memory((u32, u32)),
    Point(ProgramPointId),
    /// A rewritten or unverified view has no evidence it still names the
    /// recorded bytes. Keep its explicit view in the key.
    View(ProgramPointId, (u32, u32)),
}

impl PartialEq for ProgramPoint {
    fn eq(&self, other: &Self) -> bool {
        match (self.read_version_id(), other.read_version_id()) {
            (None, None) => self.memory == other.memory,
            _ => self.read_key() == other.read_key(),
        }
    }
}

impl Eq for ProgramPoint {}

impl std::hash::Hash for ProgramPoint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if self.read_version_id().is_some() {
            self.read_key().hash(state);
        } else {
            self.memory.hash(state);
        }
    }
}

impl PartialOrd for ProgramPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProgramPoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.read_version_id(), other.read_version_id()) {
            (None, None) => self.memory.cmp(&other.memory),
            _ => self.read_key().cmp(&other.read_key()),
        }
    }
}

impl ProgramPoint {
    /// A point built from a bare memory state, with no place on a path: it
    /// claims nothing about where its memory is true. Production code is
    /// converting to [`Self::viewing`] and [`Self::walked`];
    /// `build_support/read_construction.rs` holds its uses to a shrinking
    /// count, and it goes when that count reaches zero.
    pub fn unplaced(memory: &SharedMemory) -> Self {
        Self {
            memory: memory.clone(),
            path: PathLink::default(),
            read: ReadSelection::Legacy(
                memory
                    .occurrence()
                    .map_or(LegacyPlace::Unplaced, LegacyPlace::TrueAt),
            ),
        }
    }

    /// [`Self::unplaced`], for tests.
    #[cfg(test)]
    pub fn at(memory: &SharedMemory) -> Self {
        Self::unplaced(memory)
    }

    /// A memory-named read of `memory` made at `site`: [`Self::viewing`]
    /// when `memory` is `site`'s own state, else [`Self::walked`], which
    /// claims nothing about where `memory` is true.
    pub(crate) fn read_at(memory: &SharedMemory, site: &ProgramPoint) -> Self {
        if memory == site.shared_memory() {
            Self::viewing(memory, site)
        } else {
            Self::walked(memory, site)
        }
    }

    /// [`Self::read_at`] when the caller has a site, else
    /// [`Self::unplaced`].
    pub(crate) fn read_at_optional(memory: &SharedMemory, site: Option<&ProgramPoint>) -> Self {
        match site {
            Some(site) => Self::read_at(memory, site),
            None => Self::unplaced(memory),
        }
    }

    /// `memory`, a state equal to `source`'s or a view of it (a
    /// substitution, a materialization, a projection), placed where
    /// `source`'s memory is placed. Named by `memory`.
    pub(crate) fn viewing(memory: &SharedMemory, source: &ProgramPoint) -> Self {
        Self {
            memory: memory.clone(),
            path: PathLink::default(),
            read: ReadSelection::Legacy(source.place()),
        }
    }

    /// The legacy walk's memory for a read made at `read_at`. The memory
    /// belongs to an earlier point the walk does not name, so it is placed
    /// as walked from `read_at`, not as true there. Named by `memory`.
    pub(crate) fn walked(memory: &SharedMemory, read_at: &ProgramPoint) -> Self {
        // A memory some point held is true there, whoever walked to it.
        let place = match memory.occurrence() {
            Some(node) => LegacyPlace::TrueAt(node),
            None => match read_at.place() {
                LegacyPlace::TrueAt(path) | LegacyPlace::WalkedFrom(path) => {
                    LegacyPlace::WalkedFrom(path)
                }
                LegacyPlace::Unplaced => LegacyPlace::Unplaced,
                LegacyPlace::OwnPath => unreachable!("a place is never the own path"),
            },
        };
        Self {
            memory: memory.clone(),
            path: PathLink::default(),
            read: ReadSelection::Legacy(place),
        }
    }

    /// Where this point's memory belongs, for a point built from it.
    fn place(&self) -> LegacyPlace {
        if let Some(node) = &self.path.0 {
            return LegacyPlace::TrueAt(node.clone());
        }
        match &self.read {
            ReadSelection::Legacy(
                place @ (LegacyPlace::TrueAt(_) | LegacyPlace::WalkedFrom(_)),
            ) => place.clone(),
            // A state never placed on a path (a scratch state) stands nowhere.
            _ => LegacyPlace::Unplaced,
        }
    }

    /// The first point whose state `memory` is, or of which it is a view.
    pub(crate) fn memory_occurrence_id(memory: &SharedMemory) -> Option<ProgramPointId> {
        memory.occurrence().map(|node| node.id)
    }

    /// The point this point's memory is the state at: its own path's point,
    /// or the point a memory-named point is placed as true at. `None` when
    /// it is only walked from a read, or has no place.
    pub(crate) fn memory_point_id(&self) -> Option<ProgramPointId> {
        if let Some(id) = self.path.id() {
            return Some(id);
        }
        match &self.read {
            ReadSelection::Legacy(LegacyPlace::TrueAt(node)) => Some(node.id),
            _ => None,
        }
    }

    /// The point on a path a read through this point was made at: the
    /// point's own path when it has one, else the place its memory was
    /// given. `None` for an unplaced point.
    pub(crate) fn read_site(&self) -> Option<PathLink> {
        if self.path.id().is_some() {
            return Some(self.path.clone());
        }
        match &self.read {
            ReadSelection::Legacy(LegacyPlace::TrueAt(node) | LegacyPlace::WalkedFrom(node)) => {
                Some(PathLink(Some(node.clone()), IndexedView::Recorded))
            }
            _ => None,
        }
    }

    /// The point a `SymbolicMemory` value stands at, interning it first. Callers
    /// that already hold an interned state use [`ProgramPoint::at`].
    pub(crate) fn of_memory(memory: &SymbolicMemory) -> Self {
        Self::unplaced(&intern_memory(memory.clone()))
    }

    /// The first point of a new path, standing at `memory`: a place no other
    /// point leads to, such as the memory a pure theorem quantifies over. Unlike
    /// [`ProgramPoint::of_memory`], the point has a place on a path, so reads
    /// there can be followed back along it.
    pub(crate) fn starting_at(memory: &SymbolicMemory) -> Self {
        let shared = intern_memory_ref(memory);
        let path = PathLink::default().after(shared.clone(), memory.pending_steps.clone());
        Self {
            memory: shared,
            path,
            read: ReadSelection::Legacy(LegacyPlace::OwnPath),
        }
    }

    /// The point a state stands at on its path.
    #[cfg_attr(not(test), allow(dead_code))]
    /// The point a state with `memory` stands at, `path` being the last
    /// point it reached. Steps the state has taken since, still in the
    /// memory's log, are a point of their own after that one, so the point
    /// handed out holds the memory it names. The log determines the
    /// successor even when the steps return to the predecessor's contents.
    pub(super) fn of_state(memory: &SymbolicMemory, path: &PathLink) -> Self {
        assert!(
            memory.pending_steps.is_none(),
            "a state with staged steps is read before its atomic region completes"
        );
        Self {
            memory: intern_memory_ref(memory),
            path: path.clone(),
            read: ReadSelection::Legacy(LegacyPlace::OwnPath),
        }
    }

    pub(crate) fn shared_memory(&self) -> &SharedMemory {
        &self.memory
    }

    /// This point with its memory's values renamed: the same place on the
    /// path, its memory spelled with substituted variables.
    pub(crate) fn with_renamed_memory(&self, memory: SharedMemory) -> Self {
        Self {
            memory,
            path: self.path.clone(),
            read: self.read.clone(),
        }
    }

    /// Where on its path this point is.
    pub(crate) fn path_link(&self) -> &PathLink {
        &self.path
    }

    /// The interned memory state this point stands for, by value.
    pub(crate) fn into_shared_memory(self) -> SharedMemory {
        self.memory
    }

    pub(crate) fn memory(&self) -> &SymbolicMemory {
        self.memory.memory()
    }

    /// This point's identity on its path, or none for a point built from a
    /// bare memory state.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn id(&self) -> Option<ProgramPointId> {
        self.path.id()
    }

    /// The point in a read's key, whether selected exactly or as a version.
    pub(crate) fn read_version_id(&self) -> Option<ProgramPointId> {
        if !matches!(self.read, ReadSelection::Legacy(_)) {
            self.id()
        } else {
            None
        }
    }

    pub(in crate::kernel) fn read_key(&self) -> ReadKey {
        match self.read_version_id() {
            Some(id) => self.read_key_at(id),
            None => ReadKey::Memory(self.memory.arena_id()),
        }
    }

    /// Read applications use the execution version when known. Legacy views
    /// retain their existing read identity across pure memory materialization.
    pub(in crate::kernel) fn congruence_read_key(&self) -> ReadKey {
        match self.read_version_id() {
            Some(id) => self.read_key_at(id),
            None => ReadKey::Memory(self.memory.read_identity()),
        }
    }

    pub(in crate::kernel) fn observation_key(&self) -> ReadKey {
        match self.id() {
            Some(id) => self.read_key_at(id),
            None => ReadKey::Memory(self.memory.arena_id()),
        }
    }

    /// The read can be identified by the point alone, including through a
    /// view that only materialized names for bytes the point already held.
    pub(crate) fn has_certified_read_view(&self) -> bool {
        matches!(self.observation_key(), ReadKey::Point(_))
    }

    fn read_key_at(&self, id: ProgramPointId) -> ReadKey {
        if self.path.matches_indexed_view(&self.memory) {
            ReadKey::Point(id)
        } else {
            ReadKey::View(id, self.memory.arena_id())
        }
    }

    pub(crate) fn names_exact_read(&self, read: &Self) -> bool {
        self.id()
            .is_some_and(|id| self.read_key_at(id) == read.read_key())
    }

    /// Whether this recorded view can name the supplied read. A selected
    /// version admits another certified view of the same point. An
    /// unselected read still has a memory identity in its kernel term.
    pub(crate) fn names_read_view(&self, read: &Self) -> bool {
        if read.read_version_id().is_some() {
            self.names_exact_read(read)
        } else {
            read.id().is_some_and(|id| {
                self.id() == Some(id) && self.memory.arena_id() == read.memory.arena_id()
            })
        }
    }

    /// An exact read keeps the selected point even if another point has equal
    /// memory or supplies the cell's ordinary version.
    pub(in crate::kernel) fn for_exact_read(mut self) -> Self {
        // A point with no path has no point to keep: an exact selection of it
        // reads as a legacy one. Keep the legacy read site it recorded.
        if self.id().is_none() {
            return self;
        }
        self.read = ReadSelection::Exact;
        self
    }

    /// The same view identified by its memory, as an unselected point is.
    /// Reads through it still use the recorded path's cell versions.
    pub(in crate::kernel) fn for_legacy_read(mut self) -> Self {
        self.read = ReadSelection::Legacy(LegacyPlace::OwnPath);
        self
    }

    /// This point selected as an indexed cell read, as an unwritten static
    /// cell's entry version is: for tests that build one cell's load from
    /// two selection kinds of one point.
    #[cfg(test)]
    pub(in crate::kernel) fn for_indexed_cell_read(mut self) -> Self {
        self.read = ReadSelection::IndexedCell;
        self
    }

    pub(crate) fn is_exact_read(&self) -> bool {
        matches!(self.read, ReadSelection::Exact) && self.id().is_some()
    }

    /// Skip the recorded suffix that is already known to leave the entire
    /// parameter storage alone. An unverified view cannot use the suffix.
    pub(in crate::kernel) fn parameter_read_start(&self, block: &AddressBase) -> Self {
        if !external_storage(block) {
            return self.clone();
        }
        let anchor = self
            .path
            .0
            .as_ref()
            .filter(|_| self.path.matches_indexed_view(&self.memory))
            .and_then(|point| point.external_read_start.as_ref());
        if let Some(anchor) = anchor
            && let Some(point) = anchor.point.upgrade()
        {
            return Self {
                memory: anchor.memory.clone(),
                path: PathLink(Some(point), anchor.view.clone()),
                read: ReadSelection::Legacy(LegacyPlace::OwnPath),
            };
        }
        self.clone()
    }

    /// A recorded version for an array in automatic, static, heap, or caller storage.
    pub(in crate::kernel) fn indexed_array_version(&self, block: &AddressBase) -> Option<Self> {
        if indexed_array_object(block) {
            return self.indexed_block_array_version(block);
        }
        if !external_storage(block) {
            return None;
        }
        let anchor = external_array_anchor(&self.path, &self.memory)?;
        let origin = anchor.point.upgrade()?;
        if !origin.function_entry && *block != AddressBase::ExternalArgument {
            return None;
        }
        Some(Self {
            memory: anchor.memory,
            path: PathLink(Some(origin), anchor.view),
            read: ReadSelection::Exact,
        })
    }

    fn indexed_block_array_version(&self, block: &AddressBase) -> Option<Self> {
        if !self.path.matches_indexed_view(&self.memory) {
            return None;
        }
        let current = self.path.0.as_ref()?;
        if current.function_entry && block.is_static_storage_block() {
            return Some(self.clone().for_exact_read());
        }
        let versions = current.array_block_versions.as_ref()?;
        if let Some(write) = versions.writes.get(block) {
            let version = write.point.upgrade()?;
            return Some(Self {
                memory: version.memory.clone(),
                path: PathLink(Some(version), IndexedView::Recorded),
                read: ReadSelection::Exact,
            });
        }
        if !block.is_static_storage_block() {
            return None;
        }
        versions.static_entry.as_ref()?.read(ReadSelection::Exact)
    }

    /// A scalar supplied by the caller can have a version even when no
    /// store supplies a value. Use the recorded disjoint suffix only when
    /// it reaches a verified function-entry view.
    pub(crate) fn entry_integer_version(&self, pointer: &Address, kind: LoadKind) -> Option<Self> {
        if !kind.is_word32()
            && !matches!(
                kind,
                LoadKind::Int8
                    | LoadKind::UInt8
                    | LoadKind::Int16
                    | LoadKind::UInt16
                    | LoadKind::Bits64
                    | LoadKind::Int128
                    | LoadKind::UInt128
            )
        {
            return None;
        }
        self.external_entry_read(pointer, Some(kind.byte_width()), false)
    }

    pub(crate) fn generic_entry_version(
        &self,
        pointer: &Address,
        parameter: super::TypeParameterName,
    ) -> Option<Self> {
        if parameter.is_enum() {
            return None;
        }
        self.external_entry_read(pointer, None, false)
    }

    /// The entry version of a caller cell of `bytes`, when unknown its width
    /// is `None`: from a suffix that left all caller storage alone, or, for
    /// a known width, from a record of the caller bytes written since entry.
    fn external_entry_read(
        &self,
        pointer: &Address,
        bytes: Option<u32>,
        allow_materialized_entry: bool,
    ) -> Option<Self> {
        if pointer.base != AddressBase::ExternalArgument {
            return None;
        }
        self.external_entry_read_from_suffix(pointer, allow_materialized_entry)
            .or_else(|| {
                let bytes = bytes?;
                if !self.path.matches_indexed_view(&self.memory) {
                    return None;
                }
                self.path
                    .0
                    .as_ref()?
                    .external_entry_writes
                    .as_ref()?
                    .unwritten_entry_read(pointer, bytes, allow_materialized_entry)
            })
    }

    fn external_entry_read_from_suffix(
        &self,
        pointer: &Address,
        allow_materialized_entry: bool,
    ) -> Option<Self> {
        let mut entry = self.parameter_read_start(&pointer.base);
        let node = entry.path.0.as_ref()?;
        // Entry setup can attach a proof view to the root without executing
        // a write. Its selected reads name the original entry bytes, including
        // when a symbolic index does not pick one of its materialized cells.
        if !node.function_entry
            || !entry.path.matches_indexed_view(&entry.memory)
            || node.memory.memory() != &SymbolicMemory::default()
            || (!allow_materialized_entry && entry.memory() != &SymbolicMemory::default())
        {
            return None;
        }
        entry.memory = node.memory.clone();
        entry.path.1 = IndexedView::Recorded;
        entry.read = ReadSelection::Entry;
        Some(entry)
    }

    pub(in crate::kernel) fn is_entry_read(&self) -> bool {
        matches!(self.read, ReadSelection::Entry) && self.path.matches_indexed_view(&self.memory)
    }

    /// A rewritten address keeps this entry only when ordinary lowering can
    /// select it for the new cell too.
    pub(in crate::kernel) fn entry_version_after_rewrite(
        &self,
        pointer: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        if self.is_entry_read() {
            self.entry_integer_version(pointer, kind)
        } else {
            None
        }
    }

    /// The original entry version that a logical read or a materialized
    /// observation can name even when entry setup attached a proof view.
    pub(crate) fn entry_cell_version(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        match value_type {
            ProgramType::Int8
            | ProgramType::UInt8
            | ProgramType::Int16
            | ProgramType::UInt16
            | ProgramType::Int32
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64
            | ProgramType::Int128
            | ProgramType::UInt128 => self
                .external_entry_read(pointer, Some(value_type.byte_width()), true)
                .or_else(|| self.entry_read_through_loaded_pointer(pointer, value_type)),
            value_type if value_type.is_pointer() => {
                self.external_entry_read(pointer, Some(value_type.byte_width()), true)
            }
            ProgramType::Parameter(parameter) if !parameter.is_enum() => {
                self.external_entry_read(pointer, None, true)
            }
            _ => None,
        }
    }

    /// A pointer read at this function's entry cannot designate a local
    /// created later. A suffix already known to affect only local storage
    /// therefore leaves the caller cell it designates at the entry version.
    fn entry_read_through_loaded_pointer(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        let loaded = pointer.as_loaded_value()?;
        let current = self.path.0.as_ref()?;
        if !self.has_certified_read_view() {
            return None;
        }
        // The existing 64-bit model-pointer reads use the current entry
        // name. Other widths need the pointer's own recorded entry load.
        if current.function_entry && matches!(value_type, ProgramType::Int64 | ProgramType::UInt64)
        {
            return Some(self.clone().for_exact_read());
        }
        let entry = self.parameter_read_start(&AddressBase::ExternalArgument);
        let root = entry.path.0.as_ref()?;
        (root.function_entry
            && entry.has_certified_read_view()
            && loaded.point.has_certified_read_view()
            && loaded.point.read_version_id() == entry.id())
        .then(|| entry.for_exact_read())
    }

    pub(in crate::kernel) fn supports_static_entry_version(
        pointer: &Address,
        value_type: ProgramType,
    ) -> bool {
        pointer.base.is_static_storage_block()
            && MachineIntegerType::from_program_type(value_type).is_some()
    }

    /// The entry version of a static integer cell for which the recorded
    /// path has no writes to any byte it reads.
    pub(in crate::kernel) fn unwritten_static_scalar_version(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        if !Self::supports_static_entry_version(pointer, value_type)
            || !self.has_certified_read_view()
        {
            return None;
        }
        let current = self.path.0.as_ref()?;
        if current.function_entry {
            let mut entry = self.clone();
            entry.read = ReadSelection::IndexedCell;
            return Some(entry);
        }
        let versions = current.array_block_versions.as_ref()?;
        if let Some(write) = versions.writes.get(&pointer.base) {
            let written = write.static_writes.as_ref()?;
            let mut span = super::static_cell_byte_span(pointer, value_type.byte_width())?;
            // Indexed call ranges have signed 32-bit byte endpoints. A
            // fixed scalar offset can use the rest of the address space.
            let limit = i64::from(i32::MAX);
            let changed_by_call = span.start < limit
                && written
                    .calls
                    .latest(span.start as u32..span.end.min(limit) as u32)
                    .is_some();
            if changed_by_call
                || span.any(|byte| {
                    crate::instrumentation::record_deterministic_work(1);
                    written.stores.contains(&byte)
                })
            {
                return None;
            }
        }
        versions
            .static_entry
            .as_ref()?
            .read(ReadSelection::IndexedCell)
    }

    /// Connect an entry read already established by the legacy path resolver
    /// to the recorded entry on this execution path. The resolved view can
    /// be the entry itself or the recorded input of the last block write.
    /// The view only certifies the choice; the entry point identifies the read.
    pub(in crate::kernel) fn static_entry_matching_resolved_read(
        &self,
        pointer: &Address,
        value_type: ProgramType,
        resolved: &SharedMemory,
    ) -> Option<Self> {
        if !self.has_certified_read_view() {
            return None;
        }
        let entry = self
            .path
            .0
            .as_ref()?
            .array_block_versions
            .as_ref()?
            .static_entry
            .as_ref()?;
        if entry.memory.arena_id() == resolved.arena_id() {
            return entry.read(ReadSelection::IndexedCell);
        }
        let latest = self.indexed_array_version(&pointer.base)?;
        let transition = latest.path.0.as_ref()?;
        let [before] = transition.predecessors.as_ref() else {
            return None;
        };
        let steps = transition.steps.as_ref()?;
        if !steps.contiguous
            || steps.first_base.arena_id() != resolved.arena_id()
            || !before.matches_indexed_view(&steps.first_base)
        {
            return None;
        }
        Self {
            memory: steps.first_base.clone(),
            path: before.clone(),
            read: ReadSelection::Legacy(LegacyPlace::OwnPath),
        }
        .unwritten_static_scalar_version(pointer, value_type)
    }

    /// The version a read of `pointer` as `value_type` is named at from this
    /// point, when the point indexes select one. Producers are moving to this
    /// one question, asked after a value the memory holds for the cell
    /// (`design/point-named-reads.md`, P1), so that two producers of one cell
    /// at one point name it alike. Logical integer reads ask it.
    pub(crate) fn read_version(&self, pointer: &Address, value_type: ProgramType) -> Option<Self> {
        if MachineIntegerType::from_program_type(value_type).is_none() && !value_type.is_pointer() {
            return None;
        }
        self.ordinary_typed_version(pointer, value_type)
            .or_else(|| self.entry_cell_version(pointer, value_type))
    }

    pub(crate) fn ordinary_typed_version(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        self.indexed_typed_version(pointer, value_type)
            .or_else(|| {
                MachineIntegerType::from_program_type(value_type)?;
                self.call_output_integer_version(pointer, LoadKind::of_type(value_type)?)
            })
            .or_else(|| self.unwritten_static_scalar_version(pointer, value_type))
            .or_else(|| self.entry_cell_version(pointer, value_type))
    }

    pub(in crate::kernel) fn supports_local_call_output(pointer: &Address) -> bool {
        indexed_local(&pointer.base) && matches!(pointer.offset.view(), OffsetView::Constant(0))
    }

    pub(in crate::kernel) fn call_output_integer_version(
        &self,
        pointer: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        if pointer.base.is_static_storage_block() {
            return self.whole_static_call_output(pointer, kind.byte_width());
        }
        if !Self::supports_local_call_output(pointer) {
            return None;
        }
        self.indexed_version(pointer, kind.byte_width(), |effect| {
            matches!(
                effect,
                MemoryDerivation::ObjectInitializationRecorded {
                    call_output: Some(output),
                    ..
                } if kind.reads_word_of(*output)
            )
        })
    }

    /// A call with one complete static scalar in its checked footprint creates
    /// that word's next version, even though the caller does not know its bits.
    fn whole_static_call_output(&self, pointer: &Address, bytes: u32) -> Option<Self> {
        use crate::kernel::effective_type::CAccessClass;

        let memory = self.memory();
        if !matches!(pointer.offset.view(), OffsetView::Constant(0))
            || memory.block_size(&pointer.base)?.as_const()? != bytes
            || !matches!(
                memory.declared_class(pointer),
                Some(CAccessClass::Scalar(_))
            )
        {
            return None;
        }
        let mut version = self.indexed_block_array_version(&pointer.base)?;
        let source = &version.path.0.as_ref()?.steps.as_ref()?.step;
        let MemoryDerivation::CallHavoc { mutable_ranges, .. } = source.as_ref() else {
            return None;
        };
        let [range] = mutable_ranges.as_slice() else {
            return None;
        };
        if range.base().base != pointer.base || super::static_call_range(range)?.0 != (0..bytes) {
            return None;
        }
        version.read = ReadSelection::CallOutput;
        Some(version)
    }

    pub(crate) fn supports_indexed_version(pointer: &Address) -> bool {
        read_bucket(&pointer.base).is_some()
            || (pointer.base.is_static_storage_block()
                && matches!(pointer.offset.view(), OffsetView::Constant(0)))
    }

    /// A direct integer cell's version, if this path has a recorded direct write
    /// and the transitions after it preserve the object by construction.
    pub(crate) fn indexed_integer_version(
        &self,
        pointer: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        self.indexed_version(pointer, kind.byte_width(), |store| {
            integer_store_bits(store).is_some_and(|(stored_kind, _)| stored_kind == kind)
        })
    }

    pub(crate) fn indexed_typed_version(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        let indexed_algebraic = matches!(value_type, ProgramType::Parameter(ty)
            if indexed_local(&pointer.base)
                && matches!(pointer.offset.view(), OffsetView::Constant(_))
                && !ty.has_abstract_size());
        if let Some(category) = super::PointerLoadCategory::of_type(value_type) {
            return self.indexed_pointer_version(pointer, Some(category));
        }
        if value_type == ProgramType::Bool || value_type.is_pointer() || indexed_algebraic {
            return self.indexed_version(pointer, value_type.byte_width(), |store| {
                matches!(store, MemoryDerivation::Store { value, .. } if value.program_type() == value_type)
            });
        }
        self.indexed_integer_version(pointer, LoadKind::of_type(value_type)?)
    }

    /// The version a pointer load of `category` names at this point when a
    /// recorded store wrote exactly its eight-byte cell. A load's identity is
    /// its version point and cell, not the pointee type it decodes at
    /// (`design/loads.md`, "Pointers"): a store of a pointer of the same
    /// category answers it at any pointee type, while a store of the other
    /// category does not. A partial or overlapping store still ends the
    /// version by `indexed_version`'s extent check.
    ///
    /// With no category the question is about the cell's bytes, not a
    /// decoding of them: a store of a pointer of either category answers.
    pub(crate) fn indexed_pointer_version(
        &self,
        pointer: &Address,
        category: Option<super::PointerLoadCategory>,
    ) -> Option<Self> {
        self.indexed_version(pointer, super::C_POINTER_BYTE_WIDTH, |store| {
            matches!(store, MemoryDerivation::Store { value, .. }
                if super::PointerLoadCategory::of_type(value.program_type())
                    .is_some_and(|stored| category.is_none_or(|category| stored == category)))
        })
    }

    /// The version a slice load names at this point when a recorded store
    /// wrote a slice to exactly its 16-byte cell
    /// (`design/rust-slice-values.md`, step 2b-ii-b). A store into either
    /// word ends the version by `indexed_version`'s extent check.
    pub(crate) fn indexed_slice_version(&self, pointer: &Address) -> Option<Self> {
        self.indexed_version(pointer, super::WIDE_POINTER_BYTE_WIDTH, |store| {
            matches!(store, MemoryDerivation::Store { value, .. }
                if value.program_type().is_slice_pointer())
        })
    }

    pub(super) fn abstract_local_version(
        &self,
        pointer: &Address,
        parameter: super::TypeParameterName,
    ) -> Option<Self> {
        if !indexed_local(&pointer.base)
            || !matches!(pointer.offset.view(), OffsetView::Constant(0))
        {
            return None;
        }
        self.indexed_version(pointer, super::ABSTRACT_VALUE_WIDTH, |store| {
            matches!(store, MemoryDerivation::Store { value, .. }
                if value.program_type() == ProgramType::Parameter(parameter))
        })
    }

    fn indexed_version(
        &self,
        pointer: &Address,
        bytes: u32,
        matches_source: impl FnOnce(&MemoryDerivation) -> bool,
    ) -> Option<Self> {
        if pointer.base.is_static_storage_block() {
            return self.indexed_whole_static_store(pointer, bytes, matches_source);
        }
        let bucket = read_bucket(&pointer.base)?;
        let node = self.path.0.as_ref()?;
        if !self.path.matches_indexed_view(&self.memory) {
            return None;
        }
        let (anchor, start) = read_displacement(&pointer.offset)?;
        let end = start.checked_add(i64::from(bytes))?;
        let block = node.point_read_index.blocks.get(bucket)?;
        if block.origin != read_origin(pointer, anchor) {
            return None;
        }
        let write = block.cells.get(&start)?;
        if write.end != end || !matches_source(&write.source) {
            return None;
        }
        let version = write.version.upgrade()?;
        Some(Self {
            memory: version.memory.clone(),
            path: PathLink(Some(version), IndexedView::Recorded),
            read: if matches!(
                write.source.as_ref(),
                MemoryDerivation::ObjectInitializationRecorded {
                    call_output: Some(_),
                    ..
                }
            ) {
                ReadSelection::CallOutput
            } else {
                ReadSelection::IndexedWrite(write.source.clone())
            },
        })
    }

    /// A whole-object scalar can use the block's recorded version directly.
    /// Select one store from the sealed point, without searching older effects.
    fn indexed_whole_static_store(
        &self,
        pointer: &Address,
        bytes: u32,
        matches_source: impl FnOnce(&MemoryDerivation) -> bool,
    ) -> Option<Self> {
        if !matches!(pointer.offset.view(), OffsetView::Constant(0))
            || self.memory().block_size(&pointer.base)?.as_const()? != bytes
        {
            return None;
        }
        let mut version = self.indexed_block_array_version(&pointer.base)?;
        let source = &version.path.0.as_ref()?.steps.as_ref()?.step;
        let MemoryDerivation::Store {
            pointer: written,
            value,
            ..
        } = source.as_ref()
        else {
            return None;
        };
        if written != pointer || value.byte_width() != bytes || !matches_source(source) {
            return None;
        }
        version.read = ReadSelection::IndexedWrite(source.clone());
        Some(version)
    }

    /// The recorded value of this indexed read's defining store.
    pub(crate) fn indexed_integer_store_bits(&self) -> Option<&OldMachineTerm> {
        integer_store_bits(self.indexed_write()?).map(|(_, bits)| bits)
    }

    /// A detached observation can name the same store as an indexed read
    /// when it retains that store's exact snapshot and cell.
    pub(in crate::kernel) fn names_detached_store_read(
        &self,
        detached: &Self,
        address: &Address,
        kind: LoadKind,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        detached.id().is_none()
            && detached.shared_memory().arena_id() == self.shared_memory().arena_id()
            && self.indexed_write().is_some_and(|write| {
                matches!(write, MemoryDerivation::Store { pointer, .. } if pointer == address)
                    && integer_store_bits(write).is_some_and(|(stored, _)| stored == kind)
            })
    }

    pub(in crate::kernel) fn indexed_stored_value(&self) -> Option<&StoredMemoryValue> {
        let MemoryDerivation::Store { value, .. } = self.indexed_write()? else {
            return None;
        };
        Some(value)
    }

    fn indexed_write(&self) -> Option<&MemoryDerivation> {
        match &self.read {
            ReadSelection::IndexedWrite(store) if self.path.matches_indexed_view(&self.memory) => {
                Some(store)
            }
            _ => None,
        }
    }

    /// The identities of the points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessor_ids(&self) -> Vec<ProgramPointId> {
        self.path.predecessor_ids()
    }

    /// True when this point is later in the recorded history than `other`.
    /// SymbolicMemory state ids strictly increase along derivation edges, so comparing
    /// them orders two points of one arena without walking.
    pub(crate) fn is_later_than(&self, other: &Self) -> bool {
        let (arena, id) = self.memory.arena_id();
        let (other_arena, other_id) = other.memory.arena_id();
        arena == other_arena && id > other_id
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::PathLink;

    fn memory_holding(value: u32) -> SymbolicMemory {
        let block: AddressBase = "local:slot".into();
        let slot = Address::new(block.clone(), AddressOffset::constant(0));
        SymbolicMemory::new()
            .with_block(block, 4)
            .store(slot, ProgramValue::Int32(OldMachineTerm::constant(value)))
    }

    fn slot() -> Address {
        Address::new("local:slot".into(), AddressOffset::constant(0))
    }

    fn stored(state: &ExecutionState, value: u32) -> ExecutionState {
        let memory = state
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(OldMachineTerm::constant(value)));
        state.clone().with_memory(memory)
    }

    /// Two paths store different values and then the same one, so they end
    /// in one interned memory, whose arena history is the first path's. Each
    /// final point still holds the store its own path made, from its own
    /// predecessor's memory.
    #[test]
    fn each_point_holds_the_steps_its_own_path_took() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let left_mid = stored(&start, 1);
        let right_mid = stored(&start, 2);
        let left = stored(&left_mid, 3);
        let right = stored(&right_mid, 3);
        assert_eq!(left.program_point(), right.program_point());

        let base_of_only_step = |state: &ExecutionState| {
            let steps = state.path_link().steps().expect("a store is a step");
            let mut steps = steps.newest_first();
            let (step, produced) = steps.next().unwrap();
            assert!(steps.next().is_none());
            assert_eq!(produced, state.program_point().shared_memory());
            step.base().clone()
        };
        assert_eq!(
            base_of_only_step(&left),
            *left_mid.program_point().shared_memory()
        );
        assert_eq!(
            base_of_only_step(&right),
            *right_mid.program_point().shared_memory()
        );
        assert!(left.memory().pending_steps.is_none());
    }

    /// A legacy read records where its memory belongs, and the record is no
    /// part of its identity: the read placed at a site is the same term as
    /// the read of the same memory built from that memory alone. A view of
    /// a state is placed as true there; the legacy walk's memory, and any
    /// view of it, only as walked from there.
    /// A memory a point held is true at the first point that held it,
    /// whoever builds a point from it: an earlier state reached by a walk is
    /// placed at its own point, not the read's. A memory no point held has
    /// no place. Identity stays the memory.
    #[test]
    fn a_memory_is_placed_at_the_point_that_held_it() {
        let earlier = stored(&ExecutionState::default().with_memory(memory_holding(0)), 1);
        let earlier_point = earlier.program_point();
        let later = stored(&earlier, 2);
        let read_at = later.program_point();
        let walked = ProgramPoint::walked(earlier_point.shared_memory(), &read_at);
        assert!(matches!(
            walked.read,
            super::ReadSelection::Legacy(super::LegacyPlace::TrueAt(_))
        ));
        assert!(
            walked
                .read_site()
                .is_some_and(|path| path.id() == earlier_point.id())
        );
        assert_eq!(walked, ProgramPoint::at(earlier_point.shared_memory()));
        let never_held = crate::kernel::intern_memory(memory_holding(9));
        assert!(ProgramPoint::at(&never_held).read_site().is_none());
    }

    #[test]
    fn a_legacy_read_records_its_place_without_changing_its_term() {
        let state = stored(&ExecutionState::default().with_memory(memory_holding(0)), 1);
        let site = state.program_point();
        let memory = site.shared_memory().clone();
        let bare = ProgramPoint::at(&memory);
        let sited = ProgramPoint::read_at(&memory, &site);
        // The memory is the state at the site, so even a point built from
        // it alone is placed there.
        assert!(bare.read_site().is_some_and(|path| path.id() == site.id()));
        assert!(sited.read_site().is_some_and(|path| path.id() == site.id()));
        assert_eq!(sited.read_key(), bare.read_key());
        assert_eq!(sited, bare);
        assert_eq!(
            OldMachineTerm::read_named(sited.clone(), slot(), LoadKind::Int32),
            OldMachineTerm::read_named(bare.clone(), slot(), LoadKind::Int32)
        );
        let rebuilt = ProgramPoint::read_at(&memory, &sited);
        assert!(
            rebuilt
                .read_site()
                .is_some_and(|path| path.id() == site.id())
        );
        assert!(matches!(
            sited.read,
            super::ReadSelection::Legacy(super::LegacyPlace::TrueAt(_))
        ));
        // A walked memory no point held is placed only as walked from the
        // read, and a view of it inherits that.
        let never_held = crate::kernel::intern_memory(memory_holding(9));
        let walked = ProgramPoint::walked(&never_held, &site);
        assert!(matches!(
            walked.read,
            super::ReadSelection::Legacy(super::LegacyPlace::WalkedFrom(_))
        ));
        assert!(
            walked
                .read_site()
                .is_some_and(|path| path.id() == site.id())
        );
        assert_eq!(walked, ProgramPoint::at(&never_held));
        assert!(matches!(
            ProgramPoint::viewing(&never_held, &walked).read,
            super::ReadSelection::Legacy(super::LegacyPlace::WalkedFrom(_))
        ));
        // A point with no path has no point for an exact selection to keep,
        // so it keeps its read site, and its term is unchanged.
        let exact = sited.clone().for_exact_read();
        assert!(exact.read_site().is_some_and(|path| path.id() == site.id()));
        assert_eq!(exact.read_key(), bare.read_key());
        assert!(!exact.is_exact_read());
    }

    /// A state set up by steps before its first point begins at the memory
    /// those steps started from, so a walk back can cross them.
    #[test]
    fn a_path_begins_before_its_first_steps() {
        let state = ExecutionState::default().with_memory(memory_holding(0));
        let point = state.program_point();
        let [start] = point.path_link().predecessors() else {
            panic!("the first point follows the path's start");
        };
        assert!(start.predecessors().is_empty());
        assert_eq!(start.memory(), Some(&intern_memory(SymbolicMemory::new())));
    }

    /// A point that starts a path has an identity even when no step reached
    /// its memory.
    #[test]
    fn a_starting_point_has_a_place_on_a_path() {
        let point = ProgramPoint::starting_at(&SymbolicMemory::new());
        assert!(point.id().is_some());
        assert!(
            ProgramPoint::of_memory(&SymbolicMemory::new())
                .id()
                .is_none()
        );
    }

    /// A join records where its arms split.
    #[test]
    fn a_join_records_where_its_arms_split() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let left = stored(&start, 1);
        let right = stored(&start, 1);
        let mut joined = left.clone();
        joined.join_program_points(&left, &right, start.path_link());
        assert_eq!(
            joined.path_link().split().and_then(PathLink::id),
            start.program_point().id()
        );
    }

    #[test]
    fn a_single_loop_exit_keeps_the_caller_array_read_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let block = AddressBase::ExternalArgument;
        let cell = Address::new(block.clone(), AddressOffset::constant(0));
        let effect = entry.clone().with_memory(
            entry
                .memory()
                .clone()
                .store(cell, ProgramValue::Int32(OldMachineTerm::constant(7))),
        );
        let mut joined = effect.clone();
        joined.join_loop_exit_program_points(&[&effect]);
        assert_ne!(joined.program_point_id(), effect.program_point_id());
        let selected = joined
            .program_point()
            .indexed_array_version(&block)
            .expect("the join keeps the caller array version");
        assert_eq!(selected.read_version_id(), effect.program_point_id());
    }

    #[test]
    fn an_entry_read_names_its_point_without_a_store_receipt() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let other_entry = ExecutionState::new().begin_function_entry_memory();
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let select = |state: &ExecutionState| {
            state
                .program_point()
                .ordinary_typed_version(&pointer, ProgramType::Int32)
        };
        let version = select(&entry).expect("an ordinary entry version");
        assert_eq!(version.read_version_id(), entry.program_point().id());
        assert!(version.indexed_integer_store_bits().is_none());
        let pointer_entry = entry
            .program_point()
            .ordinary_typed_version(&pointer, ProgramType::Int32Pointer)
            .expect("an ordinary entry pointer version");
        assert_eq!(pointer_entry, version);
        assert!(pointer_entry.indexed_stored_value().is_none());
        assert_ne!(select(&other_entry).unwrap(), version);

        let declared = entry
            .clone()
            .with_memory(entry.memory().clone().with_block("local:slot", 4));
        let after_local_store = stored(&declared, 3);
        assert_eq!(select(&after_local_store), Some(version.clone()));
        let exact = after_local_store.program_point().for_exact_read();
        assert!(exact.is_exact_read());
        assert_ne!(exact, version);

        let overwritten =
            after_local_store
                .clone()
                .with_memory(after_local_store.memory().clone().store(
                    pointer.clone(),
                    ProgramValue::Int32(OldMachineTerm::constant(7)),
                ));
        let new_version = select(&overwritten).expect("the defining store is indexed");
        assert_ne!(new_version, version);
        assert_eq!(
            new_version.indexed_integer_store_bits(),
            Some(&OldMachineTerm::constant(7))
        );
        let detached = ProgramPoint::at(new_version.shared_memory());
        assert!(new_version.names_detached_store_read(&detached, &pointer, LoadKind::Int32));
        assert!(!new_version.names_detached_store_read(&detached, &pointer, LoadKind::UInt32));
        assert!(!new_version.names_detached_store_read(
            &ProgramPoint::at(version.shared_memory()),
            &pointer,
            LoadKind::Int32,
        ));
    }

    #[test]
    fn int32_through_an_entry_pointer_keeps_entry_after_a_local_store() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let pointer_slot = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let pointer = Pointer::from_point_read(
            entry.program_point().for_exact_read(),
            ProgramType::Int32Pointer,
            &pointer_slot,
        );
        assert!(matches!(pointer.address().base, AddressBase::Load(_)));
        let declared = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(slot().base.clone(), 4));
        let after_local_store = stored(&declared, 3);
        let select = |state: &ExecutionState| {
            state
                .program_point()
                .ordinary_typed_version(pointer.address(), ProgramType::Int32)
                .and_then(|version| version.read_version_id())
        };
        assert_eq!(select(&after_local_store), entry.program_point().id());

        let after_external_store =
            after_local_store
                .clone()
                .with_memory(after_local_store.memory().clone().store(
                    pointer_slot,
                    ProgramValue::Int32(OldMachineTerm::constant(7)),
                ));
        assert_eq!(select(&after_external_store), None);
    }

    #[test]
    fn int32_through_an_unanchored_pointer_does_not_claim_an_entry_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let point = entry.program_point();
        let slot = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let pointer = Pointer::from_point_read(
            point.clone().for_legacy_read(),
            ProgramType::Int32Pointer,
            &slot,
        );
        assert!(matches!(pointer.address().base, AddressBase::Load(_)));
        assert!(
            point
                .ordinary_typed_version(pointer.address(), ProgramType::Int32)
                .is_none()
        );
    }

    #[test]
    fn caller_read_versions_survive_both_outcomes_of_fresh_allocation() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let caller_cell = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let loaded = Pointer::from_point_read(
            entry.program_point().for_exact_read(),
            ProgramType::UInt64Pointer,
            &caller_cell.offset_by_bytes(8),
        );
        let allocation = Address::symbolic(Variable(38_132));
        let pending =
            entry
                .clone()
                .with_memory(entry.memory().clone().with_pending_heap_allocation(
                    allocation.clone(),
                    AllocationSize::int32(16),
                    false,
                ));
        let assert_entry = |state: &ExecutionState| {
            for pointer in [&caller_cell, loaded.address()] {
                let version = state
                    .program_point()
                    .entry_cell_version(pointer, ProgramType::UInt64);
                assert_eq!(
                    version.as_ref().and_then(ProgramPoint::read_version_id),
                    entry.program_point().id(),
                );
            }
        };
        assert_entry(&pending);
        for succeeds in [false, true] {
            let (memory, _, _) = pending
                .memory()
                .clone()
                .resolve_pending_heap_allocation(&allocation, succeeds)
                .expect("resolve the pending allocation");
            assert_entry(&pending.clone().with_memory(memory));
        }
    }

    #[test]
    fn a_join_retains_the_common_external_entry() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let declared = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(slot().base.clone(), 4));
        let first = stored(&declared, 1);
        let second = stored(&declared, 2);
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(4));
        let join = |left: &ExecutionState, right: &ExecutionState| {
            let mut joined = left.clone();
            joined.join_program_points(left, right, declared.path_link());
            joined.program_point()
        };
        let entry_id = entry.program_point().id();
        assert_eq!(
            join(&first, &second)
                .entry_integer_version(&pointer, LoadKind::Int32)
                .and_then(|point| point.read_version_id()),
            entry_id,
        );

        let changed = second.clone().with_memory(second.memory().clone().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(3)),
        ));
        assert!(
            join(&first, &changed)
                .entry_integer_version(&pointer, LoadKind::Int32)
                .is_none()
        );
    }

    #[test]
    fn a_join_keeps_shared_array_versions_and_renames_changed_blocks() {
        let _session = crate::kernel::VerificationSession::enter();
        let static_cell = SymbolicMemory::global_pointer("static_array");
        let local_array = SymbolicMemory::local_pointer("local_array");
        let other = slot();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let entry_id = entry.observation_point_id();
        let write = |state: &ExecutionState, address: &Address, bits| {
            state.clone().with_memory(state.memory().clone().store(
                address.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(bits)),
            ))
        };
        let version = |point: &ProgramPoint, address: &Address| {
            point
                .indexed_array_version(&address.base)
                .and_then(|point| point.read_version_id())
        };
        let mut work = Vec::new();
        for count in [4, 16, 64, 256] {
            let mut before = entry.clone().with_memory(
                entry
                    .memory()
                    .clone()
                    .with_block(other.base.clone(), 4)
                    .with_block(local_array.base.clone(), 4),
            );
            for index in 0..count {
                let local = SymbolicMemory::local_pointer(format!("unrelated_{index}"));
                before = before
                    .clone()
                    .with_memory(before.memory().clone().with_block(local.base.clone(), 4));
            }
            let before = write(&before, &local_array, 7);
            let left = write(&before, &other, 1);
            let right = write(&before, &other, 2);
            let join = |left: &ExecutionState, right: &ExecutionState| {
                let mut result = left.clone();
                result.join_program_points(left, right, before.path_link());
                result.program_point()
            };
            let (joined, cost) =
                crate::instrumentation::measure_deterministic_work(|| join(&left, &right));
            assert_eq!(version(&joined, &static_cell), entry_id);
            assert_eq!(
                version(&joined, &local_array),
                before.observation_point_id(),
            );
            assert_eq!(version(&joined, &other), joined.id());
            work.push(cost);

            let changed = write(&right, &static_cell, 7);
            let joined = join(&left, &changed);
            assert_eq!(version(&joined, &static_cell), joined.id());

            let unclassified = write(&right, &Address::symbolic(Variable(1_037_601)), 7);
            assert!(version(&join(&left, &unclassified), &static_cell).is_none());
        }
        assert!(work.iter().all(|&cost| cost <= work[0] + 64), "{work:?}");
    }

    #[test]
    fn fixed_offset_versions_match_the_path_and_stop_at_overlaps_or_log_gaps() {
        let _session = crate::kernel::VerificationSession::enter();
        let left = slot();
        let right = left.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(left.base.clone(), 8));
        let store_word = |state: &ExecutionState, address: Address, bits| {
            state.clone().with_memory(
                state
                    .memory()
                    .clone()
                    .store(address, ProgramValue::Int32(OldMachineTerm::constant(bits))),
            )
        };
        let written = store_word(&start, right.clone(), 7);
        let sibling = store_word(&written, left.clone(), 1);
        let version = |state: &ExecutionState| {
            state
                .program_point()
                .indexed_integer_version(&right, LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        let walked = crate::kernel::resource_tracker::cell_version_on_path(
            sibling.path_link(),
            &right,
            4.into(),
        );
        assert_eq!(
            walked.and_then(|point| point.id()),
            written.program_point_id()
        );
        assert_eq!(version(&sibling), written.program_point_id());

        let overlapping = store_word(&sibling, left.offset_by_bytes(2), 0);
        assert_eq!(version(&overlapping), None);
        let byte = ProgramValue::UInt8(OldMachineTerm::narrow_constant(
            MachineIntegerType::UInt8,
            0,
        ));
        let middle_byte = sibling.clone().with_memory(
            sibling
                .memory()
                .clone()
                .store(right.offset_by_bytes(1), byte),
        );
        assert_eq!(version(&middle_byte), None);
        assert_eq!(version(&sibling), written.program_point_id());

        let replacement = sibling.memory().clone().store(
            right.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(9)),
        );
        let unlogged = sibling
            .clone()
            .with_materialized_memory_at_current_point(replacement);
        assert_eq!(unlogged.program_point_id(), sibling.program_point_id());
        assert_eq!(version(&unlogged), None);
        assert_eq!(version(&store_word(&unlogged, left, 2)), None);
    }

    #[test]
    fn a_join_keeps_the_shared_store_and_declines_a_same_value_rewrite() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = slot();
        let other = slot.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), 8));
        let split = stored(&start, 7);
        let write_sibling = |value| {
            split.clone().with_memory(split.memory().clone().store(
                other.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(value)),
            ))
        };
        let left = write_sibling(2);
        let right = write_sibling(3);
        let mut joined = left.clone();
        joined.join_program_points(&left, &right, split.path_link());
        let version = |state: &ExecutionState, pointer: &Address| {
            state
                .program_point()
                .indexed_integer_version(pointer, LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        assert_eq!(version(&joined, &slot), split.program_point_id());
        let walked = crate::kernel::resource_tracker::cell_version_on_path(
            joined.path_link(),
            &slot,
            4.into(),
        );
        assert_eq!(
            walked.and_then(|point| point.id()),
            split.program_point_id()
        );
        assert_eq!(version(&joined, &other), None);

        let rewritten = stored(&left, 7);
        assert_eq!(rewritten.memory(), left.memory());
        joined.join_program_points(&left, &rewritten, split.path_link());
        assert_eq!(version(&joined, &slot), None);
    }

    #[test]
    fn checked_call_and_loop_footprints_keep_the_other_object_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = slot();
        let other = Address::new("local:other".into(), AddressOffset::constant(0));
        let start = ExecutionState::new().with_memory(
            SymbolicMemory::new()
                .with_block(slot.base.clone(), 4)
                .with_block(other.base.clone(), 4),
        );
        let written = stored(&start, 7);
        let written = written.clone().with_memory(written.memory().clone().store(
            other.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(2)),
        ));
        let version = |state: &ExecutionState, pointer: &Address| {
            state
                .program_point()
                .indexed_integer_version(pointer, LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        let expected = version(&written, &slot);
        assert!(expected.is_some());
        let range = MemoryRange::new(other.clone(), 0.into(), 1.into());
        let called =
            written
                .clone()
                .with_memory(written.memory().clone().with_storage_memory_havoc(
                    Variable(38_131),
                    std::slice::from_ref(&range),
                    &PureFactContext::new(),
                ));
        assert_eq!(version(&called, &slot), expected);
        assert_eq!(version(&called, &other), None);
        let unknown =
            called
                .clone()
                .with_memory(called.memory().clone().with_storage_memory_havoc(
                    Variable(38_132),
                    &[MemoryRange::unnamed_footprint()],
                    &PureFactContext::new(),
                ));
        assert_eq!(version(&unknown, &slot), None);

        let mut head = written.clone();
        head.replace_loop_head_local_cell(
            other.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(3)),
        );
        let memory = head
            .memory()
            .clone()
            .with_loop_memory_havoc_preserving_borrows(
                Variable(38_133),
                &std::collections::BTreeSet::new(),
                Some(&[range]),
                None,
            );
        head.set_loop_head_memory(memory);
        assert_ne!(head.program_point_id(), written.program_point_id());
        assert_eq!(version(&head, &slot), expected);
        assert_eq!(version(&head, &other), None);
        let mut exit = head.clone();
        exit.join_loop_exit_program_points(&[&head]);
        assert_ne!(exit.program_point_id(), head.program_point_id());
        assert_eq!(version(&exit, &slot), expected);
        let rewritten = stored(&head, 7);
        exit.join_loop_exit_program_points(&[&head, &rewritten]);
        assert_eq!(version(&exit, &slot), None);
    }

    #[test]
    fn an_overlapping_write_or_a_log_gap_ends_the_earlier_batch_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let first = slot();
        let second = first.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(first.base.clone(), 8));
        let store = |place, value| (place, ProgramValue::Int32(OldMachineTerm::constant(value)));
        let (address, value) = store(first.clone(), 7);
        let initial = start.memory().clone().store(address, value);
        let (address, value) = store(second.clone(), 8);
        let batch = initial.clone().store(address, value);
        let kind = LoadKind::Int32;
        let version = |state: &ExecutionState, place: &Address| {
            state.program_point().indexed_integer_version(place, kind)
        };
        let overlap = start.clone().with_memory(batch.store(
            first.offset_by_bytes(2),
            ProgramValue::UInt8(OldMachineTerm::narrow_constant(
                MachineIntegerType::UInt8,
                0,
            )),
        ));
        assert!(version(&overlap, &first).is_none());
        assert_eq!(
            version(&overlap, &second)
                .unwrap()
                .indexed_integer_store_bits(),
            Some(&OldMachineTerm::constant(8))
        );

        let gap = initial.with_uninitialized_object(Address::symbolic(Variable(38_130)), 4);
        let (address, value) = store(second, 9);
        let detached = start.with_memory(gap.store(address, value));
        assert!(version(&detached, &first).is_none());
    }

    #[test]
    fn named_cell_views_retain_logged_versions_without_reading_their_suffix() {
        let _session = crate::kernel::VerificationSession::enter();
        let start =
            ExecutionState::new().with_memory(SymbolicMemory::new().with_block("local:slot", 4));
        let written = stored(&start, 7);
        let version = |state: &ExecutionState| {
            state
                .program_point()
                .indexed_integer_version(&slot(), LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        let mut work = Vec::new();
        for count in [4, 64, 1024] {
            let mut memory = written.memory().clone();
            let external = Address::symbolic(Variable(38_127));
            for index in 0..count {
                memory = memory.materialize_named_cell(
                    external.offset_by_bytes(4 * index),
                    ProgramValue::Int32(OldMachineTerm::constant(index)),
                );
            }
            let (named, used) = crate::instrumentation::measure_deterministic_work(|| {
                written
                    .clone()
                    .with_materialized_memory_at_current_point(memory)
            });
            assert_eq!(named.program_point_id(), written.program_point_id());
            assert_eq!(version(&named), written.program_point_id());
            assert!(named.memory().pending_steps.is_none());
            work.push(used);
        }
        assert!(work.iter().all(|&used| used <= work[0] + 64), "{work:?}");

        // A replacement whose log performed a real store cannot carry the
        // old version even when it writes the same value to the same cell.
        let same_contents = written
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(OldMachineTerm::constant(7)));
        assert_eq!(&same_contents, written.memory());
        let rejected = written
            .clone()
            .with_materialized_memory_at_current_point(same_contents.clone());
        assert_eq!(version(&rejected), None);
        let next = written
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(OldMachineTerm::constant(13)));
        let indexed = written.clone().with_memory(next);
        assert_eq!(version(&indexed), indexed.program_point_id());
        let unlogged = written.clone().with_materialized_memory_at_current_point(
            same_contents.materialize_named_cell(
                Address::symbolic(Variable(38_129)),
                ProgramValue::Int32(OldMachineTerm::constant(99)),
            ),
        );
        assert_eq!(version(&unlogged), None);
    }

    #[test]
    fn entry_memory_views_share_one_root_before_the_first_execution_store() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let root = entry.program_point_id().unwrap();
        let slot = slot();
        let declared = entry
            .clone()
            .with_function_entry_memory(entry.memory().clone().with_block(slot.base.clone(), 4));
        let initialized =
            declared
                .clone()
                .with_function_entry_memory(declared.memory().clone().store(
                    slot.clone(),
                    ProgramValue::Int32(OldMachineTerm::constant(7)),
                ));
        for view in [&declared, &initialized] {
            assert_eq!(view.observation_point_id(), Some(root));
            assert!(view.path_link().steps().is_none());
            assert!(view.path_link().predecessors().is_empty());
        }
        let executed = stored(&initialized, 9);
        assert_eq!(executed.path_link().predecessor_ids(), vec![root]);
        assert_ne!(executed.program_point_id(), Some(root));
        assert_eq!(
            executed
                .program_point()
                .indexed_integer_version(&slot, LoadKind::Int32)
                .and_then(|point| point.read_version_id()),
            executed.program_point_id(),
        );
    }

    /// The arena's stored instance carries no path's steps.
    #[test]
    fn the_arena_keeps_no_steps() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let memory = start
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(OldMachineTerm::constant(5)));
        assert!(memory.pending_steps.is_some());
        assert!(intern_memory_ref(&memory).memory().pending_steps.is_none());
    }

    /// A state with staged steps stands between points: asking it for its
    /// point is a defect in the region that staged them.
    #[test]
    #[should_panic(
        expected = "a state with staged steps is read before its atomic region completes"
    )]
    fn a_state_with_staged_steps_has_no_point() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let mut staged = start.clone();
        staged.stage_memory(
            start
                .memory()
                .clone()
                .store(slot(), ProgramValue::Int32(OldMachineTerm::constant(7))),
        );
        staged.program_point();
    }

    /// A state that takes another state's memory continues that state's
    /// path, through the steps that made the memory, not its own.
    #[test]
    fn taking_another_states_memory_continues_its_path() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let elsewhere = stored(&start, 1);
        let taken = elsewhere
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(OldMachineTerm::constant(2)));
        let mut here = start.clone();
        here.set_memory_continuing(&elsewhere, taken);
        assert_eq!(
            here.program_point().predecessor_ids(),
            vec![elsewhere.program_point().id().unwrap()]
        );
        assert!(here.path_link().steps().is_some());

        let mut same = start.clone();
        same.set_memory_of(&elsewhere);
        assert_eq!(same.program_point().id(), elsewhere.program_point().id());
    }

    /// A path is a chain of points; dropping a long one must not recurse
    /// once per link.
    #[test]
    fn a_long_path_drops_without_recursing_per_point() {
        let memory = intern_memory(SymbolicMemory::new());
        let mut point = PathLink::default();
        for _ in 0..200_000 {
            point = point.after(memory.clone(), None);
        }
        drop(point);
    }

    /// Two paths that write different values and then the same one end in
    /// equal states, as two `return`s that each end their locals' lifetimes
    /// do. They are still two points, each reached from its own path.
    #[test]
    fn two_paths_to_equal_memory_reach_two_points() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let left_mid = start.clone().with_memory(memory_holding(1));
        let right_mid = start.clone().with_memory(memory_holding(2));
        let left = left_mid.clone().with_memory(memory_holding(3));
        let right = right_mid.clone().with_memory(memory_holding(3));

        assert_eq!(left, right);
        assert_eq!(left.program_point(), right.program_point());
        assert_ne!(left.program_point().id(), right.program_point().id());
        assert_eq!(
            left.program_point().predecessor_ids(),
            vec![left_mid.program_point().id().unwrap()]
        );
        assert_eq!(
            right.program_point().predecessor_ids(),
            vec![right_mid.program_point().id().unwrap()]
        );

        let mut joined = left.clone();
        joined.join_program_points(&left, &right, start.path_link());
        assert_eq!(
            joined.program_point().predecessor_ids(),
            vec![
                left.program_point().id().unwrap(),
                right.program_point().id().unwrap()
            ]
        );
    }
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/program_point.rs");
    }

    /// One cell at one memory state named by a selected point and by its
    /// memory is reported once, with the line that built the memory-named
    /// read.
    /// A cell named one way, however often, is not.
    #[test]
    fn the_mixed_read_name_audit_reports_a_cell_named_both_ways() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let entry = ExecutionState::new().begin_function_entry_memory();
        let selected = entry
            .program_point()
            .entry_integer_version(&cell, LoadKind::Int32)
            .expect("an entry read");
        let observe = |point: &ProgramPoint| {
            crate::kernel::mixed_read_names::observe(point, &cell, LoadKind::Int32);
        };
        let reports = crate::kernel::mixed_read_names::capture(|| {
            observe(&selected);
            observe(&selected);
            let bare = ProgramPoint::at(selected.shared_memory());
            let _read = OldMachineTerm::read_named(bare.clone(), cell.clone(), LoadKind::Int32);
            observe(&bare);
            observe(&bare);
        });
        let [report] = reports.as_slice() else {
            panic!("{reports:?}");
        };
        assert!(report.contains("program_point.rs"), "{report}");
        assert!(crate::kernel::mixed_read_names::capture(|| observe(&selected)).is_empty());
    }
}

#[cfg(test)]
mod size_tests {
    /// A place costs a read term no size: it holds the point alone, and a
    /// read term is held inline in every machine term.
    #[test]
    fn a_placed_point_is_no_larger_than_an_unplaced_one() {
        assert!(std::mem::size_of::<super::ReadSelection>() <= 16);
        assert!(std::mem::size_of::<super::ProgramPoint>() <= 64);
    }
}
