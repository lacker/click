//! A snapshot's cell map: concrete cells plus symbolic runs of seeded cells.
//!
//! A contract that holds a constant range, `views a[0..N]`, makes every
//! element of it a known cell at entry: the cell at `a + i` holds the load of
//! `a + i` in the memory the range was seeded over. Storing those `N` cells
//! one by one made the size of a proof depend on the numeric length of the
//! range, so a [`CellRun`] records the whole range once instead. Every
//! consumer still sees exactly the cells seeding would have stored:
//! [`CellStore::logical`] is that cell map, and each mutation keeps the run
//! and the concrete map in one canonical form.
//!
//! A function's entry names every element of a symbolic static-storage array
//! (a global or `static` array whose contents the function does not know) the
//! same way, one element at a time, so a `static char buf[65536]` cost 65,536
//! cells at every entry. Such an array is a run too. Its slots spell their
//! loads as the entry does ([`RunValueMode::SymbolicStorage`]): an element of
//! pointer type is a fresh symbolic pointer, which may point into any block,
//! rather than a pointer into the run's own block. The mode is part of the
//! run's identity.
//!
//! Static storage whose contents the function does know (program startup,
//! or a `const` array) used to be stored element by element too, so
//! `int32 buf[1000000];` cost a million stores before `main` began. The
//! elements its initializer leaves at one value are a run whose every slot
//! holds that value ([`RunValueMode::Constant`]), with the written elements
//! stored over it.
//!
//! **Canonical form.** For each run, a slot is either *live* — it holds the
//! run's value and the concrete map has no entry at its pointer — or a
//! *hole*, whose pointer the concrete map may or may not hold, and never with
//! the run's own value. A store of the run's value into a hole refills the
//! slot rather than caching a concrete copy, and holes are kept as disjoint,
//! non-adjacent intervals. A pointer is a live slot of at most one run. A run
//! with no live slot holds no cell and is retired: the store never keeps one,
//! so it neither costs a later scan nor makes two stores with the same cells
//! differ in representation. Runs are never split.
//!
//! **Index.** The runs are one persistent ordered map keyed by [`RunKey`]:
//! the run's block, then where its slots are anchored in the block (a
//! constant base offset, or one symbolic offset every slot shifts from), then
//! the rest of what [`CellRun::same_slots_as`] compares. So the runs of one
//! block are one key range ([`AliasCandidates`] walks runs exactly as it
//! walks cells), the runs a pointer can be a slot of are found without
//! visiting the others, two stores' runs pair up by key, and two stores that
//! share their runs' persistent nodes are compared, hashed and diffed in the
//! work of what they do not share. The key orders the run's source memory by
//! its content hash before its structure, so no key comparison walks a
//! memory unless two sources' hashes collide. A slot is spelled as a load of
//! its address is ([`CellRun::slot_pointer`]): its run's base plus a constant,
//! folded into any constant the base ends in, so every slot lies on its
//! base's *line*, the base's block and the stem the base adds a constant to
//! (`CoverLine`). Every run is also filed by the bytes its slots span on its
//! line, in `CellStore::span_cover`, so a pointer finds exactly the runs
//! whose span on its line holds it. Equality, hashing and ordering read only the
//! concrete map and the run map, never that cover or the cached counts,
//! which are functions of the run map, so a store's identity does not
//! depend on the order its runs were added in.
use super::alias_candidates::BlockKeyed;
use super::{
    AliasCandidates, CType, CValue, Pointer, PointerBlock, PointerOffsetTerm, SharedCMemory,
    SnapshotMap, SnapshotMapChange, SnapshotSet,
};
use crate::kernel::primitives::Bitvector32Term;
use crate::kernel::primitives::LoadKind;
use crate::kernel::{PureFactContext, Variable};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::ops::Bound;
use std::sync::OnceLock;

/// Disjoint, non-adjacent, ascending half-open index intervals.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct IndexIntervals {
    intervals: SnapshotSet<(u32, u32)>,
}

impl IndexIntervals {
    /// The interval holding `index`, if any.
    fn interval_of(&self, index: u32) -> Option<(u32, u32)> {
        self.intervals
            .range(..=(index, u32::MAX))
            .next_back()
            .copied()
            .filter(|(low, high)| *low <= index && index < *high)
    }

    pub(crate) fn contains(&self, index: u32) -> bool {
        self.interval_of(index).is_some()
    }

    /// Whether one merged interval covers all of `[low, high)`.
    pub(crate) fn covers_range(&self, low: u32, high: u32) -> bool {
        low >= high || self.interval_of(low).is_some_and(|(_, end)| end >= high)
    }

    /// The indexes in these intervals and not in `other`'s, linear in the
    /// two interval counts.
    pub(crate) fn difference(&self, other: &Self) -> Self {
        let mut result = Self::default();
        let removed = other.intervals.iter().copied().collect::<Vec<_>>();
        let mut next = 0usize;
        for (low, high) in self.intervals.iter().copied() {
            while next < removed.len() && removed[next].1 <= low {
                next += 1;
            }
            let mut start = low;
            let mut position = next;
            while start < high {
                match removed.get(position) {
                    Some((removed_low, removed_high)) if *removed_low < high => {
                        if start < *removed_low {
                            result.insert_range(start, *removed_low);
                        }
                        start = start.max(*removed_high);
                        position += 1;
                    }
                    _ => {
                        result.insert_range(start, high);
                        start = high;
                    }
                }
            }
        }
        result
    }

    /// The indexes in both.
    pub(crate) fn intersection(&self, other: &Self) -> Self {
        self.difference(&self.difference(other))
    }

    /// The intervals, ascending.
    pub(crate) fn intervals(&self) -> Vec<(u32, u32)> {
        self.intervals.iter().copied().collect()
    }

    /// Bounded diagnostic consumers can inspect intervals without allocating
    /// or enumerating the rest of the run's holes.
    pub(crate) fn diagnostic_intervals(&self) -> impl Iterator<Item = (u32, u32)> + '_ {
        self.intervals.iter().copied()
    }

    /// Every index, ascending.
    pub(crate) fn indexes(&self) -> impl Iterator<Item = u32> + '_ {
        self.intervals.iter().flat_map(|(low, high)| *low..*high)
    }

    /// Adds `[low, high)`, merging every interval it touches.
    pub(crate) fn insert_range(&mut self, mut low: u32, mut high: u32) {
        if low >= high {
            return;
        }
        let touching = self
            .intervals
            .range(..=(high, u32::MAX))
            .rev()
            .take_while(|(_, other_high)| *other_high >= low)
            .copied()
            .collect::<Vec<_>>();
        for (other_low, other_high) in touching {
            low = low.min(other_low);
            high = high.max(other_high);
            self.intervals.remove(&(other_low, other_high));
        }
        self.intervals.insert((low, high));
    }

    pub(crate) fn insert(&mut self, index: u32) {
        self.insert_range(index, index + 1);
    }

    /// Every index of `[0, count)`.
    pub(crate) fn full(count: u32) -> Self {
        let mut all = Self::default();
        all.insert_range(0, count);
        all
    }

    /// The indexes in exactly one of the two.
    pub(crate) fn symmetric_difference(&self, other: &Self) -> Self {
        let mut result = self.difference(other);
        for (low, high) in other.difference(self).intervals.iter() {
            result.insert_range(*low, *high);
        }
        result
    }

    /// How many intervals there are.
    pub(crate) fn interval_count(&self) -> usize {
        self.intervals.len()
    }

    /// Removes one index, splitting the interval that held it.
    pub(crate) fn remove(&mut self, index: u32) {
        let Some((low, high)) = self.interval_of(index) else {
            return;
        };
        self.intervals.remove(&(low, high));
        if low < index {
            self.intervals.insert((low, index));
        }
        if index + 1 < high {
            self.intervals.insert((index + 1, high));
        }
    }

    /// How many indexes the intervals hold.
    pub(crate) fn count(&self) -> u64 {
        self.intervals
            .iter()
            .map(|(low, high)| u64::from(high - low))
            .sum()
    }

    /// The indexes of `[0, count)` outside every interval, ascending, as
    /// half-open intervals.
    pub(crate) fn gaps(&self, count: u32) -> Vec<(u32, u32)> {
        self.gap_intervals(count).collect()
    }

    /// [`Self::gaps`], walked without collecting them.
    pub(crate) fn gap_intervals(&self, count: u32) -> impl Iterator<Item = (u32, u32)> + '_ {
        let mut intervals = self.intervals.iter();
        let mut next = 0u32;
        std::iter::from_fn(move || {
            while next < count {
                match intervals.next() {
                    Some((low, high)) => {
                        let gap = (next, (*low).min(count));
                        next = next.max(*high);
                        if gap.0 < gap.1 {
                            return Some(gap);
                        }
                    }
                    None => {
                        let gap = (next, count);
                        next = count;
                        return Some(gap);
                    }
                }
            }
            None
        })
    }
}

/// How a run spells the load of each element in its source as the value the
/// element's cell holds. Part of the run's identity: two runs over the same
/// slots whose modes differ hold different values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RunValueMode {
    /// The value a seeded range stores: [`cell_run_value`] of the element's
    /// canonical load.
    Load,
    /// The value a symbolic static-storage cell holds at function entry
    /// ([`crate::kernel::eval::symbolic_storage_cell_value`]): a fresh
    /// symbolic pointer named by the load for an object pointer, which may
    /// point into any block, and the typed load otherwise. The run's source
    /// holds only the storage's block, and every element's access width is
    /// declared for the whole run
    /// ([`crate::kernel::eval::declare_symbolic_array_access_widths`]) rather
    /// than recorded as the element is named.
    SymbolicStorage,
    /// Every slot holds this one value, whatever the source: the known
    /// initial contents of static storage whose initializer leaves the
    /// elements zero (or another constant), stored as C would store them.
    /// The source is the empty memory, and the value is part of the mode,
    /// so two constant runs over the same slots are one run exactly when
    /// they hold one value.
    Constant(CValue),
    /// An immutable snapshot copy. Slot i reads source_base + i * stride,
    /// rather than its destination address. Used only for scalar elements.
    Copy { source_base: Pointer },
}

/// `count` seeded cells at `base`, `base + width`, …: the cell at element `i`
/// holds the load of that element in `source`, typed as `element_type` and
/// spelled as `mode` says, exactly as a store of that value would have left
/// it.
#[derive(Clone)]
pub struct CellRun {
    base: Pointer,
    element_width: u32,
    element_type: CType,
    count: u32,
    source: SharedCMemory,
    mode: RunValueMode,
    holes: IndexIntervals,
}

impl CellRun {
    pub(crate) fn new(
        base: Pointer,
        element_width: u32,
        element_type: CType,
        count: u32,
        source: SharedCMemory,
        holes: IndexIntervals,
    ) -> Self {
        Self::new_with_mode(
            base,
            element_width,
            element_type,
            count,
            source,
            RunValueMode::Load,
            holes,
        )
    }

    /// [`Self::new`] for a run whose values `mode` spells.
    pub(crate) fn new_with_mode(
        base: Pointer,
        element_width: u32,
        element_type: CType,
        count: u32,
        source: SharedCMemory,
        mode: RunValueMode,
        holes: IndexIntervals,
    ) -> Self {
        Self {
            base,
            element_width,
            element_type,
            count,
            source,
            mode,
            holes,
        }
    }

    /// This run with `holes` in place of its own: the same slots holding the
    /// same values.
    pub(crate) fn with_holes(&self, holes: IndexIntervals) -> Self {
        Self {
            holes,
            ..self.clone()
        }
    }

    /// Exact source of an entire footprint supplied by this materialization
    /// edge. This says nothing about subsequent writes or other retained runs.
    /// The egraph is trusted kernel state; admission checks only these slots.
    pub(crate) fn read_source(&self, pointer: &Pointer, bytes: u32) -> Option<SharedCMemory> {
        let width = self.element_width();
        if bytes == 0
            || width == 0
            || width != self.value_width()
            || !bytes.is_multiple_of(width)
            || !matches!(self.value_mode(), RunValueMode::Load)
        {
            return None;
        }
        for offset in (0..bytes).step_by(width as usize) {
            crate::instrumentation::record_deterministic_work(1);
            let index = self.slot_index(&pointer.offset_by_bytes(offset))?;
            if self.holes().contains(index) {
                return None;
            }
        }
        Some(self.source().clone())
    }

    /// How the run spells each element's value.
    pub(crate) fn value_mode(&self) -> &RunValueMode {
        &self.mode
    }

    /// The run's place in a store's index: see [`RunKey`].
    pub(crate) fn key(&self) -> RunKey {
        RunKey {
            block: self.base.block.clone(),
            anchor: RunAnchor::of(&self.base.offset),
            shape: RunShape::Of {
                element_width: self.element_width,
                element_type: self.element_type,
                count: self.count,
                source: RunSource(self.source.clone()),
                mode: self.mode.clone(),
            },
        }
    }

    /// The largest byte distance of a slot from the base.
    fn span(&self) -> u64 {
        u64::from(self.count.saturating_sub(1)) * u64::from(self.element_width)
    }

    /// The live slots, as intervals.
    pub(crate) fn live_intervals(&self) -> IndexIntervals {
        IndexIntervals::full(self.count).difference(&self.holes)
    }

    /// Bound all live slots with two hole-index lookups. Internal holes stay
    /// inside this conservative footprint; neither holes nor slots are walked.
    pub(crate) fn live_byte_footprint(&self) -> Option<(Pointer, u32)> {
        let last = self.count.checked_sub(1)?;
        crate::instrumentation::record_deterministic_work(2);
        let first = self.holes.interval_of(0).map_or(0, |(_, end)| end);
        let end = self
            .holes
            .interval_of(last)
            .map_or(self.count, |(start, _)| start);
        let slots = end.checked_sub(first)?.checked_sub(1)?;
        let bytes = slots
            .checked_mul(self.element_width)?
            .checked_add(self.value_width())?;
        Some((self.slot_pointer(first), bytes))
    }

    pub(crate) fn base(&self) -> &Pointer {
        &self.base
    }

    pub(crate) fn element_width(&self) -> u32 {
        self.element_width
    }

    pub(crate) fn count(&self) -> u32 {
        self.count
    }

    /// The memory every slot's load reads.
    pub(crate) fn source(&self) -> &SharedCMemory {
        &self.source
    }

    /// The memory range the run's elements span, element 0 up to `count`.
    pub(crate) fn range(&self) -> super::CMemoryRange {
        super::CMemoryRange::new_with_element_width(
            self.base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(self.count),
            self.element_width,
        )
    }

    /// The C type of every slot's value.
    pub(crate) fn element_type(&self) -> CType {
        self.element_type
    }

    /// How many bytes each slot's value occupies.
    pub(crate) fn value_width(&self) -> u32 {
        self.element_type.byte_width()
    }

    pub(crate) fn holes(&self) -> &IndexIntervals {
        &self.holes
    }

    /// The pointer of element `index`, spelled as a load of that address
    /// spells it: the base's offset plus a constant byte shift through
    /// [`PointerOffsetTerm::add`], which folds the shift into a constant the
    /// base already ends in. So element 1 of a run based at `p + 16` with
    /// stride 4 is `p + 20`, not `(p + 16) + 4`, and a question about a load
    /// of `p + 20` is the same question whether a run or a cell answers it.
    pub(crate) fn slot_pointer(&self, index: u32) -> Pointer {
        let shift = i64::from(index) * i64::from(self.element_width);
        Pointer {
            block: self.base.block.clone(),
            offset: PointerOffsetTerm::add(
                self.base.offset.clone(),
                PointerOffsetTerm::Constant(shift),
            ),
        }
    }

    /// Where the run's slots lie: the block and the stem every slot's offset
    /// adds a constant to ([`offset_stem_and_constant`]), and the constant
    /// byte offsets of the first and last slot on that line.
    fn slot_line_span(&self) -> (CoverLine, i64, i64) {
        let (stem, start) = offset_stem_and_constant(&self.base.offset);
        let span = i64::try_from(self.span()).unwrap_or(i64::MAX);
        (
            CoverLine {
                block: self.base.block.clone(),
                stem: stem.cloned(),
            },
            start,
            start.saturating_add(span),
        )
    }

    /// The element whose slot is spelled exactly `pointer`, hole or not.
    pub(crate) fn slot_index(&self, pointer: &Pointer) -> Option<u32> {
        if pointer.block != self.base.block {
            return None;
        }
        let width = i64::from(self.element_width);
        let (base_stem, base_constant) = offset_stem_and_constant(&self.base.offset);
        let (stem, constant) = offset_stem_and_constant(&pointer.offset);
        if stem != base_stem {
            return None;
        }
        let shift = constant.checked_sub(base_constant)?;
        if shift < 0 || shift % width != 0 {
            return None;
        }
        let index = u32::try_from(shift / width).ok()?;
        (index < self.count && self.slot_pointer(index) == *pointer).then_some(index)
    }

    /// The element whose slot is `pointer` and is live.
    pub(crate) fn live_slot_index(&self, pointer: &Pointer) -> Option<u32> {
        self.slot_index(pointer)
            .filter(|index| !self.holes.contains(*index))
    }

    /// The value every live slot `index` holds. Naming goes through the
    /// per-origin-epoch load cache: retaining a named value in the run would
    /// skip the mint that refreshes its live origin in a later verification.
    pub(crate) fn value(&self, index: u32) -> CValue {
        self.named_value(index)
    }

    /// The value slot `index` holds: the load of its pointer in the source,
    /// typed as the element and spelled as the run's mode says.
    fn named_value(&self, index: u32) -> CValue {
        let pointer = self.slot_pointer(index);
        // A slot of an abstract type parameter holds the load of its type.
        if let CType::Parameter(parameter) = self.element_type {
            let (source, pointer) = match &self.mode {
                RunValueMode::Copy { source_base } => (
                    self.source.clone(),
                    source_base.offset_by_bytes(index * self.element_width),
                ),
                RunValueMode::Constant(value) => return value.clone(),
                RunValueMode::Load | RunValueMode::SymbolicStorage => {
                    (self.source.clone(), pointer)
                }
            };
            return super::AlgebraicTermNode::parameter_load(source, pointer, parameter);
        }
        match &self.mode {
            RunValueMode::Load => {
                let load = crate::kernel::canonical_form_of_load(
                    self.source.clone(),
                    pointer.clone(),
                    LoadKind::of_type(self.element_type)
                        .expect("memory ranges cannot contain aggregate elements"),
                );
                cell_run_value(self.element_type, load)
            }
            RunValueMode::SymbolicStorage => crate::kernel::eval::symbolic_storage_cell_value(
                self.source.memory(),
                &pointer,
                self.element_type,
                false,
            )
            .expect("a symbolic storage run holds only element types with a value"),
            RunValueMode::Constant(value) => value.clone(),
            RunValueMode::Copy { source_base } => {
                let source_pointer = source_base.offset_by_bytes(index * self.element_width);
                let load = crate::kernel::canonical_form_of_load(
                    self.source.clone(),
                    source_pointer.clone(),
                    LoadKind::of_type(self.element_type).expect("scalar snapshot element"),
                );
                cell_run_value(self.element_type, load)
            }
        }
    }

    pub(crate) fn live_count(&self) -> u64 {
        u64::from(self.count) - self.holes.count().min(u64::from(self.count))
    }

    /// The live slots, descending in element order: the order a walk meets
    /// the stores a `CellsSeeded` edge stands for.
    pub(crate) fn live_indexes_newest_first(&self) -> impl Iterator<Item = u32> + '_ {
        self.holes
            .gaps(self.count)
            .into_iter()
            .rev()
            .flat_map(|(low, high)| (low..high).rev())
    }

    /// The live slots, ascending in element order.
    pub(crate) fn live_indexes(&self) -> impl Iterator<Item = u32> + '_ {
        self.holes
            .gap_intervals(self.count)
            .flat_map(|(low, high)| low..high)
    }

    /// Whether `other` is this run with possibly other holes: the same slots
    /// holding the same values wherever both are live.
    pub(crate) fn same_slots_as(&self, other: &Self) -> bool {
        self.base == other.base
            && self.element_width == other.element_width
            && self.element_type == other.element_type
            && self.count == other.count
            && self.source == other.source
            && self.mode == other.mode
    }

    #[allow(clippy::type_complexity)]
    fn descriptor(
        &self,
    ) -> (
        &Pointer,
        u32,
        CType,
        u32,
        &SharedCMemory,
        &RunValueMode,
        &IndexIntervals,
    ) {
        (
            &self.base,
            self.element_width,
            self.element_type,
            self.count,
            &self.source,
            &self.mode,
            &self.holes,
        )
    }
}

impl std::fmt::Debug for CellRun {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CellRun")
            .field("base", &self.base)
            .field("element_width", &self.element_width)
            .field("element_type", &self.element_type)
            .field("count", &self.count)
            .field("mode", &self.mode)
            .field("holes", &self.holes)
            .finish_non_exhaustive()
    }
}

impl PartialEq for CellRun {
    fn eq(&self, other: &Self) -> bool {
        self.descriptor() == other.descriptor()
    }
}

impl Eq for CellRun {}

impl Hash for CellRun {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.descriptor().hash(state);
    }
}

impl PartialOrd for CellRun {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CellRun {
    /// By `RunKey`, then holes: a source memory is compared by structure
    /// only when two sources' content hashes collide.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key()
            .cmp(&other.key())
            .then_with(|| self.holes.cmp(&other.holes))
    }
}

/// A run's source memory, ordered by content hash before structure. The
/// order is a function of the memories' contents, so it is the same in every
/// check, and it reaches the structural comparison only for two distinct
/// memories whose hashes collide.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RunSource(SharedCMemory);

impl PartialOrd for RunSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RunSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .content_hash
            .cmp(&other.0.content_hash)
            .then_with(|| {
                if self.0 == other.0 {
                    std::cmp::Ordering::Equal
                } else {
                    self.0.memory.cmp(&other.0.memory)
                }
            })
    }
}

/// Where a run's base sits in its block: a constant offset, or a symbolic
/// one. Every slot is on the base's line (see [`CellRun::slot_pointer`]),
/// which is how a pointer finds a run; the anchor only orders runs. The
/// first and last variants bound key ranges and are no run's anchor.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RunAnchor {
    Least,
    Constant(i64),
    Symbolic(PointerOffsetTerm),
    Greatest,
}

impl RunAnchor {
    fn of(offset: &PointerOffsetTerm) -> Self {
        match offset {
            PointerOffsetTerm::Constant(constant) => Self::Constant(*constant),
            offset => Self::Symbolic(offset.clone()),
        }
    }
}

/// The rest of a run's identity: what [`CellRun::same_slots_as`] compares
/// beyond the base. The first and last variants bound key ranges.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RunShape {
    Least,
    Of {
        element_width: u32,
        element_type: CType,
        count: u32,
        source: RunSource,
        mode: RunValueMode,
    },
    Greatest,
}

/// A run's key in a store's run map: block first, so a block's runs are one
/// key range, then anchor, then shape. Two runs have one key exactly when
/// they have the same slots holding the same values
/// ([`CellRun::same_slots_as`]).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RunKey {
    block: PointerBlock,
    anchor: RunAnchor,
    shape: RunShape,
}

impl RunKey {
    fn bound(block: &PointerBlock, anchor: RunAnchor, shape: RunShape) -> Self {
        Self {
            block: block.clone(),
            anchor,
            shape,
        }
    }
}

impl BlockKeyed for RunKey {
    fn key_block(&self) -> &PointerBlock {
        &self.block
    }

    fn first_key_of(block: &PointerBlock) -> Self {
        Self::bound(block, RunAnchor::Least, RunShape::Least)
    }
}

/// The value a seeded cell of type `element_type` at `pointer` holds when its
/// load is `load`: the load itself for a scalar, the load's truth for a
/// `bool`, a pointer into the cell's own block scaled by the pointee for an
/// object pointer, and the load's function identity for a function pointer.
pub(crate) fn cell_run_value(element_type: CType, load: Bitvector32Term) -> CValue {
    match element_type {
        // The byte rule (Stage 5): the `Bool` `load != 0`.
        CType::Bool => crate::kernel::bool_value(load),
        CType::Int8 => CValue::Int8(load),
        CType::Int16 => CValue::Int16(load),
        CType::Int32 => CValue::Int32(load),
        CType::UInt8 => CValue::UInt8(load),
        CType::UInt16 => CValue::UInt16(load),
        CType::UInt32 => CValue::UInt32(load),
        CType::Int64 => CValue::Int64(load),
        CType::Int128 => CValue::Int128(load),
        CType::UInt64 => CValue::UInt64(load),
        CType::UInt128 => CValue::UInt128(load),
        CType::Float32 => CValue::Float32(load),
        CType::Float64 => CValue::Float64(load),
        CType::FunctionPointer(_) => {
            let variable = match &load {
                Bitvector32Term::Variable(variable)
                    if crate::kernel::is_load_variable(variable) =>
                {
                    *variable
                }
                Bitvector32Term::MemoryLoad(_, _, _) => {
                    crate::kernel::load_variable_for_term(&load)
                        .map(|(variable, _)| variable)
                        .expect("exact function-pointer loads have canonical identities")
                }
                _ => unreachable!(
                    "symbolic function-pointer fields use raw or canonical exact loads"
                ),
            };
            CValue::typed_pointer(Pointer::symbolic_function(variable), element_type)
        }
        c_type if c_type.is_pointer() => {
            // A seeded pointer cell is already a typed read, even before a
            // C load observes it. Retain its exact producer definition so a
            // later logical read through an alias can use load congruence.
            let definition = match &load {
                Bitvector32Term::MemoryLoad(_, _, _) => Some(load.clone()),
                Bitvector32Term::Variable(variable) => {
                    crate::kernel::registered_load_term_for_variable(variable)
                }
                _ => None,
            };
            let value = Pointer::loaded(&load).expect("a pointer cell's canonical read is a load");
            if let Some(Bitvector32Term::MemoryLoad(snapshot, address, LoadKind::Int32)) =
                definition
            {
                crate::kernel::equality_graph::EqualityGraph::default()
                    .register_pointer_read_definition(&value, &snapshot, &address);
                return CValue::Pointer(crate::kernel::CPointerValue::from_read(
                    value, c_type, &snapshot, &address,
                ));
            }
            CValue::typed_pointer(value, c_type)
        }
        _ => unreachable!("memory ranges cannot contain aggregate elements"),
    }
}

/// Where two cell stores differ: concrete pointers, and slot intervals of
/// runs whose pointers are left unspelled.
pub(crate) struct DifferingCells {
    pub(crate) pointers: Vec<Pointer>,
    pub(crate) run_slots: Vec<(CellRun, IndexIntervals)>,
}

/// Which live slots of a run a per-cell rule holds for, answered for the
/// whole run at once.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SlotSet {
    /// Every live slot.
    All,
    /// No slot.
    Nothing,
    /// The live slots of elements `low..high`.
    Elements(u32, u32),
    /// Every live slot except those of elements `low..high`.
    Except(u32, u32),
    /// Undecided for the run as a whole: ask the rule of every live slot.
    PerSlot,
}

/// What a whole-run answer claims about the per-cell rule it stands for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RuleAnswer {
    /// Exactly the slots the per-cell rule accepts.
    Exact,
    /// A sound answer that may differ from the per-cell rule's syntactic
    /// ladder, argued where the rule is defined: it keeps a superset of the
    /// cells that rule keeps, or decides from the byte arithmetic every slot
    /// shares what the ladder decides from a spelling.
    /// A cache-forgetting rule may instead drop extra slots: every kept slot
    /// must be sound, and the caller must record any extra lost knowledge.
    Sound,
}

/// The largest run debug builds check a whole-run answer against, slot by
/// slot. A check, not a behavior: release builds and larger runs use the
/// whole-run answer alone.
#[cfg(debug_assertions)]
pub const CHECKED_RUN_SLOTS: u32 = 64;

impl SlotSet {
    #[cfg(debug_assertions)]
    fn holds(&self, index: u32) -> Option<bool> {
        match self {
            Self::All => Some(true),
            Self::Nothing => Some(false),
            Self::Elements(low, high) => Some(*low <= index && index < *high),
            Self::Except(low, high) => Some(!(*low <= index && index < *high)),
            Self::PerSlot => None,
        }
    }

    /// The live slots this answer names, asking nothing for `PerSlot`, which
    /// names every live slot for the caller to ask itself.
    fn live_indexes(&self, run: &CellRun, visited: &mut usize) -> Vec<u32> {
        match self {
            Self::Nothing => Vec::new(),
            Self::Elements(low, high) => {
                let high = (*high).min(run.count);
                (*low..high.max(*low))
                    .filter(|index| !run.holes.contains(*index))
                    .collect()
            }
            Self::Except(low, high) => {
                let indexes = run
                    .live_indexes()
                    .filter(|index| !(*low <= *index && *index < *high))
                    .collect::<Vec<_>>();
                *visited += indexes.len();
                indexes
            }
            Self::All | Self::PerSlot => {
                let indexes = run.live_indexes().collect::<Vec<_>>();
                *visited += indexes.len();
                indexes
            }
        }
    }

    #[cfg(debug_assertions)]
    fn check_against(&self, run: &CellRun, rule: &mut impl FnMut(&Pointer, &CValue) -> bool) {
        if matches!(self, Self::PerSlot) || run.count > CHECKED_RUN_SLOTS {
            return;
        }
        for index in run.live_indexes() {
            let Some(holds) = self.holds(index) else {
                continue;
            };
            let pointer = run.slot_pointer(index);
            let value = run.value(index);
            let expected = rule(&pointer, &value);
            assert_eq!(
                Some(holds),
                Some(expected),
                "whole-run answer {self:?} disagrees with the per-cell rule at element {index} of {run:?}"
            );
        }
    }
}

impl CellRun {
    /// Makes every live slot outside `decision` a hole; a `PerSlot` decision
    /// asks `keep` of each live slot.
    fn keep_only(
        &mut self,
        decision: SlotSet,
        keep: &mut impl FnMut(&Pointer, &CValue) -> bool,
        visited: &mut usize,
    ) {
        match decision {
            SlotSet::All => {}
            SlotSet::Nothing => self.holes.insert_range(0, self.count),
            SlotSet::Elements(low, high) => {
                self.holes.insert_range(0, low.min(self.count));
                self.holes.insert_range(high.min(self.count), self.count);
            }
            SlotSet::Except(low, high) => {
                self.holes
                    .insert_range(low.min(self.count), high.min(self.count));
            }
            SlotSet::PerSlot => {
                let dropped = self
                    .live_indexes()
                    .filter(|index| {
                        *visited += 1;
                        let pointer = self.slot_pointer(*index);
                        let value = self.value(*index);
                        !keep(&pointer, &value)
                    })
                    .collect::<Vec<_>>();
                for index in dropped {
                    self.holes.insert(index);
                }
            }
        }
    }
}

/// The slots of one run that a whole-run retain dropped: the run (its new
/// holes included) and the elements, live before the retain, that it made
/// holes. A dropped slot's value is forgotten; what its bytes held is for
/// the caller to keep or not ([`CellStore::retain_by`]).
pub(crate) struct DroppedRunSlots {
    pub(crate) run: CellRun,
    pub(crate) elements: IndexIntervals,
}

/// A snapshot's cells: the concrete map and the seeded runs, in canonical
/// form, the runs indexed by [`RunKey`] (see the module comment).
#[derive(Default)]
pub(crate) struct CellStore {
    concrete: SnapshotMap<Pointer, CValue>,
    runs: SnapshotMap<RunKey, CellRun>,
    /// The held runs, by the bytes from their first slot to their last on
    /// their line ([`CoverLine`]): each line's covered bytes cut into
    /// disjoint segments, keyed by line and first byte, each naming the runs
    /// whose span covers it in key order. Adjacent touching segments name
    /// different runs, so there are at most two per run. A function of the
    /// run map, left out of equality, hashing and ordering.
    span_cover: imbl::OrdMap<(CoverLine, i64), CoverSegment>,
    /// The live slots of every run together; a function of the runs.
    run_cells: u64,
    /// The logical cell map, built on first need when there are runs. A
    /// single-cell mutation updates it in place; any other resets it. A
    /// function of the two maps above.
    logical: OnceLock<SnapshotMap<Pointer, CValue>>,
    ordered_index: std::sync::Mutex<Option<OrderedIndexCache>>,
    pointer_reachable_index: std::sync::Mutex<Option<PointerReachableIndex>>,
    parameter_partition_index: std::sync::Mutex<Option<ParameterPartitionIndex>>,
}

#[derive(Clone)]
struct ParameterPartitionIndex {
    cells: SnapshotMap<Pointer, CValue>,
    runs: SnapshotMap<RunKey, CellRun>,
    known_runs: crate::persistent::PersistentMap<Pointer, std::sync::Arc<Vec<RunKey>>>,
    unknown_runs: SnapshotMap<RunKey, ()>,
    run_bases: SnapshotMap<RunKey, Pointer>,
    resources: crate::kernel::ResourceContext,
    known: SnapshotMap<(Pointer, Pointer), ()>,
    unknown: SnapshotMap<Pointer, ()>,
    bases: SnapshotMap<Pointer, Pointer>,
}

/// The concrete cells a pointer value can reach, with their values: every
/// cell outside the slot of a local whose address is never taken
/// ([`super::block_is_never_address_taken_local`]). Kept beside the store and
/// caught up by diffing the concrete map it was taken from, so a store only
/// pays for the cells changed since; a change to the addressability registry
/// rebuilds it.
#[derive(Clone)]
struct PointerReachableIndex {
    cells: SnapshotMap<Pointer, CValue>,
    generation: u64,
    reachable: SnapshotMap<Pointer, CValue>,
    external: SnapshotMap<Pointer, CValue>,
}

#[derive(Clone)]
struct OrderedIndexCache {
    cells: SnapshotMap<Pointer, CValue>,
    chains: crate::kernel::assumptions::variable_chains::VariableChains,
    block: PointerBlock,
    base: PointerOffsetTerm,
    stride: i64,
    root: Variable,
    known: SnapshotMap<usize, Pointer>,
    unknown: SnapshotMap<Pointer, ()>,
}

impl Clone for CellStore {
    fn clone(&self) -> Self {
        Self {
            concrete: self.concrete.clone(),
            runs: self.runs.clone(),
            span_cover: self.span_cover.clone(),
            run_cells: self.run_cells,
            logical: self.logical.clone(),
            ordered_index: std::sync::Mutex::new(self.ordered_index.lock().unwrap().clone()),
            pointer_reachable_index: std::sync::Mutex::new(
                self.pointer_reachable_index.lock().unwrap().clone(),
            ),
            parameter_partition_index: std::sync::Mutex::new(
                self.parameter_partition_index.lock().unwrap().clone(),
            ),
        }
    }
}

#[cfg(test)]
thread_local! {
    /// How many runs pointer lookups have visited on this thread: the
    /// scaling regressions' measure of a lookup, which positions in the run
    /// map without charging work.
    static RUNS_VISITED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The bytes `[start, end)` of one line covered by exactly these runs'
/// spans; see `CellStore::span_cover`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CoverSegment {
    end: i64,
    runs: Vec<RunKey>,
}

/// The addresses of one block that differ only in a constant byte offset: a
/// constant offset (no stem), or one stem plus a constant. See
/// [`offset_stem_and_constant`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CoverLine {
    block: PointerBlock,
    stem: Option<PointerOffsetTerm>,
}

/// An offset as the stem [`PointerOffsetTerm::add`] shifts by a constant, and
/// that constant: `(None, c)` for a constant offset, `(Some(stem), c)` for
/// `stem + c` (with every trailing constant `add` folds into one peeled
/// off), and `(Some(offset), 0)` for any other offset. `add` of a constant
/// to an offset moves only the constant, so every slot of a run, and every
/// load spelling one of its addresses, lies on its base's line.
pub(crate) fn offset_stem_and_constant(
    offset: &PointerOffsetTerm,
) -> (Option<&PointerOffsetTerm>, i64) {
    let mut stem = offset;
    let mut constant = 0i64;
    loop {
        if let Some(value) = stem.as_const() {
            return (None, constant.saturating_add(value));
        }
        let PointerOffsetTerm::Add(left, right) = stem else {
            return (Some(stem), constant);
        };
        let Some(value) = right.as_const() else {
            return (Some(stem), constant);
        };
        constant = constant.saturating_add(value);
        stem = left;
    }
}

/// One held run's slot at a pointer.
struct SlotAt<'a> {
    run: &'a CellRun,
    index: u32,
}

impl CellStore {
    /// Index checked whole-cell membership in an atomic parameter partition.
    /// Follow persistent cell deltas; unrelated members are not queried at
    /// every store. Runs and union views retain their ordinary rules.
    pub(in crate::kernel) fn parameter_store_candidates(
        &self,
        pointer: &Pointer,
        bytes: u32,
        candidates: &AliasCandidates,
        gap_kept: &[(Pointer, Pointer)],
        assumptions: &PureFactContext,
    ) -> Option<Vec<Pointer>> {
        if crate::kernel::reasoning::store_gap::store_gap_skip_disabled()
            || crate::kernel::assumptions::implicit_reasoning_provenance_capturing()
            || crate::kernel::assumptions::reasoning_interrupted()
        {
            return None;
        }
        let (resources, write_base) = assumptions.parameter_store_partition(pointer, bytes)?;
        let alias_bases = assumptions.parameter_store_alias_bases(&write_base)?;
        self.prepare_parameter_partition(resources);
        let guard = self.parameter_partition_index.lock().unwrap();
        let index = guard.as_ref().expect("prepared parameter partition");
        let mut selected = candidates
            .entries(&index.unknown)
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        for base in alias_bases {
            let mut start = Bound::Included((base.clone(), Pointer::null()));
            for (low, high) in gap_kept {
                selected.extend(
                    index
                        .known
                        .range((start, Bound::Excluded((base.clone(), low.clone()))))
                        .map(|((_, key), _)| key.clone()),
                );
                start = Bound::Excluded((base.clone(), high.clone()));
            }
            selected.extend(
                index
                    .known
                    .range((start, Bound::Unbounded))
                    .take_while(|((known_base, _), _)| *known_base == base)
                    .map(|((_, key), _)| key.clone()),
            );
        }
        Some(selected)
    }

    pub(in crate::kernel) fn prepare_parameter_partition(
        &self,
        resources: &crate::kernel::ResourceContext,
    ) {
        let assumptions = PureFactContext::new();
        let mut guard = self.parameter_partition_index.lock().unwrap();
        let previous = guard.take();
        let mut changes = BTreeMap::new();
        let mut run_changes = BTreeSet::new();
        if let Some(index) = &previous {
            run_changes.extend(
                index
                    .runs
                    .diff(&self.runs)
                    .filter(|change| change.key().block == PointerBlock::ExternalArgument)
                    .map(|change| change.key().clone()),
            );
            for change in index.cells.diff(&self.concrete) {
                let key = match change {
                    SnapshotMapChange::Added(key)
                    | SnapshotMapChange::Changed(key)
                    | SnapshotMapChange::Removed(key) => key,
                };
                if key.block == PointerBlock::ExternalArgument {
                    changes.insert(key.clone(), self.concrete.contains_key(key));
                }
            }
            for change in index
                .resources
                .flat_owned_memory_ranges()
                .diff(resources.flat_owned_memory_ranges())
            {
                let added = matches!(change, SnapshotMapChange::Added(_));
                let range = match change {
                    SnapshotMapChange::Added(range)
                    | SnapshotMapChange::Changed(range)
                    | SnapshotMapChange::Removed(range) => range,
                };
                if let Some(base) =
                    crate::kernel::assumptions::parameter_partition_root(range.base())
                {
                    // A changed ownership root can change only its known runs.
                    if let Some(runs) = index.known_runs.get(&base) {
                        run_changes.extend(runs.iter().cloned());
                    }
                    for ((_, key), _) in index
                        .known
                        .range((
                            Bound::Included((base.clone(), Pointer::null())),
                            Bound::Unbounded,
                        ))
                        .take_while(|((root, _), _)| *root == base)
                    {
                        changes.insert(key.clone(), self.concrete.contains_key(key));
                    }
                }
                // Unknown cells need a new membership check after a new
                // owning range is admitted; known unrelated members stay put.
                if added {
                    for key in index.unknown.keys() {
                        changes.insert(key.clone(), self.concrete.contains_key(key));
                    }
                    run_changes.extend(index.unknown_runs.keys().cloned());
                }
            }
        } else {
            let parameters = AliasCandidates::only_block(&PointerBlock::ExternalArgument);
            changes.extend(
                parameters
                    .entries(&self.concrete)
                    .map(|(key, _)| (key.clone(), true)),
            );
            run_changes.extend(parameters.entries(&self.runs).map(|(key, _)| key.clone()));
        }
        let mut index = previous.unwrap_or_else(|| ParameterPartitionIndex {
            cells: self.concrete.clone(),
            runs: self.runs.clone(),
            known_runs: Default::default(),
            unknown_runs: Default::default(),
            run_bases: SnapshotMap::new(),
            resources: resources.clone(),
            known: SnapshotMap::new(),
            unknown: SnapshotMap::new(),
            bases: SnapshotMap::new(),
        });
        for (key, present) in changes {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(base) = index.bases.get(&key).cloned() {
                index.known.remove(&(base, key.clone()));
                index.bases.remove(&key);
            }
            index.unknown.remove(&key);
            if !present {
                continue;
            }
            let value = self.concrete.get(&key).expect("changed cell exists");
            if let Some(base) = assumptions.parameter_partition_cell_base(
                resources,
                &key,
                crate::kernel::reasoning::cell_access_byte_width(value),
            ) {
                index.known.insert((base.clone(), key.clone()), ());
                index.bases.insert(key, base);
            } else {
                index.unknown.insert(key, ());
            }
        }
        for key in run_changes {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(base) = index.run_bases.get(&key).cloned() {
                let mut runs = index
                    .known_runs
                    .get(&base)
                    .expect("indexed run root")
                    .clone();
                std::sync::Arc::make_mut(&mut runs).retain(|held| held != &key);
                if runs.is_empty() {
                    index.known_runs.remove(&base);
                } else {
                    index.known_runs.insert(base, runs);
                }
                index.run_bases.remove(&key);
            }
            index.unknown_runs.remove(&key);
            let Some(run) = self.runs.get(&key) else {
                continue;
            };
            // Cover the entire run, including holes, so retaining its live
            // slots never relies on an incomplete byte footprint.
            let base = run
                .count()
                .checked_sub(1)
                .and_then(|last| last.checked_mul(run.element_width()))
                .and_then(|offset| offset.checked_add(run.value_width()))
                .and_then(|bytes| {
                    assumptions.parameter_partition_cell_base(resources, run.base(), bytes)
                });
            if let Some(base) = base {
                let mut runs = index.known_runs.get(&base).cloned().unwrap_or_default();
                std::sync::Arc::make_mut(&mut runs).push(key.clone());
                index.known_runs.insert(base.clone(), runs);
                index.run_bases.insert(key, base);
            } else {
                index.unknown_runs.insert(key, ());
            }
        }
        index.cells = self.concrete.clone();
        index.runs = self.runs.clone();
        index.resources = resources.clone();
        *guard = Some(index);
    }

    /// Concrete cells not wholly held by the caller's retained flat owners.
    pub(in crate::kernel) fn call_unowned_candidates(
        &self,
        resources: &crate::kernel::ResourceContext,
        candidates: &AliasCandidates,
    ) -> (Vec<Pointer>, Vec<RunKey>) {
        self.prepare_parameter_partition(resources);
        let guard = self.parameter_partition_index.lock().unwrap();
        let index = guard.as_ref().expect("prepared partition");
        let ordinary = candidates.excluding_external_arguments();
        let mut cells = candidates
            .entries(&index.unknown)
            .map(|(key, _)| key.clone())
            .chain(ordinary.entries(&self.concrete).map(|(key, _)| key.clone()))
            .collect::<Vec<_>>();
        let mut runs = candidates
            .entries(&index.unknown_runs)
            .map(|(key, _)| key.clone())
            .chain(ordinary.entries(&self.runs).map(|(key, _)| key.clone()))
            .collect::<Vec<_>>();
        cells.sort_unstable();
        runs.sort_unstable();
        (cells, runs)
    }

    /// Concrete cells whose canonical address lies on the region's line.
    /// Include the bounded prefix that an eight-byte cell could overlap.
    /// As for run slot candidates, use address ranges rather than scanning
    /// other parameter bases that share the external-argument block.
    pub(crate) fn concrete_region_candidates<'a>(
        &'a self,
        base: &Pointer,
        bytes: u32,
    ) -> Vec<(&'a Pointer, &'a CValue)> {
        let (stem, start) = offset_stem_and_constant(&base.offset);
        let low = start.saturating_sub(7);
        let high = start.saturating_add(i64::from(bytes));
        let at = |offset| Pointer {
            block: base.block.clone(),
            offset,
        };
        match stem {
            None => self
                .concrete
                .range(at(PointerOffsetTerm::Constant(low))..at(PointerOffsetTerm::Constant(high)))
                .collect(),
            Some(stem) => {
                let shifted = |shift| {
                    at(PointerOffsetTerm::Add(
                        Box::new(stem.clone()),
                        Box::new(PointerOffsetTerm::Constant(shift)),
                    ))
                };
                let mut result: Vec<_> = self.concrete.range(shifted(low)..shifted(high)).collect();
                if low <= 0 && 0 < high {
                    let key = at(stem.clone());
                    result.extend(self.concrete.range(key.clone()..=key));
                }
                result
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// The ordinary candidate cells, omitting only array cells which the
    /// recorded strict path places a full scalar width away from this store.
    /// The derivative cache follows persistent-map deltas between stores.
    /// The concrete cells a pointer value can reach, in key order: every cell
    /// except those in the slot of a local whose address is never taken,
    /// which no pointer value designates. Costs the cells changed since this
    /// store's lineage last asked, plus the cells returned.
    pub(in crate::kernel) fn pointer_reachable_cells(&self) -> Vec<Pointer> {
        self.caught_up_pointer_reachable()
            .keys()
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .cloned()
            .collect()
    }

    /// The pointer-reachable concrete cells with their values, a persistent
    /// map sharing structure with every earlier answer on this store's
    /// lineage. Costs the cells changed since that lineage last asked.
    pub(in crate::kernel) fn caught_up_pointer_reachable(&self) -> SnapshotMap<Pointer, CValue> {
        self.caught_up_load_reachable(false)
    }

    /// External pointers cannot observe local slots, heaps, or temporaries.
    /// Maintain that projection beside the general reachable map by delta.
    pub(in crate::kernel) fn caught_up_external_reachable(&self) -> SnapshotMap<Pointer, CValue> {
        self.caught_up_load_reachable(true)
    }

    fn caught_up_load_reachable(&self, external: bool) -> SnapshotMap<Pointer, CValue> {
        let generation = super::memory_state::never_address_taken_generation();
        let mut guard = self.pointer_reachable_index.lock().unwrap();
        let mut index = guard
            .take()
            .filter(|index| index.generation == generation)
            .unwrap_or_else(|| PointerReachableIndex {
                cells: SnapshotMap::new(),
                generation,
                reachable: SnapshotMap::new(),
                external: SnapshotMap::new(),
            });
        let changes = index
            .cells
            .diff(&self.concrete)
            .map(|change| match change {
                super::persistent_map::SnapshotMapChange::Added(key)
                | super::persistent_map::SnapshotMapChange::Changed(key) => key.clone(),
                super::persistent_map::SnapshotMapChange::Removed(key) => key.clone(),
            })
            .collect::<Vec<_>>();
        for key in changes {
            if super::block_is_never_address_taken_local(&key.block) {
                continue;
            }
            if key
                .block
                .observable_by_load(&PointerBlock::ExternalArgument)
            {
                match self.concrete.get(&key) {
                    Some(value) => {
                        index.external.insert(key.clone(), value.clone());
                    }
                    None => {
                        index.external.remove(&key);
                    }
                }
            }
            match self.concrete.get(&key) {
                Some(value) => {
                    index.reachable.insert(key, value.clone());
                }
                None => {
                    index.reachable.remove(&key);
                }
            }
        }
        index.cells = self.concrete.clone();
        let reachable = if external {
            index.external.clone()
        } else {
            index.reachable.clone()
        };
        *guard = Some(index);
        reachable
    }

    /// Projects the concrete cells onto what a load through an unresolved
    /// pointer (`Symbolic`, `LoadedPointer`, or an external block) can observe,
    /// keeping a cell when `keep` holds. Such a block may alias every block
    /// except the slot of a local whose address is never taken and, for a
    /// loaded pointer, locals that did not exist when it was read; so `keep`
    /// can only reject a cell of a `local:` block or of the load's own block
    /// (a constant offset shown disjoint). The projection therefore starts
    /// from the corresponding reachable map (external pointers also exclude
    /// local, heap, and temporary storage), shared and caught up by its own
    /// changes, and asks `keep` about those two key ranges alone: its cost is
    /// those cells and the changes since, not the cells of other objects.
    /// `None` when the store holds runs, which the general projection handles.
    pub(in crate::kernel) fn retain_for_unresolved_load(
        &mut self,
        load: &Pointer,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
    ) -> Option<usize> {
        if !self.runs.is_empty() {
            return None;
        }
        let mut reachable = if matches!(
            load.block,
            PointerBlock::ExternalArgument | PointerBlock::ExternalObject(_)
        ) {
            self.caught_up_external_reachable()
        } else {
            self.caught_up_pointer_reachable()
        };
        let locals = PointerBlock::Concrete("local:".to_string());
        let own_block = reachable
            .range::<_, Pointer>((
                Bound::Included(Pointer::first_key_of(&load.block)),
                Bound::Unbounded,
            ))
            .take_while(|(key, _)| key.block == load.block);
        let local_cells = reachable
            .range::<_, Pointer>((
                Bound::Included(Pointer::first_key_of(&locals)),
                Bound::Unbounded,
            ))
            .take_while(|(key, _)| key.block.starts_with("local:"));
        let mut visited = 0usize;
        let rejected = local_cells
            .chain(own_block)
            .filter(|(pointer, value)| {
                visited += 1;
                !keep(pointer, value)
            })
            .map(|(pointer, _)| pointer.clone())
            .collect::<Vec<_>>();
        // Reachable is a subset of concrete. Equal lengths and no rejected
        // entries mean this projection changes nothing. Keep the original
        // persistent root: rebuilding an equal map makes snapshot interning
        // compare every cell again for each fresh unresolved address.
        if rejected.is_empty() && reachable.len() == self.concrete.len() {
            return Some(visited);
        }
        for pointer in &rejected {
            reachable.remove(pointer);
        }
        self.reset();
        self.concrete = reachable;
        // The producer already knows this projection. Retain its index
        // directly instead of diffing away every omitted cell on the next read.
        let index = self
            .pointer_reachable_index
            .get_mut()
            .unwrap()
            .as_mut()
            .expect("the reachable projection prepared its index");
        index.cells = self.concrete.clone();
        index.reachable = self.concrete.clone();
        if matches!(
            load.block,
            PointerBlock::ExternalArgument | PointerBlock::ExternalObject(_)
        ) {
            index.external = self.concrete.clone();
        } else {
            for pointer in rejected {
                index.external.remove(&pointer);
            }
        }
        Some(visited)
    }

    pub(in crate::kernel) fn ordered_store_candidates(
        &self,
        pointer: &Pointer,
        bytes: u32,
        candidates: &AliasCandidates,
        assumptions: &PureFactContext,
    ) -> Option<Vec<Pointer>> {
        use crate::kernel::assumptions::variable_chains::array_index;
        if bytes == 0
            || crate::kernel::reasoning::store_gap::store_gap_skip_disabled()
            || crate::kernel::assumptions::implicit_reasoning_provenance_capturing()
            || crate::kernel::assumptions::reasoning_interrupted()
        {
            return None;
        }
        let (base, variable, stride) = array_index(&pointer.offset)?;
        if base.as_const().is_none()
            && !crate::kernel::reasoning::store_gap::anchor_is_normal(base, assumptions)
        {
            return None;
        }
        let span = assumptions.signed_variable_chains.span(variable)?;
        let mut guard = self.ordered_index.lock().unwrap();
        let mut index = guard.take().filter(|index| {
            index.block == pointer.block
                && index.base == *base
                && index.stride == stride
                && index.root == span.root
                && index
                    .chains
                    .shares_sources(&assumptions.signed_variable_chains)
        });
        let mut changes = Vec::new();
        if let Some(previous) = &index {
            for change in previous.cells.diff(&self.concrete) {
                match change {
                    super::persistent_map::SnapshotMapChange::Added(key) => {
                        changes.push((key.clone(), true))
                    }
                    super::persistent_map::SnapshotMapChange::Removed(key) => {
                        changes.push((key.clone(), false))
                    }
                    super::persistent_map::SnapshotMapChange::Changed(_) => {}
                }
            }
        } else {
            changes.extend(self.concrete.keys().cloned().map(|key| (key, true)));
            index = Some(OrderedIndexCache {
                cells: self.concrete.clone(),
                chains: assumptions.signed_variable_chains.clone(),
                block: pointer.block.clone(),
                base: base.clone(),
                stride,
                root: span.root,
                known: SnapshotMap::new(),
                unknown: SnapshotMap::new(),
            });
        }
        let mut index = index.unwrap();
        for (key, added) in changes {
            crate::instrumentation::record_deterministic_work(1);
            let rank =
                array_index(&key.offset).and_then(|(cell_base, cell_variable, cell_stride)| {
                    if key.block != pointer.block || cell_base != base || cell_stride != stride {
                        return None;
                    }
                    let cell_span = assumptions.signed_variable_chains.span(cell_variable)?;
                    (cell_span.root == span.root).then_some(cell_span.rank)
                });
            if let Some(rank) = rank {
                if added {
                    index.known.insert(rank, key);
                } else {
                    index.known.remove(&rank);
                }
            } else if added {
                index.unknown.insert(key, ());
            } else {
                index.unknown.remove(&key);
            }
        }
        index.cells = self.concrete.clone();
        let low_distance =
            (crate::kernel::MAX_SCALAR_ACCESS_BYTES as u64).div_ceil(stride as u64) as usize;
        let high_distance = u64::from(bytes).div_ceil(stride as u64) as usize;
        let low = span.rank.saturating_sub(low_distance.saturating_sub(1));
        let high = span.rank.saturating_add(high_distance);
        let mut selected = candidates
            .entries(&index.unknown)
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        selected.extend(index.known.range(low..high).map(|(_, key)| key.clone()));
        *guard = Some(index);
        Some(selected)
    }

    pub(super) fn retain_selected_concrete_by(
        &mut self,
        selected: &[Pointer],
        candidates: &AliasCandidates,
        selected_runs: Option<&[RunKey]>,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> Vec<DroppedRunSlots> {
        self.reset();
        for key in selected {
            crate::instrumentation::record_deterministic_work(1);
            if self
                .concrete
                .get(key)
                .is_some_and(|value| !keep(key, value))
            {
                self.concrete.remove(key);
            }
        }
        let runs = match selected_runs {
            Some(keys) => keys
                .iter()
                .filter_map(|key| self.runs.get(key).map(|run| (key.clone(), run.clone())))
                .collect(),
            None => self.visited_runs(Some(candidates)),
        };
        self.retain_runs_from(runs, keep, &mut run_rule)
    }

    /// The concrete cells alone, without any run: what a caller that only
    /// ever asks about cells outside every run may read directly.
    pub(crate) fn concrete(&self) -> &SnapshotMap<Pointer, CValue> {
        &self.concrete
    }

    /// Whether the store holds exactly this run: the same slots answered
    /// from the same source, with the same holes.
    pub(crate) fn holds_run(&self, run: &CellRun) -> bool {
        self.runs.get(&run.key()) == Some(run)
    }

    /// Every run, in key order. Every run has a live slot.
    pub(crate) fn runs(&self) -> impl Iterator<Item = &CellRun> + '_ {
        self.runs.values()
    }

    /// The runs on which the two stores' run maps differ, as `(held here,
    /// held in other)` per differing key, ascending; see
    /// [`SnapshotMap::diff`], which skips shared subtrees and charges one
    /// unit per difference.
    pub(crate) fn run_diff<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = (Option<&'a CellRun>, Option<&'a CellRun>)> + 'a {
        self.runs.diff(&other.runs).map(move |change| {
            let key = change.key();
            (self.runs.get(key), other.runs.get(key))
        })
    }

    /// How many runs the store holds.
    #[cfg(test)]
    pub(crate) fn run_count(&self) -> usize {
        self.runs.len()
    }

    /// The runs of one block, in key order, without visiting another
    /// block's.
    pub(crate) fn runs_in_block<'a>(
        &'a self,
        block: &PointerBlock,
    ) -> impl Iterator<Item = &'a CellRun> + 'a {
        let lower = RunKey::first_key_of(block);
        let upper = RunKey::bound(block, RunAnchor::Greatest, RunShape::Greatest);
        self.runs
            .range::<_, RunKey>((Bound::Included(lower), Bound::Included(upper)))
            .map(|(_, run)| run)
    }

    /// Held runs whose slot span meets `probe` on the same exact address
    /// line. This selects cache keys, not semantic pointer aliases: an alias
    /// through facts still uses the ordinary memory reasoning and invalidation.
    /// Work follows the represented cover segments and candidate runs, never
    /// the numeric element count or runs on other symbolic address stems.
    pub(crate) fn runs_meeting_slot_span(&self, probe: &CellRun) -> Vec<&CellRun> {
        let (line, first, last) = probe.slot_line_span();
        let leading = self
            .span_cover
            .range(..=(line.clone(), first))
            .next_back()
            .filter(|((held_line, _), segment)| held_line == &line && segment.end > first);
        let following = self.span_cover.range((
            Bound::Excluded((line.clone(), first)),
            Bound::Included((line, last)),
        ));
        let mut keys = BTreeSet::new();
        for (_, segment) in leading.into_iter().chain(following) {
            crate::instrumentation::record_deterministic_work(1);
            for key in segment.runs.iter() {
                crate::instrumentation::record_deterministic_work(1);
                keys.insert(key);
            }
        }
        keys.into_iter()
            .map(|key| self.runs.get(key).expect("a covering run is held"))
            .collect()
    }

    /// The runs `candidates` admits, in key order, without visiting a run of
    /// another block.
    pub(crate) fn candidate_runs<'a>(
        &'a self,
        candidates: &'a AliasCandidates,
    ) -> impl Iterator<Item = &'a CellRun> + 'a {
        candidates.entries(&self.runs).map(|(_, run)| run)
    }

    /// The runs based exactly at `offset` in `block`, in key order, without
    /// visiting another run.
    pub(crate) fn runs_based_at<'a>(
        &'a self,
        block: &PointerBlock,
        offset: &PointerOffsetTerm,
    ) -> impl Iterator<Item = &'a CellRun> + 'a {
        let anchor = RunAnchor::of(offset);
        self.runs_anchored(block, anchor.clone(), anchor)
    }

    /// The runs of `block` anchored from `low` through `high`, in key order.
    fn runs_anchored<'a>(
        &'a self,
        block: &PointerBlock,
        low: RunAnchor,
        high: RunAnchor,
    ) -> impl Iterator<Item = &'a CellRun> + 'a {
        let lower = RunKey::bound(block, low, RunShape::Least);
        let upper = RunKey::bound(block, high, RunShape::Greatest);
        self.runs
            .range::<_, RunKey>((Bound::Included(lower), Bound::Included(upper)))
            .map(|(_, run)| run)
    }

    /// Every held run that has a slot, live or not, spelled exactly
    /// `pointer`, in key order. Only runs whose span on the pointer's line
    /// ([`CoverLine`]) holds it are visited, which the span cover names
    /// exactly: a slot's offset is its run's base plus a constant, so it lies
    /// on the base's line.
    fn slots_at<'a>(&'a self, pointer: &'a Pointer) -> impl Iterator<Item = SlotAt<'a>> + 'a {
        let (stem, offset) = offset_stem_and_constant(&pointer.offset);
        let line = CoverLine {
            block: pointer.block.clone(),
            stem: stem.cloned(),
        };
        self.runs_covering(&line, offset)
            .into_iter()
            .filter_map(move |run| {
                // Positioning in the run map is a persistent-map lookup, as a
                // concrete cell's is, and is not charged; a visited run that
                // does not hold the slot is.
                #[cfg(test)]
                RUNS_VISITED.with(|visited| visited.set(visited.get() + 1));
                let index = run.slot_index(pointer);
                if index.is_none() {
                    crate::instrumentation::record_deterministic_work(1);
                }
                index.map(|index| SlotAt { run, index })
            })
    }

    /// The run holding a live slot at `pointer`, and the slot's element.
    fn live_run_slot<'a>(&'a self, pointer: &'a Pointer) -> Option<SlotAt<'a>> {
        if self.runs.is_empty() {
            return None;
        }
        self.slots_at(pointer)
            .find(|slot| !slot.run.holes.contains(slot.index))
    }

    /// Replaces the run at `key` with `run`, or removes it: a run with no
    /// live slot is retired rather than held.
    fn set_run(&mut self, key: &RunKey, run: Option<CellRun>) {
        let old = self.runs.remove(key);
        if let Some(old) = &old {
            self.run_cells -= old.live_count();
        }
        let run = run.filter(|run| run.live_count() > 0);
        // A run's key fixes its slots, so the cover changes only when a key
        // arrives or leaves.
        match (&old, &run) {
            (Some(old), None) => self.uncover(key, old),
            (None, Some(run)) => self.cover(key, run),
            _ => {}
        }
        if let Some(run) = run {
            self.run_cells += run.live_count();
            self.runs.insert(key.clone(), run);
        }
    }

    /// The held runs whose span on `line` holds `offset`, in key order: one
    /// lookup of the cover segment holding it.
    fn runs_covering<'a>(&'a self, line: &CoverLine, offset: i64) -> Vec<&'a CellRun> {
        let Some(((segment_line, _), segment)) =
            self.span_cover.range(..=(line.clone(), offset)).next_back()
        else {
            return Vec::new();
        };
        if segment_line != line || segment.end <= offset {
            return Vec::new();
        }
        segment
            .runs
            .iter()
            .map(|key| self.runs.get(key).expect("a covering run is held"))
            .collect()
    }

    /// Splits the cover segment of `line` holding `offset`, if one does
    /// and starts below it, so that a segment starts there.
    fn split_cover_at(&mut self, line: &CoverLine, offset: i64) {
        let Some(((segment_line, start), segment)) = self
            .span_cover
            .range(..(line.clone(), offset))
            .next_back()
            .map(|(key, segment)| (key.clone(), segment.clone()))
        else {
            return;
        };
        if segment_line != *line || segment.end <= offset {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        self.span_cover.insert(
            (line.clone(), start),
            CoverSegment {
                end: offset,
                runs: segment.runs.clone(),
            },
        );
        self.span_cover.insert((line.clone(), offset), segment);
    }

    /// Joins the segment of `line` ending at `offset` with the one starting
    /// there when they name the same runs.
    fn join_cover_at(&mut self, line: &CoverLine, offset: i64) {
        let Some(after) = self.span_cover.get(&(line.clone(), offset)).cloned() else {
            return;
        };
        let Some(((before_line, before_start), before)) = self
            .span_cover
            .range(..(line.clone(), offset))
            .next_back()
            .map(|(key, segment)| (key.clone(), segment.clone()))
        else {
            return;
        };
        if before_line != *line || before.end != offset || before.runs != after.runs {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        self.span_cover.remove(&(line.clone(), offset));
        self.span_cover.insert(
            (line.clone(), before_start),
            CoverSegment {
                end: after.end,
                runs: before.runs,
            },
        );
    }

    /// Files a newly held run under the bytes it spans on its line. Costs
    /// the segments its span meets.
    fn cover(&mut self, key: &RunKey, run: &CellRun) {
        let (line, start, last) = run.slot_line_span();
        let end = last.saturating_add(1);
        self.split_cover_at(&line, start);
        self.split_cover_at(&line, end);
        let met = self
            .span_cover
            .range((line.clone(), start)..(line.clone(), end))
            .map(|((_, segment_start), segment)| (*segment_start, segment.clone()))
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(met.len() + 1);
        let mut cursor = start;
        for (segment_start, mut segment) in met {
            if cursor < segment_start {
                self.span_cover.insert(
                    (line.clone(), cursor),
                    CoverSegment {
                        end: segment_start,
                        runs: vec![key.clone()],
                    },
                );
            }
            let position = segment
                .runs
                .binary_search(key)
                .expect_err("a newly held run is in no segment");
            segment.runs.insert(position, key.clone());
            cursor = segment.end;
            self.span_cover
                .insert((line.clone(), segment_start), segment);
        }
        if cursor < end {
            self.span_cover.insert(
                (line.clone(), cursor),
                CoverSegment {
                    end,
                    runs: vec![key.clone()],
                },
            );
        }
        self.join_cover_at(&line, start);
        self.join_cover_at(&line, end);
    }

    /// Withdraws a run no longer held from the bytes it spans on its line.
    /// Costs the segments its span meets.
    fn uncover(&mut self, key: &RunKey, run: &CellRun) {
        let (line, start, last) = run.slot_line_span();
        let end = last.saturating_add(1);
        let met = self
            .span_cover
            .range((line.clone(), start)..(line.clone(), end))
            .map(|((_, segment_start), segment)| (*segment_start, segment.clone()))
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(met.len() + 1);
        for (segment_start, mut segment) in met {
            let position = segment
                .runs
                .binary_search(key)
                .expect("a held run is in every segment of its span");
            segment.runs.remove(position);
            if segment.runs.is_empty() {
                self.span_cover.remove(&(line.clone(), segment_start));
            } else {
                self.span_cover
                    .insert((line.clone(), segment_start), segment);
            }
        }
        self.join_cover_at(&line, start);
        self.join_cover_at(&line, end);
    }

    /// Applies each `(key, run)` replacement, after a walk that collected
    /// them.
    fn apply_run_updates(&mut self, updates: Vec<(RunKey, CellRun)>) {
        for (key, run) in updates {
            self.set_run(&key, Some(run));
        }
    }

    /// The whole cell map, exactly as per-cell seeding would have stored it.
    /// O(1) without runs; with runs it is built once per store, at a cost of
    /// every live slot, and kept up to date through single-cell mutations.
    pub(crate) fn logical(&self) -> &SnapshotMap<Pointer, CValue> {
        if self.runs.is_empty() {
            return &self.concrete;
        }
        self.logical.get_or_init(|| {
            let _timing = crate::instrumentation::OperationTiming::new(
                "kernel",
                "cell store",
                "cell store: logical map",
            );
            let mut map = self.concrete.clone();
            crate::instrumentation::record_deterministic_work(
                usize::try_from(self.run_cells).unwrap_or(usize::MAX),
            );
            for run in self.runs.values() {
                for index in run.live_indexes() {
                    map.insert(run.slot_pointer(index), run.value(index));
                }
            }
            map
        })
    }

    fn reset(&mut self) {
        self.logical = OnceLock::new();
    }

    /// An explicitly stored value, without synthesizing a run-slot value.
    /// Dependency selection must not introduce a run's generated load atoms.
    pub(in crate::kernel) fn explicitly_stored_value(&self, pointer: &Pointer) -> Option<&CValue> {
        self.concrete.get(pointer)
    }

    /// Inspect a scalar atom without copying an unrelated symbolic expression.
    pub(crate) fn bitvector_variable_at(&self, pointer: &Pointer) -> Option<Variable> {
        fn variable(value: &CValue) -> Option<Variable> {
            match value {
                crate::kernel::integer_c_value!(term) => match term {
                    Bitvector32Term::Variable(variable) => Some(*variable),
                    _ => None,
                },
                _ => None,
            }
        }
        if let Some(value) = self.concrete.get(pointer) {
            return variable(value);
        }
        let slot = self.live_run_slot(pointer)?;
        if let RunValueMode::Constant(value) = &slot.run.mode {
            return variable(value);
        }
        variable(&slot.run.value(slot.index))
    }

    /// The cell at `pointer`, read from a run slot without building the
    /// logical map.
    pub(crate) fn get(&self, pointer: &Pointer) -> Option<CValue> {
        if let Some(value) = self.concrete.get(pointer) {
            return Some(value.clone());
        }
        self.live_run_slot(pointer)
            .map(|slot| slot.run.value(slot.index))
    }

    pub(crate) fn contains_key(&self, pointer: &Pointer) -> bool {
        self.concrete.contains_key(pointer) || self.live_run_slot(pointer).is_some()
    }

    /// How many bytes the cell at `pointer` holds, read from a run slot's
    /// element type without naming the slot's value: [`Self::get`]'s
    /// `byte_width`, at the cost of the lookup alone.
    pub(crate) fn value_width_at(&self, pointer: &Pointer) -> Option<u32> {
        if let Some(value) = self.concrete.get(pointer) {
            return Some(value.byte_width());
        }
        self.live_run_slot(pointer)
            .map(|slot| slot.run.value_width())
    }

    /// Initialized bytes starting at one addressed cell. Dense runs stop at
    /// their next hole, found by an ordered lookup rather than enumerating
    /// live intervals. A strided run authorizes only the selected cell.
    pub(crate) fn contiguous_bytes_at(&self, pointer: &Pointer) -> Option<u32> {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(value) = self.concrete.get(pointer) {
            return Some(value.byte_width());
        }
        let slot = self.live_run_slot(pointer)?;
        let width = slot.run.value_width();
        if width != slot.run.element_width {
            return Some(width);
        }
        let end = slot
            .run
            .holes
            .intervals
            .range((slot.index, 0)..)
            .next()
            .map_or(slot.run.count, |(low, _)| *low);
        end.checked_sub(slot.index)?.checked_mul(width)
    }

    /// Whether the live run slots `observable` accepts are the same cells in
    /// both stores, answered from the runs alone: `Some(true)` when they are,
    /// so the observable cells agree exactly when the concrete ones do, and
    /// `Some(false)` when they cannot agree. `None` when the runs do not pair
    /// up and only the logical maps can tell.
    ///
    /// The runs pair up by key, and only the keys the two run maps differ
    /// on are visited. An observable run held by one store alone leaves the
    /// answer to the logical maps. One held by both with other holes has a
    /// slot live on one side and a hole on the other, and the canonical form
    /// keeps a concrete cell at a hole only when it holds something other
    /// than the run's value.
    pub(crate) fn observable_runs_match(
        &self,
        other: &Self,
        mut observable: impl FnMut(&CellRun) -> bool,
    ) -> Option<bool> {
        if self.runs.ptr_eq(&other.runs) {
            return Some(true);
        }
        let mut holes_differ = false;
        for change in self.runs.diff(&other.runs) {
            match change {
                SnapshotMapChange::Removed(key) => {
                    if observable(self.runs.get(key).expect("a removed key is held")) {
                        return None;
                    }
                }
                SnapshotMapChange::Added(key) => {
                    if observable(other.runs.get(key).expect("an added key is held")) {
                        return None;
                    }
                }
                SnapshotMapChange::Changed(key) => {
                    holes_differ |= observable(self.runs.get(key).expect("a changed key is held"));
                }
            }
        }
        Some(!holes_differ)
    }

    /// The logical cells `candidates` admits, ascending, as
    /// `candidates.entries(self.logical())` yields them, without laying out
    /// a run: each admitted run's live slots are spelled and valued only as
    /// the walk reaches them. The concrete candidates and each run's slots
    /// are ascending, so a merge of them is the logical walk. A caller that
    /// stops early pays only for what it visited, plus a logarithmic step
    /// per cell in the number of admitted runs.
    pub(crate) fn candidate_logical_entries<'a>(
        &'a self,
        candidates: &'a AliasCandidates,
    ) -> impl Iterator<Item = (Pointer, CValue)> + 'a {
        self.candidate_logical_entries_selected(candidates, None, None)
    }

    pub(crate) fn candidate_logical_entries_selected<'a>(
        &'a self,
        candidates: &'a AliasCandidates,
        selected: Option<&'a [Pointer]>,
        selected_runs: Option<&'a [RunKey]>,
    ) -> impl Iterator<Item = (Pointer, CValue)> + 'a {
        type Sequence<'a> = Box<dyn Iterator<Item = (Pointer, CValue)> + 'a>;
        let concrete: Sequence<'a> = match selected {
            Some(selected) => Box::new(selected.iter().filter_map(|pointer| {
                self.concrete
                    .get(pointer)
                    .cloned()
                    .map(|value| (pointer.clone(), value))
            })),
            None => Box::new(
                candidates
                    .entries(&self.concrete)
                    .map(|(pointer, value)| (pointer.clone(), value.clone())),
            ),
        };
        let mut sequences: Vec<Sequence<'a>> = vec![concrete];
        let runs: Box<dyn Iterator<Item = &CellRun> + '_> = match selected_runs {
            Some(keys) => Box::new(keys.iter().filter_map(|key| self.runs.get(key))),
            None => Box::new(self.candidate_runs(candidates)),
        };
        for run in runs {
            // Element 0 is spelled as the base itself and every later element
            // as the base plus its shift, so the two are ascending apart.
            sequences.push(Box::new(
                (!run.holes.contains(0))
                    .then(|| (run.slot_pointer(0), run.value(0)))
                    .into_iter(),
            ));
            sequences.push(Box::new(
                run.holes
                    .gaps(run.count)
                    .into_iter()
                    .flat_map(|(low, high)| low.max(1)..high)
                    .map(move |index| (run.slot_pointer(index), run.value(index))),
            ));
        }
        let mut values = Vec::with_capacity(sequences.len());
        let mut heads = std::collections::BinaryHeap::new();
        for (position, sequence) in sequences.iter_mut().enumerate() {
            match sequence.next() {
                Some((pointer, value)) => {
                    heads.push(std::cmp::Reverse((pointer, position)));
                    values.push(Some(value));
                }
                None => values.push(None),
            }
        }
        std::iter::from_fn(move || {
            let std::cmp::Reverse((pointer, position)) = heads.pop()?;
            let value = values[position].take().expect("a queued head has a value");
            if let Some((next_pointer, next_value)) = sequences[position].next() {
                heads.push(std::cmp::Reverse((next_pointer, position)));
                values[position] = Some(next_value);
            }
            Some((pointer, value))
        })
    }

    /// How many entries represent the cells: each concrete cell and each
    /// run, whatever its length. The measure of work that visits the
    /// representation rather than every logical cell.
    pub(crate) fn representation_len(&self) -> usize {
        self.concrete.len() + self.runs.len()
    }

    pub(crate) fn len(&self) -> usize {
        self.concrete.len() + usize::try_from(self.run_cells).unwrap_or(usize::MAX)
    }

    pub(crate) fn iter(
        &self,
    ) -> imbl::ordmap::Iter<'_, Pointer, CValue, imbl::shared_ptr::DefaultSharedPtr> {
        self.logical().iter()
    }

    pub(crate) fn keys(
        &self,
    ) -> imbl::ordmap::Keys<'_, Pointer, CValue, imbl::shared_ptr::DefaultSharedPtr> {
        self.logical().keys()
    }

    pub(crate) fn range<R>(
        &self,
        range: R,
    ) -> imbl::ordmap::RangedIter<'_, Pointer, CValue, imbl::shared_ptr::DefaultSharedPtr>
    where
        R: std::ops::RangeBounds<Pointer>,
    {
        self.logical().range(range)
    }

    /// The entries on which the two stores differ; see [`SnapshotMap::diff`].
    /// Two stores over the same runs differ exactly where their concrete maps
    /// do, by the canonical form.
    pub(crate) fn diff<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = SnapshotMapChange<'a, Pointer>> + 'a {
        if self.runs == other.runs {
            self.concrete.diff(&other.concrete)
        } else {
            self.logical().diff(other.logical())
        }
    }

    /// The concrete cells this store holds that `earlier` did not hold with
    /// the same value, with their values: every concrete cell when there is
    /// no earlier store. Runs are not visited. For stores derived from one
    /// another the walk is proportional to the changed cells.
    pub(crate) fn changed_concrete_cells<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<(&'a Pointer, &'a CValue)> {
        match earlier {
            Some(earlier) => earlier
                .concrete
                .diff(&self.concrete)
                .filter_map(|change| match change {
                    SnapshotMapChange::Added(pointer) | SnapshotMapChange::Changed(pointer) => {
                        self.concrete.get(pointer).map(|value| (pointer, value))
                    }
                    SnapshotMapChange::Removed(_) => None,
                })
                .collect(),
            None => self.concrete.iter().collect(),
        }
    }

    /// The pointers at which the two stores' logical maps differ, ascending,
    /// without laying out a run the other store shares; see
    /// [`Self::differing_cells`].
    pub(crate) fn differing_pointers(&self, other: &Self) -> Vec<Pointer> {
        let differing = self.differing_cells(other);
        let mut pointers = differing
            .pointers
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        for (run, slots) in differing.run_slots {
            crate::instrumentation::record_deterministic_work(
                usize::try_from(slots.count()).unwrap_or(usize::MAX),
            );
            pointers.extend(slots.indexes().map(|index| run.slot_pointer(index)));
        }
        pointers.into_iter().collect()
    }

    /// Exactly the pointers at which the two stores' logical maps differ,
    /// with each run's differing slots left as intervals where every slot in
    /// them differs, for a caller that can pass over slots it proves
    /// irrelevant without spelling their pointers.
    ///
    /// Only what the two stores do not share is visited: the concrete maps'
    /// diff and the run maps' diff, both walked by persistent-node identity.
    /// A run held by both with other holes differs at the slots live on one
    /// side only; a run held by one differs at its live slots. Such a slot
    /// agrees with the other side only where that side holds the same value
    /// there, and the other side can hold a value at a live slot of this
    /// store's run only in a concrete cell — which the concrete diff visits,
    /// since the live side holds no concrete cell there — or in a live slot
    /// of another run that differs between the stores in the same block: a
    /// run both stores hold alike is live at that slot on both sides, and
    /// two runs are never live at one slot. So the concrete diff's pointers
    /// are checked one by one, and a run's slots are checked one by one only
    /// when another differing run shares its block.
    pub(crate) fn differing_cells(&self, other: &Self) -> DifferingCells {
        let concrete_changes = self
            .concrete
            .diff(&other.concrete)
            .map(|change| change.key().clone())
            .collect::<Vec<_>>();
        if self.runs.ptr_eq(&other.runs) || self.runs == other.runs {
            return DifferingCells {
                pointers: concrete_changes,
                run_slots: Vec::new(),
            };
        }
        let mut differing_runs: Vec<(CellRun, IndexIntervals)> = Vec::new();
        let mut differing_runs_per_block =
            std::collections::BTreeMap::<&PointerBlock, usize>::new();
        for change in self.runs.diff(&other.runs) {
            let (run, slots) = match change {
                SnapshotMapChange::Removed(key) => {
                    let run = self.runs.get(key).expect("a removed key is held");
                    (run, run.live_intervals())
                }
                SnapshotMapChange::Added(key) => {
                    let run = other.runs.get(key).expect("an added key is held");
                    (run, run.live_intervals())
                }
                SnapshotMapChange::Changed(key) => {
                    let left = self.runs.get(key).expect("a changed key is held");
                    let right = other.runs.get(key).expect("a changed key is held");
                    let slots = left
                        .holes
                        .symmetric_difference(&right.holes)
                        .intersection(&IndexIntervals::full(left.count));
                    (left, slots)
                }
            };
            *differing_runs_per_block.entry(&run.base.block).or_default() += 1;
            differing_runs.push((run.clone(), slots));
        }
        crate::instrumentation::record_deterministic_work(differing_runs.len());
        let mut pointers = Vec::new();
        let concrete_changes = concrete_changes.into_iter().collect::<BTreeSet<_>>();
        for pointer in &concrete_changes {
            crate::instrumentation::record_deterministic_work(1);
            if self.get(pointer) != other.get(pointer) {
                pointers.push(pointer.clone());
            }
        }
        let mut run_slots = Vec::new();
        for (run, mut slots) in differing_runs {
            if differing_runs_per_block[&run.base.block] > 1 {
                crate::instrumentation::record_deterministic_work(
                    usize::try_from(slots.count()).unwrap_or(usize::MAX),
                );
                for index in slots.indexes() {
                    let pointer = run.slot_pointer(index);
                    if !concrete_changes.contains(&pointer)
                        && self.get(&pointer) != other.get(&pointer)
                    {
                        pointers.push(pointer);
                    }
                }
                continue;
            }
            for pointer in run_slot_candidates_in(&run, |low, high| {
                concrete_changes.range::<Pointer, _>((low, high))
            }) {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(index) = run.slot_index(pointer) {
                    slots.remove(index);
                }
            }
            if slots.count() > 0 {
                run_slots.push((run, slots));
            }
        }
        pointers.sort();
        pointers.dedup();
        DifferingCells {
            pointers,
            run_slots,
        }
    }

    /// Whether the two stores hold exactly the same cells: the same pointers
    /// with the same values, however each store represents them.
    ///
    /// `==` compares the concrete map and the run map, and those can differ
    /// between two stores with one logical map: a path that wrote a run's
    /// only slot and wrote the run's value back holds a concrete cell where
    /// a path that never wrote it holds the live slot, because the first
    /// path's store retired the run. A run is exactly its logical cells (the
    /// module comment), so this is an equivalence of what a consumer reads
    /// and nothing weaker. The work is [`Self::differing_cells`]': what the
    /// two stores do not share.
    pub(crate) fn same_cells_as(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        let differing = self.differing_cells(other);
        differing.pointers.is_empty() && differing.run_slots.is_empty()
    }

    /// See [`SnapshotMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.runs.eq_relative_to(&other.runs, &base.runs)
            && self
                .concrete
                .eq_relative_to(&other.concrete, &base.concrete)
    }

    /// See [`SnapshotMap::is_without`], over the logical maps: `self` is
    /// `before` with exactly the cells at `removed` gone, which is what the
    /// two stores' differing pointers say when each of them is absent here.
    pub(crate) fn is_without(&self, before: &Self, removed: &[&Pointer]) -> bool {
        if self.runs.is_empty() && before.runs.is_empty() {
            return self.concrete.is_without(&before.concrete, removed);
        }
        if self.len() + removed.len() != before.len() {
            return false;
        }
        let differing = before.differing_pointers(self);
        differing.len() == removed.len()
            && differing
                .iter()
                .zip(removed)
                .all(|(differing, removed)| differing == *removed && !self.contains_key(differing))
    }

    /// Stores `value` at `pointer`, in canonical form.
    pub(crate) fn insert(&mut self, pointer: Pointer, value: CValue) {
        if let Some(logical) = self.logical.get_mut() {
            logical.insert(pointer.clone(), value.clone());
        }
        if self.runs.is_empty() {
            self.concrete.insert(pointer, value);
            return;
        }
        let live = self
            .live_run_slot(&pointer)
            .map(|slot| (slot.run.clone(), slot.index));
        if let Some((mut run, index)) = live {
            if run.value(index) == value {
                return;
            }
            run.holes.insert(index);
            self.set_run(&run.key(), Some(run));
            self.concrete.insert(pointer, value);
            return;
        }
        let refilled = self
            .slots_at(&pointer)
            .find(|slot| slot.run.value(slot.index) == value)
            .map(|slot| (slot.run.clone(), slot.index));
        if let Some((mut run, index)) = refilled {
            run.holes.remove(index);
            self.set_run(&run.key(), Some(run));
            self.concrete.remove(&pointer);
            return;
        }
        self.concrete.insert(pointer, value);
    }

    /// Removes the cell at `pointer`, returning what it held.
    pub(crate) fn remove(&mut self, pointer: &Pointer) -> Option<CValue> {
        if let Some(logical) = self.logical.get_mut() {
            logical.remove(pointer);
        }
        let held = self
            .live_run_slot(pointer)
            .map(|slot| (slot.run.clone(), slot.index));
        if let Some((mut run, index)) = held {
            let value = run.value(index);
            run.holes.insert(index);
            self.set_run(&run.key(), Some(run));
            return Some(value);
        }
        self.concrete.remove(pointer)
    }

    /// Whether every cell and run on which the two stores differ lies in one
    /// of `blocks`, visiting only those.
    pub(crate) fn differs_only_within(
        &self,
        other: &Self,
        blocks: &dyn super::memory_state::BlockMembership,
    ) -> bool {
        self.concrete
            .diff(&other.concrete)
            .all(|change| blocks.contains_block(&change.key().block))
            && self.runs.diff(&other.runs).all(|change| {
                let key = change.key();
                self.runs
                    .get(key)
                    .or_else(|| other.runs.get(key))
                    .is_some_and(|run| blocks.contains_block(&run.base().block))
            })
    }

    /// Drops the values `self` and `others` do not all hold alike, for the
    /// join of stores that are arms of one split, and returns the blocks in
    /// which any of them holds such a value.
    ///
    /// The stores share every subtree no arm touched, so only the entries on
    /// which they differ are visited: the work is the arms' changes, not the
    /// stores. A concrete cell `self` holds and another store lacks or holds
    /// with another value goes unless `keeps_cell` protects it; a run `self`
    /// holds and another store lacks or holds with other holes is decided by
    /// `run_rule`, as [`Self::retain_by`] decides one. Everything else every
    /// store holds alike and is kept unvisited.
    pub(crate) fn retain_agreed_with(
        &mut self,
        others: &[&Self],
        mut keeps_cell: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> BTreeSet<PointerBlock> {
        let held = self.clone();
        let mut blocks = BTreeSet::new();
        let mut cells = BTreeSet::new();
        let mut runs = BTreeMap::new();
        let mut visited = 0usize;
        for other in others {
            for change in held.concrete.diff(&other.concrete) {
                match change {
                    SnapshotMapChange::Added(pointer) => {
                        blocks.insert(pointer.block.clone());
                    }
                    SnapshotMapChange::Removed(pointer) | SnapshotMapChange::Changed(pointer) => {
                        cells.insert(pointer.clone());
                    }
                }
            }
            for change in held.runs.diff(&other.runs) {
                let key = change.key();
                match held.runs.get(key) {
                    Some(run) => {
                        runs.insert(key.clone(), run.clone());
                    }
                    None => {
                        if let Some(run) = other.runs.get(key) {
                            blocks.insert(run.base().block.clone());
                        }
                    }
                }
            }
        }
        if cells.is_empty() && runs.is_empty() {
            return blocks;
        }
        self.reset();
        for pointer in cells {
            visited += 1;
            let Some(value) = self.concrete.get(&pointer) else {
                continue;
            };
            if !keeps_cell(&pointer, value) {
                self.concrete.remove(&pointer);
                blocks.insert(pointer.block.clone());
            }
        }
        for (key, mut run) in runs {
            visited += 1;
            let (decision, _) = run_rule(&run);
            let before = run.holes.clone();
            run.keep_only(decision, &mut keeps_cell, &mut visited);
            if run.holes != before {
                blocks.insert(run.base().block.clone());
                self.set_run(&key, Some(run));
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
        blocks
    }

    /// Keeps only the cells `keep` accepts, visiting every cell.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&Pointer, &CValue) -> bool) {
        self.reset();
        self.concrete.retain(&mut keep);
        self.retain_run_slots(false, None, keep);
    }

    /// [`Self::retain`] with a whole-run answer from `run_rule`, as for
    /// [`Self::retain_only_candidates_by`]. Returns the run slots it dropped.
    pub(crate) fn retain_by(
        &mut self,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> Vec<DroppedRunSlots> {
        self.reset();
        self.concrete.retain(&mut keep);
        self.retain_runs_by(None, keep, &mut run_rule)
    }

    /// Keeps the candidate cells `keep` accepts, leaving cells outside the
    /// candidates unvisited as [`AliasCandidates::retain_map`] does, with a
    /// whole-run answer from `run_rule` as for
    /// [`Self::retain_only_candidates_by`], for a `keep` that the
    /// caller has shown accepts every concrete cell inside the key ranges
    /// `kept`: those cells are kept without being visited
    /// ([`AliasCandidates::retain_map_outside`]). Runs are asked as before.
    /// Returns the run slots it dropped.
    pub(crate) fn retain_candidates_outside_by(
        &mut self,
        candidates: &AliasCandidates,
        kept: &[(Pointer, Pointer)],
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> Vec<DroppedRunSlots> {
        self.reset();
        candidates.retain_map_outside(&mut self.concrete, kept, &mut keep);
        self.retain_runs_by(Some(candidates), keep, &mut run_rule)
    }

    /// The runs a retain visits: those `candidates` admits, or every run.
    fn visited_runs(&self, candidates: Option<&AliasCandidates>) -> Vec<(RunKey, CellRun)> {
        match candidates {
            Some(candidates) => candidates
                .entries(&self.runs)
                .map(|(key, run)| (key.clone(), run.clone()))
                .collect(),
            None => self
                .runs
                .iter()
                .map(|(key, run)| (key.clone(), run.clone()))
                .collect(),
        }
    }

    fn retain_runs_by(
        &mut self,
        candidates: Option<&AliasCandidates>,
        keep: impl FnMut(&Pointer, &CValue) -> bool,
        run_rule: &mut impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> Vec<DroppedRunSlots> {
        self.retain_runs_from(self.visited_runs(candidates), keep, run_rule)
    }

    fn retain_runs_from(
        &mut self,
        runs: Vec<(RunKey, CellRun)>,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        run_rule: &mut impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> Vec<DroppedRunSlots> {
        let mut visited = 0usize;
        let mut updates = Vec::new();
        let mut dropped = Vec::new();
        for (key, mut run) in runs {
            visited += 1;
            let (decision, answer) = run_rule(&run);
            #[cfg(debug_assertions)]
            if answer == RuleAnswer::Exact {
                crate::instrumentation::uncharged_debug_check(|| {
                    decision.check_against(&run, &mut keep);
                });
            }
            let _ = answer;
            let before = run.holes.clone();
            run.keep_only(decision, &mut keep, &mut visited);
            if run.holes != before {
                // Linear in the two hole interval counts, which the walk
                // above already paid to build.
                dropped.push(DroppedRunSlots {
                    elements: run.holes.difference(&before),
                    run: run.clone(),
                });
                updates.push((key, run));
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
        self.apply_run_updates(updates);
        dropped
    }

    /// Keeps only the candidate cells `keep` accepts, and no cell outside the
    /// candidates, with a whole-run answer: `run_rule`
    /// says which of a candidate run's live slots to keep, and only a run it
    /// answers [`SlotSet::PerSlot`] for is asked slot by slot. An answer the
    /// rule calls [`RuleAnswer::Exact`] is what `keep` would say of every
    /// slot, and debug builds check that on every run of at most
    /// [`CHECKED_RUN_SLOTS`] slots.
    pub(crate) fn retain_only_candidates_by(
        &mut self,
        candidates: &AliasCandidates,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> usize {
        self.reset();
        let mut visited = 0usize;
        let kept = candidates
            .entries(&self.concrete)
            .filter(|(pointer, value)| {
                visited += 1;
                keep(pointer, value)
            })
            .map(|(pointer, value)| (pointer.clone(), value.clone()))
            .collect::<Vec<_>>();
        if kept.len() != self.concrete.len() {
            self.concrete = kept.into_iter().collect();
        }
        if self.runs.is_empty() {
            return visited;
        }
        // Only the candidate runs survive, so the run map is rebuilt from
        // them alone, as the concrete map is.
        let candidate_runs = self.visited_runs(Some(candidates));
        let mut kept_runs = Self::default();
        for (key, mut run) in candidate_runs {
            visited += 1;
            let (decision, answer) = run_rule(&run);
            #[cfg(debug_assertions)]
            if answer == RuleAnswer::Exact {
                crate::instrumentation::uncharged_debug_check(|| {
                    decision.check_against(&run, &mut keep);
                });
            }
            let _ = answer;
            run.keep_only(decision, &mut keep, &mut visited);
            kept_runs.set_run(&key, Some(run));
        }
        if kept_runs.runs != self.runs {
            self.runs = kept_runs.runs;
            self.span_cover = kept_runs.span_cover;
            self.run_cells = kept_runs.run_cells;
        }
        visited
    }

    /// The first candidate cell, in the whole map's order, that `found`
    /// accepts. A run answers through `run_rule`, as for
    /// [`Self::retain_only_candidates_by`]; a run can hold the match only at
    /// a slot in the set it answers.
    pub(crate) fn find_candidate_by(
        &self,
        candidates: &AliasCandidates,
        mut found: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) -> (Option<CValue>, usize) {
        let mut visited = 0usize;
        let mut best: Option<(Pointer, CValue)> = candidates
            .entries(&self.concrete)
            .find(|(pointer, value)| {
                visited += 1;
                found(pointer, value)
            })
            .map(|(pointer, value)| (pointer.clone(), value.clone()));
        for run in self.candidate_runs(candidates) {
            visited += 1;
            let (decision, answer) = run_rule(run);
            #[cfg(debug_assertions)]
            if answer == RuleAnswer::Exact {
                crate::instrumentation::uncharged_debug_check(|| {
                    decision.check_against(run, &mut found);
                });
            }
            let _ = answer;
            for index in decision.live_indexes(run, &mut visited) {
                let pointer = run.slot_pointer(index);
                if best.as_ref().is_some_and(|(best, _)| *best <= pointer) {
                    continue;
                }
                let value = run.value(index);
                if found(&pointer, &value) {
                    best = Some((pointer, value));
                }
            }
        }
        (best.map(|(_, value)| value), visited)
    }

    /// Asks `keep` of every live slot of the visited runs (the candidate
    /// runs when `only_candidates`, else every run) and makes a hole of each
    /// slot it rejects.
    fn retain_run_slots(
        &mut self,
        only_candidates: bool,
        candidates: Option<&AliasCandidates>,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
    ) {
        if self.runs.is_empty() {
            return;
        }
        let mut visited = 0usize;
        let mut updates = Vec::new();
        let visited_runs = self.visited_runs(candidates.filter(|_| only_candidates));
        for (key, mut run) in visited_runs {
            let dropped = run
                .live_indexes()
                .filter(|index| {
                    visited += 1;
                    let pointer = run.slot_pointer(*index);
                    let value = run.value(*index);
                    !keep(&pointer, &value)
                })
                .collect::<Vec<_>>();
            if dropped.is_empty() {
                continue;
            }
            for index in dropped {
                run.holes.insert(index);
            }
            updates.push((key, run));
        }
        crate::instrumentation::record_deterministic_work(visited);
        self.apply_run_updates(updates);
    }

    /// Every cell rewritten by `map`, in canonical form. A run whose every
    /// live slot `map` leaves exactly as it is stays a run; any other run's
    /// cells become concrete cells of the result. So a rewrite that changes
    /// nothing hands back an equal store, as it did when every seeded cell
    /// was concrete.
    ///
    /// `singled_out` may name, for a run, the one slot `map` could change
    /// while leaving every other slot of its spelling shape alone: a
    /// substitution of one slot's own load variable. That slot is mapped by
    /// itself and the rest of the run is asked as a whole.
    pub(crate) fn map_cells(
        &self,
        mut map: impl FnMut(&Pointer, &CValue) -> (Pointer, CValue),
        mut singled_out: impl FnMut(&CellRun) -> Option<u32>,
    ) -> Self {
        self.map_cells_preserving_runs(&mut map, &mut singled_out, |_| false)
    }

    /// The same map with a caller's structural whole-run identity argument.
    /// `unchanged` must establish that `map` leaves every live pointer and
    /// value unchanged, without sampling a run whose source is nonuniform.
    /// Small runs audit that argument against every represented slot.
    pub(crate) fn map_cells_preserving_runs(
        &self,
        mut map: impl FnMut(&Pointer, &CValue) -> (Pointer, CValue),
        mut singled_out: impl FnMut(&CellRun) -> Option<u32>,
        mut unchanged: impl FnMut(&CellRun) -> bool,
    ) -> Self {
        let mut result = Self::default();
        let mut rewritten = Vec::new();
        for (key, run) in self.runs.iter() {
            if unchanged(run) {
                crate::instrumentation::record_deterministic_work(1);
                #[cfg(debug_assertions)]
                if run.count() <= CHECKED_RUN_SLOTS {
                    crate::instrumentation::uncharged_debug_check(|| {
                        for index in run.live_indexes() {
                            let pointer = run.slot_pointer(index);
                            let value = run.value(index);
                            assert_eq!(map(&pointer, &value), (pointer, value));
                        }
                    });
                }
                result.set_run(key, Some(run.clone()));
                continue;
            }
            // The singled-out slot is set aside before the rest is asked as a
            // whole: its change is the one the representatives cannot see.
            match singled_out(run).filter(|index| !run.holes.contains(*index)) {
                Some(index) => {
                    let mut rest = run.clone();
                    rest.holes.insert(index);
                    if run_unchanged_by_uniform_map(&rest, &mut map) {
                        rewritten.push(map(&run.slot_pointer(index), &run.value(index)));
                        result.set_run(key, Some(rest));
                        continue;
                    }
                }
                None => {
                    if run_unchanged_by_uniform_map(run, &mut map) {
                        result.set_run(key, Some(run.clone()));
                        continue;
                    }
                }
            }
            let mut cells = Vec::new();
            let mut unchanged = true;
            for index in run.live_indexes() {
                let pointer = run.slot_pointer(index);
                let value = run.value(index);
                let (mapped_pointer, mapped_value) = map(&pointer, &value);
                unchanged &= mapped_pointer == pointer && mapped_value == value;
                cells.push((mapped_pointer, mapped_value));
            }
            if unchanged {
                result.set_run(key, Some(run.clone()));
            } else {
                rewritten.extend(cells);
            }
        }
        for (pointer, value) in self.concrete.iter() {
            let (pointer, value) = map(pointer, value);
            result.insert(pointer, value);
        }
        for (pointer, value) in rewritten {
            result.insert(pointer, value);
        }
        result.reset();
        result
    }

    /// Stores every live slot of `run` into this store at once, as inserting
    /// each slot's value would, or returns `false` having changed nothing
    /// when only slot by slot can say what that leaves.
    ///
    /// A slot of `run` live here in a run with the same slots already holds
    /// its value. One that is a hole here becomes live again, and whatever
    /// concrete cell sat at it is replaced. With no such run here, `run` is
    /// added, holes and all, and the concrete cells at its live slots are
    /// replaced the same way. Any other run over the block could hold one of
    /// these slots itself, which only slot by slot can sort out.
    pub(crate) fn install_run(&mut self, run: &CellRun) -> bool {
        let key = run.key();
        let mut block_runs = 0usize;
        let other_live = self.runs_in_block(&run.base.block).any(|held| {
            block_runs += 1;
            !held.same_slots_as(run)
        });
        crate::instrumentation::record_deterministic_work(block_runs + 1);
        if other_live {
            return false;
        }
        self.reset();
        let (revived, installed) = match self.runs.get(&key) {
            Some(held) => {
                let revived = held.holes.difference(&run.holes);
                let mut installed = held.clone();
                installed.holes = held.holes.intersection(&run.holes);
                (revived, installed)
            }
            None => (run.live_intervals(), run.clone()),
        };
        self.set_run(&key, Some(installed));
        // The concrete cells at revived slots are replaced: named slot by
        // slot when there are fewer revived slots than concrete cells, and
        // otherwise found among the concrete cells where the run's slots lie.
        let revived_count = revived.count();
        crate::instrumentation::record_deterministic_work(revived.interval_count());
        let replaced = if revived_count <= self.concrete.len() as u64 {
            crate::instrumentation::record_deterministic_work(
                usize::try_from(revived_count).unwrap_or(usize::MAX),
            );
            revived
                .indexes()
                .map(|index| run.slot_pointer(index))
                .collect::<Vec<_>>()
        } else {
            run_slot_candidates_in(run, |low, high| {
                self.concrete
                    .range::<_, Pointer>((low, high))
                    .map(|(pointer, _)| pointer)
            })
            .filter(|pointer| {
                crate::instrumentation::record_deterministic_work(1);
                run.slot_index(pointer)
                    .is_some_and(|index| revived.contains(index))
            })
            .cloned()
            .collect::<Vec<_>>()
        };
        for pointer in replaced {
            self.concrete.remove(&pointer);
        }
        true
    }

    /// Adds a run. The caller makes every slot already holding a cell here a
    /// hole of the new run, so the cells it holds keep their values and the
    /// canonical form holds. A run with the same slots already here is live
    /// only at the new run's holes, so the two merge into one run live at
    /// both's live slots.
    pub(crate) fn add_run(&mut self, run: CellRun) {
        self.reset();
        let key = run.key();
        let merged = match self.runs.get(&key) {
            Some(held) => {
                let mut merged = held.clone();
                merged.holes = held.holes.intersection(&run.holes);
                merged
            }
            None => run,
        };
        self.set_run(&key, Some(merged));
    }
}

/// The entries of an ordered pointer collection that can be slots of `run`,
/// ascending, found by `range` over the few key intervals such slots occupy
/// on the run's line: the constant offsets from the first slot to the last
/// for a constant base, and otherwise the stem itself (when a slot's
/// constant cancels) and the stem plus each constant from the first slot's
/// to the last's. Visits only entries in those intervals.
fn run_slot_candidates_in<'a, I>(
    run: &CellRun,
    mut range: impl FnMut(Bound<Pointer>, Bound<Pointer>) -> I,
) -> impl Iterator<Item = &'a Pointer> + 'a
where
    I: Iterator<Item = &'a Pointer> + 'a,
{
    let (line, first, last) = run.slot_line_span();
    let at = |offset: PointerOffsetTerm| Pointer {
        block: line.block.clone(),
        offset,
    };
    let mut intervals = Vec::new();
    match &line.stem {
        None => {
            intervals.push(range(
                Bound::Included(at(PointerOffsetTerm::Constant(first))),
                Bound::Included(at(PointerOffsetTerm::Constant(last))),
            ));
        }
        Some(stem) => {
            if first <= 0 && 0 <= last {
                intervals.push(range(
                    Bound::Included(at(stem.clone())),
                    Bound::Included(at(stem.clone())),
                ));
            }
            let shifted = |shift: i64| {
                at(PointerOffsetTerm::Add(
                    Box::new(stem.clone()),
                    Box::new(PointerOffsetTerm::Constant(shift)),
                ))
            };
            intervals.push(range(
                Bound::Included(shifted(first)),
                Bound::Included(shifted(last)),
            ));
        }
    }
    intervals.into_iter().flatten()
}

/// Whether `map` leaves every live slot of `run` as it is, answered from the
/// run's spelling-shape representatives when
/// [`run_shape_representatives`] finds its slots uniform.
///
/// Every `map` [`CellStore::map_cells`] is given rewrites a cell's pointer
/// and value term by term (a substitution, or the canonical form of the
/// loads they mention), and a uniform run's slots differ only in the constant
/// shift of their pointers and in which element their value's load names:
/// each value is the load, from one memory, of its own slot's pointer. A
/// rewrite that leaves one slot of a spelling shape alone therefore finds
/// nothing to change in the base, the memory or a constant shift, which is
/// all any other slot of that shape mentions. `false` sends the caller slot by
/// slot, which is always right.
///
/// [`run_shape_representatives`]: crate::kernel::reasoning::memory_resolution::run_shape_representatives
fn run_unchanged_by_uniform_map(
    run: &CellRun,
    map: &mut impl FnMut(&Pointer, &CValue) -> (Pointer, CValue),
) -> bool {
    let Some(representatives) =
        crate::kernel::reasoning::memory_resolution::run_shape_representatives(run)
    else {
        return false;
    };
    crate::instrumentation::record_deterministic_work(representatives.len());
    let unchanged_at = |index: u32, map: &mut dyn FnMut(&Pointer, &CValue) -> (Pointer, CValue)| {
        let pointer = run.slot_pointer(index);
        let value = run.value(index);
        let (mapped_pointer, mapped_value) = map(&pointer, &value);
        mapped_pointer == pointer && mapped_value == value
    };
    if !representatives
        .iter()
        .all(|index| unchanged_at(*index, &mut *map))
    {
        return false;
    }
    #[cfg(debug_assertions)]
    if run.count() <= CHECKED_RUN_SLOTS {
        crate::instrumentation::uncharged_debug_check(|| {
            for index in run.live_indexes() {
                assert!(
                    unchanged_at(index, &mut *map),
                    "a map left a run's representatives alone but changed element {index} of {run:?}"
                );
            }
        });
    }
    true
}

impl FromIterator<(Pointer, CValue)> for CellStore {
    /// A store of exactly these cells and no run. A caller rebuilding a
    /// store cell by cell from another's logical map gets the same logical
    /// cells, all concrete.
    fn from_iter<I: IntoIterator<Item = (Pointer, CValue)>>(iter: I) -> Self {
        Self {
            concrete: iter.into_iter().collect(),
            ..Self::default()
        }
    }
}

impl std::fmt::Debug for CellStore {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.runs.is_empty() {
            return self.concrete.fmt(formatter);
        }
        formatter
            .debug_struct("CellStore")
            .field("concrete", &self.concrete)
            .field("runs", &self.runs.values().collect::<Vec<_>>())
            .finish()
    }
}

impl PartialEq for CellStore {
    fn eq(&self, other: &Self) -> bool {
        self.concrete == other.concrete && self.runs == other.runs
    }
}

impl Eq for CellStore {}

impl Hash for CellStore {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.concrete.hash(state);
        if !self.runs.is_empty() {
            self.runs.hash(state);
        }
    }
}

impl PartialOrd for CellStore {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CellStore {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.concrete
            .cmp(&other.concrete)
            .then_with(|| self.runs.cmp(&other.runs))
    }
}

impl<'a> IntoIterator for &'a CellStore {
    type Item = (&'a Pointer, &'a CValue);
    type IntoIter = imbl::ordmap::Iter<'a, Pointer, CValue, imbl::shared_ptr::DefaultSharedPtr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    //! The run index against a per-cell model, and its cost against the
    //! number of runs.

    use super::*;
    use crate::kernel::primitives::{CMemory, Variable};
    use std::collections::BTreeMap;

    fn source(tag: u32) -> SharedCMemory {
        crate::kernel::intern_c_memory(
            CMemory::new().with_block(format!("cell-store-source-{tag}").as_str(), 4),
        )
    }

    fn at(block: &PointerBlock, offset: PointerOffsetTerm) -> Pointer {
        Pointer {
            block: block.clone(),
            offset,
        }
    }

    fn constant(block: &PointerBlock, offset: i64) -> Pointer {
        at(block, PointerOffsetTerm::Constant(offset))
    }

    fn run(base: Pointer, element_width: u32, count: u32, source: &SharedCMemory) -> CellRun {
        let element_type = if element_width == 1 {
            CType::UInt8
        } else {
            CType::Int32
        };
        CellRun::new(
            base,
            element_width,
            element_type,
            count,
            source.clone(),
            IndexIntervals::default(),
        )
    }

    /// Seeds `run` as `CMemory::with_seeded_cells` does: every slot that
    /// already holds a cell is a hole of the new run. The model stores each
    /// seeded slot one by one.
    fn seed(store: &mut CellStore, model: &mut BTreeMap<Pointer, CValue>, mut run: CellRun) {
        for index in 0..run.count() {
            let pointer = run.slot_pointer(index);
            assert_eq!(store.contains_key(&pointer), model.contains_key(&pointer));
            match model.entry(pointer) {
                std::collections::btree_map::Entry::Occupied(_) => run.holes.insert(index),
                std::collections::btree_map::Entry::Vacant(slot) => {
                    slot.insert(run.value(index));
                }
            }
        }
        store.add_run(run);
    }

    fn logical_model(store: &CellStore) -> BTreeMap<Pointer, CValue> {
        store
            .logical()
            .iter()
            .map(|(pointer, value)| (pointer.clone(), value.clone()))
            .collect()
    }

    fn model_diff(
        left: &BTreeMap<Pointer, CValue>,
        right: &BTreeMap<Pointer, CValue>,
    ) -> Vec<Pointer> {
        left.keys()
            .chain(right.keys())
            .filter(|pointer| left.get(*pointer) != right.get(*pointer))
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// A deterministic stream of small numbers.
    struct Stream(u64);

    impl Stream {
        fn next(&mut self, bound: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 33) % bound
        }
    }

    /// Random seeds, stores, removals and retains over runs in one block at
    /// overlapping and adjacent ranges of both strides, in a block whose
    /// runs are anchored at symbolic offsets, and in a second block; after
    /// every step each store's cells, lookups, diffs against every earlier
    /// store, equality and relative equality agree with a per-cell model.
    /// A slot of a run based at `p + 16` is spelled as a load of its
    /// address is, `p + 20`, not `(p + 16) + 4`: the run answers for that
    /// load, a store there refills or displaces that slot, and a run based
    /// at `p - 4` has a slot at bare `p`.
    #[test]
    fn slots_are_spelled_as_loads_spell_their_addresses() {
        let block = PointerBlock::Symbolic(Variable(9_310_101));
        let stem = PointerOffsetTerm::Variable(Variable(9_310_102));
        let shifted = |shift: i64| {
            at(
                &block,
                PointerOffsetTerm::add(stem.clone(), PointerOffsetTerm::Constant(shift)),
            )
        };
        let seeded = run(shifted(16), 4, 3, &source(1));
        assert_eq!(seeded.slot_pointer(1), shifted(20));
        assert_eq!(seeded.slot_index(&shifted(20)), Some(1));
        assert_eq!(seeded.slot_index(&shifted(22)), None);
        let mut store = CellStore::new();
        store.add_run(seeded.clone());
        assert_eq!(store.get(&shifted(24)), Some(seeded.value(2)));
        assert_eq!(
            store.value_width_at(&shifted(24)),
            Some(seeded.value(2).byte_width())
        );
        assert_eq!(store.value_width_at(&shifted(28)), None);
        store.insert(shifted(20), CValue::Int32(Bitvector32Term::Constant(7)));
        assert_eq!(
            store.get(&shifted(20)),
            Some(CValue::Int32(Bitvector32Term::Constant(7)))
        );
        assert_eq!(store.len(), 3);
        let below = run(shifted(-4), 4, 3, &source(1));
        assert_eq!(below.slot_pointer(1), at(&block, stem.clone()));
        assert_eq!(below.slot_index(&at(&block, stem.clone())), Some(1));
    }

    // Exercise every mutation and lookup in the deterministic streams. Check
    // adjacent snapshots every step and all retained snapshots at doubling
    // checkpoints and the final step, rather than every historical pair.
    #[test]
    #[ignore = "nightly: model-based mutation and retained-history regression"]
    fn the_run_index_agrees_with_a_per_cell_model() {
        let global = PointerBlock::Concrete("cell-store-global".to_string());
        let other = PointerBlock::Concrete("cell-store-other".to_string());
        let symbolic = PointerBlock::Symbolic(Variable(9_310_001));
        let anchor = PointerOffsetTerm::Variable(Variable(9_310_002));
        let symbolic_bases = [
            anchor.clone(),
            PointerOffsetTerm::add(anchor.clone(), PointerOffsetTerm::Constant(8)),
            PointerOffsetTerm::add(anchor.clone(), PointerOffsetTerm::Constant(-8)),
        ];
        let sources = [source(1), source(2)];
        for seed_value in 1..=24u64 {
            let mut stream = Stream(seed_value);
            let mut store = CellStore::new();
            let mut model = BTreeMap::new();
            let mut history: Vec<(CellStore, BTreeMap<Pointer, CValue>)> = Vec::new();
            let mut pointers = Vec::new();
            for offset in 0..48 {
                pointers.push(constant(&global, offset));
            }
            for offset in (0..16).step_by(4) {
                pointers.push(constant(&other, offset));
            }
            // Every address on the anchor's line, spelled as a load spells
            // it: runs based at the anchor, eight bytes past it and eight
            // bytes before it share these slots, and a slot of the last can
            // be the bare anchor.
            pointers.push(at(&symbolic, anchor.clone()));
            for shift in (-8..32).filter(|shift| *shift != 0) {
                pointers.push(at(
                    &symbolic,
                    PointerOffsetTerm::add(anchor.clone(), PointerOffsetTerm::Constant(shift)),
                ));
            }
            let mut runs_seen = Vec::<CellRun>::new();
            for step in 0..60usize {
                match stream.next(10) {
                    0..=2 => {
                        let width = if stream.next(3) == 0 { 1 } else { 4 };
                        let count = 1 + stream.next(6) as u32;
                        let source = &sources[stream.next(2) as usize];
                        let base = match stream.next(4) {
                            0 | 1 => constant(&global, (stream.next(9) * 4) as i64),
                            2 => constant(&other, (stream.next(3) * 4) as i64),
                            _ => at(&symbolic, symbolic_bases[stream.next(3) as usize].clone()),
                        };
                        // A quarter of the runs spell their values as a
                        // symbolic static array's entry does, and a quarter
                        // hold one of two constants, as initialized static
                        // storage does: the same slots under another mode,
                        // or another constant, are another run.
                        let plain = run(base, width, count, source);
                        let with_mode = |mode: RunValueMode| {
                            CellRun::new_with_mode(
                                plain.base().clone(),
                                plain.element_width(),
                                plain.element_type(),
                                plain.count(),
                                plain.source().clone(),
                                mode,
                                IndexIntervals::default(),
                            )
                        };
                        let seeded = match stream.next(4) {
                            0 => with_mode(RunValueMode::SymbolicStorage),
                            1 => {
                                let constant = Bitvector32Term::Constant(stream.next(2) as u32);
                                with_mode(RunValueMode::Constant(if width == 1 {
                                    CValue::UInt8(constant)
                                } else {
                                    CValue::Int32(constant)
                                }))
                            }
                            _ => plain.clone(),
                        };
                        runs_seen.push(seeded.clone());
                        seed(&mut store, &mut model, seeded);
                    }
                    3..=5 => {
                        let pointer = pointers[stream.next(pointers.len() as u64) as usize].clone();
                        // Half the stores write back a value some run holds
                        // at that pointer, so holes are refilled.
                        let run_value = runs_seen
                            .iter()
                            .filter_map(|run| {
                                run.slot_index(&pointer).map(|index| run.value(index))
                            })
                            .next();
                        let value = match (stream.next(2), run_value) {
                            (0, Some(value)) => value,
                            _ => CValue::Int32(Bitvector32Term::Constant(stream.next(3) as u32)),
                        };
                        store.insert(pointer.clone(), value.clone());
                        model.insert(pointer, value);
                    }
                    6 | 7 => {
                        let pointer = pointers[stream.next(pointers.len() as u64) as usize].clone();
                        assert_eq!(store.remove(&pointer), model.remove(&pointer));
                    }
                    8 => {
                        let modulus = 2 + stream.next(3) as i64;
                        let keep = |pointer: &Pointer, _: &CValue| !matches!(pointer.offset, PointerOffsetTerm::Constant(offset) if offset % (4 * modulus) == 0);
                        store.retain(keep);
                        model.retain(|pointer, value| keep(pointer, value));
                    }
                    _ => {
                        let only = AliasCandidates::only_block(&global);
                        let keep = |pointer: &Pointer, _: &CValue| !matches!(pointer.offset, PointerOffsetTerm::Constant(offset) if offset % 8 == 4);
                        store.retain_candidates_outside_by(&only, &[], keep, |_| {
                            (SlotSet::PerSlot, RuleAnswer::Exact)
                        });
                        model.retain(|pointer, value| {
                            pointer.block != global || keep(pointer, value)
                        });
                    }
                }
                assert!(
                    store.logical().iter().eq(model.iter()),
                    "seed {seed_value}: logical cells differ from the per-cell model"
                );
                assert_eq!(store.len(), model.len());
                assert!(store.runs().all(|run| run.live_count() > 0));
                assert_eq!(
                    store.span_cover,
                    cover_of_runs(&store),
                    "seed {seed_value}: the cover is a function of the runs"
                );
                for pointer in &pointers {
                    assert_eq!(store.get(pointer), model.get(pointer).cloned());
                }
                // Check every transition, and the full retained history at
                // doubling checkpoints and at the final (deepest) state.
                // Keep every snapshot alive so copy-on-write sharing is unchanged.
                let compare_all = (step + 1).is_power_of_two() || step + 1 == 60;
                let comparisons = if compare_all {
                    &history[..]
                } else {
                    &history[history.len().saturating_sub(1)..]
                };
                for (earlier, earlier_model) in comparisons {
                    // The reference maps are immutable during this pair's checks.
                    // Their difference is symmetric; compute that oracle once.
                    let expected = model_diff(&model, earlier_model);
                    assert_eq!(
                        store.differing_pointers(earlier),
                        expected,
                        "seed {seed_value}"
                    );
                    if store == *earlier {
                        assert_eq!(&model, earlier_model, "equal stores hold one cell map");
                    }
                    if store.eq_relative_to(earlier, earlier) {
                        assert_eq!(&model, earlier_model);
                    }
                    let differing = earlier.differing_pointers(&store);
                    assert_eq!(differing, expected);
                    let removed = differing.iter().collect::<Vec<_>>();
                    assert_eq!(
                        store.is_without(earlier, &removed),
                        removed.iter().all(|pointer| !model.contains_key(*pointer)),
                    );
                }
                history.push((store.clone(), model.clone()));
            }
        }
    }

    /// A store's identity does not depend on the order its runs were added
    /// in: the same disjoint runs seeded in two orders give equal stores
    /// with equal hashes, and one more store into a slot makes both differ
    /// alike.
    #[test]
    fn runs_added_in_different_orders_make_one_store() {
        let global = PointerBlock::Concrete("cell-store-order".to_string());
        let sources = [source(3), source(4)];
        let runs = (0..12)
            .map(|index| {
                run(
                    constant(&global, 16 * index),
                    4,
                    2 + (index as u32 % 2),
                    &sources[index as usize % 2],
                )
            })
            .collect::<Vec<_>>();
        let build = |order: &mut dyn Iterator<Item = &CellRun>| {
            let mut store = CellStore::new();
            let mut model = BTreeMap::new();
            for run in order {
                seed(&mut store, &mut model, run.clone());
            }
            store
        };
        let forward = build(&mut runs.iter());
        let backward = build(&mut runs.iter().rev());
        let hash = |store: &CellStore| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            store.hash(&mut hasher);
            hasher.finish()
        };
        assert!(forward == backward);
        assert_eq!(hash(&forward), hash(&backward));
        assert_eq!(forward.cmp(&backward), std::cmp::Ordering::Equal);
        let mut forward_stored = forward.clone();
        let mut backward_stored = backward.clone();
        let written = constant(&global, 20);
        forward_stored.insert(written.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
        backward_stored.insert(written.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
        assert!(forward_stored == backward_stored);
        assert!(forward_stored != forward);
        assert_eq!(forward_stored.differing_pointers(&backward), vec![written]);
    }

    /// `same_cells_as` is equality of the logical maps and nothing weaker:
    /// it holds across the two representations of one set of cells, and
    /// fails for a cell with another value, a cell one store lacks, and a
    /// cell one store has extra.
    #[test]
    fn same_cells_as_compares_cells_and_not_their_representation() {
        let global = PointerBlock::Concrete("cell-store-same-cells".to_string());
        let seeded = run(constant(&global, 0), 4, 3, &source(6));
        let mut store = CellStore::new();
        let mut model = BTreeMap::new();
        seed(&mut store, &mut model, seeded.clone());
        let mut restored = store.clone();
        for index in 0..3 {
            restored.insert(
                seeded.slot_pointer(index),
                CValue::Int32(Bitvector32Term::Constant(index)),
            );
        }
        for index in 0..3 {
            restored.insert(seeded.slot_pointer(index), seeded.value(index));
        }
        // One set of cells, held as a run on one side and concretely on the
        // other: structurally different, the same cells.
        assert!(restored != store);
        assert!(restored.same_cells_as(&store));
        assert!(store.same_cells_as(&restored));

        let mut other_value = restored.clone();
        other_value.insert(
            seeded.slot_pointer(1),
            CValue::Int32(Bitvector32Term::Constant(41)),
        );
        assert!(!other_value.same_cells_as(&store));
        assert!(!store.same_cells_as(&other_value));

        let mut missing = restored.clone();
        missing.remove(&seeded.slot_pointer(2));
        assert!(!missing.same_cells_as(&store));
        assert!(!store.same_cells_as(&missing));

        let mut extra = restored.clone();
        extra.insert(
            constant(&global, 400),
            CValue::Int32(Bitvector32Term::Constant(0)),
        );
        assert!(!extra.same_cells_as(&store));
        assert!(!store.same_cells_as(&extra));
    }

    /// `CMemory::same_contents_as` looks through the cell cache's layout and
    /// through nothing else. A block that is read-only on one side, a block
    /// one side lacks, an ended automatic object, and a forget mark (a
    /// snapshot identity: the marked memory is not known to be the one it
    /// forgot from) each keep two memories with the same cells apart.
    #[test]
    fn same_contents_as_keeps_every_other_component_exact() {
        let block = "cell-store-same-contents";
        let global = PointerBlock::Concrete(block.to_string());
        let seeded = run(constant(&global, 0), 4, 2, &source(7));
        let mut cells = CellStore::new();
        let mut model = BTreeMap::new();
        seed(&mut cells, &mut model, seeded.clone());
        let mut concrete = cells.clone();
        // Writing every slot retires the run, so writing the run's values
        // back leaves them as concrete cells.
        for index in 0..2 {
            concrete.insert(
                seeded.slot_pointer(index),
                CValue::Int32(Bitvector32Term::Constant(9)),
            );
        }
        for index in 0..2 {
            concrete.insert(seeded.slot_pointer(index), seeded.value(index));
        }
        let with_cells = |cells: &CellStore| {
            let mut memory = CMemory::new().with_block(block, 8);
            memory.cells = std::sync::Arc::new(cells.clone());
            memory
        };
        let as_run = with_cells(&cells);
        let as_cells = with_cells(&concrete);
        assert!(as_run != as_cells);
        assert!(as_run.same_contents_as(&as_cells));
        assert!(as_cells.same_contents_as(&as_run));

        let mut read_only = CMemory::new().with_read_only_block(block, 8);
        read_only.cells = std::sync::Arc::new(concrete.clone());
        assert!(!as_run.same_contents_as(&read_only));

        let mut another_block = as_cells.clone().with_block("cell-store-same-contents-2", 4);
        another_block.cells = std::sync::Arc::new(concrete.clone());
        assert!(!as_run.same_contents_as(&another_block));

        let mut ended = as_cells.clone();
        std::sync::Arc::make_mut(&mut ended.forgotten)
            .ended_local_blocks
            .insert(PointerBlock::Concrete("local:lifetime:0:x".to_string()));
        assert!(!as_run.same_contents_as(&ended));

        let mut forgot = as_cells.clone();
        forgot.mark_forgotten_from(&source(8));
        assert!(!as_run.same_contents_as(&forgot));
        assert!(!forgot.same_contents_as(&as_run));
    }

    /// A run whose every slot is written is retired, and a store holding a
    /// retired run's cells concretely has the cells of one that holds them
    /// in the run: equal cell maps, and no difference between the two.
    #[test]
    fn a_run_whose_every_slot_is_written_is_retired() {
        let global = PointerBlock::Concrete("cell-store-retire".to_string());
        let seeded = run(constant(&global, 0), 4, 3, &source(5));
        let mut store = CellStore::new();
        let mut model = BTreeMap::new();
        seed(&mut store, &mut model, seeded.clone());
        let mut written = store.clone();
        for index in 0..3 {
            written.insert(
                seeded.slot_pointer(index),
                CValue::Int32(Bitvector32Term::Constant(index)),
            );
        }
        assert_eq!(written.run_count(), 0);
        assert_eq!(written.len(), 3);
        // Writing the run's own values back leaves concrete cells with the
        // run's values: the same cells as the seeded store, which the diff
        // sees even though one side holds them in a run and the other not.
        let mut restored = written.clone();
        for index in 0..3 {
            restored.insert(seeded.slot_pointer(index), seeded.value(index));
        }
        assert_eq!(logical_model(&restored), logical_model(&store));
        assert!(restored.differing_pointers(&store).is_empty());
        assert!(store.differing_pointers(&restored).is_empty());
        // A hole left by a removal keeps the run, whose other slots stay.
        let mut removed = store.clone();
        assert_eq!(
            removed.remove(&seeded.slot_pointer(1)),
            Some(seeded.value(1))
        );
        assert_eq!(removed.run_count(), 1);
        assert_eq!(
            removed.differing_pointers(&store),
            vec![seeded.slot_pointer(1)]
        );
    }

    /// Two runs of one block with other strides, both live at slots the
    /// other covers, and a store whose other run holds the same value at a
    /// slot: the index still finds each live slot's one run, and a slot
    /// held alike by different runs on the two sides is no difference.
    #[test]
    fn runs_covering_one_slot_differ_only_where_their_values_do() {
        let global = PointerBlock::Concrete("cell-store-cover".to_string());
        let source = source(6);
        let words = run(constant(&global, 0), 4, 4, &source);
        let bytes = run(constant(&global, 0), 1, 16, &source);
        // One store holds the word run whole; the other the byte run.
        let mut left = CellStore::new();
        let mut left_model = BTreeMap::new();
        seed(&mut left, &mut left_model, words.clone());
        let mut right = CellStore::new();
        let mut right_model = BTreeMap::new();
        seed(&mut right, &mut right_model, bytes.clone());
        // Each store also gets the other run over the slots its own run left.
        seed(&mut left, &mut left_model, bytes.clone());
        seed(&mut right, &mut right_model, words.clone());
        assert_eq!(logical_model(&left), left_model);
        assert_eq!(logical_model(&right), right_model);
        assert_eq!(
            left.differing_pointers(&right),
            model_diff(&left_model, &right_model)
        );
        // A store that spans both runs' slots.
        for pointer in [constant(&global, 4), constant(&global, 5)] {
            left.insert(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
            left_model.insert(pointer, CValue::Int32(Bitvector32Term::Constant(1)));
        }
        assert_eq!(logical_model(&left), left_model);
        assert_eq!(
            left.differing_pointers(&right),
            model_diff(&left_model, &right_model)
        );
    }

    /// The span cover built afresh from `store`'s runs alone.
    fn cover_of_runs(store: &CellStore) -> imbl::OrdMap<(CoverLine, i64), CoverSegment> {
        let mut fresh = CellStore::new();
        for run in store.runs() {
            fresh.set_run(&run.key(), Some(run.clone()));
        }
        fresh.span_cover
    }

    /// One run spanning a million slots beside 1 to 1000 small runs of the
    /// same block: a constant load of a small run's slot, or of a byte no
    /// run spans, visits only the runs whose span holds it. Before the
    /// cover, a constant pointer was looked up among every constant-based
    /// run of its block starting at most the largest held span below it,
    /// which the one long run made every small run beneath the probe.
    #[test]
    fn a_long_run_does_not_widen_constant_lookups() {
        let block = PointerBlock::Concrete("cell-store-long-run".to_string());
        let samples = [1usize, 10, 100, 1000].map(|small| {
            // Each size starts with cold version caches; otherwise the first
            // sample alone pays for the shared block-version prefix.
            let _session = crate::kernel::VerificationSession::enter();
            let source = source(11);
            // No two of these runs share a slot, so each is added whole.
            let mut store = CellStore::new();
            for index in 0..small {
                store.add_run(run(constant(&block, 8 * index as i64), 4, 1, &source));
            }
            store.add_run(run(
                constant(&block, 8 * small as i64),
                4,
                1_000_000,
                &source,
            ));
            let probe = constant(&block, 8 * (small / 2) as i64);
            let gap = constant(&block, 8 * (small / 2) as i64 + 4);
            let long_slot = constant(&block, 8 * small as i64 + 4 * 500_000);
            let visited = work(|| {
                for _ in 0..16 {
                    assert!(store.get(&probe).is_some());
                    assert!(store.get(&gap).is_none());
                    assert!(store.get(&long_slot).is_some());
                }
            });
            (small, visited)
        });
        let (_, visited) = samples[0];
        // Each round visits at most the probe's run and the long run, a few
        // times each.
        assert!(visited <= 16 * 5, "{samples:?}");
        assert!(
            samples.iter().all(|(_, sample)| *sample == visited),
            "constant lookups grow with the small runs: {samples:?}"
        );
    }

    /// How much deterministic work `operation` charges, plus how many runs
    /// its pointer lookups visit.
    fn work(operation: impl FnOnce()) -> usize {
        let before = RUNS_VISITED.with(std::cell::Cell::get);
        let work = crate::instrumentation::measure_deterministic_work(operation).1;
        work + RUNS_VISITED.with(std::cell::Cell::get) - before
    }

    /// A store of `runs` one-slot runs laid out by `layout`, each in canonical
    /// form, and the pointers of its slots.
    fn many_runs(runs: usize, layout: &dyn Fn(usize) -> Pointer) -> (CellStore, Vec<Pointer>) {
        let source = source(7);
        let mut store = CellStore::new();
        let mut model = BTreeMap::new();
        let mut pointers = Vec::new();
        for index in 0..runs {
            let base = layout(index);
            pointers.push(base.clone());
            seed(&mut store, &mut model, run(base, 4, 1, &source));
        }
        (store, pointers)
    }

    /// Loads, stores, diffs and comparisons against a store of 1 to 1000
    /// small runs cost work that does not grow with the number of runs, in
    /// one block at adjacent constant offsets, one block per run, and one
    /// block with every run at its own symbolic anchor. Before the index a
    /// load and a store scanned every run, and two stores whose runs did not
    /// pair up were compared by laying out both logical maps.
    #[test]
    fn run_operations_cost_the_same_whatever_the_number_of_runs() {
        let one_block = PointerBlock::Concrete("cell-store-scaling".to_string());
        let symbolic = PointerBlock::Symbolic(Variable(9_320_000));
        let layouts: [(&str, Box<dyn Fn(usize) -> Pointer>); 3] = [
            (
                "adjacent constant ranges of one block",
                Box::new(|index| constant(&one_block, 4 * index as i64)),
            ),
            (
                "one block per run",
                Box::new(|index| {
                    constant(
                        &PointerBlock::Symbolic(Variable(9_330_000 + index as u64)),
                        0,
                    )
                }),
            ),
            (
                "symbolic anchors of one block",
                Box::new(|index| {
                    at(
                        &symbolic,
                        PointerOffsetTerm::Variable(Variable(9_340_000 + index as u64)),
                    )
                }),
            ),
        ];
        for (name, layout) in &layouts {
            let samples = [1usize, 10, 100, 1000].map(|runs| {
                let (store, pointers) = many_runs(runs, layout.as_ref());
                let probe = pointers[runs / 2].clone();
                let value = CValue::Int32(Bitvector32Term::Constant(3));
                // Loads of a run slot and of a pointer no run holds.
                let loads = work(|| {
                    for _ in 0..16 {
                        assert!(store.get(&probe).is_some());
                        assert!(store.get(&constant(&one_block, -8)).is_none());
                    }
                });
                // A store into a slot, and the diff and comparisons of the
                // store before and after it, both ways.
                let mut stored = store.clone();
                let stores = work(|| stored.insert(probe.clone(), value.clone()));
                let diffs = work(|| {
                    assert_eq!(stored.differing_pointers(&store), vec![probe.clone()]);
                    assert_eq!(store.differing_pointers(&stored), vec![probe.clone()]);
                });
                let compares = work(|| {
                    assert!(stored != store);
                    assert!(!stored.eq_relative_to(&store, &store));
                    assert_eq!(stored.observable_runs_match(&store, |_| true), None);
                    assert!(!stored.is_without(&store, &[]));
                });
                // Two stores whose runs do not pair up: removing the probe's
                // cell retires its one-slot run.
                let mut reseeded = store.clone();
                reseeded.remove(&probe);
                let unpaired = work(|| {
                    assert_eq!(reseeded.differing_pointers(&store), vec![probe.clone()]);
                });
                (runs, loads, stores, diffs, compares, unpaired)
            });
            let (_, loads, stores, diffs, compares, unpaired) = samples[0];
            // Each of the 16 slot loads visits the one run holding the slot;
            // the load no run holds visits none.
            assert_eq!(loads, 16, "{name}: {samples:?}");
            for (
                runs,
                sample_loads,
                sample_stores,
                sample_diffs,
                sample_compares,
                sample_unpaired,
            ) in samples
            {
                // Flat: every sample costs what one run costs. Positioning in
                // the persistent maps is logarithmic and charges nothing.
                assert!(
                    sample_loads <= loads
                        && sample_stores <= stores + 2
                        && sample_diffs <= diffs + 4
                        && sample_compares <= compares + 4
                        && sample_unpaired <= unpaired + 4,
                    "{name}: work grows with {runs} runs: {samples:?}"
                );
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/cell_store/tests.rs");
    }
}
