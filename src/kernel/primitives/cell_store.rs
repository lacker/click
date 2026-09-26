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
//! **Canonical form.** For each run, a slot is either *live* — it holds the
//! run's value and the concrete map has no entry at its pointer — or a
//! *hole*, whose pointer the concrete map may or may not hold, and never with
//! the run's own value. A store of the run's value into a hole refills the
//! slot rather than caching a concrete copy, and holes are kept as disjoint,
//! non-adjacent intervals. Runs are never removed or split, so every snapshot
//! derived from one seeded state carries the same runs, and two snapshots
//! with one logical cell map have one representation. Equality, hashing and
//! ordering therefore read the representation, in O(1) for the runs.

use super::{
    AliasCandidates, CType, CValue, Pointer, PointerOffsetTerm, SharedCMemory, SnapshotMap,
    SnapshotMapChange, SnapshotSet,
};
use crate::kernel::primitives::Bitvector32Term;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

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
        let mut gaps = Vec::new();
        let mut next = 0;
        for (low, high) in self.intervals.iter() {
            if next < *low {
                gaps.push((next, (*low).min(count)));
            }
            next = next.max(*high);
        }
        if next < count {
            gaps.push((next, count));
        }
        gaps.retain(|(low, high)| low < high);
        gaps
    }
}

/// `count` seeded cells at `base`, `base + width`, …: the cell at element `i`
/// holds the load of that element in `source`, typed as `element_type`,
/// exactly as a store of [`cell_run_value`] would have left it.
#[derive(Clone)]
pub struct CellRun {
    base: Pointer,
    element_width: u32,
    element_type: CType,
    count: u32,
    source: SharedCMemory,
    holes: IndexIntervals,
    /// Every slot, holes included, materialized on first need. A function
    /// of the fields above, so it is excluded from equality and hashing and
    /// shared by every copy of the run.
    slots: Arc<OnceLock<SnapshotMap<Pointer, CValue>>>,
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
        Self {
            base,
            element_width,
            element_type,
            count,
            source,
            holes,
            slots: Arc::new(OnceLock::new()),
        }
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

    /// The pointer of element `index`, spelled exactly as contract seeding
    /// spells it: the base's offset plus a constant byte shift, folded when
    /// either side is a constant and elided when the shift is zero.
    pub(crate) fn slot_pointer(&self, index: u32) -> Pointer {
        let shift = i64::from(index) * i64::from(self.element_width);
        let offset = match (&self.base.offset, shift) {
            (_, 0) => self.base.offset.clone(),
            (PointerOffsetTerm::Constant(base), shift) => PointerOffsetTerm::Constant(base + shift),
            (base, shift) => PointerOffsetTerm::Add(
                Box::new(base.clone()),
                Box::new(PointerOffsetTerm::Constant(shift)),
            ),
        };
        Pointer {
            block: self.base.block.clone(),
            offset,
        }
    }

    /// The element whose slot is spelled exactly `pointer`, hole or not.
    pub(crate) fn slot_index(&self, pointer: &Pointer) -> Option<u32> {
        if pointer.block != self.base.block {
            return None;
        }
        let width = i64::from(self.element_width);
        let shift = match (&self.base.offset, &pointer.offset) {
            (PointerOffsetTerm::Constant(base), PointerOffsetTerm::Constant(offset)) => {
                offset - base
            }
            (base, offset) if base == offset => 0,
            (base, PointerOffsetTerm::Add(left, right)) if left.as_ref() == base => {
                match right.as_ref() {
                    PointerOffsetTerm::Constant(shift) if *shift != 0 => *shift,
                    _ => return None,
                }
            }
            _ => return None,
        };
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

    /// The value every live slot `index` holds.
    pub(crate) fn value(&self, index: u32) -> CValue {
        let pointer = self.slot_pointer(index);
        let load = crate::kernel::canonical_form_of_load(self.source.clone(), pointer.clone());
        cell_run_value(&pointer, self.element_type, load)
    }

    pub(crate) fn live_count(&self) -> u64 {
        u64::from(self.count) - self.holes.count().min(u64::from(self.count))
    }

    /// Every slot, holes included, in ascending pointer order.
    fn all_slots(&self) -> &SnapshotMap<Pointer, CValue> {
        self.slots.get_or_init(|| {
            crate::instrumentation::record_deterministic_work(self.count as usize);
            (0..self.count)
                .map(|index| (self.slot_pointer(index), self.value(index)))
                .collect()
        })
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
            .gaps(self.count)
            .into_iter()
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
    }

    fn descriptor(&self) -> (&Pointer, u32, CType, u32, &SharedCMemory, &IndexIntervals) {
        (
            &self.base,
            self.element_width,
            self.element_type,
            self.count,
            &self.source,
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
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.descriptor().cmp(&other.descriptor())
    }
}

/// The value a seeded cell of type `element_type` at `pointer` holds when its
/// load is `load`: the load itself for a scalar, the load's truth for a
/// `bool`, a pointer into the cell's own block scaled by the pointee for an
/// object pointer, and the load's function identity for a function pointer.
pub(crate) fn cell_run_value(
    pointer: &Pointer,
    element_type: CType,
    load: Bitvector32Term,
) -> CValue {
    match element_type {
        CType::Bool => CValue::Bool(Bitvector32Term::if_then_else(
            super::ConditionTerm::Bitvector32Equal(
                Box::new(load),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        CType::Int8 => CValue::Int8(load),
        CType::Int16 => CValue::Int16(load),
        CType::Int32 => CValue::Int32(load),
        CType::UInt8 => CValue::UInt8(load),
        CType::UInt16 => CValue::UInt16(load),
        CType::UInt32 => CValue::UInt32(load),
        CType::Int64 => CValue::Int64(load),
        CType::UInt64 => CValue::UInt64(load),
        CType::Float32 => CValue::Float32(load),
        CType::Float64 => CValue::Float64(load),
        CType::FunctionPointer(_) => {
            let variable = match &load {
                Bitvector32Term::Variable(variable)
                    if crate::kernel::is_load_variable(variable) =>
                {
                    *variable
                }
                Bitvector32Term::MemoryLoad(_, _) => crate::kernel::load_variable_for_term(&load)
                    .map(|(variable, _)| variable)
                    .expect("exact function-pointer loads have canonical identities"),
                _ => unreachable!(
                    "symbolic function-pointer fields use raw or canonical exact loads"
                ),
            };
            CValue::typed_pointer(Pointer::symbolic_function(variable), element_type)
        }
        c_type if c_type.is_pointer() => CValue::typed_pointer(
            Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::scale_int32(
                    load,
                    i64::from(
                        c_type
                            .pointee_type()
                            .expect("pointer element type has a pointee")
                            .byte_width(),
                    ),
                ),
            },
            c_type,
        ),
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
    /// Every live slot outside elements `low..high`; the rule of each live
    /// slot inside them is asked.
    AskWithin(u32, u32),
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
    Sound,
}

/// The largest run debug builds check a whole-run answer against, slot by
/// slot. A check, not a behavior: release builds and larger runs use the
/// whole-run answer alone.
#[cfg(debug_assertions)]
pub const CHECKED_RUN_SLOTS: u32 = 64;

impl SlotSet {
    fn holds(&self, index: u32) -> Option<bool> {
        match self {
            Self::All => Some(true),
            Self::Nothing => Some(false),
            Self::Elements(low, high) => Some(*low <= index && index < *high),
            Self::Except(low, high) => Some(!(*low <= index && index < *high)),
            Self::AskWithin(low, high) => (!(*low <= index && index < *high)).then_some(true),
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
            Self::All | Self::AskWithin(..) | Self::PerSlot => {
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
            SlotSet::AskWithin(low, high) => {
                let high = high.min(self.count);
                let dropped = (low..high.max(low))
                    .filter(|index| !self.holes.contains(*index))
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

/// A snapshot's cells: the concrete map and the seeded runs, in canonical
/// form (see the module comment).
#[derive(Clone, Default)]
pub(crate) struct CellStore {
    concrete: SnapshotMap<Pointer, CValue>,
    runs: Arc<Vec<CellRun>>,
    /// The logical cell map, built on first need when there are runs. Reset
    /// by every mutation; a function of the two fields above.
    logical: OnceLock<SnapshotMap<Pointer, CValue>>,
}

impl CellStore {
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// The concrete cells alone, without any run: what a caller that only
    /// ever asks about cells outside every run may read directly.
    pub(crate) fn concrete(&self) -> &SnapshotMap<Pointer, CValue> {
        &self.concrete
    }

    pub(crate) fn runs(&self) -> &[CellRun] {
        &self.runs
    }

    /// The whole cell map, exactly as per-cell seeding would have stored it.
    /// O(1) without runs; with runs it is built once per mutated store, at a
    /// cost of the concrete cells and holes plus each run after the first.
    pub(crate) fn logical(&self) -> &SnapshotMap<Pointer, CValue> {
        if self.runs.is_empty() {
            return &self.concrete;
        }
        self.logical.get_or_init(|| {
            let mut runs = self.runs.iter();
            let first = runs.next().expect("nonempty runs");
            let mut map = first.all_slots().clone();
            for (low, high) in first.holes.intervals.iter() {
                for index in *low..*high {
                    map.remove(&first.slot_pointer(index));
                }
            }
            for run in runs {
                for index in run.live_indexes() {
                    map.insert(run.slot_pointer(index), run.value(index));
                }
            }
            for (pointer, value) in self.concrete.iter() {
                map.insert(pointer.clone(), value.clone());
            }
            map
        })
    }

    fn reset(&mut self) {
        self.logical = OnceLock::new();
    }

    /// The run holding a live slot at `pointer`, and the slot's element.
    fn live_run_slot(&self, pointer: &Pointer) -> Option<(usize, u32)> {
        self.runs
            .iter()
            .enumerate()
            .find_map(|(position, run)| run.live_slot_index(pointer).map(|index| (position, index)))
    }

    /// The cell at `pointer`, read from a run slot without building the
    /// logical map.
    pub(crate) fn get(&self, pointer: &Pointer) -> Option<CValue> {
        if let Some(value) = self.concrete.get(pointer) {
            return Some(value.clone());
        }
        self.live_run_slot(pointer)
            .map(|(position, index)| self.runs[position].value(index))
    }

    pub(crate) fn contains_key(&self, pointer: &Pointer) -> bool {
        self.concrete.contains_key(pointer) || self.live_run_slot(pointer).is_some()
    }

    /// Whether the live run slots `observable` accepts are the same cells in
    /// both stores, answered from the runs alone: `Some(true)` when they are,
    /// so the observable cells agree exactly when the concrete ones do, and
    /// `Some(false)` when they cannot agree. `None` when the runs do not pair
    /// up and only the logical maps can tell.
    ///
    /// Runs with no live slot hold no cell and are passed over. The rest pair
    /// up in order when each pair is one run with possibly other holes. A slot
    /// live on one side and a hole on the other then makes the logical maps
    /// differ there: the hole holds either no cell or a concrete one, and the
    /// canonical form keeps a concrete cell at a hole only when it holds
    /// something other than the run's value.
    pub(crate) fn observable_runs_match(
        &self,
        other: &Self,
        mut observable: impl FnMut(&CellRun) -> bool,
    ) -> Option<bool> {
        if Arc::ptr_eq(&self.runs, &other.runs) {
            return Some(true);
        }
        let left = self
            .runs
            .iter()
            .filter(|run| run.live_count() > 0 && observable(run))
            .collect::<Vec<_>>();
        let right = other
            .runs
            .iter()
            .filter(|run| run.live_count() > 0 && observable(run))
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(left.len() + right.len());
        if left.len() != right.len()
            || left
                .iter()
                .zip(&right)
                .any(|(left, right)| !left.same_slots_as(right))
        {
            return None;
        }
        Some(
            left.iter()
                .zip(&right)
                .all(|(left, right)| left.holes == right.holes),
        )
    }

    /// The logical cells `candidates` admits, ascending, as
    /// `candidates.entries(self.logical())` yields them, without laying out
    /// a run: each admitted run's live slots are spelled and valued only as
    /// the walk reaches them. The concrete candidates and each run's slots
    /// are ascending, so a merge of them is the logical walk. A caller that
    /// stops early pays only for what it visited.
    pub(crate) fn candidate_logical_entries<'a>(
        &'a self,
        candidates: &'a AliasCandidates,
    ) -> impl Iterator<Item = (Pointer, CValue)> + 'a {
        type Sequence<'a> = Box<dyn Iterator<Item = (Pointer, CValue)> + 'a>;
        let mut sequences: Vec<Sequence<'a>> = vec![Box::new(
            candidates
                .entries(&self.concrete)
                .map(|(pointer, value)| (pointer.clone(), value.clone())),
        )];
        for run in self.runs.iter() {
            if run.live_count() == 0 || !candidates.admits_block(&run.base.block) {
                continue;
            }
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
        let mut heads = sequences
            .iter_mut()
            .map(|sequence| sequence.next())
            .collect::<Vec<_>>();
        std::iter::from_fn(move || {
            let least = heads
                .iter()
                .enumerate()
                .filter_map(|(position, head)| {
                    head.as_ref().map(|(pointer, _)| (position, pointer))
                })
                .min_by(|(_, left), (_, right)| left.cmp(right))
                .map(|(position, _)| position)?;
            let next = sequences[least].next();
            std::mem::replace(&mut heads[least], next)
        })
    }

    /// How many entries represent the cells: each concrete cell and each
    /// run, whatever its length. The measure of work that visits the
    /// representation rather than every logical cell.
    pub(crate) fn representation_len(&self) -> usize {
        self.concrete.len() + self.runs.len()
    }

    pub(crate) fn len(&self) -> usize {
        self.concrete.len()
            + self
                .runs
                .iter()
                .map(|run| run.live_count() as usize)
                .sum::<usize>()
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

    /// The pointers at which the two stores' logical maps differ, ascending,
    /// without laying out a run whose slots the other store's run shares.
    ///
    /// Runs pair up when each run with a live slot on either side has one on
    /// the other with the same slots ([`CellRun::same_slots_as`]). Then a slot
    /// live on both sides holds the same value on both, with no concrete cell
    /// beside it, and a slot live on one side only differs: the other side
    /// holds either nothing there or a concrete cell, which the canonical form
    /// keeps only when it holds something other than the run's value. Every
    /// other difference is a concrete one. Runs that do not pair up compare
    /// the logical maps.
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

    /// [`Self::differing_pointers`] with each run's differing slots left as
    /// intervals, for a caller that can pass over slots it proves irrelevant
    /// without spelling their pointers.
    pub(crate) fn differing_cells(&self, other: &Self) -> DifferingCells {
        if Arc::ptr_eq(&self.runs, &other.runs) || self.runs == other.runs {
            return DifferingCells {
                pointers: self
                    .concrete
                    .diff(&other.concrete)
                    .map(|change| change.key().clone())
                    .collect(),
                run_slots: Vec::new(),
            };
        }
        let logical = || DifferingCells {
            pointers: self.logical_differing_pointers(other),
            run_slots: Vec::new(),
        };
        let live = |store: &Self| {
            store
                .runs
                .iter()
                .filter(|run| run.live_count() > 0)
                .cloned()
                .collect::<Vec<_>>()
        };
        let left = live(self);
        let right = live(other);
        crate::instrumentation::record_deterministic_work(left.len() + right.len());
        let partner = |run: &CellRun, store: &Self| {
            store
                .runs
                .iter()
                .find(|candidate| candidate.same_slots_as(run))
                .cloned()
        };
        // A run with no partner is still read whole when the other store has
        // no run with a live slot over its block: each of its live slots then
        // differs unless the other store holds that very value concretely.
        let alone = |run: &CellRun, among: &[CellRun]| {
            among
                .iter()
                .all(|candidate| candidate.base.block != run.base.block)
        };
        let mut pairs: Vec<(CellRun, CellRun)> = Vec::new();
        let mut unpaired = Vec::new();
        for run in &left {
            match partner(run, other) {
                Some(other_run) => pairs.push((run.clone(), other_run)),
                None if alone(run, &right) => unpaired.push((run.clone(), other)),
                None => return logical(),
            }
        }
        for run in &right {
            if pairs.iter().any(|(_, paired)| paired.same_slots_as(run)) {
                continue;
            }
            match partner(run, self) {
                Some(other_run) => pairs.push((other_run, run.clone())),
                None if alone(run, &left) => unpaired.push((run.clone(), self)),
                None => return logical(),
            }
        }
        let mut pointers = self
            .concrete
            .diff(&other.concrete)
            .map(|change| change.key().clone())
            .collect::<Vec<_>>();
        let mut run_slots = Vec::new();
        for (run, other_store) in unpaired {
            // The other store's concrete cells at this run's live slots that
            // hold the run's value are the only slots that agree.
            let mut differing = IndexIntervals::default();
            for (low, high) in run.holes.gaps(run.count) {
                differing.insert_range(low, high);
            }
            let agreeing = other_store
                .concrete
                .iter()
                .filter_map(|(pointer, value)| {
                    crate::instrumentation::record_deterministic_work(1);
                    run.live_slot_index(pointer)
                        .filter(|index| run.value(*index) == *value)
                })
                .collect::<Vec<_>>();
            for index in agreeing {
                differing.remove(index);
            }
            run_slots.push((run, differing));
        }
        for (left_run, right_run) in pairs {
            let mut differing = left_run.holes.difference(&right_run.holes);
            for (low, high) in right_run.holes.difference(&left_run.holes).intervals() {
                differing.insert_range(low, high);
            }
            if differing.count() > 0 {
                run_slots.push((left_run, differing));
            }
        }
        pointers.sort();
        pointers.dedup();
        DifferingCells {
            pointers,
            run_slots,
        }
    }

    fn logical_differing_pointers(&self, other: &Self) -> Vec<Pointer> {
        self.logical()
            .diff(other.logical())
            .map(|change| change.key().clone())
            .collect()
    }

    /// See [`SnapshotMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.runs == other.runs
            && self
                .concrete
                .eq_relative_to(&other.concrete, &base.concrete)
    }

    /// See [`SnapshotMap::is_without`], over the logical maps.
    pub(crate) fn is_without(&self, before: &Self, removed: &[&Pointer]) -> bool {
        if self.runs.is_empty() && before.runs.is_empty() {
            return self.concrete.is_without(&before.concrete, removed);
        }
        self.logical().is_without(before.logical(), removed)
    }

    /// Stores `value` at `pointer`, in canonical form.
    pub(crate) fn insert(&mut self, pointer: Pointer, value: CValue) {
        self.reset();
        if self.runs.is_empty() {
            self.concrete.insert(pointer, value);
            return;
        }
        if let Some((position, index)) = self.live_run_slot(&pointer) {
            if self.runs[position].value(index) == value {
                return;
            }
            Arc::make_mut(&mut self.runs)[position].holes.insert(index);
            self.concrete.insert(pointer, value);
            return;
        }
        let refilled = self.runs.iter().position(|run| {
            run.slot_index(&pointer)
                .is_some_and(|index| run.value(index) == value)
        });
        if let Some(position) = refilled {
            let index = self.runs[position]
                .slot_index(&pointer)
                .expect("the refilled run holds the slot");
            Arc::make_mut(&mut self.runs)[position].holes.remove(index);
            self.concrete.remove(&pointer);
            return;
        }
        self.concrete.insert(pointer, value);
    }

    /// Removes the cell at `pointer`, returning what it held.
    pub(crate) fn remove(&mut self, pointer: &Pointer) -> Option<CValue> {
        self.reset();
        if let Some((position, index)) = self.live_run_slot(pointer) {
            let value = self.runs[position].value(index);
            Arc::make_mut(&mut self.runs)[position].holes.insert(index);
            return Some(value);
        }
        self.concrete.remove(pointer)
    }

    /// Keeps only the cells `keep` accepts, visiting every cell.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&Pointer, &CValue) -> bool) {
        self.reset();
        self.concrete.retain(&mut keep);
        self.retain_run_slots(|_| true, keep);
    }

    /// [`Self::retain`] with a whole-run answer from `run_rule`, as for
    /// [`Self::retain_only_candidates_by`].
    pub(crate) fn retain_by(
        &mut self,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) {
        self.reset();
        self.concrete.retain(&mut keep);
        self.retain_runs_by(|_| true, keep, &mut run_rule);
    }

    /// [`Self::retain_candidates`] with a whole-run answer from `run_rule`,
    /// as for [`Self::retain_only_candidates_by`].
    pub(crate) fn retain_candidates_by(
        &mut self,
        candidates: &AliasCandidates,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        mut run_rule: impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) {
        self.reset();
        candidates.retain_map(&mut self.concrete, &mut keep);
        self.retain_runs_by(
            |run| candidates.admits_block(&run.base.block),
            keep,
            &mut run_rule,
        );
    }

    fn retain_runs_by(
        &mut self,
        mut visits: impl FnMut(&CellRun) -> bool,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
        run_rule: &mut impl FnMut(&CellRun) -> (SlotSet, RuleAnswer),
    ) {
        if self.runs.is_empty() {
            return;
        }
        let mut visited = 0usize;
        let runs = Arc::make_mut(&mut self.runs);
        for run in runs.iter_mut() {
            if !visits(run) {
                continue;
            }
            visited += 1;
            let (decision, answer) = run_rule(run);
            #[cfg(debug_assertions)]
            if answer == RuleAnswer::Exact {
                crate::instrumentation::uncharged_debug_check(|| {
                    decision.check_against(run, &mut keep);
                });
            }
            let _ = answer;
            run.keep_only(decision, &mut keep, &mut visited);
        }
        crate::instrumentation::record_deterministic_work(visited);
    }

    /// Keeps only the cells `keep` accepts among the candidates; every other
    /// cell is kept. See [`AliasCandidates::retain_map`].
    pub(crate) fn retain_candidates(
        &mut self,
        candidates: &AliasCandidates,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
    ) {
        self.reset();
        candidates.retain_map(&mut self.concrete, &mut keep);
        self.retain_run_slots(|run| candidates.admits_block(&run.base.block), keep);
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
        let runs = Arc::make_mut(&mut self.runs);
        for run in runs.iter_mut() {
            if !candidates.admits_block(&run.base.block) {
                run.holes.insert_range(0, run.count);
                continue;
            }
            visited += 1;
            let (decision, answer) = run_rule(run);
            #[cfg(debug_assertions)]
            if answer == RuleAnswer::Exact {
                crate::instrumentation::uncharged_debug_check(|| {
                    decision.check_against(run, &mut keep);
                });
            }
            let _ = answer;
            run.keep_only(decision, &mut keep, &mut visited);
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
        for run in self.runs.iter() {
            if !candidates.admits_block(&run.base.block) {
                continue;
            }
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

    fn retain_run_slots(
        &mut self,
        mut visits: impl FnMut(&CellRun) -> bool,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
    ) {
        if self.runs.is_empty() {
            return;
        }
        let mut visited = 0usize;
        let runs = Arc::make_mut(&mut self.runs);
        for run in runs.iter_mut() {
            if !visits(run) {
                continue;
            }
            let dropped = run
                .live_indexes()
                .filter(|index| {
                    visited += 1;
                    let pointer = run.slot_pointer(*index);
                    let value = run.value(*index);
                    !keep(&pointer, &value)
                })
                .collect::<Vec<_>>();
            for index in dropped {
                run.holes.insert(index);
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
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
        let mut result = Self {
            concrete: SnapshotMap::new(),
            runs: Arc::new(Vec::new()),
            logical: OnceLock::new(),
        };
        let mut rewritten = Vec::new();
        for run in self.runs.iter() {
            // The singled-out slot is set aside before the rest is asked as a
            // whole: its change is the one the representatives cannot see.
            match singled_out(run).filter(|index| !run.holes.contains(*index)) {
                Some(index) => {
                    let mut rest = run.clone();
                    rest.holes.insert(index);
                    if run_unchanged_by_uniform_map(&rest, &mut map) {
                        rewritten.push(map(&run.slot_pointer(index), &run.value(index)));
                        Arc::make_mut(&mut result.runs).push(rest);
                        continue;
                    }
                }
                None => {
                    if run_unchanged_by_uniform_map(run, &mut map) {
                        Arc::make_mut(&mut result.runs).push(run.clone());
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
                Arc::make_mut(&mut result.runs).push(run.clone());
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
    /// replaced the same way. Any other run over the block with a live slot
    /// could hold one of these slots itself, which only slot by slot can
    /// sort out.
    pub(crate) fn install_run(&mut self, run: &CellRun) -> bool {
        crate::instrumentation::record_deterministic_work(self.runs.len() + 1);
        let same = self.runs.iter().position(|held| held.same_slots_as(run));
        let other_live = self.runs.iter().enumerate().any(|(position, held)| {
            Some(position) != same && held.base.block == run.base.block && held.live_count() > 0
        });
        if other_live {
            return false;
        }
        self.reset();
        let all_slots = {
            let mut all = IndexIntervals::default();
            all.insert_range(0, run.count);
            all
        };
        let revived = match same {
            Some(position) => {
                let held = &self.runs[position];
                let revived = held.holes.difference(&run.holes);
                let holes = held.holes.intersection(&run.holes);
                Arc::make_mut(&mut self.runs)[position].holes = holes;
                revived
            }
            None => {
                Arc::make_mut(&mut self.runs).push(run.clone());
                all_slots.difference(&run.holes)
            }
        };
        let revived_count = revived.count();
        crate::instrumentation::record_deterministic_work(
            revived.intervals.len()
                + usize::try_from(revived_count.min(self.concrete.len() as u64))
                    .unwrap_or(usize::MAX),
        );
        if revived_count <= self.concrete.len() as u64 {
            for index in revived.indexes() {
                self.concrete.remove(&run.slot_pointer(index));
            }
        } else {
            self.concrete.retain(|pointer, _| {
                run.slot_index(pointer)
                    .is_none_or(|index| !revived.contains(index))
            });
        }
        true
    }

    /// Adds a run. The caller makes every slot already holding a cell here a
    /// hole of the new run, so the cells it holds keep their values and the
    /// canonical form holds.
    pub(crate) fn add_run(&mut self, run: CellRun) {
        self.reset();
        Arc::make_mut(&mut self.runs).push(run);
    }

    /// This store's runs over another concrete map, for a caller rebuilding
    /// the concrete cells while the runs stay as they are.
    #[allow(dead_code)]
    pub(crate) fn with_concrete(&self, concrete: SnapshotMap<Pointer, CValue>) -> Self {
        Self {
            concrete,
            runs: self.runs.clone(),
            logical: OnceLock::new(),
        }
    }
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
            runs: Arc::new(Vec::new()),
            logical: OnceLock::new(),
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
            .field("runs", &self.runs)
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
