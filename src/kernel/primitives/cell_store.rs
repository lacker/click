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

    /// The live slots, ascending in element order.
    pub(crate) fn live_indexes(&self) -> impl Iterator<Item = u32> + '_ {
        self.holes
            .gaps(self.count)
            .into_iter()
            .flat_map(|(low, high)| low..high)
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

    pub(crate) fn get(&self, pointer: &Pointer) -> Option<&CValue> {
        if self.runs.is_empty() {
            return self.concrete.get(pointer);
        }
        self.logical().get(pointer)
    }

    pub(crate) fn contains_key(&self, pointer: &Pointer) -> bool {
        self.concrete.contains_key(pointer) || self.live_run_slot(pointer).is_some()
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

    pub(crate) fn values(
        &self,
    ) -> imbl::ordmap::Values<'_, Pointer, CValue, imbl::shared_ptr::DefaultSharedPtr> {
        self.logical().values()
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
    /// candidates.
    pub(crate) fn retain_only_candidates(
        &mut self,
        candidates: &AliasCandidates,
        mut keep: impl FnMut(&Pointer, &CValue) -> bool,
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
        visited
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
    pub(crate) fn map_cells(
        &self,
        mut map: impl FnMut(&Pointer, &CValue) -> (Pointer, CValue),
    ) -> Self {
        let mut result = Self {
            concrete: SnapshotMap::new(),
            runs: Arc::new(Vec::new()),
            logical: OnceLock::new(),
        };
        let mut rewritten = Vec::new();
        for run in self.runs.iter() {
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
