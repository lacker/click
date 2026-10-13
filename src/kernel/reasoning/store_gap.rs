//! The cells of a store's own block that its constant byte gap keeps, as key
//! ranges a store never has to visit.
//!
//! [`crate::kernel::CMemory::without_possible_aliasing_cells`] decides every
//! earlier cell of the written block, and the cell map offers no way to keep
//! a group of cells without asking each, so `N` stores to cells the facts
//! keep apart used to ask `N^2/2` questions. Most of those cells are not a
//! question at all: a cell at `S + c` beside a store at `S + k` shares the
//! store's symbolic anchor `S`, and the constant gap `c - k` decides whether
//! their bytes meet. That is the rule a run's slots already follow
//! ([`super::memory_resolution::run_slots_kept_by_store`], its `Shift`
//! branch).
//!
//! # What is skipped, and why the answer is the same
//!
//! The ranges this module returns name only cells whose offset is spelled
//! `Constant(c)` beside a store at `Constant(k)`, or `Add(S, Constant(c))`
//! beside a store at `Add(S, Constant(k))` or at bare `S`, for one anchor
//! `S`, with `c != 0` and the two byte windows disjoint for every cell width
//! (`c + 16 <= k` or `k + bytes <= c`; no `CValue` is wider than sixteen
//! bytes, and a `Void` cell stands in sixteen). Because [`PointerOffsetTerm`] orders
//! `Constant` before every other variant, the keys `Add(S, Constant(c))` for
//! `c` in one interval are exactly one contiguous key range, and so are the
//! keys `Constant(c)`.
//!
//! For each such cell the store's per-cell ladder answers "keep", and it
//! reads no fact on the way:
//!
//! * normalization leaves the cell's offset as it is: the anchor's scaled
//!   values are variables, which exact-load normalization never rewrites,
//!   and rebuilding `Add(S, Constant(c))` with `c != 0` over an anchor that
//!   is neither a constant nor ends in one is the same term (checked once
//!   per store on the anchor, [`anchor_is_normal`]);
//! * `StoreByteInterval::overwrites` compares the same atoms at shifts that
//!   differ by `c - k`, and the windows are disjoint;
//! * `access_byte_overlap` finds the constant shift `c - k` —
//!   `pointer_byte_offset_from_base` cancels the shared `S` through the
//!   bitvector `subtract` rule for two sums with one base (checked once per
//!   store on the anchor's byte form, [`anchor_byte_form_cancels`]), or reads
//!   `c` directly against a bare-`S` store — and answers `Separate`;
//! * `pointers_proven_distinct_for_memory_resolution` proves distinctness by
//!   its offset-cancellation rung, which matches the shared `S` by
//!   structural identity before it would consult a fact, and then compares
//!   two different constants; for two constant offsets, the offset
//!   disequality rung decides `Constant(c) == Constant(k)` false.
//!
//! The rungs before those (ownership, the range rungs after them) can only
//! keep a cell too. So skipping these cells changes neither the result nor
//! the forget mark: a kept cell never sets it. Two things the ladder does
//! besides answering are not reproduced, and each disables the skip:
//! while implicit reasoning provenance is being captured, the ownership
//! rung records the composition it used, so nothing is skipped; and once the
//! verification deadline has passed, the ladder refuses every question, so
//! nothing is skipped either. A deadline that passes during one store's scan
//! can still leave that store keeping cells the ladder would have dropped
//! for want of time; keeping them is what the byte arithmetic proves, and
//! the verification has failed on its deadline anyway.
//!
//! Every other cell of the block goes down the unchanged ladder. Debug
//! builds re-ask the ladder about the skipped cells (a bounded sample per
//! store) and fail if it would drop one.

use crate::kernel::{Bitvector32Term, Pointer, PointerOffsetTerm, PureFactContext};

/// The widest cell there is: no `CValue` is wider, and a cell holding
/// `Void` stands in this width too.
const WIDEST_CELL: i64 = crate::kernel::MAX_SCALAR_ACCESS_BYTES;

/// The constants the ranges ever name: small enough that every 32-bit byte
/// difference the ladder computes between two of them is exact.
const CONSTANT_LIMIT: i64 = 1 << 29;

#[cfg(test)]
thread_local! {
    static STORE_GAP_SKIP_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `body` with every store asking every cell, as it did before these
/// ranges: the reference the skipping store is checked against.
#[cfg(test)]
pub(in crate::kernel) fn with_store_gap_skip_disabled<R>(body: impl FnOnce() -> R) -> R {
    let previous = STORE_GAP_SKIP_DISABLED.with(|flag| flag.replace(true));
    let result = body();
    STORE_GAP_SKIP_DISABLED.with(|flag| flag.set(previous));
    result
}

#[cfg(test)]
pub(in crate::kernel) fn store_gap_skip_disabled() -> bool {
    STORE_GAP_SKIP_DISABLED.with(std::cell::Cell::get)
}

#[cfg(not(test))]
pub(in crate::kernel) fn store_gap_skip_disabled() -> bool {
    false
}

/// The key ranges, inclusive, ascending and disjoint, of cells in the
/// store's own block that a store of `bytes` bytes at `store` (already
/// normalized) keeps by its constant byte gap alone. Empty whenever the
/// store's shape is not one the module comment covers.
pub(in crate::kernel) fn store_gap_kept_ranges(
    store: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Vec<(Pointer, Pointer)> {
    if bytes == 0
        || store_gap_skip_disabled()
        || crate::kernel::assumptions::implicit_reasoning_provenance_capturing()
        || crate::kernel::assumptions::reasoning_interrupted()
    {
        return Vec::new();
    }
    let bytes = i64::from(bytes);
    let key = |offset: PointerOffsetTerm| Pointer {
        block: store.block.clone(),
        offset,
    };
    match &store.offset {
        PointerOffsetTerm::Constant(k) => kept_shifts(*k, bytes, false)
            .into_iter()
            .map(|(low, high)| {
                (
                    key(PointerOffsetTerm::Constant(low)),
                    key(PointerOffsetTerm::Constant(high)),
                )
            })
            .collect(),
        offset => {
            // `Add(S, Constant(k))`, or a bare anchor `S` at shift 0.
            let (anchor, k, bare) = match offset {
                PointerOffsetTerm::Add(anchor, trailing) => match trailing.as_ref() {
                    PointerOffsetTerm::Constant(k) => (anchor.as_ref(), *k, false),
                    _ => (offset, 0, true),
                },
                _ => (offset, 0, true),
            };
            // Against a bare store the cancellation rung matches the anchor
            // itself as the store's whole offset, which only a non-sum
            // anchor is (a sum takes the two-sums branch of that rung).
            if bare && matches!(anchor, PointerOffsetTerm::Add(..)) {
                return Vec::new();
            }
            if !anchor_is_normal(anchor, assumptions)
                || (!bare && !anchor_byte_form_cancels(anchor))
                || !anchor_shift_is_small(anchor)
            {
                return Vec::new();
            }
            kept_shifts(k, bytes, true)
                .into_iter()
                .map(|(low, high)| {
                    let at = |shift: i64| {
                        key(PointerOffsetTerm::Add(
                            Box::new(anchor.clone()),
                            Box::new(PointerOffsetTerm::Constant(shift)),
                        ))
                    };
                    (at(low), at(high))
                })
                .collect()
        }
    }
}

/// The shift intervals, inclusive and ascending, whose cells a store of
/// `bytes` bytes at shift `k` provably misses: every shift at most `k - 8`
/// and at least `k + bytes`, within the constant limit, and not zero where
/// `exclude_zero` (the anchor itself is its own key, never inside a range).
fn kept_shifts(k: i64, bytes: i64, exclude_zero: bool) -> Vec<(i64, i64)> {
    if !(-CONSTANT_LIMIT..=CONSTANT_LIMIT).contains(&k) || bytes > WIDEST_CELL {
        return Vec::new();
    }
    let mut intervals = Vec::new();
    for (low, high) in [
        (-CONSTANT_LIMIT, k - WIDEST_CELL),
        (k + bytes, CONSTANT_LIMIT),
    ] {
        if exclude_zero && low <= 0 && 0 <= high {
            intervals.push((low, -1));
            intervals.push((1, high));
        } else {
            intervals.push((low, high));
        }
    }
    intervals.retain(|(low, high)| low <= high);
    intervals
}

/// Whether normalizing an offset `Add(anchor, Constant(c))`, `c != 0`,
/// gives back that same term: the anchor's scaled values are plain
/// variables, which exact-load normalization never rewrites, and the
/// anchor rebuilds to itself and neither is nor ends in a constant, so the
/// smart `add` keeps the trailing constant where it is.
pub(in crate::kernel) fn anchor_is_normal(
    anchor: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if anchor.as_const().is_some() {
        return false;
    }
    if let PointerOffsetTerm::Add(_, trailing) = anchor
        && trailing.as_const().is_some()
    {
        return false;
    }
    if !anchor
        .scaled_values()
        .into_iter()
        .all(|value| matches!(value, Bitvector32Term::Variable(_)))
    {
        return false;
    }
    crate::kernel::memory_provenance::normalize_exact_memory_loads_in_pointer_offset(
        anchor,
        assumptions,
    ) == *anchor
}

/// Whether the byte forms of `anchor + c` and `anchor + k` subtract to the
/// constant `c - k`: the anchor has a 32-bit byte form `T` that the
/// bitvector `add` leaves beside a nonzero constant as `T + c` (it is not a
/// constant, and not a difference the constant could cancel), so the
/// `subtract` rule for two sums with one base cancels `T`.
fn anchor_byte_form_cancels(anchor: &PointerOffsetTerm) -> bool {
    super::path_facts::byte_offset_from_pointer_offset(anchor).is_some_and(|form| {
        !matches!(
            form,
            Bitvector32Term::Constant(_) | Bitvector32Term::Subtract(..)
        )
    })
}

/// Whether the constant summands of the anchor are small, so the atom and
/// shift split every cell's byte test reads cannot overflow. The anchor's
/// scaled values are variables ([`anchor_is_normal`]), and the split keeps
/// every non-constant scaled index whole, so the anchor's atoms are the same
/// for each cell `Add(anchor, Constant(c))` and the store, and the cells'
/// shifts differ from the store's by exactly `c - k`.
fn anchor_shift_is_small(anchor: &PointerOffsetTerm) -> bool {
    let (_, shift) = super::memory_resolution::offset_atoms_and_constant(anchor);
    shift.abs() <= CONSTANT_LIMIT
}

/// How many skipped cells at each end of a range a debug build re-asks the
/// ladder about. The ends are the cells nearest the store's window and the
/// constant limit, where an off-by-one would show first. The count is kept
/// small because a debug check is not free: its reasoning checkpoints are
/// charged as work, so re-asking every skipped cell would make a debug
/// build's store as quadratic as the ladder it spares.
#[cfg(debug_assertions)]
const CHECKED_GAP_CELLS: usize = 2;

/// Debug builds: the ladder keeps every skipped cell it is asked about, the
/// [`CHECKED_GAP_CELLS`] at each end of each range.
#[cfg(debug_assertions)]
pub(in crate::kernel) fn check_gap_kept_cells(
    cells: &crate::kernel::primitives::CellStore,
    kept: &[(Pointer, Pointer)],
    store: &Pointer,
    keep: &mut impl FnMut(&Pointer, &crate::kernel::CValue) -> bool,
) {
    for (low, high) in kept {
        let range = || cells.concrete().range::<_, Pointer>(low..=high);
        let first = range().take(CHECKED_GAP_CELLS).collect::<Vec<_>>();
        let last = range().rev().take(CHECKED_GAP_CELLS).collect::<Vec<_>>();
        for (cell, value) in first
            .into_iter()
            .chain(last.into_iter().filter(|(cell, _)| {
                // Not asked twice where the two ends meet.
                range()
                    .take(CHECKED_GAP_CELLS)
                    .all(|(first, _)| first != *cell)
            }))
        {
            assert!(
                keep(cell, value),
                "a store at {store:?} skipped the cell at {cell:?} by its constant byte gap, \
                 but the ladder drops it"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{CMemory, CValue, ConditionTerm, Variable};

    fn variable(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    /// The anchors the generated offsets are built on: a scaled parameter
    /// offset (eligible both bare and with a constant), a pointer-offset
    /// variable and a 64-bit index (eligible bare only: neither has a 32-bit
    /// byte form), and a sum (eligible with a constant only).
    fn anchors() -> Vec<PointerOffsetTerm> {
        vec![
            PointerOffsetTerm::scale_int32(variable(900), 4),
            PointerOffsetTerm::Variable(Variable(901)),
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(variable(900), 4),
                PointerOffsetTerm::scale_int32(variable(902), 1),
            ),
            PointerOffsetTerm::scale_int64(variable(904), 8, false),
        ]
    }

    fn value_of_width(width: u32, seed: u32) -> CValue {
        match width {
            1 => CValue::UInt8(Bitvector32Term::Constant(seed & 0xff)),
            2 => CValue::Int16(Bitvector32Term::Constant(seed & 0x7fff)),
            4 => CValue::Int32(Bitvector32Term::Constant(seed)),
            8 => CValue::Int64(Bitvector32Term::Int64Constant(i64::from(seed))),
            16 => match crate::kernel::c_uint128_literal((1u128 << 127) | u128::from(seed)) {
                crate::kernel::CExpression::Value(value) => value,
                _ => unreachable!("literal is a value"),
            },
            _ => unreachable!("tested scalar width"),
        }
    }

    fn contexts() -> Vec<PureFactContext> {
        let index = variable(903);
        vec![
            PureFactContext::new(),
            PureFactContext::new().assume_condition(
                ConditionTerm::equal(index.clone(), Bitvector32Term::Constant(2)),
                true,
            ),
            PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(index, Bitvector32Term::Constant(3)),
                    true,
                ),
            PureFactContext::new().assume_condition(
                ConditionTerm::equal(variable(900), Bitvector32Term::Constant(1)),
                true,
            ),
        ]
    }

    /// A small deterministic generator, so a failure names its trial.
    struct Generator(u64);

    impl Generator {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }

        fn shift(&mut self) -> i64 {
            i64::try_from(self.below(49)).expect("small") - 24
        }
    }

    /// One store's offset in a trial built on `anchor` (or on constants
    /// alone, when `anchor` is `None`): mostly constant shifts of it, now and
    /// then another anchor, a symbolic index, or a spelling the smart
    /// constructors never make.
    fn generated_offset(
        generator: &mut Generator,
        anchor: Option<&PointerOffsetTerm>,
        anchors: &[PointerOffsetTerm],
    ) -> PointerOffsetTerm {
        let other =
            anchors[usize::try_from(generator.below(anchors.len() as u64)).expect("small")].clone();
        let Some(anchor) = anchor.cloned() else {
            return match generator.below(24) {
                // A symbolic index among constants: the ladder decides it,
                // and its drops put forget marks on the results.
                0 => PointerOffsetTerm::scale_int32(variable(903), 4),
                1 => PointerOffsetTerm::add(other, PointerOffsetTerm::Constant(generator.shift())),
                _ => PointerOffsetTerm::Constant(generator.shift()),
            };
        };
        match generator.below(24) {
            0 => PointerOffsetTerm::add(anchor, PointerOffsetTerm::scale_int32(variable(903), 4)),
            1 => PointerOffsetTerm::add(other, PointerOffsetTerm::Constant(generator.shift())),
            2 => PointerOffsetTerm::Constant(generator.shift()),
            // Spellings the smart constructor never makes, which the ranges
            // must neither contain nor be fooled by.
            3 => PointerOffsetTerm::Add(Box::new(anchor), Box::new(PointerOffsetTerm::Constant(0))),
            4 => PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(generator.shift())),
                Box::new(anchor),
            ),
            _ => PointerOffsetTerm::add(anchor, PointerOffsetTerm::Constant(generator.shift())),
        }
    }

    fn store(
        memory: CMemory,
        pointer: &Pointer,
        value: CValue,
        context: &PureFactContext,
    ) -> CMemory {
        memory
            .without_possible_aliasing_cells(pointer, value.byte_width(), context)
            .store_with_context(pointer.clone(), value, context)
    }

    /// Cells of `memory` inside the ranges a store would skip.
    fn skipped_cells(memory: &CMemory, ranges: &[(Pointer, Pointer)]) -> usize {
        ranges
            .iter()
            .map(|(low, high)| {
                memory
                    .cells
                    .concrete()
                    .range::<_, Pointer>(low..=high)
                    .count()
            })
            .sum()
    }

    /// Runs `stores` from an empty block both ways, checks the two memories
    /// agree after every store, and returns the skipping one together with
    /// how many cells its stores skipped.
    fn stored_both_ways(stores: &[(PointerOffsetTerm, CValue)]) -> (CMemory, usize) {
        let context = PureFactContext::new();
        let mut fast = CMemory::new().with_block("store-gap", 64);
        let mut full = fast.clone();
        let mut skipped = 0;
        for (offset, value) in stores {
            let pointer = Pointer {
                block: "store-gap".into(),
                offset: offset.clone(),
            };
            skipped += skipped_cells(
                &fast,
                &store_gap_kept_ranges(&pointer, value.byte_width(), &context),
            );
            fast = store(fast, &pointer, value.clone(), &context);
            full = with_store_gap_skip_disabled(|| store(full, &pointer, value.clone(), &context));
            assert!(
                fast == full,
                "the store at {pointer:?} left different memories"
            );
        }
        (fast, skipped)
    }

    fn at(offset: &PointerOffsetTerm) -> Pointer {
        Pointer {
            block: "store-gap".into(),
            offset: offset.clone(),
        }
    }

    /// The byte-level cases the store drop has been wrong about before, each
    /// run both ways and checked for its own outcome: a wide store over the
    /// last narrow cell, a byte store inside a wide cell, one anchor at two
    /// widths, negative shifts, and forget marks compared after a drop.
    #[test]
    fn constant_gap_skipping_keeps_the_byte_level_drops() {
        let anchor = PointerOffsetTerm::scale_int32(variable(900), 4);
        let shifted =
            |shift: i64| PointerOffsetTerm::add(anchor.clone(), PointerOffsetTerm::Constant(shift));
        let int32 = |value: u32| CValue::Int32(Bitvector32Term::Constant(value));
        let int64 = |value: i64| CValue::Int64(Bitvector32Term::Int64Constant(value));
        // Far cells on both sides, which every later store skips.
        let far = [(shifted(-64), int32(90)), (shifted(64), int32(91))];

        // A wide store over the last narrow cell drops it and keeps the ones
        // below it; the far cells stay.
        let mut stores = far.to_vec();
        stores.extend([
            (shifted(0), int32(1)),
            (shifted(4), int32(2)),
            (shifted(8), int32(3)),
        ]);
        stores.push((shifted(8), int64(9)));
        let (memory, skipped) = stored_both_ways(&stores);
        assert!(skipped > 0, "the far cells were never skipped");
        assert_eq!(memory.known_value(&at(&shifted(8))), Some(int64(9)));
        assert_eq!(memory.known_value(&at(&shifted(4))), Some(int32(2)));
        assert_eq!(memory.known_value(&at(&shifted(64))), Some(int32(91)));

        // A byte store inside a wide cell drops the wide cell and forgets.
        let mut stores = far.to_vec();
        stores.push((shifted(0), int64(5)));
        let (before, _) = stored_both_ways(&stores);
        stores.push((shifted(3), CValue::UInt8(Bitvector32Term::Constant(7))));
        let (memory, _) = stored_both_ways(&stores);
        assert_eq!(memory.known_value(&at(&shifted(0))), None);
        assert!(
            memory.forgotten != before.forgotten,
            "a partial overwrite must forget"
        );
        assert_eq!(memory.known_value(&at(&shifted(-64))), Some(int32(90)));

        // One anchor at two widths: an `int16` two bytes into a four-byte
        // store goes, one just past it stays.
        let mut stores = far.to_vec();
        stores.extend([
            (shifted(6), CValue::Int16(Bitvector32Term::Constant(4))),
            (shifted(8), CValue::Int16(Bitvector32Term::Constant(5))),
            (shifted(4), int32(6)),
        ]);
        let (memory, _) = stored_both_ways(&stores);
        assert_eq!(memory.known_value(&at(&shifted(6))), None);
        assert_eq!(
            memory.known_value(&at(&shifted(8))),
            Some(CValue::Int16(Bitvector32Term::Constant(5)))
        );

        // Negative shifts, anchored and constant: an eight-byte cell ending
        // where a store begins stays, one the store reaches into goes.
        let constant = PointerOffsetTerm::Constant;
        for offset in [&shifted as &dyn Fn(i64) -> PointerOffsetTerm, &constant] {
            let (memory, _) = stored_both_ways(&[
                (offset(-40), int32(1)),
                (offset(-16), int64(2)),
                (offset(-8), int64(3)),
                (offset(0), int32(4)),
                (offset(40), int32(5)),
            ]);
            assert_eq!(memory.known_value(&at(&offset(-8))), Some(int64(3)));
            let (memory, _) = stored_both_ways(&[
                (offset(-40), int32(1)),
                (offset(-16), int64(2)),
                (offset(-8), int64(3)),
                (offset(-4), int64(4)),
                (offset(40), int32(5)),
            ]);
            assert_eq!(memory.known_value(&at(&offset(-8))), None);
            assert_eq!(memory.known_value(&at(&offset(-16))), Some(int64(2)));
            assert_eq!(memory.known_value(&at(&offset(-40))), Some(int32(1)));
        }

        // Forget marks after a drop: a symbolic store forgets the anchored
        // cells, and the constant stores after it compare equal, marks and
        // all, whether they skip or ask.
        let (memory, _) = stored_both_ways(&[
            (shifted(0), int32(1)),
            (shifted(32), int32(2)),
            (
                PointerOffsetTerm::add(
                    anchor.clone(),
                    PointerOffsetTerm::scale_int32(variable(903), 4),
                ),
                int32(3),
            ),
            (shifted(64), int32(4)),
            (shifted(96), int32(5)),
            (shifted(-32), int64(6)),
        ]);
        assert_eq!(memory.known_value(&at(&shifted(0))), None);
        assert_eq!(memory.known_value(&at(&shifted(64))), Some(int32(4)));
    }

    /// The ranges defend themselves against a store offset that is not in
    /// the normal form a store is handed: they stay empty rather than name
    /// keys whose cells would normalize to other offsets.
    #[test]
    fn constant_gap_ranges_need_a_normal_anchor() {
        let context = PureFactContext::new();
        let scaled = PointerOffsetTerm::scale_int32(variable(900), 4);
        let unnormal = [
            // A zero the smart constructor would drop.
            PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::Constant(0)),
                    Box::new(scaled.clone()),
                )),
                Box::new(PointerOffsetTerm::Constant(8)),
            ),
            // A trailing constant the smart constructor would fold.
            PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Add(
                    Box::new(scaled.clone()),
                    Box::new(PointerOffsetTerm::Constant(4)),
                )),
                Box::new(PointerOffsetTerm::Constant(8)),
            ),
            // A load, which normalization may rewrite.
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(CMemory::new()),
                        Box::new(at(&PointerOffsetTerm::Constant(0))),
                        crate::kernel::LoadKind::Bits32,
                    ),
                    4,
                ),
                PointerOffsetTerm::Constant(8),
            ),
        ];
        for offset in unnormal {
            assert!(
                store_gap_kept_ranges(&at(&offset), 4, &context).is_empty(),
                "a store at {offset:?} should skip nothing"
            );
        }
        assert!(
            !store_gap_kept_ranges(
                &at(&PointerOffsetTerm::add(
                    scaled,
                    PointerOffsetTerm::Constant(8)
                )),
                4,
                &context
            )
            .is_empty()
        );
    }

    /// Generated store sequences — widths 1, 2, 4, 8 and 16, overlapping and
    /// adjacent, constant and anchored offsets on four anchor shapes,
    /// negative shifts, symbolic indices whose drops leave forget marks, and
    /// non-canonical spellings — produce the same memory, forget mark
    /// included, after every store whether the constant-gap cells are
    /// skipped or asked.
    #[test]
    #[ignore = "nightly: 5s in the parallel gate"]
    fn skipping_constant_gap_cells_leaves_every_store_unchanged() {
        let anchors = anchors();
        let contexts = contexts();
        let mut generator = Generator(0x9e37_79b9_7f4a_7c15);
        let mut skipped = 0usize;
        let mut forgot = 0usize;
        for trial in 0..480 {
            let context = &contexts[trial % contexts.len()];
            let anchor = anchors.get(trial / contexts.len() % (anchors.len() + 1));
            let mut fast = CMemory::new().with_block("store-gap", 64);
            let mut full = fast.clone();
            for step in 0..48 {
                let pointer = Pointer {
                    block: "store-gap".into(),
                    offset: generated_offset(&mut generator, anchor, &anchors),
                };
                let width = [1, 2, 4, 8, 16][usize::try_from(generator.below(5)).expect("small")];
                let value =
                    value_of_width(width, u32::try_from(generator.below(1000)).expect("small"));
                skipped += skipped_cells(&fast, &store_gap_kept_ranges(&pointer, width, context));
                let before = fast.clone();
                fast = store(fast, &pointer, value.clone(), context);
                full = with_store_gap_skip_disabled(|| store(full, &pointer, value, context));
                forgot += usize::from(fast.forgotten != before.forgotten);
                assert!(
                    fast == full,
                    "trial {trial} step {step}: the store at {pointer:?} ({width} bytes) left \
                     different memories\nskipping: {fast:?}\nasking:   {full:?}"
                );
            }
        }
        // The comparison has to be about something: many cells skipped, and
        // many stores that forgot.
        assert!(skipped > 20_000, "only {skipped} cells were skipped");
        assert!(forgot > 2_000, "only {forgot} stores forgot a cell");
    }
}
