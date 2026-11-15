//! The bytes of storage with an initialization history that a C store has
//! initialized, kept apart from the cached cell values.
//!
//! Automatic storage and fresh `malloc` storage start out uninitialized, and a
//! read of a byte no store has written is undefined. A cached cell is
//! evidence that its bytes were written, but a cell is a *value*, and values
//! are forgotten for reasons that have nothing to do with initialization: a
//! store the facts cannot place, a loop or call havoc, a join. A store only
//! ever initializes bytes, so none of those events makes an initialized byte
//! uninitialized again. This record is what survives them: the value is gone,
//! and the byte reads as initialized-but-unknown instead of as a read of
//! uninitialized storage.
//!
//! Entries are keyed by the pointer that starts them and carry a byte length.
//! Constant-offset entries of one block are *runs*: disjoint, non-adjacent
//! intervals, merged as they are recorded, so a fully written array is one
//! entry however many element stores wrote it, and a covering query is one
//! predecessor lookup. A symbolic-offset entry is an exact spelling with the
//! widest access recorded at it; it covers only a read at that spelling.
//!
//! Every operation touches the entries of the one block it names (O(log n)
//! to position plus the entries it merges or visits), never unrelated blocks.

use super::{AliasCandidates, HashedOrdMap, Pointer, PointerBlock, PointerOffsetTerm};

/// See the module comment.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct InitializedBytes {
    /// Start pointer to byte length. Invariant: within one block, the
    /// constant-offset entries are pairwise disjoint and non-adjacent, and
    /// every length is nonzero.
    entries: HashedOrdMap<Pointer, u32>,
}

fn constant_start(block: &PointerBlock, offset: i64) -> Pointer {
    Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

impl InitializedBytes {
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// The entries as a state map, for the generic observable-entry and
    /// relative-equality comparisons.
    pub(crate) fn as_map(&self) -> &HashedOrdMap<Pointer, u32> {
        &self.entries
    }

    /// Equality of two records derived from `base`; see
    /// [`HashedOrdMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.entries.eq_relative_to(&other.entries, &base.entries)
    }

    /// The run of constant offsets in `block` that starts at or before
    /// `offset`, nearest first: the only run that can contain it.
    fn run_at_or_before(&self, block: &PointerBlock, offset: i64) -> Option<(i64, i64)> {
        self.entries
            .range(constant_start(block, i64::MIN)..=constant_start(block, offset))
            .next_back()
            .and_then(|(start, length)| {
                let start = start.offset.as_const()?;
                Some((start, start + i64::from(*length)))
            })
    }

    /// Whether every one of the `byte_width` bytes at `pointer` is recorded
    /// as initialized.
    pub(crate) fn covers(&self, pointer: &Pointer, byte_width: u32) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        match pointer.offset.as_const() {
            Some(offset) => self
                .run_at_or_before(&pointer.block, offset)
                .is_some_and(|(_, end)| end >= offset + i64::from(byte_width)),
            None => self
                .entries
                .get(pointer)
                .is_some_and(|length| *length >= byte_width),
        }
    }

    /// The end of the run of `block` holding the byte at `offset`, if one
    /// does: one predecessor lookup.
    pub(crate) fn run_end_holding(&self, block: &PointerBlock, offset: i64) -> Option<i64> {
        crate::instrumentation::record_deterministic_work(1);
        self.run_at_or_before(block, offset)
            .map(|(_, end)| end)
            .filter(|end| *end > offset)
    }

    /// Whether one run of `block` holds every byte in `start..end`.
    pub(crate) fn covers_interval(&self, block: &PointerBlock, start: i64, end: i64) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.run_at_or_before(block, start)
            .is_some_and(|(_, run_end)| run_end >= end)
    }

    /// The constant-offset runs of `block`, ascending, as start and length.
    pub(crate) fn constant_runs_in_block(&self, block: &PointerBlock) -> Vec<(i64, u32)> {
        let runs = AliasCandidates::only_block(block)
            .entries(&self.entries)
            .filter_map(|(start, length)| Some((start.offset.as_const()?, *length)))
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(runs.len() + 1);
        runs
    }

    /// Records that the `byte_width` bytes at `pointer` are initialized.
    /// Returns whether the record changed: recording bytes it already covers
    /// leaves it (and so the state's content) exactly as it was.
    pub(crate) fn record(&mut self, pointer: &Pointer, byte_width: u32) -> bool {
        if byte_width == 0 {
            return false;
        }
        let Some(offset) = pointer.offset.as_const() else {
            if self
                .entries
                .get(pointer)
                .is_some_and(|length| *length >= byte_width)
            {
                return false;
            }
            self.entries.insert(pointer.clone(), byte_width);
            return true;
        };
        let block = &pointer.block;
        let mut start = offset;
        let mut end = offset + i64::from(byte_width);
        if let Some((before_start, before_end)) = self.run_at_or_before(block, offset)
            && before_end >= start
        {
            if before_end >= end {
                return false;
            }
            start = before_start;
        }
        // Every later run that the new interval reaches or touches merges.
        let merged = self
            .entries
            .range(constant_start(block, start)..=constant_start(block, end))
            .filter_map(|(key, length)| {
                key.offset
                    .as_const()
                    .map(|key_start| (key.clone(), key_start + i64::from(*length)))
            })
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(merged.len() + 1);
        for (key, key_end) in merged {
            end = end.max(key_end);
            self.entries.remove(&key);
        }
        let Ok(length) = u32::try_from(end - start) else {
            // Wider than any object; recording nothing only loses knowledge.
            return false;
        };
        self.entries.insert(constant_start(block, start), length);
        true
    }

    /// Forgets the `byte_width` bytes at `pointer`: at a constant offset, the
    /// part of every run that holds them, splitting a run that straddles
    /// either end; at a symbolic offset, the entry of that exact spelling.
    /// Returns whether the record changed.
    pub(crate) fn forget(&mut self, pointer: &Pointer, byte_width: u32) -> bool {
        let Some(start) = pointer.offset.as_const() else {
            return self.entries.remove(pointer).is_some();
        };
        if byte_width == 0 {
            return false;
        }
        let block = &pointer.block;
        let end = start + i64::from(byte_width);
        let first = self
            .run_at_or_before(block, start)
            .filter(|(_, run_end)| *run_end > start)
            .map_or(start, |(run_start, _)| run_start);
        let overlapping = self
            .entries
            .range(constant_start(block, first)..constant_start(block, end))
            .filter_map(|(key, length)| {
                let key_start = key.offset.as_const()?;
                let key_end = key_start + i64::from(*length);
                (key_end > start && key_start < end).then_some((key_start, key_end))
            })
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(overlapping.len() + 1);
        if overlapping.is_empty() {
            return false;
        }
        for (run_start, run_end) in overlapping {
            self.entries.remove(&constant_start(block, run_start));
            if run_start < start {
                self.entries.insert(
                    constant_start(block, run_start),
                    u32::try_from(start - run_start).expect("a piece of a run"),
                );
            }
            if run_end > end {
                self.entries.insert(
                    constant_start(block, end),
                    u32::try_from(run_end - end).expect("a piece of a run"),
                );
            }
        }
        true
    }

    /// Forgets every entry of `block`: its object's lifetime ended, so a
    /// later object must start uninitialized.
    pub(crate) fn forget_block(&mut self, block: &PointerBlock) {
        AliasCandidates::only_block(block).retain_map(&mut self.entries, |_, _| false);
    }

    /// Removes the candidate entries `keep` rejects, as
    /// [`AliasCandidates::retain_map`]. Removing whole entries keeps the run
    /// invariant.
    pub(crate) fn retain_candidates(
        &mut self,
        candidates: &AliasCandidates,
        keep: impl FnMut(&Pointer, &u32) -> bool,
    ) {
        candidates.retain_map(&mut self.entries, keep);
    }

    /// The bytes both records cover. A constant run keeps the parts the other
    /// record's runs cover; a symbolic spelling needs the same spelling in
    /// both, at the narrower width. The result keeps the run invariant: two
    /// clipped pieces are separated by a gap of one side or the other.
    pub(crate) fn intersection(&self, other: &Self) -> Self {
        // Equal records intersect to themselves. Two records derived from
        // one are compared along the paths that changed.
        if self.entries.ptr_eq(&other.entries) || self.entries == other.entries {
            return self.clone();
        }
        let mut result = HashedOrdMap::new();
        let mut visited = 0usize;
        for (pointer, length) in self.entries.iter() {
            visited += 1;
            let Some(start) = pointer.offset.as_const() else {
                if let Some(other_length) = other.entries.get(pointer) {
                    result.insert(pointer.clone(), (*length).min(*other_length));
                }
                continue;
            };
            let end = start + i64::from(*length);
            let first = other
                .run_at_or_before(&pointer.block, start)
                .map_or(start, |(other_start, _)| other_start);
            for (other_pointer, other_length) in other
                .entries
                .range(constant_start(&pointer.block, first)..constant_start(&pointer.block, end))
            {
                visited += 1;
                let Some(other_start) = other_pointer.offset.as_const() else {
                    continue;
                };
                let other_end = other_start + i64::from(*other_length);
                let piece_start = start.max(other_start);
                let piece_end = end.min(other_end);
                if piece_start < piece_end {
                    result.insert(
                        constant_start(&pointer.block, piece_start),
                        u32::try_from(piece_end - piece_start).expect("a piece of a run"),
                    );
                }
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
        Self { entries: result }
    }

    /// The same record with every start pointer rewritten, re-merged so the
    /// run invariant holds even where the rewrite made a symbolic start
    /// constant.
    pub(crate) fn map_pointers(&self, mut rewrite: impl FnMut(&Pointer) -> Pointer) -> Self {
        let mut result = Self::default();
        for (pointer, length) in self.entries.iter() {
            result.record(&rewrite(pointer), *length);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(block: &str, offset: i64) -> Pointer {
        constant_start(&PointerBlock::from(block), offset)
    }

    #[test]
    fn element_stores_merge_into_one_run() {
        let mut record = InitializedBytes::default();
        assert!(record.record(&at("local:a", 4), 4));
        assert!(record.record(&at("local:a", 0), 4));
        assert!(record.record(&at("local:a", 12), 4));
        assert_eq!(record.len(), 2);
        assert!(!record.covers(&at("local:a", 8), 4));
        assert!(record.record(&at("local:a", 8), 4));
        assert_eq!(record.len(), 1);
        assert!(record.covers(&at("local:a", 0), 16));
        assert!(!record.covers(&at("local:a", 0), 17));
        assert!(!record.record(&at("local:a", 6), 1));
        // Another block is untouched by the merge and uncovered.
        assert!(!record.covers(&at("local:b", 0), 1));
    }

    #[test]
    fn a_partial_record_does_not_cover_its_neighbour() {
        let mut record = InitializedBytes::default();
        record.record(&at("local:a", 0), 4);
        assert!(!record.covers(&at("local:a", 2), 4));
        assert!(record.covers(&at("local:a", 2), 2));
        assert!(!record.covers(&at("local:a", 4), 4));
    }

    #[test]
    fn forgetting_splits_the_run_that_holds_the_bytes() {
        let mut record = InitializedBytes::default();
        record.record(&at("local:a", 0), 16);
        assert!(record.forget(&at("local:a", 4), 4));
        assert_eq!(record.len(), 2);
        assert!(record.covers(&at("local:a", 0), 4));
        assert!(!record.covers(&at("local:a", 4), 1));
        assert!(record.covers(&at("local:a", 8), 8));
        assert!(!record.forget(&at("local:a", 4), 4));
        assert!(record.forget(&at("local:a", 2), 8));
        assert!(record.covers(&at("local:a", 0), 2));
        assert!(!record.covers(&at("local:a", 2), 1));
        assert!(record.covers(&at("local:a", 10), 6));
    }

    #[test]
    fn intersection_keeps_the_bytes_both_sides_cover() {
        let mut left = InitializedBytes::default();
        left.record(&at("local:a", 0), 16);
        let mut right = InitializedBytes::default();
        right.record(&at("local:a", 4), 4);
        right.record(&at("local:a", 12), 8);
        right.record(&at("local:b", 0), 4);
        let both = left.intersection(&right);
        assert_eq!(both.len(), 2);
        assert!(both.covers(&at("local:a", 4), 4));
        assert!(both.covers(&at("local:a", 12), 4));
        assert!(!both.covers(&at("local:a", 0), 4));
        assert!(!both.covers(&at("local:a", 16), 4));
        assert!(!both.covers(&at("local:b", 0), 4));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/initialized_bytes/tests.rs");
    }
}
