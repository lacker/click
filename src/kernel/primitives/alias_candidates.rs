//! The entries of a pointer-keyed snapshot collection that an access into
//! one block can alias.
//!
//! Every memory map and heap collection in a `CMemory` is keyed by a
//! `Pointer` (or by a key whose ordering starts with one), and `Pointer`
//! orders by `block` first. `PointerBlock` in turn orders by variant:
//!
//! ```text
//! Concrete < StringLiteral < Function < FunctionSymbolic < ExternalArgument
//!          < ExternalObject < Symbolic < Heap < Temporary
//! ```
//!
//! So the entries of one block are one contiguous key range, every
//! `Symbolic` block sits in one contiguous range, and every `Heap` and
//! `Temporary` block sits at the end.
//!
//! [`PointerBlock::proven_distinct`] is the kernel's only structural block
//! separation rule, and it has a shape these ranges follow:
//!
//! * a `Symbolic` block is never distinct from anything, so an access into
//!   one may alias every entry;
//! * two different blocks are distinct whenever either is `Heap` or
//!   `Temporary`, so an access into `Heap(id)` or `Temporary(id)` can only
//!   alias entries in that same block and entries in `Symbolic` blocks;
//! * two different `Concrete` names are distinct, so an access into a
//!   `Concrete` block can alias its own block and the non-heap blocks after
//!   the `Concrete` variant (`local:` blocks also skip the two external
//!   variants, which are distinct from them);
//! * every other access can alias at most the non-heap prefix of the map:
//!   storage the program declares, bounded by source size and not by the
//!   number of allocations.
//!
//! [`AliasCandidates`] names exactly those key ranges. An entry outside them
//! is in a block `proven_distinct` from the access's block, so every alias,
//! containment or overlap question a memory rule asks of it is already
//! answered "separate" by the first rung of its ladder. A rule that keeps
//! such entries (a store, a havoc) or never matches them (an exact-pointer
//! heap lookup) may therefore visit the candidate ranges alone and decide
//! the same thing, at a cost bounded by the storage that can actually alias
//! the access rather than by all of memory. The candidate set is a superset
//! of the non-distinct blocks, never a subset: every rule still asks its own
//! question of every candidate, so a coarser range only costs time.
//!
//! Iteration is in ascending key order and visits each entry at most once,
//! so a "first matching entry" search over the candidates finds the same
//! entry a search over the whole collection would.

use super::{CType, Pointer, PointerBlock, PointerOffsetTerm, SnapshotMap, SnapshotSet, Variable};
use std::hash::Hash;
use std::ops::Bound;

/// A snapshot-collection key whose ordering is by pointer block first.
pub(crate) trait BlockKeyed: Ord + Clone {
    fn key_block(&self) -> &PointerBlock;
    /// The smallest key of this type whose block is `block`.
    fn first_key_of(block: &PointerBlock) -> Self;
}

impl BlockKeyed for PointerBlock {
    fn key_block(&self) -> &PointerBlock {
        self
    }

    fn first_key_of(block: &PointerBlock) -> Self {
        block.clone()
    }
}

impl BlockKeyed for Pointer {
    fn key_block(&self) -> &PointerBlock {
        &self.block
    }

    fn first_key_of(block: &PointerBlock) -> Self {
        // `Constant` is `PointerOffsetTerm`'s first variant, so this offset
        // orders below every offset term.
        Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(i64::MIN),
        }
    }
}

impl BlockKeyed for (Pointer, CType) {
    fn key_block(&self) -> &PointerBlock {
        &self.0.block
    }

    fn first_key_of(block: &PointerBlock) -> Self {
        // `Void` is `CType`'s first variant.
        (Pointer::first_key_of(block), CType::Void)
    }
}

/// The upper end of one interval of blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Upper {
    /// Up to and including this block.
    Through(PointerBlock),
    /// Every block strictly below this one.
    Before(PointerBlock),
    Unbounded,
}

impl Upper {
    fn admits(&self, block: &PointerBlock) -> bool {
        match self {
            Self::Through(last) => block <= last,
            Self::Before(end) => block < end,
            Self::Unbounded => true,
        }
    }

    /// Whether an interval starting at `start` touches or overlaps one that
    /// ends here, so that the two can be walked as one key range.
    fn reaches(&self, start: Option<&PointerBlock>) -> bool {
        match (self, start) {
            (Self::Unbounded, _) => true,
            (_, None) => true,
            (Self::Through(last), Some(start)) => start <= last,
            (Self::Before(end), Some(start)) => start <= end,
        }
    }

    fn max(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unbounded, _) | (_, Self::Unbounded) => Self::Unbounded,
            (Self::Through(left), Self::Through(right)) => Self::Through(left.max(right)),
            (Self::Before(left), Self::Before(right)) => Self::Before(left.max(right)),
            (Self::Through(last), Self::Before(end)) | (Self::Before(end), Self::Through(last)) => {
                if last >= end {
                    Self::Through(last)
                } else {
                    Self::Before(end)
                }
            }
        }
    }
}

/// One interval of blocks: from `start` (inclusive; `None` is the first
/// block) up to `end`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct BlockInterval {
    start: Option<PointerBlock>,
    end: Upper,
}

impl BlockInterval {
    #[cfg(test)]
    fn contains(&self, block: &PointerBlock) -> bool {
        self.start.as_ref().is_none_or(|start| block >= start) && self.end.admits(block)
    }

    fn entries<'a, K: BlockKeyed, V>(
        &'a self,
        map: &'a SnapshotMap<K, V>,
    ) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
        let lower = self.start.as_ref().map_or(Bound::Unbounded, |start| {
            Bound::Included(K::first_key_of(start))
        });
        let upper = match &self.end {
            Upper::Before(end) => Bound::Excluded(K::first_key_of(end)),
            Upper::Through(_) | Upper::Unbounded => Bound::Unbounded,
        };
        map.range::<_, K>((lower, upper))
            .take_while(move |(key, _)| self.end.admits(key.key_block()))
    }

    fn elements<'a, K: BlockKeyed>(
        &'a self,
        set: &'a SnapshotSet<K>,
    ) -> impl Iterator<Item = &'a K> + 'a {
        let lower = self.start.as_ref().map_or(Bound::Unbounded, |start| {
            Bound::Included(K::first_key_of(start))
        });
        let upper = match &self.end {
            Upper::Before(end) => Bound::Excluded(K::first_key_of(end)),
            Upper::Through(_) | Upper::Unbounded => Bound::Unbounded,
        };
        set.range::<_, K>((lower, upper))
            .take_while(move |key| self.end.admits(key.key_block()))
    }
}

fn first_string_literal() -> PointerBlock {
    PointerBlock::StringLiteral {
        identity: String::new(),
        bytes: Vec::new(),
    }
}

fn first_symbolic() -> PointerBlock {
    PointerBlock::Symbolic(Variable(0))
}

fn first_heap() -> PointerBlock {
    PointerBlock::Heap(0)
}

/// The blocks whose entries an access may alias; see the module comment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AliasCandidates {
    /// Ascending, pairwise disjoint and non-adjacent.
    intervals: Vec<BlockInterval>,
}

impl AliasCandidates {
    /// Every block that is not [`PointerBlock::proven_distinct`] from
    /// `block`, as a few key ranges (a superset; see the module comment).
    pub(crate) fn of_block(block: &PointerBlock) -> Self {
        let own = || BlockInterval {
            start: Some(block.clone()),
            end: Upper::Through(block.clone()),
        };
        let symbolic = || BlockInterval {
            start: Some(first_symbolic()),
            end: Upper::Before(first_heap()),
        };
        let intervals = match block {
            // A symbolic block may be constrained to any address.
            PointerBlock::Symbolic(_) => vec![BlockInterval {
                start: None,
                end: Upper::Unbounded,
            }],
            // A fresh identity is distinct from every other identity except
            // a symbolic one.
            PointerBlock::Heap(_) | PointerBlock::Temporary(_) => vec![symbolic(), own()],
            // Distinct concrete names are distinct; a `local:` block is also
            // distinct from the external variants.
            PointerBlock::Concrete(_) if block.starts_with("local:") => vec![
                own(),
                BlockInterval {
                    start: Some(first_string_literal()),
                    end: Upper::Before(PointerBlock::ExternalArgument),
                },
                symbolic(),
            ],
            PointerBlock::Concrete(_) => vec![
                own(),
                BlockInterval {
                    start: Some(first_string_literal()),
                    end: Upper::Before(first_heap()),
                },
            ],
            PointerBlock::StringLiteral { .. }
            | PointerBlock::Function(_)
            | PointerBlock::FunctionSymbolic(_)
            | PointerBlock::ExternalArgument
            | PointerBlock::ExternalObject(_) => vec![BlockInterval {
                start: None,
                end: Upper::Before(first_heap()),
            }],
        };
        Self { intervals }
    }

    /// Exactly the entries of `block`: for a rule that only ever touches
    /// the block it names (retiring one automatic object, forgetting one
    /// field), rather than everything that may alias it.
    pub(crate) fn only_block(block: &PointerBlock) -> Self {
        Self {
            intervals: vec![BlockInterval {
                start: Some(block.clone()),
                end: Upper::Through(block.clone()),
            }],
        }
    }

    /// The union of [`Self::of_block`] over several blocks.
    pub(crate) fn of_blocks<'a>(blocks: impl IntoIterator<Item = &'a PointerBlock>) -> Self {
        let mut intervals = blocks
            .into_iter()
            .flat_map(|block| Self::of_block(block).intervals)
            .collect::<Vec<_>>();
        // `None` (the first block) orders first.
        intervals.sort_by(|left, right| left.start.cmp(&right.start));
        let mut merged = Vec::<BlockInterval>::with_capacity(intervals.len());
        for interval in intervals {
            match merged.last_mut() {
                Some(last) if last.end.reaches(interval.start.as_ref()) => {
                    last.end = std::mem::replace(&mut last.end, Upper::Unbounded).max(interval.end);
                }
                _ => merged.push(interval),
            }
        }
        Self { intervals: merged }
    }

    /// The candidate entries of a persistent map keyed by block, ascending:
    /// one logarithmic step to each candidate block the map holds, and none
    /// to a block outside the candidates, so the walk costs the candidate
    /// blocks present rather than the map.
    pub(crate) fn persistent_block_entries<'a, V>(
        &'a self,
        map: &'a crate::persistent::PersistentMap<PointerBlock, V>,
    ) -> Vec<(&'a PointerBlock, &'a V)> {
        let mut entries = Vec::new();
        for interval in &self.intervals {
            let mut next = match &interval.start {
                Some(start) => match map.get(start) {
                    Some(value) => Some((start, value)),
                    None => map.get_greater_than(start),
                },
                None => map.iter().next(),
            };
            while let Some((block, value)) = next {
                if !interval.end.admits(block) {
                    break;
                }
                entries.push((block, value));
                next = map.get_greater_than(block);
            }
        }
        entries
    }

    /// Whether an entry in `block` is among the candidates.
    pub(crate) fn admits_block(&self, block: &PointerBlock) -> bool {
        self.intervals.iter().any(|interval| {
            interval.start.as_ref().is_none_or(|start| block >= start) && interval.end.admits(block)
        })
    }

    /// Whether an entry in `block` is among the candidates.
    #[cfg(test)]
    pub(crate) fn contains_block(&self, block: &PointerBlock) -> bool {
        self.intervals
            .iter()
            .any(|interval| interval.contains(block))
    }

    /// The candidate entries of `map`, ascending. O(log n) per interval to
    /// position plus the entries visited.
    pub(crate) fn entries<'a, K: BlockKeyed, V>(
        &'a self,
        map: &'a SnapshotMap<K, V>,
    ) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
        self.intervals
            .iter()
            .flat_map(move |interval| interval.entries(map))
    }

    /// The candidate elements of `set`, ascending.
    pub(crate) fn elements<'a, K: BlockKeyed>(
        &'a self,
        set: &'a SnapshotSet<K>,
    ) -> impl Iterator<Item = &'a K> + 'a {
        self.intervals
            .iter()
            .flat_map(move |interval| interval.elements(set))
    }

    /// Removes the candidate entries `keep` rejects. Entries outside the
    /// candidates are kept without being visited, so this equals
    /// `map.retain(keep)` for any `keep` that accepts every entry in a
    /// block proven distinct from the candidates' blocks. Charges one work
    /// unit per candidate visited.
    pub(crate) fn retain_map<K: BlockKeyed + Hash, V: Clone + Hash>(
        &self,
        map: &mut SnapshotMap<K, V>,
        mut keep: impl FnMut(&K, &V) -> bool,
    ) {
        let mut visited = 0usize;
        let dropped = self
            .entries(map)
            .inspect(|_| visited += 1)
            .filter(|(key, value)| !keep(key, value))
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(visited);
        for key in dropped {
            map.remove(&key);
        }
    }

    /// [`Self::retain_map`] for a set.
    pub(crate) fn retain_set<K: BlockKeyed + Hash>(
        &self,
        set: &mut SnapshotSet<K>,
        mut keep: impl FnMut(&K) -> bool,
    ) {
        let mut visited = 0usize;
        let dropped = self
            .elements(set)
            .inspect(|_| visited += 1)
            .filter(|key| !keep(key))
            .cloned()
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(visited);
        for key in dropped {
            set.remove(&key);
        }
    }

    /// Whether some candidate entry satisfies `found`. Equals
    /// `map.iter().any(found)` for any `found` that rejects every entry in a
    /// block proven distinct from the candidates' blocks. Charges one work
    /// unit per candidate visited.
    pub(crate) fn any_entry<K: BlockKeyed, V>(
        &self,
        map: &SnapshotMap<K, V>,
        mut found: impl FnMut(&K, &V) -> bool,
    ) -> bool {
        let mut visited = 0usize;
        let answer = self.entries(map).any(|(key, value)| {
            visited += 1;
            found(key, value)
        });
        crate::instrumentation::record_deterministic_work(visited);
        answer
    }

    /// [`Self::any_entry`] for a set.
    pub(crate) fn any_element<K: BlockKeyed>(
        &self,
        set: &SnapshotSet<K>,
        mut found: impl FnMut(&K) -> bool,
    ) -> bool {
        let mut visited = 0usize;
        let answer = self.elements(set).any(|key| {
            visited += 1;
            found(key)
        });
        crate::instrumentation::record_deterministic_work(visited);
        answer
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_blocks() -> Vec<PointerBlock> {
        vec![
            PointerBlock::Concrete("global:g".to_string()),
            PointerBlock::Concrete("global:h".to_string()),
            PointerBlock::Concrete("local:x".to_string()),
            PointerBlock::Concrete("local:y".to_string()),
            PointerBlock::Concrete("static:f:s".to_string()),
            PointerBlock::StringLiteral {
                identity: "a".to_string(),
                bytes: b"one".to_vec(),
            },
            PointerBlock::StringLiteral {
                identity: "b".to_string(),
                bytes: b"two".to_vec(),
            },
            PointerBlock::Function("f".to_string()),
            PointerBlock::FunctionSymbolic(Variable(3)),
            PointerBlock::ExternalArgument,
            PointerBlock::ExternalObject(Variable(4)),
            PointerBlock::ExternalObject(Variable(5)),
            PointerBlock::Symbolic(Variable(0)),
            PointerBlock::Symbolic(Variable(7)),
            PointerBlock::Heap(0),
            PointerBlock::Heap(1),
            PointerBlock::Heap(9),
            PointerBlock::Temporary(0),
            PointerBlock::Temporary(2),
        ]
    }

    fn cells_of(blocks: &[PointerBlock]) -> SnapshotMap<Pointer, u32> {
        let mut map = SnapshotMap::new();
        for (index, block) in blocks.iter().enumerate() {
            for offset in [0, 4, 8] {
                map.insert(
                    Pointer {
                        block: block.clone(),
                        offset: PointerOffsetTerm::Constant(offset),
                    },
                    index as u32,
                );
            }
            map.insert(
                Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Variable(Variable(1)),
                },
                index as u32,
            );
        }
        map
    }

    #[test]
    fn candidates_cover_every_block_not_proven_distinct() {
        let blocks = sample_blocks();
        for access in &blocks {
            let candidates = AliasCandidates::of_block(access);
            for other in &blocks {
                if !access.proven_distinct(other) {
                    assert!(
                        candidates.contains_block(other),
                        "{other:?} may alias {access:?} but is not a candidate"
                    );
                }
            }
            assert!(candidates.contains_block(access));
        }
    }

    #[test]
    fn persistent_block_entries_are_the_ascending_candidate_blocks() {
        let blocks = sample_blocks();
        let mut map = crate::persistent::PersistentMap::default();
        for (index, block) in blocks.iter().enumerate() {
            map.insert(block.clone(), index);
        }
        let mut accesses = blocks
            .iter()
            .map(|block| vec![block.clone()])
            .collect::<Vec<_>>();
        accesses.push(vec![PointerBlock::Heap(1), PointerBlock::Heap(9)]);
        for access in accesses {
            let candidates = AliasCandidates::of_blocks(&access);
            let walked = candidates
                .persistent_block_entries(&map)
                .into_iter()
                .map(|(block, index)| (block.clone(), *index))
                .collect::<Vec<_>>();
            let filtered = map
                .iter()
                .filter(|(block, _)| candidates.contains_block(block))
                .map(|(block, index)| (block.clone(), *index))
                .collect::<Vec<_>>();
            assert_eq!(walked, filtered, "{access:?}");
        }
    }

    #[test]
    fn candidates_exclude_unrelated_heap_blocks() {
        let heap = AliasCandidates::of_block(&PointerBlock::Heap(1));
        assert!(!heap.contains_block(&PointerBlock::Heap(0)));
        assert!(!heap.contains_block(&PointerBlock::Temporary(0)));
        assert!(!heap.contains_block(&PointerBlock::Concrete("global:g".to_string())));
        assert!(heap.contains_block(&PointerBlock::Symbolic(Variable(7))));
        let global = AliasCandidates::of_block(&PointerBlock::Concrete("global:g".to_string()));
        assert!(!global.contains_block(&PointerBlock::Heap(0)));
        assert!(!global.contains_block(&PointerBlock::Concrete("global:h".to_string())));
    }

    #[test]
    fn candidate_iteration_is_the_ascending_filter_of_the_whole_map() {
        let blocks = sample_blocks();
        let map = cells_of(&blocks);
        let mut accesses = blocks
            .iter()
            .map(|block| vec![block.clone()])
            .collect::<Vec<_>>();
        accesses.push(vec![PointerBlock::Heap(1), PointerBlock::Heap(9)]);
        accesses.push(vec![
            PointerBlock::Heap(1),
            PointerBlock::Concrete("local:x".to_string()),
        ]);
        accesses.push(vec![
            PointerBlock::Concrete("global:g".to_string()),
            PointerBlock::Concrete("local:y".to_string()),
            PointerBlock::Temporary(2),
        ]);
        accesses.push(vec![
            PointerBlock::Heap(0),
            PointerBlock::Symbolic(Variable(7)),
        ]);
        for access in &accesses {
            let candidates = AliasCandidates::of_blocks(access);
            let visited = candidates.entries(&map).collect::<Vec<_>>();
            let expected = map
                .iter()
                .filter(|(pointer, _)| candidates.contains_block(&pointer.block))
                .collect::<Vec<_>>();
            assert_eq!(visited, expected, "candidates of {access:?}");
            for block in &blocks {
                if access.iter().any(|access| !access.proven_distinct(block)) {
                    assert!(candidates.contains_block(block));
                }
            }
        }
    }
}
