//! Persistent ordered collections with a cached content hash.
//!
//! Kernel memory snapshots are interned by content and share their maps with
//! every snapshot derived from them. A `std` `BTreeMap` behind an `Arc` must
//! be cloned whole before a shared map can change, and hashing or comparing
//! it visits every entry, so one store into a memory of `n` cells cost O(n)
//! twice over. These wrappers keep the snapshot's maps as persistent B-trees
//! (`imbl::OrdMap` / `imbl::OrdSet`): a clone is O(1), and an insert or
//! removal copies only the O(log n) path it changes.
//!
//! Each wrapper also carries its content hash, maintained incrementally as the
//! wrapping sum of one fixed-key hash per entry. The sum is commutative, so
//! equal contents hash equally whatever order they were built in, and a
//! mutation adjusts it by the entries it adds or removes. `Hash` writes only
//! that sum and the length, so hashing a map is O(1). Equality uses the
//! persistent-node identity and the cached hash as fast paths before it falls
//! back to an elementwise comparison, which it charges to the deterministic
//! work counters per element compared.
//!
//! The content hash is never persisted; it only has to be deterministic
//! within and across runs, which `DefaultHasher::new()` (fixed keys) is.

use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::ops::RangeBounds;

fn entry_hash<T: Hash + ?Sized>(entry: &T) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    entry.hash(&mut hasher);
    hasher.finish()
}

fn map_entry_hash<K: Hash, V: Hash>(key: &K, value: &V) -> u64 {
    entry_hash(&(key, value))
}

/// A persistent ordered map with an O(1) content hash.
pub(crate) struct SnapshotMap<K, V> {
    map: imbl::OrdMap<K, V>,
    hash: u64,
}

impl<K, V> SnapshotMap<K, V> {
    pub(crate) fn new() -> Self {
        Self {
            map: imbl::OrdMap::new(),
            hash: 0,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Whether the two maps share one persistent root. `true` implies equal
    /// content; `false` says nothing.
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        self.map.ptr_eq(&other.map)
    }

    #[cfg(test)]
    /// The cached content hash: a function of the entries alone.
    pub(crate) fn content_hash(&self) -> u64 {
        self.hash
    }
}

impl<K: Ord, V> SnapshotMap<K, V> {
    pub(crate) fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.get(key)
    }

    pub(crate) fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.contains_key(key)
    }

    /// Entries in ascending key order; double-ended.
    pub(crate) fn iter(&self) -> imbl::ordmap::Iter<'_, K, V, imbl::shared_ptr::DefaultSharedPtr> {
        self.map.iter()
    }

    pub(crate) fn keys(&self) -> imbl::ordmap::Keys<'_, K, V, imbl::shared_ptr::DefaultSharedPtr> {
        self.map.keys()
    }

    pub(crate) fn values(
        &self,
    ) -> imbl::ordmap::Values<'_, K, V, imbl::shared_ptr::DefaultSharedPtr> {
        self.map.values()
    }

    /// Entries whose keys fall in `range`, in ascending order; double-ended.
    /// O(log n) to position plus the entries visited.
    pub(crate) fn range<R, Q>(
        &self,
        range: R,
    ) -> imbl::ordmap::RangedIter<'_, K, V, imbl::shared_ptr::DefaultSharedPtr>
    where
        R: RangeBounds<Q>,
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.range(range)
    }
}

/// One entry on which two snapshot maps differ; see [`SnapshotMap::diff`].
pub(crate) enum SnapshotMapChange<'a, K> {
    /// Present only in the first map.
    Removed(&'a K),
    /// Present only in the second map.
    Added(&'a K),
    /// Present in both maps with different values.
    Changed(&'a K),
}

impl<'a, K> SnapshotMapChange<'a, K> {
    pub(crate) fn key(&self) -> &'a K {
        match self {
            Self::Removed(key) | Self::Added(key) | Self::Changed(key) => key,
        }
    }
}

impl<K: Ord, V: PartialEq> SnapshotMap<K, V> {
    /// The entries on which `self` and `other` differ, in ascending key
    /// order.
    ///
    /// Subtrees the two maps share are skipped by node identity, so for a
    /// map derived from the other by `k` inserts or removals the walk is
    /// proportional to the `k` changed paths, not to the map. Charges one
    /// work unit per difference reported.
    pub(crate) fn diff<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = SnapshotMapChange<'a, K>> + 'a {
        self.map.diff(&other.map).map(|change| {
            crate::instrumentation::record_deterministic_work(1);
            match change {
                imbl::ordmap::DiffItem::Remove(key, _) => SnapshotMapChange::Removed(key),
                imbl::ordmap::DiffItem::Add(key, _) => SnapshotMapChange::Added(key),
                imbl::ordmap::DiffItem::Update { old: (key, _), .. } => {
                    SnapshotMapChange::Changed(key)
                }
            }
        })
    }

    /// Whether `self == other`, for two maps each derived from `base` by
    /// persistent updates, comparing the two changes from `base` instead of
    /// the maps.
    ///
    /// Two maps derived from one base share every subtree neither update
    /// touched, so each diff walks only the changed paths (see
    /// [`Self::diff`]), and the comparison costs the changes rather than the
    /// maps: this is what a re-derived snapshot pays to be recognized as an
    /// earlier child of the same base. Equal changes from one base mean equal
    /// maps whatever the maps share, so the answer never depends on sharing;
    /// only the cost does. Charges one unit per compared change, plus the
    /// depth of the tree for each walk's descent.
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        if self.map.ptr_eq(&other.map) {
            return true;
        }
        if self.hash != other.hash || self.map.len() != other.map.len() {
            return false;
        }
        crate::instrumentation::record_deterministic_work(
            2 * (usize::BITS - base.map.len().leading_zeros()) as usize,
        );
        let mut left = base.map.diff(&self.map);
        let mut right = base.map.diff(&other.map);
        loop {
            let (left, right) = match (left.next(), right.next()) {
                (None, None) => return true,
                (Some(left), Some(right)) => (left, right),
                _ => return false,
            };
            crate::instrumentation::record_deterministic_work(1);
            let same = match (left, right) {
                (
                    imbl::ordmap::DiffItem::Remove(left, _),
                    imbl::ordmap::DiffItem::Remove(right, _),
                ) => left == right,
                (
                    imbl::ordmap::DiffItem::Add(left_key, left_value),
                    imbl::ordmap::DiffItem::Add(right_key, right_value),
                )
                | (
                    imbl::ordmap::DiffItem::Update {
                        new: (left_key, left_value),
                        ..
                    },
                    imbl::ordmap::DiffItem::Update {
                        new: (right_key, right_value),
                        ..
                    },
                ) => left_key == right_key && left_value == right_value,
                _ => false,
            };
            if !same {
                return false;
            }
        }
    }

    /// Whether `self` is exactly `before` with the entries at `removed` taken
    /// out. `removed` must be ascending keys of `before`. Walks only the
    /// paths the two maps do not share (see [`Self::diff`]).
    pub(crate) fn is_without(&self, before: &Self, removed: &[&K]) -> bool {
        if self.map.len() + removed.len() != before.map.len() {
            return false;
        }
        let mut expected = removed.iter();
        for change in before.diff(self) {
            match change {
                SnapshotMapChange::Removed(key) if expected.next() == Some(&key) => {}
                _ => return false,
            }
        }
        expected.next().is_none()
    }
}

impl<K: Ord + Clone + Hash, V: Clone + Hash> SnapshotMap<K, V> {
    /// Inserts or replaces one entry. O(log n) plus hashing the entry.
    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        let added = map_entry_hash(&key, &value);
        let replaced = self.map.insert(key.clone(), value);
        if let Some(old) = &replaced {
            self.hash = self.hash.wrapping_sub(map_entry_hash(&key, old));
        }
        self.hash = self.hash.wrapping_add(added);
        replaced
    }

    /// Removes one entry. O(log n) plus hashing the entry.
    pub(crate) fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (key, value) = self.map.remove_with_key(key)?;
        self.hash = self.hash.wrapping_sub(map_entry_hash(&key, &value));
        Some(value)
    }

    /// Inserts `value` unless `key` is present; returns the stored value.
    pub(crate) fn get_or_insert(&mut self, key: K, value: V) -> &V {
        if !self.map.contains_key(&key) {
            self.insert(key.clone(), value);
        }
        self.map.get(&key).expect("entry was just ensured")
    }

    /// Keeps only the entries `keep` accepts.
    ///
    /// O(n): it visits every entry, and charges one work unit per entry.
    /// Reserved for operations that are legitimately whole-map; a
    /// per-operation hot path restricts itself to the entries that can alias
    /// the access instead (`AliasCandidates::retain_map`).
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&K, &V) -> bool) {
        crate::instrumentation::record_deterministic_work(self.map.len());
        let dropped = self
            .map
            .iter()
            .filter(|(key, value)| !keep(key, value))
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        for key in dropped {
            self.remove(&key);
        }
    }

    #[cfg(test)]
    pub(crate) fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<K, V> Clone for SnapshotMap<K, V> {
    /// O(1): the persistent root is shared.
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            hash: self.hash,
        }
    }
}

impl<K, V> Default for SnapshotMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: std::fmt::Debug + Ord, V: std::fmt::Debug> std::fmt::Debug for SnapshotMap<K, V> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_map().entries(self.map.iter()).finish()
    }
}

impl<K, V> Hash for SnapshotMap<K, V> {
    /// O(1): the cached content hash and the length.
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
        state.write_usize(self.map.len());
    }
}

impl<K: Ord, V: PartialEq> PartialEq for SnapshotMap<K, V> {
    /// O(1) when the maps share a root or differ in cached hash or length;
    /// otherwise elementwise, charging one work unit per entry compared.
    fn eq(&self, other: &Self) -> bool {
        if self.map.ptr_eq(&other.map) {
            return true;
        }
        if self.hash != other.hash || self.map.len() != other.map.len() {
            return false;
        }
        let mut compared = 0usize;
        let mut equal = true;
        for (left, right) in self.map.iter().zip(other.map.iter()) {
            compared += 1;
            if left != right {
                equal = false;
                break;
            }
        }
        crate::instrumentation::record_deterministic_work(compared);
        equal
    }
}

impl<K: Ord, V: Eq> Eq for SnapshotMap<K, V> {}

impl<K: Ord, V: Ord> PartialOrd for SnapshotMap<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: Ord, V: Ord> Ord for SnapshotMap<K, V> {
    /// Lexicographic over entries, as for `BTreeMap`. O(1) for a shared
    /// root; otherwise O(n) in the length of the common prefix.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.map.ptr_eq(&other.map) {
            return std::cmp::Ordering::Equal;
        }
        self.map.iter().cmp(other.map.iter())
    }
}

impl<K: Ord + Clone + Hash, V: Clone + Hash> FromIterator<(K, V)> for SnapshotMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        map.extend(iter);
        map
    }
}

impl<K: Ord + Clone + Hash, V: Clone + Hash> Extend<(K, V)> for SnapshotMap<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K: Ord, V> IntoIterator for &'a SnapshotMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = imbl::ordmap::Iter<'a, K, V, imbl::shared_ptr::DefaultSharedPtr>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

impl<K: Ord + Clone, V: Clone> IntoIterator for SnapshotMap<K, V> {
    type Item = (K, V);
    type IntoIter = imbl::ordmap::ConsumingIter<K, V, imbl::shared_ptr::DefaultSharedPtr>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

/// A persistent ordered set with an O(1) content hash.
pub(crate) struct SnapshotSet<K> {
    set: imbl::OrdSet<K>,
    hash: u64,
}

impl<K> SnapshotSet<K> {
    pub(crate) fn new() -> Self {
        Self {
            set: imbl::OrdSet::new(),
            hash: 0,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.set.len()
    }

    #[cfg(test)]
    pub(crate) fn content_hash(&self) -> u64 {
        self.hash
    }
}

impl<K: Ord> SnapshotSet<K> {
    pub(crate) fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.set.contains(key)
    }

    /// Elements in ascending order; double-ended.
    pub(crate) fn iter(&self) -> imbl::ordset::Iter<'_, K, imbl::shared_ptr::DefaultSharedPtr> {
        self.set.iter()
    }

    /// Elements in `range`, ascending; double-ended. O(log n) to position
    /// plus the elements visited.
    pub(crate) fn range<R, Q>(
        &self,
        range: R,
    ) -> imbl::ordset::RangedIter<'_, K, imbl::shared_ptr::DefaultSharedPtr>
    where
        R: RangeBounds<Q>,
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.set.range(range)
    }

    /// Elements in exactly one of the two sets, ascending. Empty in O(1)
    /// for a shared root; otherwise a merge over both sets, O(n + m).
    pub(crate) fn symmetric_difference<'a>(&'a self, other: &'a Self) -> Vec<&'a K> {
        let mut difference = Vec::new();
        if self.set.ptr_eq(&other.set) {
            return difference;
        }
        let mut left = self.set.iter().peekable();
        let mut right = other.set.iter().peekable();
        loop {
            match (left.peek(), right.peek()) {
                (Some(l), Some(r)) => match l.cmp(r) {
                    std::cmp::Ordering::Less => difference.extend(left.next()),
                    std::cmp::Ordering::Greater => difference.extend(right.next()),
                    std::cmp::Ordering::Equal => {
                        left.next();
                        right.next();
                    }
                },
                (Some(_), None) => difference.extend(left.next()),
                (None, Some(_)) => difference.extend(right.next()),
                (None, None) => return difference,
            }
        }
    }
}

impl<K: Ord> SnapshotSet<K> {
    /// Whether `self == other`, for two sets each derived from `base`; see
    /// [`SnapshotMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        if self.set.ptr_eq(&other.set) {
            return true;
        }
        if self.hash != other.hash || self.set.len() != other.set.len() {
            return false;
        }
        crate::instrumentation::record_deterministic_work(
            2 * (usize::BITS - base.set.len().leading_zeros()) as usize,
        );
        let mut left = base.set.diff(&self.set);
        let mut right = base.set.diff(&other.set);
        loop {
            let (left, right) = match (left.next(), right.next()) {
                (None, None) => return true,
                (Some(left), Some(right)) => (left, right),
                _ => return false,
            };
            crate::instrumentation::record_deterministic_work(1);
            let same = match (left, right) {
                (imbl::ordset::DiffItem::Add(left), imbl::ordset::DiffItem::Add(right))
                | (imbl::ordset::DiffItem::Remove(left), imbl::ordset::DiffItem::Remove(right)) => {
                    left == right
                }
                _ => false,
            };
            if !same {
                return false;
            }
        }
    }
}

impl<K: Ord + Clone + Hash> SnapshotSet<K> {
    /// Inserts one element; `true` when it was absent. O(log n).
    pub(crate) fn insert(&mut self, key: K) -> bool {
        let added = entry_hash(&key);
        let replaced = self.set.insert(key);
        if replaced.is_none() {
            self.hash = self.hash.wrapping_add(added);
        }
        replaced.is_none()
    }

    /// Removes one element; `true` when it was present. O(log n).
    pub(crate) fn remove<Q>(&mut self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let Some(removed) = self.set.remove(key) else {
            return false;
        };
        self.hash = self.hash.wrapping_sub(entry_hash(&removed));
        true
    }

    /// Keeps only the elements `keep` accepts.
    ///
    /// O(n): it visits every element, and charges one work unit per
    /// element. Reserved for operations that are legitimately whole-set.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&K) -> bool) {
        crate::instrumentation::record_deterministic_work(self.set.len());
        let dropped = self
            .set
            .iter()
            .filter(|key| !keep(key))
            .cloned()
            .collect::<Vec<_>>();
        for key in dropped {
            self.remove(&key);
        }
    }

    pub(crate) fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<K> Clone for SnapshotSet<K> {
    /// O(1): the persistent root is shared.
    fn clone(&self) -> Self {
        Self {
            set: self.set.clone(),
            hash: self.hash,
        }
    }
}

impl<K> Default for SnapshotSet<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: std::fmt::Debug + Ord> std::fmt::Debug for SnapshotSet<K> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_set().entries(self.set.iter()).finish()
    }
}

impl<K> Hash for SnapshotSet<K> {
    /// O(1): the cached content hash and the length.
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
        state.write_usize(self.set.len());
    }
}

impl<K: Ord> PartialEq for SnapshotSet<K> {
    /// O(1) when the sets share a root or differ in cached hash or length;
    /// otherwise elementwise, charging one work unit per element compared.
    fn eq(&self, other: &Self) -> bool {
        if self.set.ptr_eq(&other.set) {
            return true;
        }
        if self.hash != other.hash || self.set.len() != other.set.len() {
            return false;
        }
        let mut compared = 0usize;
        let mut equal = true;
        for (left, right) in self.set.iter().zip(other.set.iter()) {
            compared += 1;
            if left != right {
                equal = false;
                break;
            }
        }
        crate::instrumentation::record_deterministic_work(compared);
        equal
    }
}

impl<K: Ord> Eq for SnapshotSet<K> {}

impl<K: Ord> PartialOrd for SnapshotSet<K> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: Ord> Ord for SnapshotSet<K> {
    /// Lexicographic over elements, as for `BTreeSet`. O(1) for a shared
    /// root; otherwise O(n) in the length of the common prefix.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.set.ptr_eq(&other.set) {
            return std::cmp::Ordering::Equal;
        }
        self.set.iter().cmp(other.set.iter())
    }
}

impl<K: Ord + Clone + Hash> FromIterator<K> for SnapshotSet<K> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let mut set = Self::new();
        set.extend(iter);
        set
    }
}

impl<K: Ord + Clone + Hash> Extend<K> for SnapshotSet<K> {
    fn extend<I: IntoIterator<Item = K>>(&mut self, iter: I) {
        for key in iter {
            self.insert(key);
        }
    }
}

impl<'a, K: Ord> IntoIterator for &'a SnapshotSet<K> {
    type Item = &'a K;
    type IntoIter = imbl::ordset::Iter<'a, K, imbl::shared_ptr::DefaultSharedPtr>;

    fn into_iter(self) -> Self::IntoIter {
        self.set.iter()
    }
}

impl<K: Ord + Clone> IntoIterator for SnapshotSet<K> {
    type Item = K;
    type IntoIter = imbl::ordset::ConsumingIter<K, imbl::shared_ptr::DefaultSharedPtr>;

    fn into_iter(self) -> Self::IntoIter {
        self.set.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash_of<T: Hash>(value: &T) -> u64 {
        entry_hash(value)
    }

    #[test]
    fn equal_content_hashes_equally_across_insertion_orders() {
        let forward = (0..64)
            .map(|key| (key, key * 3))
            .collect::<SnapshotMap<_, _>>();
        let backward = (0..64)
            .rev()
            .map(|key| (key, key * 3))
            .collect::<SnapshotMap<_, _>>();
        assert!(!forward.ptr_eq(&backward));
        assert_eq!(forward.content_hash(), backward.content_hash());
        assert_eq!(hash_of(&forward), hash_of(&backward));
        assert_eq!(forward, backward);

        let mut built = SnapshotMap::new();
        for key in 0..80 {
            built.insert(key, key * 3);
        }
        for key in 64..80 {
            built.remove(&key);
        }
        assert_eq!(built.content_hash(), forward.content_hash());
        assert_eq!(built, forward);

        let set_forward = (0..40).collect::<SnapshotSet<_>>();
        let set_backward = (0..40).rev().collect::<SnapshotSet<_>>();
        assert_eq!(set_forward.content_hash(), set_backward.content_hash());
        assert_eq!(set_forward, set_backward);
    }

    #[test]
    fn mutations_update_the_cached_hash() {
        let mut map = (0..8).map(|key| (key, key)).collect::<SnapshotMap<_, _>>();
        let original = map.content_hash();

        assert_eq!(map.insert(3, 99), Some(3));
        let replaced = map.content_hash();
        assert_ne!(replaced, original);
        assert_eq!(map.insert(3, 3), Some(99));
        assert_eq!(map.content_hash(), original);

        assert_eq!(map.insert(20, 1), None);
        assert_ne!(map.content_hash(), original);
        assert_eq!(map.remove(&20), Some(1));
        assert_eq!(map.content_hash(), original);
        assert_eq!(map.remove(&20), None);
        assert_eq!(map.content_hash(), original);

        map.retain(|key, _| key % 2 == 0);
        let evens = (0..8)
            .filter(|key| key % 2 == 0)
            .map(|key| (key, key))
            .collect::<SnapshotMap<_, _>>();
        assert_eq!(map.content_hash(), evens.content_hash());
        assert_eq!(map, evens);
        map.clear();
        assert_eq!(map.content_hash(), 0);
        assert!(map.is_empty());

        let mut set = (0..8).collect::<SnapshotSet<_>>();
        let original = set.content_hash();
        assert!(!set.insert(4));
        assert_eq!(set.content_hash(), original);
        assert!(set.insert(40));
        assert_ne!(set.content_hash(), original);
        assert!(set.remove(&40));
        assert_eq!(set.content_hash(), original);
    }

    #[test]
    fn range_and_order_match_the_std_collections() {
        let keys = [5, 1, 9, 3, 7, 11, 2];
        let map = keys
            .iter()
            .map(|key| (*key, key * 10))
            .collect::<SnapshotMap<_, _>>();
        let std_map = keys
            .iter()
            .map(|key| (*key, key * 10))
            .collect::<std::collections::BTreeMap<_, _>>();
        let pairs = |iter: &mut dyn Iterator<Item = (&i32, &i32)>| {
            iter.map(|(key, value)| (*key, *value)).collect::<Vec<_>>()
        };
        assert_eq!(pairs(&mut map.iter()), pairs(&mut std_map.iter()));
        assert_eq!(pairs(&mut map.range(3..9)), pairs(&mut std_map.range(3..9)));
        assert_eq!(
            pairs(&mut map.range(3..=9).rev()),
            pairs(&mut std_map.range(3..=9).rev())
        );
        assert_eq!(pairs(&mut map.range(..4)), pairs(&mut std_map.range(..4)));
        assert_eq!(pairs(&mut map.range(12..)), Vec::new());
        assert_eq!(format!("{map:?}"), format!("{std_map:?}"));

        let smaller = (0..3).map(|key| (key, 0)).collect::<SnapshotMap<_, _>>();
        let larger = (0..3)
            .map(|key| (key, i32::from(key == 2)))
            .collect::<SnapshotMap<_, _>>();
        assert!(smaller < larger);
        assert_eq!(smaller.cmp(&smaller.clone()), std::cmp::Ordering::Equal);

        let set = keys.iter().copied().collect::<SnapshotSet<_>>();
        let std_set = keys
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            set.range(2..7).copied().collect::<Vec<_>>(),
            std_set.range(2..7).copied().collect::<Vec<_>>()
        );
        assert_eq!(format!("{set:?}"), format!("{std_set:?}"));
    }

    #[test]
    fn equality_charges_only_the_elements_it_compares() {
        let n = 200;
        let map = (0..n).map(|key| (key, key)).collect::<SnapshotMap<_, _>>();
        let shared = map.clone();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| map == shared);
        assert!(equal);
        assert_eq!(work, 0, "shared roots compare without visiting entries");

        let rebuilt = (0..n)
            .rev()
            .map(|key| (key, key))
            .collect::<SnapshotMap<_, _>>();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| map == rebuilt);
        assert!(equal);
        assert_eq!(
            work, n as usize,
            "separately built equal maps compare every entry"
        );

        let mut different = map.clone();
        different.insert(7, 700);
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| map == different);
        assert!(!equal);
        assert_eq!(
            work, 0,
            "a differing cached hash decides without visiting entries"
        );
    }
}
