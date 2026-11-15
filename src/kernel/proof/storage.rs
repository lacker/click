//! Persistent storage primitives for the checked proof object.
//!
//! These containers make proof forks share unchanged state while keeping
//! updates proportional to their local delta. They carry no Surface Click
//! syntax and grant no semantic transition authority.

use crate::persistent::PersistentSet;
use std::sync::Arc;

/// Clone-on-write storage for proof-state collections.
#[derive(Clone)]
pub(crate) struct SharedVec<T>(Arc<Vec<T>>);

impl<T> Default for SharedVec<T> {
    fn default() -> Self {
        Self(Arc::new(Vec::new()))
    }
}

impl<T> std::ops::Deref for SharedVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T: Clone> std::ops::DerefMut for SharedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl<T> From<Vec<T>> for SharedVec<T> {
    fn from(value: Vec<T>) -> Self {
        Self(Arc::new(value))
    }
}

impl<'a, T> IntoIterator for &'a SharedVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Clone> SharedVec<T> {
    /// The entries appended after `ancestor`. `None` when this history is
    /// not a descendant of `ancestor`: shorter than it, or diverging from it
    /// within the shared prefix. Effect histories only append within one
    /// execution lineage, so a descendant that still shares the ancestor's
    /// storage is recognized without a scan; otherwise the prefix is
    /// compared element-wise in every build profile, because the suffix is
    /// what a join publishes as the exact arm delta.
    pub(crate) fn suffix_since(&self, ancestor: &Self) -> Option<&[T]>
    where
        T: PartialEq,
    {
        if self.0.len() < ancestor.0.len() {
            return None;
        }
        if !Arc::ptr_eq(&self.0, &ancestor.0) && self.0[..ancestor.0.len()] != ancestor.0[..] {
            return None;
        }
        Some(&self.0[ancestor.0.len()..])
    }
}

/// Immutable vector roots. Balanced concatenation shares child nodes; edits
/// copy only the selected tree path and a bounded underlying vector chunk.
#[derive(Clone)]
pub(crate) struct PersistentVector<T: Clone>(Arc<PersistentVectorData<T>>);
struct PersistentVectorData<T: Clone> {
    entries: Arc<PersistentVectorNode<T>>,
    flat: std::sync::OnceLock<Vec<T>>,
}
#[derive(Clone)]
enum PersistentVectorNode<T: Clone> {
    Leaf(imbl::Vector<T>),
    Branch {
        left: Arc<Self>,
        right: Arc<Self>,
        len: usize,
        height: usize,
    },
}
impl<T: Clone> PersistentVectorNode<T> {
    fn len(&self) -> usize {
        match self {
            Self::Leaf(entries) => entries.len(),
            Self::Branch { len, .. } => *len,
        }
    }
    fn height(&self) -> usize {
        match self {
            Self::Leaf(entries) => usize::from(!entries.is_empty()),
            Self::Branch { height, .. } => *height,
        }
    }
    fn get(&self, index: usize) -> Option<&T> {
        match self {
            Self::Leaf(entries) => entries.get(index),
            Self::Branch { left, right, .. } => {
                if index < left.len() {
                    left.get(index)
                } else {
                    right.get(index - left.len())
                }
            }
        }
    }
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        match self {
            Self::Leaf(entries) => entries.get_mut(index),
            Self::Branch { left, right, .. } => {
                if index < left.len() {
                    Arc::make_mut(left).get_mut(index)
                } else {
                    Arc::make_mut(right).get_mut(index - left.len())
                }
            }
        }
    }
    fn branch(left: Arc<Self>, right: Arc<Self>) -> Arc<Self> {
        crate::instrumentation::record_deterministic_work(1);
        Arc::new(Self::Branch {
            len: left
                .len()
                .checked_add(right.len())
                .expect("vector length overflow"),
            height: 1 + left.height().max(right.height()),
            left,
            right,
        })
    }
    fn balance(left: Arc<Self>, right: Arc<Self>) -> Arc<Self> {
        if left.height() > right.height() + 1 {
            let Self::Branch {
                left: a, right: b, ..
            } = left.as_ref()
            else {
                unreachable!()
            };
            if a.height() >= b.height() {
                Self::branch(a.clone(), Self::branch(b.clone(), right))
            } else {
                let Self::Branch {
                    left: c, right: d, ..
                } = b.as_ref()
                else {
                    unreachable!()
                };
                Self::branch(
                    Self::branch(a.clone(), c.clone()),
                    Self::branch(d.clone(), right),
                )
            }
        } else if right.height() > left.height() + 1 {
            let Self::Branch {
                left: a, right: b, ..
            } = right.as_ref()
            else {
                unreachable!()
            };
            if b.height() >= a.height() {
                Self::branch(Self::branch(left, a.clone()), b.clone())
            } else {
                let Self::Branch {
                    left: c, right: d, ..
                } = a.as_ref()
                else {
                    unreachable!()
                };
                Self::branch(
                    Self::branch(left, c.clone()),
                    Self::branch(d.clone(), b.clone()),
                )
            }
        } else {
            Self::branch(left, right)
        }
    }
    fn join(left: Arc<Self>, right: Arc<Self>) -> Arc<Self> {
        if left.len() == 0 {
            return right;
        }
        if right.len() == 0 {
            return left;
        }
        if left.height() > right.height() + 1 {
            let Self::Branch {
                left: a, right: b, ..
            } = left.as_ref()
            else {
                unreachable!()
            };
            Self::balance(a.clone(), Self::join(b.clone(), right))
        } else if right.height() > left.height() + 1 {
            let Self::Branch {
                left: a, right: b, ..
            } = right.as_ref()
            else {
                unreachable!()
            };
            Self::balance(Self::join(left, a.clone()), b.clone())
        } else {
            Self::branch(left, right)
        }
    }
}
impl<T: Clone> Clone for PersistentVectorData<T> {
    fn clone(&self) -> Self {
        Self {
            entries: self.entries.clone(),
            flat: Default::default(),
        }
    }
}
impl<T: Clone> Default for PersistentVector<T> {
    fn default() -> Self {
        Self::from(Vec::new())
    }
}
impl<T: Clone> PersistentVector<T> {
    pub(crate) fn len(&self) -> usize {
        self.0.entries.len()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub(crate) fn get(&self, index: usize) -> Option<&T> {
        self.0.entries.get(index)
    }
    pub(crate) fn iter(&self) -> PersistentVectorIter<'_, T> {
        PersistentVectorIter {
            entries: &self.0.entries,
            front: 0,
            back: self.len(),
        }
    }
    pub(crate) fn as_slice(&self) -> &[T] {
        self.as_slice_with(|_| {})
    }
    pub(crate) fn as_slice_with(&self, before: impl FnOnce(&Self)) -> &[T] {
        self.0.flat.get_or_init(|| {
            before(self);
            self.iter().cloned().collect()
        })
    }
    fn edit(&mut self) -> &mut PersistentVectorNode<T> {
        let data = Arc::make_mut(&mut self.0);
        data.flat.take();
        Arc::make_mut(&mut data.entries)
    }
    pub(crate) fn push(&mut self, value: T) {
        let sibling: Self = vec![value].into();
        self.append_shared(&sibling);
    }
    pub(crate) fn iter_mut(
        &mut self,
    ) -> imbl::vector::IterMut<'_, T, imbl::shared_ptr::DefaultSharedPtr> {
        // This operation explicitly edits every trace/provenance record.
        // Materialize that output-sized set once; indexed edits stay local.
        if matches!(self.0.entries.as_ref(), PersistentVectorNode::Branch { .. }) {
            let entries = self.iter().cloned().collect();
            *self.edit() = PersistentVectorNode::Leaf(entries);
        }
        let PersistentVectorNode::Leaf(entries) = self.edit() else {
            unreachable!()
        };
        entries.iter_mut()
    }
    pub(crate) fn append_shared(&mut self, other: &Self) {
        let entries = PersistentVectorNode::join(self.0.entries.clone(), other.0.entries.clone());
        *self = Self(Arc::new(PersistentVectorData {
            entries,
            flat: Default::default(),
        }));
    }
    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
pub(crate) struct PersistentVectorIter<'a, T: Clone> {
    entries: &'a PersistentVectorNode<T>,
    front: usize,
    back: usize,
}
impl<'a, T: Clone> Iterator for PersistentVectorIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.front == self.back {
            return None;
        }
        let index = self.front;
        self.front += 1;
        self.entries.get(index)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.back - self.front;
        (len, Some(len))
    }
}
impl<T: Clone> DoubleEndedIterator for PersistentVectorIter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front == self.back {
            return None;
        }
        self.back -= 1;
        self.entries.get(self.back)
    }
}
impl<T: Clone> ExactSizeIterator for PersistentVectorIter<'_, T> {}
impl<T: Clone> From<Vec<T>> for PersistentVector<T> {
    fn from(entries: Vec<T>) -> Self {
        Self(Arc::new(PersistentVectorData {
            entries: Arc::new(PersistentVectorNode::Leaf(entries.into())),
            flat: Default::default(),
        }))
    }
}
impl<T: Clone> FromIterator<T> for PersistentVector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(entries: I) -> Self {
        Self::from(entries.into_iter().collect::<Vec<_>>())
    }
}
impl<T: Clone> Extend<T> for PersistentVector<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, entries: I) {
        self.append_shared(&entries.into_iter().collect());
    }
}
impl<T: Clone> std::ops::Index<usize> for PersistentVector<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        self.get(index).expect("vector index out of bounds")
    }
}
impl<T: Clone> std::ops::IndexMut<usize> for PersistentVector<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.edit()
            .get_mut(index)
            .expect("vector index out of bounds")
    }
}
impl<T: Clone> std::ops::Index<std::ops::Range<usize>> for PersistentVector<T> {
    type Output = [T];
    fn index(&self, range: std::ops::Range<usize>) -> &[T] {
        &self.as_slice()[range]
    }
}
impl<T: Clone> std::ops::Deref for PersistentVector<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}
impl<'a, T: Clone> IntoIterator for &'a PersistentVector<T> {
    type Item = &'a T;
    type IntoIter = PersistentVectorIter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<T: Clone + PartialEq> PartialEq for PersistentVector<T> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.iter().eq(other.iter())
    }
}
impl<T: Clone + Eq> Eq for PersistentVector<T> {}
impl<T: Clone + std::fmt::Debug> std::fmt::Debug for PersistentVector<T> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_list().entries(self.iter()).finish()
    }
}

/// Clone-on-write storage for one proof-state value.
#[derive(Clone)]
pub(crate) struct SharedValue<T>(Arc<T>);

impl<T: Default> Default for SharedValue<T> {
    fn default() -> Self {
        Self(Arc::new(T::default()))
    }
}

impl<T> std::ops::Deref for SharedValue<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T: Clone> std::ops::DerefMut for SharedValue<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl<T> From<T> for SharedValue<T> {
    fn from(value: T) -> Self {
        Self(Arc::new(value))
    }
}

impl<T: Clone> SharedValue<T> {
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

#[cfg(test)]
thread_local! {
    static SEQUENCE_COPIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Runs `op` and returns how many entries `PersistentSequence::to_vec`
/// copied on this thread while it ran.
#[cfg(test)]
pub(crate) fn measure_sequence_copies<R>(op: impl FnOnce() -> R) -> (R, usize) {
    let before = SEQUENCE_COPIES.with(std::cell::Cell::get);
    let result = op();
    let after = SEQUENCE_COPIES.with(std::cell::Cell::get);
    (result, after - before)
}

/// An append-only sequence whose forks share their complete history.
#[derive(Clone)]
pub(crate) struct PersistentSequence<T> {
    tail: Option<Arc<PersistentSequenceNode<T>>>,
    len: usize,
}

struct PersistentSequenceNode<T> {
    parent: Option<Arc<PersistentSequenceNode<T>>>,
    value: T,
}

impl<T> Default for PersistentSequence<T> {
    fn default() -> Self {
        Self { tail: None, len: 0 }
    }
}

impl<T> Drop for PersistentSequence<T> {
    fn drop(&mut self) {
        // Dropping an `Arc`-owned parent chain recursively drops every unique
        // parent and can exhaust the stack for ordinary large proof histories.
        // Unwrap the unique suffix iteratively. At the first shared ancestor,
        // releasing this sequence's reference is sufficient; whichever owner
        // eventually becomes unique performs the same iterative cleanup.
        let mut tail = self.tail.take();
        while let Some(node) = tail {
            let Ok(node) = Arc::try_unwrap(node) else {
                break;
            };
            tail = node.parent;
        }
    }
}

impl<T> PersistentSequence<T> {
    pub(crate) fn push(&mut self, value: T) {
        self.tail = Some(Arc::new(PersistentSequenceNode {
            parent: self.tail.clone(),
            value,
        }));
        self.len += 1;
    }

    pub(crate) fn clear(&mut self) {
        self.tail = None;
        self.len = 0;
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.tail.is_none()
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn iter(&self) -> PersistentSequenceIter<'_, T> {
        let mut nodes = Vec::with_capacity(self.len);
        let mut current = self.tail.as_deref();
        while let Some(node) = current {
            nodes.push(&node.value);
            current = node.parent.as_deref();
        }
        nodes.reverse();
        PersistentSequenceIter {
            entries: nodes.into_iter(),
        }
    }

    /// Return at most `limit` newest entries without materializing the full
    /// insertion ordered sequence. Persistent proof diagnostics use this
    /// tail view so report cost depends only on the displayed context.
    pub(crate) fn recent(&self, limit: usize) -> Vec<&T> {
        let mut entries = Vec::with_capacity(limit.min(self.len));
        let mut current = self.tail.as_deref();
        while entries.len() < limit {
            let Some(node) = current else { break };
            entries.push(&node.value);
            current = node.parent.as_deref();
        }
        entries
    }

    pub(crate) fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        #[cfg(test)]
        SEQUENCE_COPIES.with(|copies| copies.set(copies.get() + self.len));
        self.iter().cloned().collect()
    }

    /// The entries appended after `ancestor`'s tail, oldest first.
    ///
    /// Returns `None` when `ancestor` is not a prefix of this sequence by
    /// identity and visits only the appended suffix: a prefix lies exactly
    /// `self.len - ancestor.len` entries back, so the walk stops there.
    pub(crate) fn suffix_since(&self, ancestor: &Self) -> Option<Vec<T>>
    where
        T: Clone,
    {
        let appended = self.len.checked_sub(ancestor.len)?;
        let mut suffix = Vec::with_capacity(appended);
        let mut current = self.tail.clone();
        loop {
            if suffix.len() > appended {
                return None;
            }
            match (&current, &ancestor.tail) {
                (Some(node), Some(ancestor_tail)) if Arc::ptr_eq(node, ancestor_tail) => break,
                (None, None) => break,
                (Some(node), _) => {
                    suffix.push(node.value.clone());
                    current = node.parent.clone();
                }
                (None, Some(_)) => return None,
            }
        }
        suffix.reverse();
        Some(suffix)
    }

    /// The entries appended after the newest node an earlier call already
    /// visited, oldest first, and the visited entries just before them,
    /// newest first. Marks the returned entries visited, so forks that share
    /// a prefix read it once across calls: each call walks only its own
    /// suffix, stopping at the first node a fork already returned.
    pub(crate) fn unvisited_suffix(
        &self,
        visited: &mut std::collections::HashSet<usize>,
    ) -> (Vec<&T>, PersistentSequenceRevIter<'_, T>) {
        let mut suffix = Vec::new();
        let mut current = self.tail.as_deref();
        while let Some(node) = current {
            if !visited.insert(node as *const PersistentSequenceNode<T> as usize) {
                break;
            }
            suffix.push(&node.value);
            current = node.parent.as_deref();
        }
        suffix.reverse();
        (suffix, PersistentSequenceRevIter { current })
    }

    #[cfg(test)]
    pub(crate) fn shares_tail_with(&self, other: &Self) -> bool {
        match (&self.tail, &other.tail) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }

    #[cfg(test)]
    pub(crate) fn tail_strong_count(&self) -> Option<usize> {
        self.tail.as_ref().map(Arc::strong_count)
    }

    #[cfg(test)]
    pub(crate) fn tail_parent_is(&self, ancestor: &Self) -> bool {
        match (&self.tail, &ancestor.tail) {
            (Some(tail), Some(ancestor_tail)) => tail
                .parent
                .as_ref()
                .is_some_and(|parent| Arc::ptr_eq(parent, ancestor_tail)),
            _ => false,
        }
    }
}

impl<T: Clone> PersistentSequence<T> {
    /// Removes the newest entry while preserving any shared ancestor prefix.
    pub(crate) fn pop(&mut self) -> Option<T> {
        let tail = self.tail.take()?;
        let value = tail.value.clone();
        self.tail = tail.parent.clone();
        self.len -= 1;
        Some(value)
    }
}

/// Entries of a [`PersistentSequence`] from one node back to the first,
/// newest first, without collecting them.
pub(crate) struct PersistentSequenceRevIter<'a, T> {
    current: Option<&'a PersistentSequenceNode<T>>,
}

impl<'a, T> Iterator for PersistentSequenceRevIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.current?;
        self.current = node.parent.as_deref();
        Some(&node.value)
    }
}

pub(crate) struct PersistentSequenceIter<'a, T> {
    entries: std::vec::IntoIter<&'a T>,
}

impl<'a, T> Iterator for PersistentSequenceIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.entries.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.entries.size_hint()
    }
}

impl<T> ExactSizeIterator for PersistentSequenceIter<'_, T> {}

impl<T> DoubleEndedIterator for PersistentSequenceIter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.entries.next_back()
    }
}

impl<'a, T> IntoIterator for &'a PersistentSequence<T> {
    type Item = &'a T;
    type IntoIter = PersistentSequenceIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A deterministic insertion-ordered set with persistent exact membership.
#[derive(Clone)]
pub(crate) struct PersistentOrderedSet<T> {
    ordered: PersistentSequence<T>,
    exact: PersistentSet<T>,
}

impl<T> Default for PersistentOrderedSet<T> {
    fn default() -> Self {
        Self {
            ordered: PersistentSequence::default(),
            exact: PersistentSet::default(),
        }
    }
}

impl<T: Clone + Ord> PersistentOrderedSet<T> {
    pub(crate) fn introduced_since(&self, ancestor: &Self) -> Option<Vec<T>> {
        self.ordered.suffix_since(&ancestor.ordered)
    }

    pub(crate) fn insert(&mut self, value: T) -> bool {
        if self.exact.contains(&value) {
            return false;
        }
        self.exact = self.exact.with_value(value.clone());
        self.ordered.push(value);
        true
    }

    pub(crate) fn contains(&self, value: &T) -> bool {
        self.exact.contains(value)
    }

    pub(crate) fn len(&self) -> usize {
        self.ordered.len()
    }

    pub(crate) fn iter(&self) -> PersistentSequenceIter<'_, T> {
        self.ordered.iter()
    }

    pub(crate) fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        self.ordered.shares_tail_with(&other.ordered) && self.exact.shares_root_with(&other.exact)
    }
}

impl<'a, T: Clone + Ord> IntoIterator for &'a PersistentOrderedSet<T> {
    type Item = &'a T;
    type IntoIter = PersistentSequenceIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn suffix_since_rejects_a_diverged_prefix() {
        let ancestor = SharedVec::from(vec![1, 2, 3]);
        let mut descendant = ancestor.clone();
        descendant.push(4);
        assert_eq!(descendant.suffix_since(&ancestor), Some(&[4][..]));
        assert_eq!(ancestor.suffix_since(&ancestor), Some(&[][..]));

        // Same length as the ancestor, different content: not a descendant.
        let diverged = SharedVec::from(vec![1, 2, 9]);
        assert_eq!(diverged.suffix_since(&ancestor), None);
        // Longer, but diverging inside the shared prefix.
        let diverged_longer = SharedVec::from(vec![1, 9, 3, 4]);
        assert_eq!(diverged_longer.suffix_since(&ancestor), None);
        // Shorter than the ancestor.
        let shorter = SharedVec::from(vec![1, 2]);
        assert_eq!(shorter.suffix_since(&ancestor), None);
    }

    #[test]
    fn recent_reads_only_requested_tail_shape() {
        let mut sequence = PersistentSequence::default();
        for value in 0..10_000 {
            sequence.push(value);
        }
        assert_eq!(sequence.recent(0), Vec::<&i32>::new());
        assert_eq!(
            sequence.recent(3).into_iter().copied().collect::<Vec<_>>(),
            vec![9999, 9998, 9997]
        );
        assert_eq!(sequence.recent(20_000).len(), 10_000);
    }

    #[test]
    fn forked_clause_history_clones_only_its_final_output() {
        struct Counted(usize, Arc<AtomicUsize>);
        impl Clone for Counted {
            fn clone(&self) -> Self {
                self.1.fetch_add(1, Ordering::Relaxed);
                Self(self.0, self.1.clone())
            }
        }

        for size in [8, 32, 128, 512] {
            let clones = Arc::new(AtomicUsize::new(0));
            let mut history = PersistentSequence::default();
            for index in 0..size {
                let mut next_path = history.clone();
                next_path.push(Counted(index, clones.clone()));
                history = next_path;
            }
            assert_eq!(clones.load(Ordering::Relaxed), 0);
            let output = history.iter().cloned().collect::<Vec<_>>();
            assert_eq!(output.len(), size);
            assert_eq!(output.last().map(|value| value.0), Some(size - 1));
            assert_eq!(clones.load(Ordering::Relaxed), size);
        }
    }
}

#[cfg(test)]
mod persistent_vector_publication_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Counted {
        value: usize,
        copies: Arc<AtomicUsize>,
    }
    impl Clone for Counted {
        fn clone(&self) -> Self {
            self.copies.fetch_add(1, Ordering::Relaxed);
            Self {
                value: self.value,
                copies: self.copies.clone(),
            }
        }
    }

    // Both concatenation directions must retain old roots without cloning descendant payloads.
    #[test]
    fn terminal_vector_concatenation_shares_its_unchanged_descendants() {
        for prepend in [false, true] {
            let samples = [128, 256, 512, 1024].map(|size| {
                let copies = Arc::new(AtomicUsize::new(0));
                let mut published = PersistentVector::default();
                for value in 0..size {
                    let mut sibling: PersistentVector<_> = vec![Counted {
                        value,
                        copies: copies.clone(),
                    }]
                    .into();
                    let old = published.clone();
                    assert!(published.shares_storage_with(&old));
                    if prepend {
                        sibling.append_shared(&published);
                        published = sibling;
                    } else {
                        published.append_shared(&sibling);
                    }
                    assert_eq!(old.len(), value);
                }
                assert!(published.iter().enumerate().all(|(index, item)| {
                    item.value == if prepend { size - index - 1 } else { index }
                }));
                copies.load(Ordering::Relaxed)
            });
            for pair in samples.windows(2) {
                assert!(
                    pair[1] * 4 <= pair[0] * 9,
                    "publication copied descendants quadratically, prepend={prepend}: {samples:?}"
                );
            }
        }
    }

    // Indexed and whole-vector edits must preserve other forks and already materialized slice views.
    #[test]
    fn terminal_vector_edits_and_slice_views_preserve_forks() {
        for size in [128, 256, 512, 1024] {
            let copies = Arc::new(AtomicUsize::new(0));
            let root: PersistentVector<_> = (0..size)
                .map(|value| Counted {
                    value,
                    copies: copies.clone(),
                })
                .collect();
            let mut fork = root.clone();
            let before = copies.load(Ordering::Relaxed);
            fork[size / 2].value = size;
            assert!(
                copies.load(Ordering::Relaxed) - before <= 128,
                "an indexed edit cannot clone unrelated payloads"
            );
            assert_eq!(root[size / 2].value, size / 2);
            assert_eq!(fork[size / 2].value, size);
            let retained_state = fork.clone();
            assert_eq!(retained_state.as_slice()[size / 2].value, size);
            fork.push(Counted {
                value: size + 1,
                copies: copies.clone(),
            });
            assert_eq!(retained_state.len(), size);
            assert_eq!(fork.len(), size + 1);
            for item in fork.iter_mut() {
                item.value += 1;
            }
            assert_eq!(fork[size / 2].value, size + 1);
            assert_eq!(retained_state[size / 2].value, size);
            drop(root);
            assert_eq!(retained_state[size / 2].value, size);
            let mut iter = retained_state.iter();
            assert_eq!(iter.next().unwrap().value, 0);
            assert_eq!(iter.next_back().unwrap().value, size - 1);
            assert_eq!(iter.len(), size - 2);
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/storage/persistent_vector_publication_tests.rs");
    }
}
