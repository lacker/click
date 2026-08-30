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
    /// The entries appended after `ancestor`, by length suffix. Effect
    /// histories only append within one execution lineage; the debug build
    /// verifies the shared prefix element-wise, and `None` reports a
    /// shorter-than-ancestor history (not a descendant).
    pub(crate) fn suffix_since(&self, ancestor: &Self) -> Option<&[T]>
    where
        T: PartialEq + std::fmt::Debug,
    {
        if self.0.len() < ancestor.0.len() {
            return None;
        }
        debug_assert!(
            self.0[..ancestor.0.len()] == ancestor.0[..],
            "an effect history diverged from its claimed ancestor"
        );
        Some(&self.0[ancestor.0.len()..])
    }

    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
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
    pub(crate) fn into_value(self) -> T {
        Arc::try_unwrap(self.0).unwrap_or_else(|shared| shared.as_ref().clone())
    }

    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
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

    pub(crate) fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }

    /// The entries appended after `ancestor`'s tail, oldest first.
    ///
    /// Returns `None` when `ancestor` is not a prefix of this sequence by
    /// identity and visits only the appended suffix.
    pub(crate) fn suffix_since(&self, ancestor: &Self) -> Option<Vec<T>>
    where
        T: Clone,
    {
        let mut suffix = Vec::with_capacity(self.len.saturating_sub(ancestor.len));
        let mut current = self.tail.clone();
        loop {
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
