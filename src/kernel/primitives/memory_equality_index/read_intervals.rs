//! Persistent interval lookup for the trusted kernel's paired resource index.
//!
//! The AVL tree is ordered by (start, occurrence) and each subtree retains its
//! maximum end. A covering-range query visits only output ranges and the paths
//! needed to find them; it never walks unrelated predecessors. Updates and
//! forks share roots, and deletions repair summaries on the copied search path.
use super::super::ResourceEntryId;
use super::AddressCoordinate;
use crate::persistent::{AvlNode, insert_node, node_height, record_persistent_work, remove_node};
use std::sync::Arc;

type Key = (AddressCoordinate, ResourceEntryId);
type Value = AddressCoordinate;
type Root = Option<Arc<Node>>;

#[derive(Clone, Debug, Default)]
pub(super) struct ReadIntervals {
    root: Root,
    len: usize,
}

#[derive(Debug)]
struct Node {
    key: Arc<Key>,
    value: Arc<Value>,
    max_end: Arc<Value>,
    left: Root,
    right: Root,
    height: u16,
}

impl AvlNode for Node {
    type Key = Key;
    type Value = Value;
    fn key(&self) -> &Arc<Key> {
        &self.key
    }
    fn value(&self) -> &Arc<Value> {
        &self.value
    }
    fn left(&self) -> &Root {
        &self.left
    }
    fn right(&self) -> &Root {
        &self.right
    }
    fn height(&self) -> u16 {
        self.height
    }
    fn make(key: Arc<Key>, value: Arc<Value>, left: Root, right: Root) -> Arc<Self> {
        make_node(key, value, left, right)
    }
}

impl ReadIntervals {
    pub(super) fn len(&self) -> usize {
        self.len
    }

    pub(super) fn insert(
        &mut self,
        start: AddressCoordinate,
        end: AddressCoordinate,
        entry: ResourceEntryId,
    ) {
        let (root, inserted) =
            insert_node(self.root.as_ref(), Arc::new((start, entry)), Arc::new(end));
        self.root = Some(root);
        self.len += usize::from(inserted);
    }

    pub(super) fn remove(&mut self, start: AddressCoordinate, entry: ResourceEntryId) {
        let (root, removed) = remove_node(self.root.as_ref(), &(start, entry));
        self.root = root;
        self.len -= usize::from(removed);
    }

    pub(super) fn covering(
        &self,
        start: &AddressCoordinate,
        end: &AddressCoordinate,
    ) -> CoveringIntervals {
        CoveringIntervals {
            pending: self.root.iter().cloned().collect(),
            start: start.clone(),
            end: end.clone(),
        }
    }

    /// Used only when a class merge shifts the smaller resource payload.
    pub(super) fn iter(
        &self,
    ) -> impl Iterator<Item = (&AddressCoordinate, &AddressCoordinate, ResourceEntryId)> {
        let mut stack = Vec::new();
        let mut current = self.root.as_deref();
        std::iter::from_fn(move || {
            while let Some(node) = current {
                record_persistent_work(1);
                stack.push(node);
                current = node.left.as_deref();
            }
            let node = stack.pop()?;
            current = node.right.as_deref();
            Some((&node.key.0, node.value.as_ref(), node.key.1))
        })
    }
}

/// Owns a shared root, so permission checking need not hold the cache lock.
/// Enumeration stops as soon as the caller accepts a readable occurrence.
pub(in crate::kernel::primitives) struct CoveringIntervals {
    pending: Vec<Arc<Node>>,
    start: AddressCoordinate,
    end: AddressCoordinate,
}

impl Iterator for CoveringIntervals {
    type Item = ResourceEntryId;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.pending.pop() {
            record_persistent_work(1);
            if node.max_end.as_ref() < &self.end {
                continue;
            }
            let starts_before = node.key.0 <= self.start;
            if starts_before && let Some(right) = &node.right {
                self.pending.push(right.clone());
            }
            if let Some(left) = &node.left {
                self.pending.push(left.clone());
            }
            if starts_before && node.value.as_ref() >= &self.end {
                return Some(node.key.1);
            }
        }
        None
    }
}

fn make_node(
    key: Arc<Key>,
    value: Arc<Value>,
    left: Option<Arc<Node>>,
    right: Option<Arc<Node>>,
) -> Arc<Node> {
    record_persistent_work(1);
    let mut max_end = value.clone();
    for child in [&left, &right].into_iter().flatten() {
        if child.max_end > max_end {
            max_end = child.max_end.clone();
        }
    }
    Arc::new(Node {
        max_end,
        key,
        value,
        height: 1 + node_height(left.as_ref()).max(node_height(right.as_ref())),
        left,
        right,
    })
}

#[cfg(test)]
mod tests {
    use super::super::AffineOffset;
    use super::*;
    use std::collections::BTreeMap;

    fn coordinate(value: i128) -> AddressCoordinate {
        AddressCoordinate(AffineOffset::constant(value))
    }

    fn validate(node: Option<&Node>) -> (u16, Option<AddressCoordinate>) {
        let Some(node) = node else { return (0, None) };
        let (left_height, left_max) = validate(node.left.as_deref());
        let (right_height, right_max) = validate(node.right.as_deref());
        assert!(left_height.abs_diff(right_height) <= 1);
        assert_eq!(node.height, 1 + left_height.max(right_height));
        let max_end = [Some(node.value.as_ref().clone()), left_max, right_max]
            .into_iter()
            .flatten()
            .max()
            .unwrap();
        assert_eq!(node.max_end.as_ref(), &max_end);
        (node.height, Some(max_end))
    }

    #[test]
    fn interval_updates_match_an_independent_covering_model() {
        let mut intervals = ReadIntervals::default();
        let mut model = BTreeMap::new();
        let mut seed = 17_u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed
        };
        for step in 0..1200 {
            let entry = next() % 256;
            let start = i128::from(entry) - 128;
            if next().is_multiple_of(3) {
                intervals.remove(coordinate(start), entry);
                model.remove(&(start, entry));
            } else {
                let end = start + i128::from(next() % 200 + 1);
                intervals.insert(coordinate(start), coordinate(end), entry);
                model.insert((start, entry), end);
            }
            assert_eq!(intervals.len(), model.len());
            validate(intervals.root.as_deref());
            let start = i128::from(next() % 512) - 256;
            let end = start + i128::from(next() % 64);
            let expected = model
                .iter()
                .filter_map(|((range_start, entry), range_end)| {
                    (*range_start <= start && *range_end >= end).then_some(*entry)
                })
                .collect::<std::collections::BTreeSet<_>>();
            let actual = intervals
                .covering(&coordinate(start), &coordinate(end))
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(actual, expected, "step {step}");
        }
        let snapshot = intervals.clone();
        for (start, entry) in model.keys() {
            intervals.remove(coordinate(*start), *entry);
            validate(intervals.root.as_deref());
        }
        assert_eq!(intervals.len(), 0);
        assert!(intervals.root.is_none());
        assert_eq!(snapshot.len(), model.len());
        assert_eq!(snapshot.iter().count(), model.len());
    }
}
