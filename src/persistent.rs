use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static NODE_ALLOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A persistent AVL map. Clones share the complete root; updating one key
/// copies only the search path and any rotation nodes.
#[derive(Clone)]
pub(crate) struct PersistentMap<K, V> {
    root: Option<Arc<Node<K, V>>>,
    len: usize,
}

struct Node<K, V> {
    key: Arc<K>,
    value: Arc<V>,
    left: Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
    height: u16,
}

impl<K, V> Default for PersistentMap<K, V> {
    fn default() -> Self {
        Self { root: None, len: 0 }
    }
}

impl<K: Ord, V> PersistentMap<K, V> {
    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            match key.cmp(current.key.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return Some(current.value.as_ref()),
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        None
    }

    pub(crate) fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    pub(crate) fn with_inserted(&self, key: K, value: V) -> Self {
        let (root, inserted) = insert_node(self.root.as_ref(), Arc::new(key), Arc::new(value));
        Self {
            root: Some(root),
            len: self.len + usize::from(inserted),
        }
    }

    pub(crate) fn iter(&self) -> PersistentMapIter<'_, K, V> {
        PersistentMapIter::new(self.root.as_deref())
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }

    #[cfg(test)]
    pub(crate) fn lookup_comparisons(&self, key: &K) -> usize {
        let mut comparisons = 0;
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            comparisons += 1;
            match key.cmp(current.key.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return comparisons,
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        comparisons
    }

    #[cfg(test)]
    pub(crate) fn shares_root_with(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<K: Ord + PartialEq, V: PartialEq> PartialEq for PersistentMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<K: Ord + Eq, V: Eq> Eq for PersistentMap<K, V> {}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for PersistentMap<K, V> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

pub(crate) struct PersistentMapIter<'a, K, V> {
    stack: Vec<&'a Node<K, V>>,
}

impl<'a, K, V> PersistentMapIter<'a, K, V> {
    fn new(root: Option<&'a Node<K, V>>) -> Self {
        let mut iter = Self { stack: Vec::new() };
        iter.push_left(root);
        iter
    }

    fn push_left(&mut self, mut node: Option<&'a Node<K, V>>) {
        while let Some(current) = node {
            self.stack.push(current);
            node = current.left.as_deref();
        }
    }
}

impl<'a, K, V> Iterator for PersistentMapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        self.push_left(node.right.as_deref());
        Some((node.key.as_ref(), node.value.as_ref()))
    }
}

#[derive(Clone)]
pub(crate) struct PersistentSet<T> {
    map: PersistentMap<T, ()>,
}

impl<T> Default for PersistentSet<T> {
    fn default() -> Self {
        Self {
            map: PersistentMap::default(),
        }
    }
}

impl<T: Ord> PersistentSet<T> {
    pub(crate) fn with_value(&self, value: T) -> Self {
        Self {
            map: self.map.with_inserted(value, ()),
        }
    }

    pub(crate) fn contains(&self, value: &T) -> bool {
        self.map.contains_key(value)
    }

    #[cfg(test)]
    pub(crate) fn lookup_comparisons(&self, value: &T) -> usize {
        self.map.lookup_comparisons(value)
    }

    #[cfg(test)]
    pub(crate) fn shares_root_with(&self, other: &Self) -> bool {
        self.map.shares_root_with(&other.map)
    }
}

fn node_height<K, V>(node: Option<&Arc<Node<K, V>>>) -> u16 {
    node.map_or(0, |node| node.height)
}

fn make_node<K, V>(
    key: Arc<K>,
    value: Arc<V>,
    left: Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
) -> Arc<Node<K, V>> {
    #[cfg(test)]
    NODE_ALLOCATIONS.with(|allocations| allocations.set(allocations.get() + 1));
    Arc::new(Node {
        key,
        value,
        height: 1 + node_height(left.as_ref()).max(node_height(right.as_ref())),
        left,
        right,
    })
}

fn balance_node<K, V>(
    key: Arc<K>,
    value: Arc<V>,
    left: Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
) -> Arc<Node<K, V>> {
    let left_height = node_height(left.as_ref());
    let right_height = node_height(right.as_ref());
    if left_height > right_height + 1 {
        let left_node = left.as_ref().expect("left-heavy node has a left child");
        if node_height(left_node.left.as_ref()) >= node_height(left_node.right.as_ref()) {
            let new_right = make_node(key, value, left_node.right.clone(), right);
            return make_node(
                left_node.key.clone(),
                left_node.value.clone(),
                left_node.left.clone(),
                Some(new_right),
            );
        }
        let middle = left_node
            .right
            .as_ref()
            .expect("left-right-heavy node has a middle child");
        let new_left = make_node(
            left_node.key.clone(),
            left_node.value.clone(),
            left_node.left.clone(),
            middle.left.clone(),
        );
        let new_right = make_node(key, value, middle.right.clone(), right);
        return make_node(
            middle.key.clone(),
            middle.value.clone(),
            Some(new_left),
            Some(new_right),
        );
    }
    if right_height > left_height + 1 {
        let right_node = right.as_ref().expect("right-heavy node has a right child");
        if node_height(right_node.right.as_ref()) >= node_height(right_node.left.as_ref()) {
            let new_left = make_node(key, value, left, right_node.left.clone());
            return make_node(
                right_node.key.clone(),
                right_node.value.clone(),
                Some(new_left),
                right_node.right.clone(),
            );
        }
        let middle = right_node
            .left
            .as_ref()
            .expect("right-left-heavy node has a middle child");
        let new_left = make_node(key, value, left, middle.left.clone());
        let new_right = make_node(
            right_node.key.clone(),
            right_node.value.clone(),
            middle.right.clone(),
            right_node.right.clone(),
        );
        return make_node(
            middle.key.clone(),
            middle.value.clone(),
            Some(new_left),
            Some(new_right),
        );
    }
    make_node(key, value, left, right)
}

fn insert_node<K: Ord, V>(
    node: Option<&Arc<Node<K, V>>>,
    key: Arc<K>,
    value: Arc<V>,
) -> (Arc<Node<K, V>>, bool) {
    let Some(node) = node else {
        return (make_node(key, value, None, None), true);
    };
    match key.as_ref().cmp(node.key.as_ref()) {
        Ordering::Less => {
            let (left, inserted) = insert_node(node.left.as_ref(), key, value);
            (
                balance_node(
                    node.key.clone(),
                    node.value.clone(),
                    Some(left),
                    node.right.clone(),
                ),
                inserted,
            )
        }
        Ordering::Equal => (
            make_node(key, value, node.left.clone(), node.right.clone()),
            false,
        ),
        Ordering::Greater => {
            let (right, inserted) = insert_node(node.right.as_ref(), key, value);
            (
                balance_node(
                    node.key.clone(),
                    node.value.clone(),
                    node.left.clone(),
                    Some(right),
                ),
                inserted,
            )
        }
    }
}

#[cfg(test)]
pub(crate) fn persistent_node_allocations() -> usize {
    NODE_ALLOCATIONS.with(std::cell::Cell::get)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn persistent_map_forks_and_updates_scale_logarithmically() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut map = PersistentMap::default();
            for key in 0..size {
                map = map.with_inserted(key, key * 2);
            }
            let ancestor = map.clone();
            assert!(map.shares_root_with(&ancestor));

            let before = persistent_node_allocations();
            map = map.with_inserted(size, size * 2);
            let allocations = persistent_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 4 * logarithmic_height + 8;
            assert!(
                allocations <= allocation_bound,
                "size {size} local insertion allocated {allocations} map nodes (bound {allocation_bound})"
            );
            assert_eq!(ancestor.get(&size), None);
            assert_eq!(map.get(&size), Some(&(size * 2)));
            assert_eq!(
                map.iter()
                    .map(|(key, value)| (*key, *value))
                    .collect::<Vec<_>>(),
                (0..=size).map(|key| (key, key * 2)).collect::<Vec<_>>()
            );

            let before_update = persistent_node_allocations();
            let updated = map.with_inserted(size, 7);
            let update_allocations = persistent_node_allocations() - before_update;
            assert!(update_allocations <= allocation_bound);
            assert_eq!(map.get(&size), Some(&(size * 2)));
            assert_eq!(updated.get(&size), Some(&7));
        }
    }
}
