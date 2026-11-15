//! A canonical persistent multiset of resource facts.
//!
//! Two resource contexts holding the same facts were told apart, or found
//! equal, by walking both fact lists: a context rebuilt with the facts it
//! started from (a call takes the caller's ownership and hands it back) is
//! equal to the one it was rebuilt from, and every fact set that met both
//! paid a walk of the whole context (`roadmap/scaling.md`). This set's shape
//! is a function of its contents alone, and its nodes are interned, so two
//! sets with the same facts share one root and compare by pointer.
//!
//! **Shape.** A treap ordered by fact, each node's priority the fact's
//! content hash, ties broken by fact order: for a given multiset there is
//! exactly one such tree, whatever order its facts were inserted and
//! removed in. Insertion and removal split and merge along one path,
//! expected O(log n).
//!
//! **Interning.** Every node is made through a thread-local table keyed by
//! its fact's hash, its count and its children's addresses, holding weak
//! references. A node whose fact, count and children equal a live node's is
//! that node. By induction from the leaves, two live trees of one table with
//! equal contents are the same tree. A weak reference keeps its node's
//! allocation, so no address in the table can be reused while it stands;
//! entries are only ever dropped once their node is gone.
//!
//! **Domains.** A tree built on one thread may be extended on another, whose
//! table did not make its older nodes. Each node records the table that made
//! it and whether its whole subtree came from that table. Two pure trees of
//! one table are equal exactly when their roots are one node; any other pair
//! is compared fact by fact.
use super::{ResourceFact, Variable};
use std::cmp::Ordering;
use std::sync::{Arc, Weak};

#[derive(Clone, Default)]
pub(in crate::kernel) struct CanonicalFactSet {
    root: Option<Arc<Node>>,
}

struct Node {
    fact: ResourceFact,
    count: u32,
    priority: u64,
    left: Option<Arc<Node>>,
    right: Option<Arc<Node>>,
    len: usize,
    domain: u64,
    /// Every node of this subtree was made by `domain`'s table.
    pure: bool,
    /// [`CanonicalFactSet::syntax_ceiling`] of this subtree, once asked.
    ceiling: std::sync::OnceLock<SyntaxCeiling>,
}

/// The greatest execution-range variable a fact's written syntax names, and
/// whether that syntax names a state.
pub(in crate::kernel) type SyntaxCeiling = (Option<Variable>, bool);

type Key = (u64, u32, usize, usize);

#[cfg(test)]
thread_local! {
    /// Sets walked fact by fact, for the scaling regression.
    static WALKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(in crate::kernel) fn canonical_fact_set_walks() -> usize {
    WALKS.with(std::cell::Cell::get)
}

thread_local! {
    static DOMAIN: u64 = {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_add(1, Ordering::Relaxed)
    };
    static TABLE: std::cell::RefCell<Table> = std::cell::RefCell::new(Table::default());
}

#[derive(Default)]
struct Table {
    nodes: std::collections::HashMap<Key, Vec<Weak<Node>>>,
    made_since_sweep: usize,
}

/// How many nodes a table makes between sweeps of its dead entries.
const SWEEP_INTERVAL: usize = 1 << 16;

fn address(node: &Option<Arc<Node>>) -> usize {
    node.as_ref().map_or(0, |node| Arc::as_ptr(node) as usize)
}

fn len(node: &Option<Arc<Node>>) -> usize {
    node.as_ref().map_or(0, |node| node.len)
}

fn subtree_pure(node: &Option<Arc<Node>>, domain: u64) -> bool {
    node.as_ref()
        .is_none_or(|node| node.pure && node.domain == domain)
}

/// The node holding `fact` `count` times over `left` and `right`: the live
/// one this thread's table already made, or a new one.
fn make(
    fact: &ResourceFact,
    count: u32,
    priority: u64,
    left: Option<Arc<Node>>,
    right: Option<Arc<Node>>,
) -> Arc<Node> {
    let key = (priority, count, address(&left), address(&right));
    let domain = DOMAIN.with(|domain| *domain);
    TABLE.with(|table| {
        let mut table = table.borrow_mut();
        if let Some(bucket) = table.nodes.get_mut(&key) {
            bucket.retain(|weak| weak.strong_count() > 0);
            for weak in bucket.iter() {
                if let Some(node) = weak.upgrade()
                    && node.domain == domain
                    && node.fact == *fact
                {
                    return node;
                }
            }
        }
        let pure = subtree_pure(&left, domain) && subtree_pure(&right, domain);
        let node = Arc::new(Node {
            fact: fact.clone(),
            count,
            priority,
            len: len(&left) + len(&right) + count as usize,
            left,
            right,
            domain,
            pure,
            ceiling: std::sync::OnceLock::new(),
        });
        table
            .nodes
            .entry(key)
            .or_default()
            .push(Arc::downgrade(&node));
        table.made_since_sweep += 1;
        if table.made_since_sweep >= SWEEP_INTERVAL {
            table.made_since_sweep = 0;
            table.nodes.retain(|_, bucket| {
                bucket.retain(|weak| weak.strong_count() > 0);
                !bucket.is_empty()
            });
        }
        node
    })
}

/// Whether `left` takes precedence over `right` as a subtree root.
fn outranks(left: &Node, right: &Node) -> bool {
    (left.priority, &left.fact) > (right.priority, &right.fact)
}

fn remake(node: &Node, left: Option<Arc<Node>>, right: Option<Arc<Node>>) -> Arc<Node> {
    make(&node.fact, node.count, node.priority, left, right)
}

/// The subtrees of `node` before `fact`, holding `fact`, and after it.
fn split(
    node: &Option<Arc<Node>>,
    fact: &ResourceFact,
) -> (Option<Arc<Node>>, Option<Arc<Node>>, Option<Arc<Node>>) {
    let Some(current) = node else {
        return (None, None, None);
    };
    match fact.cmp(&current.fact) {
        Ordering::Equal => (
            current.left.clone(),
            Some(current.clone()),
            current.right.clone(),
        ),
        Ordering::Less => {
            let (less, equal, greater) = split(&current.left, fact);
            (
                less,
                equal,
                Some(remake(current, greater, current.right.clone())),
            )
        }
        Ordering::Greater => {
            let (less, equal, greater) = split(&current.right, fact);
            (
                Some(remake(current, current.left.clone(), less)),
                equal,
                greater,
            )
        }
    }
}

/// The tree holding every fact of `left`, all before every fact of `right`.
fn merge(left: Option<Arc<Node>>, right: Option<Arc<Node>>) -> Option<Arc<Node>> {
    match (left, right) {
        (None, right) => right,
        (left, None) => left,
        (Some(left), Some(right)) => {
            if outranks(&left, &right) {
                let merged = merge(left.right.clone(), Some(right));
                Some(remake(&left, left.left.clone(), merged))
            } else {
                let merged = merge(Some(left), right.left.clone());
                Some(remake(&right, merged, right.right.clone()))
            }
        }
    }
}

impl CanonicalFactSet {
    /// One more occurrence of `fact`, whose content hash is `hash`.
    pub(in crate::kernel) fn with_inserted(&self, fact: &ResourceFact, hash: u64) -> Self {
        let (less, equal, greater) = split(&self.root, fact);
        let count = equal.as_ref().map_or(0, |node| node.count) + 1;
        let node = make(fact, count, hash, None, None);
        Self {
            root: merge(merge(less, Some(node)), greater),
        }
    }

    /// One occurrence of `fact` fewer; unchanged when it holds none.
    pub(in crate::kernel) fn without_one(&self, fact: &ResourceFact, hash: u64) -> Self {
        let (less, equal, greater) = split(&self.root, fact);
        let Some(equal) = equal else {
            return self.clone();
        };
        let middle = (equal.count > 1).then(|| make(fact, equal.count - 1, hash, None, None));
        Self {
            root: merge(merge(less, middle), greater),
        }
    }

    pub(in crate::kernel) fn len(&self) -> usize {
        len(&self.root)
    }

    /// The held facts' combined [`SyntaxCeiling`]: the greatest of their
    /// variables, and whether any names a state. Each node caches its
    /// subtree's answer, and interned nodes are shared by every context that
    /// holds them, so a context derived by one insertion computes only the
    /// nodes along that insertion's path rather than every held fact.
    ///
    /// `fact_ceiling` must be the one pure function every caller passes: the
    /// cache does not record which function filled it.
    pub(in crate::kernel) fn syntax_ceiling(
        &self,
        fact_ceiling: fn(&ResourceFact) -> SyntaxCeiling,
    ) -> SyntaxCeiling {
        fn subtree(
            node: &Option<Arc<Node>>,
            fact_ceiling: fn(&ResourceFact) -> SyntaxCeiling,
        ) -> SyntaxCeiling {
            let Some(node) = node else {
                return (None, false);
            };
            // Uncharged: a node fills its cache at most once, and every node
            // was made by an insertion that its context already paid for.
            *node.ceiling.get_or_init(|| {
                let (variable, retained_state) = fact_ceiling(&node.fact);
                let (left, left_state) = subtree(&node.left, fact_ceiling);
                let (right, right_state) = subtree(&node.right, fact_ceiling);
                (
                    variable.max(left).max(right),
                    retained_state || left_state || right_state,
                )
            })
        }
        subtree(&self.root, fact_ceiling)
    }

    /// The facts in fact order, each as often as it is held.
    fn sorted(&self) -> Sorted<'_> {
        #[cfg(test)]
        WALKS.with(|walks| walks.set(walks.get() + 1));
        let mut sorted = Sorted {
            stack: Vec::new(),
            current: None,
        };
        sorted.descend(self.root.as_deref());
        sorted
    }

    /// The multiset order: equal sets in O(1) when both are canonical in one
    /// table, otherwise their sorted facts compared in turn.
    pub(in crate::kernel) fn cmp_contents(&self, other: &Self) -> Ordering {
        match (&self.root, &other.root) {
            (None, None) => return Ordering::Equal,
            (Some(left), Some(right)) if Arc::ptr_eq(left, right) => return Ordering::Equal,
            _ => {}
        }
        self.sorted().cmp(other.sorted())
    }

    /// Whether both sets hold the same facts, in O(1) when both are
    /// canonical in one table.
    pub(in crate::kernel) fn same_contents(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(left), Some(right)) => {
                if Arc::ptr_eq(left, right) {
                    return true;
                }
                if left.pure && right.pure && left.domain == right.domain {
                    return false;
                }
                left.len == right.len && self.sorted().eq(other.sorted())
            }
            _ => false,
        }
    }

    #[cfg(test)]
    pub(in crate::kernel) fn shares_root_with(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

/// An in-order walk, so a comparison stops at the first difference.
struct Sorted<'a> {
    stack: Vec<&'a Node>,
    current: Option<(&'a Node, u32)>,
}

impl<'a> Sorted<'a> {
    fn descend(&mut self, mut node: Option<&'a Node>) {
        while let Some(current) = node {
            self.stack.push(current);
            node = current.left.as_deref();
        }
    }
}

impl<'a> Iterator for Sorted<'a> {
    type Item = &'a ResourceFact;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((node, remaining)) = self.current.as_mut()
                && *remaining > 0
            {
                *remaining -= 1;
                return Some(&node.fact);
            }
            let node = self.stack.pop()?;
            self.current = Some((node, node.count));
            self.descend(node.right.as_deref());
        }
    }
}

impl std::fmt::Debug for CanonicalFactSet {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CanonicalFactSet")
            .field("len", &self.len())
            .finish()
    }
}
