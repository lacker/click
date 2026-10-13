//! Surface forms paired with the exact kernel propositions they lowered to.
//!
//! Recording a lowering records every nested pair of its connective
//! structure, so a proposition of `n` nodes has up to `n` recorded sub-pairs.
//! Each sub-pair is identified, not copied: every node of both trees is
//! interned bottom-up once, an atom by its value and a connective by its own
//! payload and its children's identities, so two nodes share an identity
//! exactly when they are equal and a connective's identity costs its payload
//! rather than its subtree. The trees themselves are copied once per
//! recording, and every recorded connective refers into that shared copy by
//! its preorder position. So recording is linear in the recorded trees, a
//! pair already recorded whole is not walked again, and a lookup costs its
//! query plus the depth of the answer's position.
use super::{
    ClickError, ClickProposition, ClickType, ContractExpression, SnapshotSelector,
    clone_click_proposition_iteratively, proof,
};
use crate::kernel::{Bitvector32Term, ConditionTerm, Pointer, Proposition, Sort, Variable};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::HashMap;
use std::sync::Arc;

/// Surface forms paired with the exact kernel propositions they lowered
/// to in one proof context.
#[derive(Clone, Debug, Default)]
pub struct SurfacePropositionMap {
    pub(in crate::surface) storage: Arc<SurfacePropositionStorage>,
}

#[derive(Clone, Debug, Default)]
pub(in crate::surface) struct SurfacePropositionStorage {
    /// Source names for qualified storage reads, independent of the heap
    /// snapshot. These are synthesis hints, never evidence of a fact.
    pub(in crate::surface) qualified_load_sources: PersistentMap<Pointer, ContractExpression>,
    /// Every interned kernel node: an atom by value, a connective by its
    /// payload and children's identities.
    kernel_atoms: PersistentMap<Arc<Proposition>, (NodeId, Arc<Proposition>)>,
    kernel_connectives: PersistentMap<KernelConnective, NodeId>,
    /// Every interned surface node, bucketed by a debug rendering of the atom
    /// or of the connective's payload and child identities. Exact equality
    /// inside a bucket preserves soundness even if two syntax variants ever
    /// acquire the same debug rendering.
    surface_atoms: PersistentMap<String, Vec<(Arc<ClickProposition>, NodeId)>>,
    surface_connectives: PersistentMap<String, Vec<(SurfaceConnective, NodeId)>>,
    /// Snapshot-blind keys of kernel connectives, by their children's keys.
    blind_connectives: PersistentMap<BlindConnective, NodeId>,
    /// Each recorded kernel's surface forms, in recording order.
    by_kernel: PersistentMap<NodeId, OrderedNodes<SurfaceRef>>,
    /// Each recorded surface's kernel lowerings, in recording order.
    by_surface: PersistentMap<NodeId, OrderedNodes<KernelRef>>,
    /// Recorded kernel facts grouped by a structural key that forgets only
    /// memory snapshot identities. Typed proof steps use this to recover a
    /// check-equivalent surface form without scanning ambient facts.
    by_snapshot_blind: PersistentMap<BlindKey, PersistentMap<NodeId, KernelRef>>,
    /// Kernel facts whose recorded surface form is one top-level
    /// predicate call. Checked predicate unfolds use this narrow bucket to
    /// recover an already-materialized body without scanning ambient facts.
    by_predicate: PersistentMap<String, PersistentMap<NodeId, KernelRef>>,
    /// Recorded universally quantified kernel facts.
    universal_kernels: PersistentMap<NodeId, KernelRef>,
    /// Pairs with a connective surface whose recording completed, so that
    /// recording them again would change nothing.
    complete: PersistentSet<(NodeId, NodeId)>,
    next_id: NodeId,
}

type NodeId = u32;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum KernelConnective {
    And(NodeId, NodeId),
    Or(NodeId, NodeId),
    Not(NodeId),
    Implies(NodeId, NodeId),
    ForAll {
        var: Variable,
        sort: Sort,
        body: NodeId,
    },
    Exists {
        name: String,
        var: Variable,
        sort: Sort,
        body: NodeId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SurfaceConnective {
    At {
        selector: SnapshotSelector,
        body: NodeId,
    },
    And(NodeId, NodeId),
    Or(NodeId, NodeId),
    Not(NodeId),
    Implies(NodeId, NodeId),
    ForAll {
        click_type: ClickType,
        name: String,
        written_name: Option<String>,
        body: NodeId,
    },
    Exists {
        click_type: ClickType,
        name: String,
        written_name: Option<String>,
        body: NodeId,
    },
    RangeAll {
        start: ContractExpression,
        end: ContractExpression,
        item: String,
        written_item: Option<String>,
        body: NodeId,
    },
    RangeAny {
        start: ContractExpression,
        end: ContractExpression,
        item: String,
        written_item: Option<String>,
        body: NodeId,
    },
}

/// [`proof::snapshot_blind_proposition_key`], by identity: an atom's own key,
/// a quantifier's exact identity (a quantifier's key is the exact
/// proposition), or an interned connective of such keys.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BlindKey {
    Atom(proof::SnapshotBlindPropositionKey),
    Exact(NodeId),
    Connective(NodeId),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BlindConnective {
    Implies(BlindKey, BlindKey),
    And(BlindKey, BlindKey),
    Or(BlindKey, BlindKey),
    Not(BlindKey),
}

/// Both trees of one recording, kept whole, with each node's subtree size in
/// preorder so that a position names a node.
#[derive(Debug)]
struct RecordedTrees {
    surface: ClickProposition,
    surface_sizes: Vec<u32>,
    kernel: Proposition,
    kernel_sizes: Vec<u32>,
}

/// A recorded node: an atom held by value, or a connective at a preorder
/// position of one recording's trees.
#[derive(Clone, Debug)]
enum NodeRef<T> {
    Atom(Arc<T>),
    Tree(Arc<RecordedTrees>, u32),
}

type KernelRef = NodeRef<Proposition>;
type SurfaceRef = NodeRef<ClickProposition>;

impl NodeRef<Proposition> {
    fn get(&self) -> &Proposition {
        match self {
            Self::Atom(atom) => atom,
            Self::Tree(trees, index) => {
                preorder_node(&trees.kernel, &trees.kernel_sizes, *index, kernel_children)
            }
        }
    }
}

impl NodeRef<ClickProposition> {
    fn get(&self) -> &ClickProposition {
        match self {
            Self::Atom(atom) => atom,
            Self::Tree(trees, index) => preorder_node(
                &trees.surface,
                &trees.surface_sizes,
                *index,
                surface_children,
            ),
        }
    }
}

/// Node identities in the order they were first added, with their nodes.
#[derive(Clone, Debug)]
struct OrderedNodes<R> {
    order: PersistentMap<u32, (NodeId, R)>,
    members: PersistentSet<NodeId>,
}

impl<R> Default for OrderedNodes<R> {
    fn default() -> Self {
        Self {
            order: PersistentMap::default(),
            members: PersistentSet::default(),
        }
    }
}

impl<R> OrderedNodes<R> {
    /// These nodes and `id` after them, or `None` when `id` is already here.
    fn with_added(&self, id: NodeId, node: impl FnOnce() -> R) -> Option<Self> {
        if self.members.contains(&id) {
            return None;
        }
        let position = u32::try_from(self.order.len()).expect("recorded forms fit in u32");
        Some(Self {
            order: self.order.with_inserted(position, (id, node())),
            members: self.members.with_value(id),
        })
    }

    fn nodes(&self) -> impl DoubleEndedIterator<Item = &(NodeId, R)> {
        self.order.iter().map(|(_, entry)| entry)
    }
}

/// A node's children: `(left, right)` of a binary connective, `(body,
/// None)` of a unary one, and nothing of an atom.
type Children<'a, T> = Option<(&'a T, Option<&'a T>)>;

fn kernel_children(proposition: &Proposition) -> Children<'_, Proposition> {
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => Some((left, Some(right))),
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => Some((body, None)),
        _ => None,
    }
}

fn surface_children(proposition: &ClickProposition) -> Children<'_, ClickProposition> {
    match proposition {
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => Some((left, Some(right))),
        ClickProposition::At {
            proposition: body, ..
        }
        | ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. }
        | ClickProposition::RangeAll { body, .. }
        | ClickProposition::RangeAny { body, .. } => Some((body, None)),
        _ => None,
    }
}

/// The node at preorder position `target`, one step per level from the root.
fn preorder_node<'a, T>(
    root: &'a T,
    sizes: &[u32],
    target: u32,
    children: impl Fn(&'a T) -> Children<'a, T>,
) -> &'a T {
    let mut node = root;
    let mut index = 0u32;
    while index != target {
        let (first, second) = children(node).expect("a preorder position lies below a connective");
        let second_index = index + 1 + sizes[index as usize + 1];
        match second {
            Some(second) if target >= second_index => {
                node = second;
                index = second_index;
            }
            _ => {
                node = first;
                index += 1;
            }
        }
    }
    node
}

/// A tree in preorder: each node, its children's positions, and its subtree
/// size.
struct Flattened<'a, T> {
    nodes: Vec<&'a T>,
    children: Vec<(u32, u32)>,
    sizes: Vec<u32>,
}

const NO_CHILD: u32 = u32::MAX;

fn flatten<'a, T>(root: &'a T, children_of: impl Fn(&'a T) -> Children<'a, T>) -> Flattened<'a, T> {
    let mut nodes = Vec::new();
    let mut children = Vec::new();
    let mut stack = vec![(root, NO_CHILD, false)];
    while let Some((node, parent, second)) = stack.pop() {
        let index = u32::try_from(nodes.len()).expect("a recorded tree fits in u32 nodes");
        nodes.push(node);
        children.push((NO_CHILD, NO_CHILD));
        if parent != NO_CHILD {
            let slot = &mut children[parent as usize];
            if second {
                slot.1 = index;
            } else {
                slot.0 = index;
            }
        }
        if let Some((first, second_child)) = children_of(node) {
            if let Some(second_child) = second_child {
                stack.push((second_child, index, true));
            }
            stack.push((first, index, false));
        }
    }
    let mut sizes = vec![1u32; nodes.len()];
    for index in (0..nodes.len()).rev() {
        let (first, second) = children[index];
        for child in [first, second] {
            if child != NO_CHILD {
                sizes[index] += sizes[child as usize];
            }
        }
    }
    Flattened {
        nodes,
        children,
        sizes,
    }
}

/// Where interning looks nodes up: [`Finder`] only finds, [`Inserter`] adds
/// every node it does not find.
trait Interner {
    fn kernel_atom(&mut self, atom: &Proposition) -> Option<(NodeId, Arc<Proposition>)>;
    fn kernel_connective(&mut self, connective: KernelConnective) -> Option<NodeId>;
    fn surface_atom(&mut self, atom: &ClickProposition) -> Option<(NodeId, Arc<ClickProposition>)>;
    fn surface_connective(&mut self, connective: SurfaceConnective) -> Option<NodeId>;
    fn blind_connective(&mut self, connective: BlindConnective) -> Option<NodeId>;
}

struct Finder<'a>(&'a SurfacePropositionStorage);

struct Inserter<'a>(&'a mut SurfacePropositionStorage);

fn find_surface_atom(
    storage: &SurfacePropositionStorage,
    key: &str,
    atom: &ClickProposition,
) -> Option<(NodeId, Arc<ClickProposition>)> {
    storage
        .surface_atoms
        .get(key)?
        .iter()
        .find_map(|(recorded, id)| (recorded.as_ref() == atom).then(|| (*id, recorded.clone())))
}

fn find_surface_connective(
    storage: &SurfacePropositionStorage,
    key: &str,
    connective: &SurfaceConnective,
) -> Option<NodeId> {
    storage
        .surface_connectives
        .get(key)?
        .iter()
        .find_map(|(recorded, id)| (recorded == connective).then_some(*id))
}

impl Interner for Finder<'_> {
    fn kernel_atom(&mut self, atom: &Proposition) -> Option<(NodeId, Arc<Proposition>)> {
        self.0.kernel_atoms.get(atom).cloned()
    }

    fn kernel_connective(&mut self, connective: KernelConnective) -> Option<NodeId> {
        self.0.kernel_connectives.get(&connective).copied()
    }

    fn surface_atom(&mut self, atom: &ClickProposition) -> Option<(NodeId, Arc<ClickProposition>)> {
        find_surface_atom(self.0, &format!("{atom:?}"), atom)
    }

    fn surface_connective(&mut self, connective: SurfaceConnective) -> Option<NodeId> {
        find_surface_connective(self.0, &format!("{connective:?}"), &connective)
    }

    fn blind_connective(&mut self, connective: BlindConnective) -> Option<NodeId> {
        self.0.blind_connectives.get(&connective).copied()
    }
}

impl Inserter<'_> {
    fn fresh_id(&mut self) -> NodeId {
        let id = self.0.next_id;
        self.0.next_id = id
            .checked_add(1)
            .expect("recorded surface nodes fit in u32 ids");
        id
    }
}

impl Interner for Inserter<'_> {
    fn kernel_atom(&mut self, atom: &Proposition) -> Option<(NodeId, Arc<Proposition>)> {
        if let Some(found) = self.0.kernel_atoms.get(atom) {
            return Some(found.clone());
        }
        let id = self.fresh_id();
        let atom = Arc::new(atom.clone());
        self.0.kernel_atoms.insert(atom.clone(), (id, atom.clone()));
        Some((id, atom))
    }

    fn kernel_connective(&mut self, connective: KernelConnective) -> Option<NodeId> {
        if let Some(id) = self.0.kernel_connectives.get(&connective) {
            return Some(*id);
        }
        let id = self.fresh_id();
        self.0.kernel_connectives.insert(connective, id);
        Some(id)
    }

    fn surface_atom(&mut self, atom: &ClickProposition) -> Option<(NodeId, Arc<ClickProposition>)> {
        let key = format!("{atom:?}");
        if let Some(found) = find_surface_atom(self.0, &key, atom) {
            return Some(found);
        }
        let id = self.fresh_id();
        let atom = Arc::new(clone_click_proposition_iteratively(atom));
        let mut bucket = self.0.surface_atoms.get(&key).cloned().unwrap_or_default();
        bucket.push((atom.clone(), id));
        self.0.surface_atoms.insert(key, bucket);
        Some((id, atom))
    }

    fn surface_connective(&mut self, connective: SurfaceConnective) -> Option<NodeId> {
        let key = format!("{connective:?}");
        if let Some(id) = find_surface_connective(self.0, &key, &connective) {
            return Some(id);
        }
        let id = self.fresh_id();
        let mut bucket = self
            .0
            .surface_connectives
            .get(&key)
            .cloned()
            .unwrap_or_default();
        bucket.push((connective, id));
        self.0.surface_connectives.insert(key, bucket);
        Some(id)
    }

    fn blind_connective(&mut self, connective: BlindConnective) -> Option<NodeId> {
        if let Some(id) = self.0.blind_connectives.get(&connective) {
            return Some(*id);
        }
        let id = self.fresh_id();
        self.0.blind_connectives.insert(connective, id);
        Some(id)
    }
}

/// Each node's identity, children before parents: `None` for a node an
/// [`Finder`] did not find, and for every node above one. An atom also has
/// its interned value.
struct Identities<T> {
    ids: Vec<Option<NodeId>>,
    atoms: Vec<Option<Arc<T>>>,
}

fn kernel_identities(
    interner: &mut impl Interner,
    tree: &Flattened<'_, Proposition>,
) -> Identities<Proposition> {
    let mut ids = vec![None; tree.nodes.len()];
    let mut atoms = vec![None; tree.nodes.len()];
    for index in (0..tree.nodes.len()).rev() {
        let (first, second) = tree.children[index];
        let child = |position: u32| ids[position as usize];
        let connective = match tree.nodes[index] {
            Proposition::And(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| KernelConnective::And(left, right)),
            Proposition::Or(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| KernelConnective::Or(left, right)),
            Proposition::Implies(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| KernelConnective::Implies(left, right)),
            Proposition::Not(_) => child(first).map(KernelConnective::Not),
            Proposition::ForAll { var, sort, .. } => {
                child(first).map(|body| KernelConnective::ForAll {
                    var: *var,
                    sort: sort.clone(),
                    body,
                })
            }
            Proposition::Exists {
                name, var, sort, ..
            } => child(first).map(|body| KernelConnective::Exists {
                name: name.clone(),
                var: *var,
                sort: sort.clone(),
                body,
            }),
            atom => {
                if let Some((id, atom)) = interner.kernel_atom(atom) {
                    ids[index] = Some(id);
                    atoms[index] = Some(atom);
                }
                continue;
            }
        };
        ids[index] = connective.and_then(|connective| interner.kernel_connective(connective));
    }
    Identities { ids, atoms }
}

fn surface_identities(
    interner: &mut impl Interner,
    tree: &Flattened<'_, ClickProposition>,
) -> Identities<ClickProposition> {
    let mut ids = vec![None; tree.nodes.len()];
    let mut atoms = vec![None; tree.nodes.len()];
    for index in (0..tree.nodes.len()).rev() {
        let (first, second) = tree.children[index];
        let child = |position: u32| ids[position as usize];
        let connective = match tree.nodes[index] {
            ClickProposition::At { selector, .. } => {
                child(first).map(|body| SurfaceConnective::At {
                    selector: selector.clone(),
                    body,
                })
            }
            ClickProposition::And(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| SurfaceConnective::And(left, right)),
            ClickProposition::Or(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| SurfaceConnective::Or(left, right)),
            ClickProposition::Implies(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| SurfaceConnective::Implies(left, right)),
            ClickProposition::Not(_) => child(first).map(SurfaceConnective::Not),
            ClickProposition::ForAll {
                click_type,
                name,
                written_name,
                ..
            } => child(first).map(|body| SurfaceConnective::ForAll {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: written_name.clone(),
                body,
            }),
            ClickProposition::Exists {
                click_type,
                name,
                written_name,
                ..
            } => child(first).map(|body| SurfaceConnective::Exists {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: written_name.clone(),
                body,
            }),
            ClickProposition::RangeAll {
                start,
                end,
                item,
                written_item,
                ..
            } => child(first).map(|body| SurfaceConnective::RangeAll {
                start: start.clone(),
                end: end.clone(),
                item: item.clone(),
                written_item: written_item.clone(),
                body,
            }),
            ClickProposition::RangeAny {
                start,
                end,
                item,
                written_item,
                ..
            } => child(first).map(|body| SurfaceConnective::RangeAny {
                start: start.clone(),
                end: end.clone(),
                item: item.clone(),
                written_item: written_item.clone(),
                body,
            }),
            atom => {
                if let Some((id, atom)) = interner.surface_atom(atom) {
                    ids[index] = Some(id);
                    atoms[index] = Some(atom);
                }
                continue;
            }
        };
        ids[index] = connective.and_then(|connective| interner.surface_connective(connective));
    }
    Identities { ids, atoms }
}

/// Each kernel node's snapshot-blind key, children before parents: `None`
/// where the key names a quantifier or connective key never interned.
fn blind_keys(
    interner: &mut impl Interner,
    tree: &Flattened<'_, Proposition>,
    ids: &[Option<NodeId>],
) -> Vec<Option<BlindKey>> {
    let mut keys: Vec<Option<BlindKey>> = vec![None; tree.nodes.len()];
    for index in (0..tree.nodes.len()).rev() {
        let (first, second) = tree.children[index];
        let child = |position: u32| keys[position as usize].clone();
        let connective = match tree.nodes[index] {
            Proposition::Implies(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| BlindConnective::Implies(left, right)),
            Proposition::And(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| BlindConnective::And(left, right)),
            Proposition::Or(..) => child(first)
                .zip(child(second))
                .map(|(left, right)| BlindConnective::Or(left, right)),
            Proposition::Not(_) => child(first).map(BlindConnective::Not),
            Proposition::ForAll { .. } | Proposition::Exists { .. } => {
                keys[index] = ids[index].map(BlindKey::Exact);
                continue;
            }
            atom => {
                keys[index] = Some(BlindKey::Atom(proof::snapshot_blind_proposition_key(atom)));
                continue;
            }
        };
        keys[index] = connective
            .and_then(|connective| interner.blind_connective(connective))
            .map(BlindKey::Connective);
    }
    keys
}

/// One recording's interned trees.
struct Recording<'a> {
    trees: Arc<RecordedTrees>,
    surface: Flattened<'a, ClickProposition>,
    surface_ids: Identities<ClickProposition>,
    kernel: Flattened<'a, Proposition>,
    kernel_ids: Identities<Proposition>,
    kernel_blind: Vec<Option<BlindKey>>,
    /// Structure checks already answered, by position pair.
    matches: HashMap<(u32, u32), bool>,
}

impl<'a> Recording<'a> {
    fn surface_node(&self, index: u32) -> &'a ClickProposition {
        self.surface.nodes[index as usize]
    }

    fn kernel_node(&self, index: u32) -> &'a Proposition {
        self.kernel.nodes[index as usize]
    }

    fn surface_id(&self, index: u32) -> NodeId {
        self.surface_ids.ids[index as usize].expect("a recorded surface node is interned")
    }

    fn kernel_id(&self, index: u32) -> NodeId {
        self.kernel_ids.ids[index as usize].expect("a recorded kernel node is interned")
    }

    fn surface_ref(&self, index: u32) -> SurfaceRef {
        match &self.surface_ids.atoms[index as usize] {
            Some(atom) => SurfaceRef::Atom(atom.clone()),
            None => SurfaceRef::Tree(self.trees.clone(), index),
        }
    }

    fn kernel_ref(&self, index: u32) -> KernelRef {
        match &self.kernel_ids.atoms[index as usize] {
            Some(atom) => KernelRef::Atom(atom.clone()),
            None => KernelRef::Tree(self.trees.clone(), index),
        }
    }

    /// Whether recording `(surface, kernel)` succeeds: whether the lowering's
    /// logical structure matches, by exactly the cases
    /// [`SurfacePropositionMap::record_one`] accepts.
    fn structure_matches(&mut self, surface: u32, kernel: u32) -> bool {
        if let Some(known) = self.matches.get(&(surface, kernel)) {
            return *known;
        }
        crate::instrumentation::record_deterministic_work(1);
        let (surface_first, surface_second) = self.surface.children[surface as usize];
        let (kernel_first, kernel_second) = self.kernel.children[kernel as usize];
        let answer = match (self.surface_node(surface), self.kernel_node(kernel)) {
            (ClickProposition::And(..), Proposition::And(..))
            | (ClickProposition::Or(..), Proposition::Or(..))
            | (ClickProposition::Implies(..), Proposition::Implies(..)) => {
                self.structure_matches(surface_first, kernel_first)
                    && self.structure_matches(surface_second, kernel_second)
            }
            (ClickProposition::Not(_), Proposition::ConditionIs(_, _)) => true,
            (ClickProposition::Not(_), Proposition::Not(_))
            | (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                self.structure_matches(surface_first, kernel_first)
            }
            (ClickProposition::Exists { .. }, Proposition::Exists { .. }) => true,
            (
                ClickProposition::And(..)
                | ClickProposition::Or(..)
                | ClickProposition::Implies(..),
                _,
            ) => {
                self.structure_matches(surface_first, kernel)
                    || self.structure_matches(surface_second, kernel)
            }
            (
                ClickProposition::ForAll { .. } | ClickProposition::Exists { .. },
                Proposition::Implies(_, _),
            ) => self.structure_matches(surface, kernel_second),
            (
                ClickProposition::Not(_)
                | ClickProposition::ForAll { .. }
                | ClickProposition::Exists { .. },
                _,
            ) => false,
            _ => true,
        };
        self.matches.insert((surface, kernel), answer);
        answer
    }
}

impl SurfacePropositionStorage {
    fn kernel_id(&self, kernel: &Proposition) -> Option<NodeId> {
        match kernel_children(kernel) {
            None => self.kernel_atoms.get(kernel).map(|(id, _)| *id),
            Some(_) => {
                kernel_identities(&mut Finder(self), &flatten(kernel, kernel_children)).ids[0]
            }
        }
    }

    fn surface_id(&self, surface: &ClickProposition) -> Option<NodeId> {
        surface_identities(&mut Finder(self), &flatten(surface, surface_children)).ids[0]
    }
}

impl SurfacePropositionMap {
    #[cfg(test)]
    pub(crate) fn shares_persistent_storage_with(&self, other: &Self) -> bool {
        let (left, right) = (&self.storage, &other.storage);
        left.qualified_load_sources
            .shares_root_with(&right.qualified_load_sources)
            && left.kernel_atoms.shares_root_with(&right.kernel_atoms)
            && left
                .kernel_connectives
                .shares_root_with(&right.kernel_connectives)
            && left.surface_atoms.shares_root_with(&right.surface_atoms)
            && left
                .surface_connectives
                .shares_root_with(&right.surface_connectives)
            && left.by_kernel.shares_root_with(&right.by_kernel)
            && left.by_surface.shares_root_with(&right.by_surface)
            && left
                .by_snapshot_blind
                .shares_root_with(&right.by_snapshot_blind)
            && left.by_predicate.shares_root_with(&right.by_predicate)
            && left
                .blind_connectives
                .shares_root_with(&right.blind_connectives)
            && left
                .universal_kernels
                .shares_root_with(&right.universal_kernels)
            && left.complete.shares_root_with(&right.complete)
            && left.next_id == right.next_id
    }

    /// Records that `surface` lowered to `kernel`, and so every nested pair
    /// of their logical structure. Charges one unit per node of each tree
    /// and per pair recorded.
    pub fn record_lowering(
        &mut self,
        surface: &ClickProposition,
        kernel: &Proposition,
    ) -> Result<(), ClickError> {
        let surface_tree = flatten(surface, surface_children);
        let kernel_tree = flatten(kernel, kernel_children);
        crate::instrumentation::record_deterministic_work(
            surface_tree.nodes.len() + kernel_tree.nodes.len(),
        );
        // A pair recorded whole before changes nothing when recorded again,
        // and finding that copies neither tree.
        if surface_children(surface).is_some() {
            let mut finder = Finder(&self.storage);
            let surface_id = surface_identities(&mut finder, &surface_tree).ids[0];
            let kernel_id = kernel_identities(&mut finder, &kernel_tree).ids[0];
            if let (Some(surface_id), Some(kernel_id)) = (surface_id, kernel_id)
                && self.storage.complete.contains(&(surface_id, kernel_id))
            {
                return Ok(());
            }
        }
        let trees = Arc::new(RecordedTrees {
            surface: clone_click_proposition_iteratively(surface),
            surface_sizes: surface_tree.sizes.clone(),
            kernel: crate::kernel::clone_proposition_iteratively(kernel),
            kernel_sizes: kernel_tree.sizes.clone(),
        });
        let mut inserter = Inserter(Arc::make_mut(&mut self.storage));
        let surface_ids = surface_identities(&mut inserter, &surface_tree);
        let kernel_ids = kernel_identities(&mut inserter, &kernel_tree);
        let kernel_blind = blind_keys(&mut inserter, &kernel_tree, &kernel_ids.ids);
        let mut recording = Recording {
            trees,
            surface: surface_tree,
            surface_ids,
            kernel: kernel_tree,
            kernel_ids,
            kernel_blind,
            matches: HashMap::new(),
        };
        self.record_from(&mut recording, 0, 0)
    }

    /// Records the pair at these positions and every pair below it as one
    /// unit: a failure forgets which pairs it completed, and keeps what it
    /// recorded.
    fn record_from(
        &mut self,
        recording: &mut Recording<'_>,
        surface: u32,
        kernel: u32,
    ) -> Result<(), ClickError> {
        let complete_before = self.storage.complete.clone();
        let mut pending = vec![(surface, kernel)];
        let mut result = Ok(());
        while let Some((surface, kernel)) = pending.pop() {
            if let Err(error) = self.record_one(recording, surface, kernel, &mut pending) {
                result = Err(error);
                break;
            }
        }
        if result.is_err() {
            Arc::make_mut(&mut self.storage).complete = complete_before;
        }
        result
    }

    fn record_one(
        &mut self,
        recording: &mut Recording<'_>,
        surface_index: u32,
        kernel_index: u32,
        pending: &mut Vec<(u32, u32)>,
    ) -> Result<(), ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        let surface = recording.surface_node(surface_index);
        let kernel = recording.kernel_node(kernel_index);
        let surface_id = recording.surface_id(surface_index);
        let kernel_id = recording.kernel_id(kernel_index);
        {
            let storage = Arc::make_mut(&mut self.storage);
            if surface_children(surface).is_some() {
                if storage.complete.contains(&(surface_id, kernel_id)) {
                    return Ok(());
                }
                storage.complete = storage.complete.with_value((surface_id, kernel_id));
            }
            if let ClickProposition::Comparison { left, right, .. } = surface {
                // Only a side that names a qualified object records anything
                // here, so the kernel form is resolved only for one. Resolving
                // restores every load the form mentions, the cached values of
                // any memory snapshot it carries included, and a statement's
                // fact carries the whole memory: doing it for every recorded
                // comparison made each `step()` cost the square of the cells
                // the proof knew.
                let qualified = [left, right].map(|side| qualified_object_access(side));
                if qualified.iter().any(Option::is_some) {
                    let resolved = crate::kernel::resolve_load_variables_from_registry(kernel);
                    if let Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(a, b)
                        | ConditionTerm::Bitvector64Equal(a, b),
                        _,
                    ) = &resolved
                    {
                        for (expression, term) in qualified.into_iter().zip([a, b]) {
                            if let Some(expression) = expression
                                && let Bitvector32Term::MemoryLoad(_, pointer, _) = term.as_ref()
                                && !storage
                                    .qualified_load_sources
                                    .contains_key(pointer.as_ref())
                            {
                                storage.qualified_load_sources = storage
                                    .qualified_load_sources
                                    .with_inserted(pointer.as_ref().clone(), expression.clone());
                            }
                        }
                    }
                }
            }
            if let ClickProposition::PredicateCall { name, .. } = surface {
                let existing = storage.by_predicate.get(name);
                if !existing.is_some_and(|facts| facts.contains_key(&kernel_id)) {
                    let facts = existing
                        .cloned()
                        .unwrap_or_default()
                        .with_inserted(kernel_id, recording.kernel_ref(kernel_index));
                    storage.by_predicate = storage.by_predicate.with_inserted(name.clone(), facts);
                }
            }
            if matches!(kernel, Proposition::ForAll { .. })
                && !storage.universal_kernels.contains_key(&kernel_id)
            {
                storage.universal_kernels = storage
                    .universal_kernels
                    .with_inserted(kernel_id, recording.kernel_ref(kernel_index));
            }
            let forms = storage
                .by_kernel
                .get(&kernel_id)
                .cloned()
                .unwrap_or_default();
            if let Some(forms) =
                forms.with_added(surface_id, || recording.surface_ref(surface_index))
            {
                storage.by_kernel = storage.by_kernel.with_inserted(kernel_id, forms);
            }
            let blind = recording.kernel_blind[kernel_index as usize]
                .clone()
                .expect("a recorded kernel node has an interned snapshot-blind key");
            let existing = storage.by_snapshot_blind.get(&blind);
            if !existing.is_some_and(|facts| facts.contains_key(&kernel_id)) {
                let facts = existing
                    .cloned()
                    .unwrap_or_default()
                    .with_inserted(kernel_id, recording.kernel_ref(kernel_index));
                storage.by_snapshot_blind = storage.by_snapshot_blind.with_inserted(blind, facts);
            }
            let lowerings = storage
                .by_surface
                .get(&surface_id)
                .cloned()
                .unwrap_or_default();
            if let Some(lowerings) =
                lowerings.with_added(kernel_id, || recording.kernel_ref(kernel_index))
            {
                storage.by_surface = storage.by_surface.with_inserted(surface_id, lowerings);
            }
        }
        let (surface_first, surface_second) = recording.surface.children[surface_index as usize];
        let (kernel_first, kernel_second) = recording.kernel.children[kernel_index as usize];
        match (surface, kernel) {
            (ClickProposition::And(..), Proposition::And(..))
            | (ClickProposition::Or(..), Proposition::Or(..))
            | (ClickProposition::Implies(..), Proposition::Implies(..)) => {
                pending.push((surface_second, kernel_second));
                pending.push((surface_first, kernel_first));
                Ok(())
            }
            // Click comparison negation is lowered by flipping the comparison
            // polarity, so either kernel boolean is possible (for example,
            // `not (x != 0)` becomes equality with polarity `true`).
            (ClickProposition::Not(_), Proposition::ConditionIs(_, _)) => Ok(()),
            (ClickProposition::Not(_), Proposition::Not(_))
            | (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                pending.push((surface_first, kernel_first));
                Ok(())
            }
            (ClickProposition::Exists { .. }, Proposition::Exists { .. }) => {
                // The existential's kernel body may include arithmetic
                // obligations scoped to its witness. It is not a lowering of
                // the written body alone, and that body is not usable outside
                // the binder. Record instantiated children when the witness
                // is opened, rather than assigning them incorrect spellings.
                Ok(())
            }
            // A connective's kernel form may collapse when one leg resolves
            // concretely (a materialized cell decides `i <= len` at a loop
            // exit, and the simplifier keeps only the live leg). Record the
            // whole kernel against whichever leg still matches its
            // structure; a kernel matching neither leg is a real
            // mislowering and still errors below.
            (
                ClickProposition::And(..)
                | ClickProposition::Or(..)
                | ClickProposition::Implies(..),
                _,
            ) if recording.structure_matches(surface_first, kernel_index)
                || recording.structure_matches(surface_second, kernel_index) =>
            {
                if self
                    .record_from(recording, surface_first, kernel_index)
                    .is_err()
                {
                    self.record_from(recording, surface_second, kernel_index)?;
                }
                Ok(())
            }
            // A quantified body that reads memory lowers to its loadability
            // premises implying the quantifier itself. The premises carry no
            // surface form of their own; record the surface quantifier
            // against the guarded conclusion.
            (
                ClickProposition::ForAll { .. } | ClickProposition::Exists { .. },
                Proposition::Implies(_, _),
            ) if recording.structure_matches(surface_index, kernel_second) => {
                self.record_from(recording, surface_index, kernel_second)
            }
            (ClickProposition::And(_, _), _)
            | (ClickProposition::Or(_, _), _)
            | (ClickProposition::Not(_), _)
            | (ClickProposition::Implies(_, _), _)
            | (ClickProposition::ForAll { .. }, _)
            | (ClickProposition::Exists { .. }, _) => {
                // The kernel form can embed whole memory snapshots; bound the
                // rendering so the diagnostic stays a diagnostic.
                let kernel = format!("{kernel:?}");
                let kernel = if kernel.len() > 600 {
                    format!("{}…", &kernel[..600])
                } else {
                    kernel
                };
                Err(ClickError::new(format!(
                    "surface proposition did not lower to matching logical structure: {surface:?} -> {kernel}"
                )))
            }
            _ => Ok(()),
        }
    }

    fn kernel_forms(&self, kernel: &Proposition) -> Option<&OrderedNodes<SurfaceRef>> {
        let id = self.storage.kernel_id(kernel)?;
        self.storage.by_kernel.get(&id)
    }

    fn surface_lowerings(&self, surface: &ClickProposition) -> Option<&OrderedNodes<KernelRef>> {
        let id = self.storage.surface_id(surface)?;
        self.storage.by_surface.get(&id)
    }

    pub(in crate::surface) fn kernels_written_by_predicate(
        &self,
        name: &String,
    ) -> impl Iterator<Item = &Proposition> {
        in_proposition_order(
            self.storage
                .by_predicate
                .get(name)
                .into_iter()
                .flat_map(|facts| facts.iter().map(|(_, node)| node)),
        )
    }

    pub fn surface(&self, kernel: &Proposition) -> Result<&ClickProposition, ClickError> {
        self.kernel_forms(kernel)
            .and_then(|forms| forms.nodes().next_back())
            .map(|(_, surface)| surface.get())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "kernel proposition has no recorded Click surface form: {kernel:?}"
                ))
            })
    }

    pub fn surfaces(&self, kernel: &Proposition) -> impl Iterator<Item = &ClickProposition> {
        self.kernel_forms(kernel)
            .into_iter()
            .flat_map(|forms| forms.nodes().map(|(_, surface)| surface.get()))
    }

    pub(in crate::surface) fn snapshot_blind_kernels(
        &self,
        kernel: &Proposition,
    ) -> impl Iterator<Item = &Proposition> {
        let tree = flatten(kernel, kernel_children);
        let mut finder = Finder(&self.storage);
        let ids = kernel_identities(&mut finder, &tree).ids;
        let key = blind_keys(&mut finder, &tree, &ids).swap_remove(0);
        in_proposition_order(
            key.and_then(|key| self.storage.by_snapshot_blind.get(&key))
                .into_iter()
                .flat_map(|facts| facts.iter().map(|(_, node)| node)),
        )
    }

    /// The recorded kernel facts that are not connectives, in proposition
    /// order: the ones among which a comparison, predicate or loadability
    /// fact is found.
    pub(in crate::surface) fn atomic_kernel_facts(&self) -> impl Iterator<Item = &Proposition> {
        self.storage
            .kernel_atoms
            .iter()
            .filter_map(|(atom, (id, _))| {
                self.storage
                    .by_kernel
                    .contains_key(id)
                    .then_some(atom.as_ref())
            })
    }

    /// The recorded universally quantified kernel facts, in proposition
    /// order.
    pub(in crate::surface) fn universal_kernel_facts(&self) -> impl Iterator<Item = &Proposition> {
        in_proposition_order(self.storage.universal_kernels.iter().map(|(_, node)| node))
    }

    pub fn available_kernel(
        &self,
        surface: &ClickProposition,
        available: &[Proposition],
    ) -> Option<&Proposition> {
        self.available_kernel_matching(surface, |kernel| available.contains(kernel))
    }

    pub(crate) fn available_kernel_matching(
        &self,
        surface: &ClickProposition,
        mut is_available: impl FnMut(&Proposition) -> bool,
    ) -> Option<&Proposition> {
        let mut matches = self
            .surface_lowerings(surface)?
            .nodes()
            .map(|(_, kernel)| kernel.get())
            .filter(|kernel| {
                crate::instrumentation::record_deterministic_work(1);
                is_available(kernel)
            });
        let kernel = matches.next()?;
        matches.next().is_none().then_some(kernel)
    }

    pub fn unique_kernel(&self, surface: &ClickProposition) -> Option<&Proposition> {
        let mut lowerings = self.surface_lowerings(surface)?.nodes();
        let (_, kernel) = lowerings.next()?;
        lowerings.next().is_none().then(|| kernel.get())
    }

    pub fn checked_surface<F>(
        &self,
        kernel: &Proposition,
        mut lower_in_current_state: F,
    ) -> Result<ClickProposition, ClickError>
    where
        F: FnMut(&ClickProposition) -> Result<Proposition, ClickError>,
    {
        let forms = self.kernel_forms(kernel).ok_or_else(|| {
            ClickError::new(format!(
                "kernel proposition has no recorded Click surface form: {kernel:?}"
            ))
        })?;
        let mut last_mismatch = None;
        for (_, surface) in forms.nodes().rev() {
            let surface = surface.get();
            match lower_in_current_state(surface) {
                Ok(lowered) if &lowered == kernel => {
                    return Ok(clone_click_proposition_iteratively(surface));
                }
                Ok(lowered) => {
                    last_mismatch = Some(format!(
                        "`{}` -> `{}`",
                        crate::surface::diagnostics::describe_click_proposition(surface),
                        crate::surface::proof_diagnostics::render::render_proposition(&lowered)
                    ))
                }
                Err(error) => {
                    last_mismatch = Some(format!(
                        "`{}` -> {}",
                        crate::surface::diagnostics::describe_click_proposition(surface),
                        error.raw_summary()
                    ))
                }
            }
        }
        Err(ClickError::new(format!(
            "none of the recorded surface forms lower to the proposition at the current proof state{}; expected `{}`",
            last_mismatch
                .map(|mismatch| format!(" (last mismatch: {mismatch})"))
                .unwrap_or_default(),
            crate::surface::proof_diagnostics::render::render_proposition(kernel),
        )))
    }
}

/// Recorded kernel nodes in proposition order.
fn in_proposition_order<'a>(
    nodes: impl Iterator<Item = &'a KernelRef>,
) -> std::vec::IntoIter<&'a Proposition> {
    let mut propositions = nodes.map(KernelRef::get).collect::<Vec<_>>();
    propositions.sort();
    propositions.into_iter()
}

/// The access a comparison side makes to a qualified object, with any
/// snapshot selector around it removed, or `None` when the side names
/// something else.
///
/// A qualified object reaches its cells through the accessors the language
/// writes on it: struct fields and one index per array dimension. Both are
/// looked through, so `alpha::values[0]` and `static_local::f::grid[0][1]`
/// are found the same way a bare `alpha::value` is. The whole accessor chain
/// is what gets returned, so the spelling reads back the cell the pointer
/// names.
fn qualified_object_access(side: &ContractExpression) -> Option<&ContractExpression> {
    let mut expression = side;
    while let ContractExpression::At {
        expression: inner, ..
    }
    | ContractExpression::Old(inner) = expression
    {
        expression = inner;
    }
    let mut base = expression;
    loop {
        base = match base {
            ContractExpression::Field { base: inner, .. } => inner,
            ContractExpression::Index(inner, _) => inner,
            ContractExpression::ArrayIndex { base: inner, .. } => inner,
            _ => break,
        };
    }
    matches!(base, ContractExpression::QualifiedC { .. }).then_some(expression)
}
