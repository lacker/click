//! Persistent branch topology for the checked proof object.
//!
//! This module owns the soundness-critical identity and allocation rules for
//! proof branches and audited splits. The checked proof core supplies each
//! branch's obligation and semantic payload, but cannot construct or reuse
//! identities independently of this collection.

use super::{PersistentOrderedSet, ProofFacts};
use crate::persistent::PersistentMap;
use std::sync::Arc;

/// Path-local state shared by one open proof branch.
///
/// `E` is an opaque language attachment during the boundary migration. The
/// kernel owns the fact and unfold state and the persistent branch shape; it
/// never interprets `E` as evidence.
#[derive(Clone)]
pub(crate) struct ProofBranchState<E> {
    pub(crate) facts: ProofFacts,
    pub(crate) unfolded_predicates: PersistentOrderedSet<String>,
    pub(crate) execution: Option<Arc<E>>,
}

/// One open branch: its current obligation and path-local state.
#[derive(Clone)]
pub(crate) struct ProofBranch<O, E> {
    pub(crate) obligation: O,
    pub(crate) state: ProofBranchState<E>,
}

impl<O: Clone, E: Clone> ProofBranch<O, E> {
    pub(crate) fn new(obligation: O, state: ProofBranchState<E>) -> Self {
        Self { obligation, state }
    }

    pub(crate) fn with_obligation(&self, obligation: O) -> Self {
        Self::new(obligation, self.state.clone())
    }

    pub(crate) fn with_state(&self, state: ProofBranchState<E>) -> Self {
        Self::new(self.obligation.clone(), state)
    }
}

/// Identity of one open semantic branch within a proof lineage.
///
/// Identity comparison is meaningful only along one ancestry chain or
/// against the recorded structure that allocated the id.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct BranchId(u64);

impl BranchId {
    pub(crate) const ROOT: Self = Self(1);
}

/// Identity of one audited split within a proof lineage.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SplitId(u64);

impl SplitId {
    pub(crate) fn owns<const ARMS: usize>(&self, branches: [BranchId; ARMS]) -> bool {
        branches
            .iter()
            .enumerate()
            .all(|(arm, branch)| branch.0 == self.0 + 1 + arm as u64)
    }

    pub(crate) fn follows(&self, branch: BranchId) -> bool {
        branch.0 < self.0
    }

    /// Whether `branch` is one of the `arms` identities this split reserved.
    /// A decided fixed-width split joins its one feasible arm in both
    /// positions, so this is the per-arm form of [`Self::owns`].
    pub(crate) fn reserves(&self, branch: BranchId, arms: usize) -> bool {
        branch.0 > self.0 && branch.0 <= self.0 + arms as u64
    }
}

/// Persistent open branches paired with their lineage-local id allocator.
///
/// A retired branch id is never reused. Candidate forks share the persistent
/// map root, so a local update copies only the changed map paths.
#[derive(Clone)]
pub(crate) struct ProofBranches<B> {
    open: PersistentMap<BranchId, B>,
    /// The checked judgment that created this proof lineage. Closing the root
    /// retires its branch identity, but finalization still needs to identify
    /// exactly which judgment the completed proof discharged.
    root: Arc<B>,
    next_id: u64,
}

impl<B: Clone> ProofBranches<B> {
    /// Creates a fresh proof's single root branch.
    pub(crate) fn root(branch: B) -> Self {
        Self {
            open: PersistentMap::default().with_inserted(BranchId::ROOT, branch.clone()),
            root: Arc::new(branch),
            next_id: BranchId::ROOT.0 + 1,
        }
    }

    pub(crate) fn root_branch(&self) -> &B {
        &self.root
    }

    pub(crate) fn get(&self, at: BranchId) -> Option<&B> {
        self.open.get(&at)
    }

    /// Whether this lineage has allocated the identity, including identities
    /// that are currently retired or reserved by a structural split.
    pub(crate) fn has_allocated(&self, at: BranchId) -> bool {
        at.0 >= BranchId::ROOT.0 && at.0 < self.next_id
    }

    #[cfg(test)]
    pub(crate) fn ids(&self) -> impl Iterator<Item = BranchId> + '_ {
        self.open.keys().copied()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (BranchId, &B)> + '_ {
        self.open.iter().map(|(id, branch)| (*id, branch))
    }

    /// Replaces an existing branch while preserving its identity.
    pub(crate) fn replace_at(&self, at: BranchId, branch: B) -> Self {
        debug_assert!(
            self.open.contains_key(&at),
            "branch refinement requires the addressed open branch"
        );
        Self {
            open: self.open.with_inserted(at, branch),
            root: self.root.clone(),
            next_id: self.next_id,
        }
    }

    /// Temporarily removes a branch without retiring or reallocating its id.
    pub(crate) fn without_at(&self, at: BranchId) -> Self {
        debug_assert!(
            self.open.contains_key(&at),
            "branch removal requires the addressed open branch"
        );
        Self {
            open: self.open.without_key(&at),
            root: self.root.clone(),
            next_id: self.next_id,
        }
    }

    /// Reinstalls a temporarily removed branch at its existing identity.
    pub(crate) fn insert_existing_at(&self, at: BranchId, branch: B) -> Self {
        debug_assert!(
            !self.open.contains_key(&at) && at.0 < self.next_id,
            "an existing branch identity must already belong to this lineage"
        );
        Self {
            open: self.open.with_inserted(at, branch),
            root: self.root.clone(),
            next_id: self.next_id,
        }
    }

    /// Closes a branch. Its identity remains retired in this lineage.
    pub(crate) fn close_at(&self, at: BranchId) -> Self {
        self.without_at(at)
    }

    /// Replaces one branch with a fixed number of labeled sibling branches.
    pub(crate) fn split_at<const ARMS: usize>(
        &self,
        at: BranchId,
        arms: [B; ARMS],
    ) -> (SplitId, [BranchId; ARMS], Self) {
        debug_assert!(
            self.open.contains_key(&at),
            "an audited split requires the addressed open branch"
        );
        let split = SplitId(self.next_id);
        let ids = std::array::from_fn(|arm| BranchId(self.next_id + 1 + arm as u64));
        let mut open = self.open.without_key(&at);
        for (id, branch) in ids.iter().zip(arms) {
            open = open.with_inserted(*id, branch);
        }
        (
            split,
            ids,
            Self {
                open,
                root: self.root.clone(),
                next_id: self.next_id + 1 + ARMS as u64,
            },
        )
    }

    /// Retires a parent and reserves the complete identity range for a split.
    /// Callers then install each feasible arm with [`Self::insert_existing_at`].
    pub(crate) fn begin_split<const ARMS: usize>(
        &self,
        at: BranchId,
    ) -> (SplitId, [BranchId; ARMS], Self) {
        debug_assert!(
            self.open.contains_key(&at),
            "an audited split requires the addressed open branch"
        );
        let split = SplitId(self.next_id);
        let ids = std::array::from_fn(|arm| BranchId(self.next_id + 1 + arm as u64));
        (
            split,
            ids,
            Self {
                open: self.open.without_key(&at),
                root: self.root.clone(),
                next_id: self.next_id + 1 + ARMS as u64,
            },
        )
    }

    /// Appends one independently generated branch.
    pub(crate) fn push(&self, branch: B) -> (BranchId, Self) {
        let id = BranchId(self.next_id);
        (
            id,
            Self {
                open: self.open.with_inserted(id, branch),
                root: self.root.clone(),
                next_id: self.next_id + 1,
            },
        )
    }

    /// Replaces several completed child branches with their parent identity.
    ///
    /// `None` when a child is not an open branch of this lineage or the
    /// parent is not a retired identity of it. These are real checks in
    /// every build profile: a join is the step that lets one arm's verdict
    /// stand for the split, so its lineage may not rest on a `debug_assert`.
    pub(crate) fn join_at(
        &self,
        children: impl IntoIterator<Item = BranchId>,
        parent: BranchId,
        branch: B,
    ) -> Option<Self> {
        let mut open = self.open.clone();
        for child in children {
            if !open.contains_key(&child) {
                return None;
            }
            open = open.without_key(&child);
        }
        if self.open.contains_key(&parent) || !self.has_allocated(parent) {
            return None;
        }
        Some(Self {
            open: open.with_inserted(parent, branch),
            root: self.root.clone(),
            next_id: self.next_id,
        })
    }

    /// Restores a parent after a fixed-width split whose infeasible reserved
    /// arms were never installed as open branches. `None` when a child was
    /// never allocated by this lineage or the parent is not retired.
    pub(crate) fn join_reserved_at(
        &self,
        children: impl IntoIterator<Item = BranchId>,
        parent: BranchId,
        branch: B,
    ) -> Option<Self> {
        let mut open = self.open.clone();
        for child in children {
            if !self.has_allocated(child) {
                return None;
            }
            open = open.without_key(&child);
        }
        if self.open.contains_key(&parent) || !self.has_allocated(parent) {
            return None;
        }
        Some(Self {
            open: open.with_inserted(parent, branch),
            root: self.root.clone(),
            next_id: self.next_id,
        })
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.open.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn next_id_for_test(&self) -> u64 {
        self.next_id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn branch_ids_are_monotonic_and_never_reused() {
        let branches = ProofBranches::root("root");
        let (first, branches) = branches.push("first");
        let branches = branches.close_at(first);
        let (second, branches) = branches.push("second");

        assert_ne!(first, second);
        assert_eq!(branches.get(second), Some(&"second"));
        assert_eq!(branches.next_id_for_test(), second.0 + 1);
    }

    #[test]
    fn fixed_width_split_reserves_infeasible_arm_identity() {
        let branches = ProofBranches::root("root");
        let (split, ids, branches) = branches.begin_split::<2>(BranchId::ROOT);
        let branches = branches.insert_existing_at(ids[0], "then");

        assert_eq!(split, SplitId(2));
        assert_eq!(ids, [BranchId(3), BranchId(4)]);
        assert_eq!(branches.get(ids[0]), Some(&"then"));
        assert_eq!(branches.get(ids[1]), None);

        let branches = branches
            .join_reserved_at(ids, BranchId::ROOT, "joined continuation")
            .expect("reserved arms join back to their retired parent");
        assert_eq!(branches.get(BranchId::ROOT), Some(&"joined continuation"));
        assert_eq!(branches.next_id_for_test(), 5);
    }

    #[test]
    fn join_rejects_missing_children_and_open_or_foreign_parents() {
        let branches = ProofBranches::root("root");
        let (split, ids, split_branches) = branches.split_at(BranchId::ROOT, ["then", "else"]);
        assert!(split.owns(ids));
        assert!(split.follows(BranchId::ROOT));
        assert!(ids.iter().all(|id| split.reserves(*id, 2)));
        assert!(!split.reserves(BranchId::ROOT, 2));
        assert!(!split.reserves(BranchId(ids[1].0 + 1), 2));

        // Both arms are still open: a join with one closed arm and one open
        // arm, or with an arm this lineage never allocated, is refused.
        let one_closed = split_branches.close_at(ids[0]);
        assert!(one_closed.join_at(ids, BranchId::ROOT, "joined").is_none());
        let unallocated = BranchId(ids[1].0 + 7);
        assert!(
            one_closed
                .join_at([ids[0], unallocated], BranchId::ROOT, "joined")
                .is_none()
        );
        assert!(
            one_closed
                .join_reserved_at([ids[0], unallocated], BranchId::ROOT, "joined")
                .is_none()
        );

        // The parent must be a retired identity of this lineage: not open,
        // and not an identity beyond the allocator.
        assert!(split_branches.join_at(ids, ids[0], "joined").is_none());
        assert!(
            split_branches
                .join_reserved_at(ids, unallocated, "joined")
                .is_none()
        );

        // The genuine join succeeds and restores the parent.
        let joined = split_branches
            .join_at(ids, BranchId::ROOT, "joined")
            .expect("both open arms join back to the retired root");
        assert_eq!(joined.get(BranchId::ROOT), Some(&"joined"));
        assert_eq!(joined.get(ids[0]), None);
        assert_eq!(joined.get(ids[1]), None);
    }
}
