//! Persistent branch topology for the checked proof object.
//!
//! This module owns the soundness-critical identity and allocation rules for
//! proof branches and audited splits. The checked proof core supplies each
//! branch's obligation and semantic payload, but cannot construct or reuse
//! identities independently of this collection.

use crate::persistent::PersistentMap;

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

/// Persistent open branches paired with their lineage-local id allocator.
///
/// A retired branch id is never reused. Candidate forks share the persistent
/// map root, so a local update copies only the changed map paths.
#[derive(Clone)]
pub(crate) struct ProofBranches<B> {
    open: PersistentMap<BranchId, B>,
    next_id: u64,
}

impl<B: Clone> ProofBranches<B> {
    /// Creates a fresh proof's single root branch.
    pub(crate) fn root(branch: B) -> Self {
        Self {
            open: PersistentMap::default().with_inserted(BranchId::ROOT, branch),
            next_id: BranchId::ROOT.0 + 1,
        }
    }

    pub(crate) fn get(&self, at: BranchId) -> Option<&B> {
        self.open.get(&at)
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
                next_id: self.next_id + 1,
            },
        )
    }

    /// Replaces several completed child branches with their parent identity.
    pub(crate) fn join_at(
        &self,
        children: impl IntoIterator<Item = BranchId>,
        parent: BranchId,
        branch: B,
    ) -> Self {
        let mut open = self.open.clone();
        for child in children {
            debug_assert!(
                open.contains_key(&child),
                "join requires every child branch"
            );
            open = open.without_key(&child);
        }
        debug_assert!(
            !open.contains_key(&parent) && parent.0 < self.next_id,
            "join must restore a retired parent identity"
        );
        Self {
            open: open.with_inserted(parent, branch),
            next_id: self.next_id,
        }
    }

    /// Restores a parent after a fixed-width split whose infeasible reserved
    /// arms were never installed as open branches.
    pub(crate) fn join_reserved_at(
        &self,
        children: impl IntoIterator<Item = BranchId>,
        parent: BranchId,
        branch: B,
    ) -> Self {
        let mut open = self.open.clone();
        for child in children {
            debug_assert!(
                child.0 < self.next_id,
                "join requires identities reserved by this lineage"
            );
            open = open.without_key(&child);
        }
        debug_assert!(
            !open.contains_key(&parent) && parent.0 < self.next_id,
            "join must restore a retired parent identity"
        );
        Self {
            open: open.with_inserted(parent, branch),
            next_id: self.next_id,
        }
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

        let branches = branches.join_reserved_at(ids, BranchId::ROOT, "joined continuation");
        assert_eq!(branches.get(BranchId::ROOT), Some(&"joined continuation"));
        assert_eq!(branches.next_id_for_test(), 5);
    }
}
