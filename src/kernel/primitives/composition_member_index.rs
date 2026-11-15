//! Candidate lookup over a context's stated resource compositions.
//!
//! A path states a composition at every call, fold, unfold and store, and
//! keeps each one: `resource_compositions` grows with the path. Separation
//! by ownership asks for a composition holding two given objects as distinct
//! owned members, and scanning every stated composition for one made each
//! such question linear in the path (`roadmap/scaling.md`). This index names
//! the compositions that can answer instead.
//!
//! **Keys.** A composition is listed under the base and block of owned
//! memory members, the keys a member lookup probes, and under the
//! `OwnedMemberKey` of owned members of other resources, the bucket a
//! direct match reads (`direct_match_candidate_positions`).
//!
//! **Incremental admission.** A state is listed only under the owned
//! members it holds beyond some earlier admitted state, its predecessor:
//! the last one of its own storage origin, read from the storage history, or
//! else the last admitted one or the root when its member index shares
//! enough persistent structure with them that the difference is smaller
//! than the state. Successive states of one resource context, a call's
//! partition beside the frame it was taken from, differ by a few facts, so
//! admission costs what changed, not what the state holds. A state with
//! no such predecessor is listed under all of its owned members. The one exception is the first composition
//! admitted, commonly the function's whole entry frame: it is not listed at
//! all but kept as the `root`, a candidate for every question, whose own
//! member indexes answer it. Holding one composition is then constant work,
//! as `ObjectEvidenceSources` holds its first source.
//!
//! **Completeness for pairs.** Let two members both be held by an admitted
//! state `S`. If `S` has no predecessor, it is listed under both members'
//! keys or is the root, which every question reads. If its predecessor lacks
//! one of the two, `S` is listed under that member's keys. Otherwise the
//! predecessor, admitted earlier, holds both, and the argument repeats on it. A question about a pair
//! that reads the candidates under both members' keys therefore reaches a
//! state holding both whenever any stated composition does. The answer it
//! derives from that state is the one `S` would give: owned members of a
//! valid composition are disjoint, so each object finds the same member.
use super::{MemoryRange, OwnedMemberKey, Pointer, PointerBlock, ResourceContext};
use crate::persistent::{PersistentMap, PersistentSet};

/// How far in size a predecessor candidate may be from the state it
/// lists: each step of distance is two more candidates, each a difference
/// walk of at most the state's size.
const NEAREST_SIZES: usize = 2;

#[derive(Clone, Default)]
pub(in crate::kernel) struct CompositionMemberIndex {
    /// Each admitted composition, by admission ordinal in this context.
    compositions: PersistentMap<u32, ResourceContext>,
    by_base: PersistentMap<Pointer, PersistentSet<u32>>,
    by_block: PersistentMap<PointerBlock, PersistentSet<u32>>,
    by_member: PersistentMap<OwnedMemberKey, PersistentSet<u32>>,
    /// The last state admitted from each storage origin. Holding it keeps
    /// the origin alive, so its address is never reused as a key.
    checkpoints: PersistentMap<usize, ResourceContext>,
    /// The latest composition admitted with each [`listed_size`]:
    /// predecessor candidates for a state of another origin, since a
    /// difference walk visits at least the difference in size.
    latest_by_size: PersistentMap<usize, u32>,
    /// The first admitted composition, unlisted; see the module comment.
    root: Option<u32>,
    /// The ordinal the next admitted composition takes.
    next: u32,
}

impl std::fmt::Debug for CompositionMemberIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CompositionMemberIndex")
            .field("compositions", &self.compositions.len())
            .finish()
    }
}

impl CompositionMemberIndex {
    /// Lists `resources`, a composition just stated, under the owned members
    /// it added since the last state of its origin admitted here.
    pub(in crate::kernel) fn admit(&mut self, resources: &ResourceContext) {
        let ordinal = self.next;
        self.next += 1;
        let origin = std::sync::Arc::as_ptr(&resources.storage.origin) as usize;
        let added = self
            .checkpoints
            .get(&origin)
            .and_then(|prior| resources.changed_owned_inputs_from(prior))
            .map(|changed| {
                changed
                    .into_iter()
                    .filter(|fact| resources.contains_exact_representation(fact))
                    .collect::<Vec<_>>()
            })
            .or_else(|| {
                let size = listed_size(resources);
                (0..=NEAREST_SIZES)
                    .flat_map(|distance| [size.checked_sub(distance), size.checked_add(distance)])
                    .flatten()
                    .filter_map(|size| self.latest_by_size.get(&size).copied())
                    .chain(self.root)
                    .collect::<std::collections::BTreeSet<_>>()
                    .into_iter()
                    .rev()
                    .filter_map(|prior| self.compositions.get(&prior))
                    .find_map(|prior| added_beyond(prior, resources))
            });
        self.latest_by_size = self
            .latest_by_size
            .with_inserted(listed_size(resources), ordinal);
        self.compositions = self.compositions.with_inserted(ordinal, resources.clone());
        self.checkpoints = self.checkpoints.with_inserted(origin, resources.clone());
        let added = match added {
            Some(added) => added,
            None if self.root.is_none() => {
                self.root = Some(ordinal);
                return;
            }
            None => resources.iter().cloned().collect(),
        };
        for fact in added {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(range) = fact.memory_own_range() {
                self.list(range, ordinal);
            } else if fact.is_own() {
                for key in OwnedMemberKey::listed(&fact) {
                    let listed = self.by_member.get(&key).cloned().unwrap_or_default();
                    self.by_member = self
                        .by_member
                        .with_inserted(key, listed.with_value(ordinal));
                }
            }
        }
    }

    /// The admitted compositions listed under any of `blocks` or `members`,
    /// owned non-memory members' keys, and the root, in admission order,
    /// each once.
    pub(in crate::kernel) fn listed_under_members<'k>(
        &self,
        blocks: impl IntoIterator<Item = &'k PointerBlock>,
        members: impl IntoIterator<Item = &'k OwnedMemberKey>,
    ) -> Vec<&ResourceContext> {
        self.listed_in(
            blocks
                .into_iter()
                .filter_map(|block| self.by_block.get(block))
                .chain(
                    members
                        .into_iter()
                        .filter_map(|member| self.by_member.get(member)),
                ),
        )
    }

    fn list(&mut self, range: &MemoryRange, ordinal: u32) {
        let base = range.base();
        let at_base = self.by_base.get(base).cloned().unwrap_or_default();
        self.by_base = self
            .by_base
            .with_inserted(base.clone(), at_base.with_value(ordinal));
        let at_block = self.by_block.get(&base.block).cloned().unwrap_or_default();
        self.by_block = self
            .by_block
            .with_inserted(base.block.clone(), at_block.with_value(ordinal));
    }

    /// The admitted compositions listed under any of `bases` or `blocks`, and
    /// the root, in admission order, each once.
    pub(in crate::kernel) fn listed_under<'k>(
        &self,
        bases: impl IntoIterator<Item = &'k Pointer>,
        blocks: impl IntoIterator<Item = &'k PointerBlock>,
    ) -> Vec<&ResourceContext> {
        self.listed_in(
            bases
                .into_iter()
                .filter_map(|base| self.by_base.get(base))
                .chain(
                    blocks
                        .into_iter()
                        .filter_map(|block| self.by_block.get(block)),
                ),
        )
    }

    /// Bounded candidates for automatic store preservation: the root and
    /// one unambiguous composition per written base. Unlike `listed_under`,
    /// this deliberately declines crowded historical buckets; explicit frame
    /// reasoning retains the complete candidate query.
    pub(in crate::kernel) fn directly_listed_under_bases<'k>(
        &self,
        bases: impl IntoIterator<Item = &'k Pointer>,
    ) -> Vec<&ResourceContext> {
        // With no listed deltas, only the root can answer. Avoid probing
        // every written base again for each cached read in this common case.
        if self.by_base.is_empty() {
            crate::instrumentation::record_deterministic_work(1);
            return self
                .root
                .and_then(|root| self.compositions.get(&root))
                .into_iter()
                .collect();
        }
        let mut ordinals = self
            .root
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        for base in bases {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(entries) = self.by_base.get(base)
                && entries.len() == 1
                && let Some(ordinal) = entries.iter().next()
            {
                ordinals.insert(*ordinal);
            }
        }
        ordinals
            .into_iter()
            .filter_map(|ordinal| self.compositions.get(&ordinal))
            .collect()
    }

    fn listed_in<'s>(
        &'s self,
        listed: impl Iterator<Item = &'s PersistentSet<u32>>,
    ) -> Vec<&'s ResourceContext> {
        let mut ordinals = self
            .root
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        for set in listed {
            for ordinal in set.iter() {
                crate::instrumentation::record_deterministic_work(1);
                ordinals.insert(*ordinal);
            }
        }
        ordinals
            .into_iter()
            .filter_map(|ordinal| self.compositions.get(&ordinal))
            .collect()
    }
}

/// The number of facts a difference walk compares: the memory facts and the
/// owned facts of other resources.
fn listed_size(resources: &ResourceContext) -> usize {
    resources.memory_input_facts().len() + resources.owned_non_memory_input_facts().len()
}

/// The memory and other owned facts `resources` holds beyond `prior`, when walking the
/// difference of their member indexes costs less than listing `resources`:
/// subtrees the two persistent indexes share are skipped, so a state
/// derived from `prior` by a few changes pays for those changes, and an
/// unrelated one stops after its own size.
fn added_beyond(
    prior: &ResourceContext,
    resources: &ResourceContext,
) -> Option<Vec<super::ResourceFact>> {
    let held = resources.memory_input_facts();
    let held_members = resources.owned_non_memory_input_facts();
    let size = listed_size(resources);
    let mut added = Vec::new();
    let changes = prior
        .memory_input_facts()
        .diff(held)
        .chain(prior.owned_non_memory_input_facts().diff(held_members));
    for (walked, change) in changes.enumerate() {
        if walked >= size {
            return None;
        }
        if let super::HashedOrdMapChange::Added(fact) = change {
            added.push(fact.clone());
        }
    }
    Some(added)
}
