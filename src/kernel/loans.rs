//! Shared-loan authority for views and synchronous borrowed-memory call receipts.
//!
//! A [`LoanLedger`] is immutable. Every update returns opaque checked
//! evidence tied to the exact predecessor state identity. The ledger deliberately
//! exposes the same participant and dependency transitions to ordinary calls,
//! named contracts and language frontends; memory authority stays in the
//! resource partition.

mod active_footprint;
mod exclusive_calls;
mod local_references;
pub(crate) mod mutex_calls;

use crate::kernel::{bits32_constant, constant_u32};
use exclusive_calls::{ExclusiveCallBinding, ExclusiveCallId, ExclusiveCallRecord};
use local_references::{LocalReferenceBinding, LocalReferenceRecord};
pub(in crate::kernel) use local_references::{LocalReferenceId, LocalScalarReference};

use super::functions::CheckedResourceFact;
use super::primitives::{
    MemorySplitOrigins, OwnedMemberKey, Pointer, PointerBlock, ResourceMemoryIntervalNode,
    memory_interval_ancestors, memory_interval_nodes, memory_range_is_proven_empty,
    memory_ranges_proven_overlapping,
};
use super::{
    MachineTerm, MemoryRange, PureFactContext, Resource, ResourceContext, ResourceDescription,
    ResourceFact, ResourceOccurrenceId, ResourceStateSource, ResourceTransferRole, Variable,
};
use crate::persistent::{PersistentMap, PersistentSet};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanParticipantId {
    arena: u64,
    ordinal: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanScopeId {
    arena: u64,
    ordinal: u64,
}

#[cfg(test)]
impl LoanScopeId {
    pub(crate) fn for_test(arena: u64, ordinal: u64) -> Self {
        Self { arena, ordinal }
    }

    pub(crate) fn arena_for_test(self) -> u64 {
        self.arena
    }

    pub(crate) fn ordinal_for_test(self) -> u64 {
        self.ordinal
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanId {
    arena: u64,
    ordinal: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanShareId {
    arena: u64,
    ordinal: u64,
}

/// A restriction a folded borrowing composite places on the scope of the
/// loan it packages: while the hold exists the scope cannot end, so the
/// owner behind the loan cannot be recovered and written while the composite
/// still describes it. A hold mints no share, scope, or recovery right, but
/// changes whether the scope may end and therefore changes the ledger identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanHoldId {
    arena: u64,
    ordinal: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewDescription {
    loan: LoanId,
    support: ResourceOccurrenceId,
    viewed: ResourceFact,
}

impl StableViewDescription {
    #[cfg(test)]
    pub(crate) fn viewed(&self) -> &ResourceFact {
        &self.viewed
    }

    #[cfg(test)]
    pub(crate) fn support(&self) -> ResourceOccurrenceId {
        self.support
    }
}

/// Identity and possession of one live loan share. This establishes a lifetime
/// dependency only: it grants no resource description, memory access, escrow
/// ownership, or close/recovery right. Every use rechecks the current ledger.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct LoanAuthorityBinding {
    loan: LoanId,
    scope: LoanScopeId,
    share: LoanShareId,
    support: ResourceOccurrenceId,
}

/// An opaque use permission for one initialized mutex. Unlike a view binding,
/// it carries no readable resource description. Possession is checked against
/// the current ledger whenever it is used.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct MutexUseBinding(LoanAuthorityBinding);

#[cfg(test)]
mod mutex_helper_binding_tests;

/// Exact root assumed at a modular boundary, retained for the preserving
/// return check. This receipt grants no close or recovery right.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexUseContractInput {
    holder: LoanParticipantId,
    pub(crate) usage: MutexUseBinding,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexUseLoan {
    scope: LoanScopeId,
    loan: LoanId,
    pub(crate) usage: MutexUseBinding,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ReborrowBinding {
    View(LoanViewBinding),
    MutexUse(MutexUseBinding),
}

impl ReborrowBinding {
    fn authority(&self) -> LoanAuthorityBinding {
        match self {
            Self::View(binding) => binding.authority(),
            Self::MutexUse(binding) => binding.0,
        }
    }
}

/// Exact binding from a resource occurrence to the live loan/share that
/// authorizes reading it. This is carried by checked state, never inferred by
/// searching the ambient ledger or resource frame.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanViewBinding {
    pub(crate) loan: LoanId,
    pub(crate) scope: LoanScopeId,
    pub(crate) share: LoanShareId,
    pub(crate) support: ResourceOccurrenceId,
    pub(crate) viewed: ResourceFact,
    /// Present on the binding of a folded borrowing composite (and on the
    /// body piece it restores when unfolded): the occurrence keeps this
    /// loan's scope open until the hold is released.
    pub(crate) hold: Option<LoanHoldId>,
}

impl LoanViewBinding {
    fn authority(&self) -> LoanAuthorityBinding {
        LoanAuthorityBinding {
            loan: self.loan,
            scope: self.scope,
            share: self.share,
            support: self.support,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LoanViewBindings {
    state: Arc<LoanViewBindingsState>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BoundViewKey {
    Memory(Pointer),
    Other(OwnedMemberKey),
}

impl BoundViewKey {
    fn of(fact: &ResourceFact) -> Self {
        match fact.memory_range() {
            Some(range) => Self::Memory(range.base().clone()),
            None => Self::Other(OwnedMemberKey::of(fact).expect("non-memory resource")),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct LoanViewBindingsState {
    pub(crate) identity: u64,
    pub(crate) map: PersistentMap<ResourceOccurrenceId, LoanViewBinding>,
    changes: imbl::Vector<(u64, ResourceOccurrenceId)>,
    by_view: PersistentMap<ResourceFact, PersistentSet<ResourceOccurrenceId>>,
    by_key: PersistentMap<BoundViewKey, PersistentSet<ResourceOccurrenceId>>,
}

impl LoanViewBindingsState {
    pub(crate) fn updated(
        &self,
        map: PersistentMap<ResourceOccurrenceId, LoanViewBinding>,
        changed: impl IntoIterator<Item = ResourceOccurrenceId>,
    ) -> Arc<Self> {
        let mut changes = self.changes.clone();
        let identity = next_loan_binding_identity();
        let mut by_view = self.by_view.clone();
        let mut by_key = self.by_key.clone();
        for occurrence in changed {
            changes.push_back((identity, occurrence));
            if let Some(old) = self.map.get(&occurrence) {
                remove_bound_occurrence(&mut by_view, &old.viewed, occurrence);
                remove_bound_occurrence(&mut by_key, &BoundViewKey::of(&old.viewed), occurrence);
            }
            if let Some(new) = map.get(&occurrence) {
                insert_bound_occurrence(&mut by_view, new.viewed.clone(), occurrence);
                insert_bound_occurrence(&mut by_key, BoundViewKey::of(&new.viewed), occurrence);
            }
        }
        Arc::new(Self {
            identity,
            map,
            changes,
            by_view,
            by_key,
        })
    }

    /// Bindings are a persistent branch-local journal. A shared prefix lets
    /// producer admission index metadata-only changes without scanning views.
    pub(crate) fn changed_occurrences_since(&self, prior: &Self) -> Vec<ResourceOccurrenceId> {
        if self.identity == prior.identity {
            return Vec::new();
        }
        // A source's history can branch. Reading both suffixes is necessary:
        // the current branch may restore an occurrence the other removed.
        let mut common = self.changes.len().min(prior.changes.len());
        while common > 0 && self.changes.get(common - 1) != prior.changes.get(common - 1) {
            crate::instrumentation::record_deterministic_work(1);
            common -= 1;
        }
        (common..self.changes.len())
            .map(|index| &self.changes[index])
            .chain((common..prior.changes.len()).map(|index| &prior.changes[index]))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .map(|(_, occurrence)| *occurrence)
            .collect()
    }
}

fn insert_bound_occurrence<K: Ord>(
    index: &mut PersistentMap<K, PersistentSet<ResourceOccurrenceId>>,
    key: K,
    occurrence: ResourceOccurrenceId,
) {
    let bucket = index
        .get(&key)
        .cloned()
        .unwrap_or_default()
        .with_value(occurrence);
    *index = index.with_inserted(key, bucket);
}

fn remove_bound_occurrence<K: Ord + Clone>(
    index: &mut PersistentMap<K, PersistentSet<ResourceOccurrenceId>>,
    key: &K,
    occurrence: ResourceOccurrenceId,
) {
    if let Some(bucket) = index.get(key) {
        let bucket = bucket.without_value(&occurrence);
        *index = if bucket.is_empty() {
            index.without_key(key)
        } else {
            index.with_inserted(key.clone(), bucket)
        };
    }
}

pub(crate) fn next_loan_binding_identity() -> u64 {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

impl PartialEq for LoanViewBindings {
    fn eq(&self, other: &Self) -> bool {
        (self.state.map.is_empty() && other.state.map.is_empty())
            || self.state.identity == other.state.identity
    }
}

impl Eq for LoanViewBindings {}

impl Hash for LoanViewBindings {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.state.map.is_empty() {
            0_u64.hash(state);
        } else {
            self.state.identity.hash(state);
        }
    }
}

impl Ord for LoanViewBindings {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.state.map.is_empty(), other.state.map.is_empty()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => self.state.identity.cmp(&other.state.identity),
        }
    }
}

impl PartialOrd for LoanViewBindings {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl LoanViewBindings {
    pub(crate) fn from_state(state: Arc<LoanViewBindingsState>) -> Self {
        Self { state }
    }

    pub(crate) fn state(&self) -> Arc<LoanViewBindingsState> {
        self.state.clone()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&ResourceOccurrenceId, &LoanViewBinding)> {
        self.state.map.iter()
    }

    pub(crate) fn get(&self, occurrence: &ResourceOccurrenceId) -> Option<&LoanViewBinding> {
        self.state.map.get(occurrence)
    }

    /// Nominate one bound occurrence, never enumerate observations or retry
    /// another binding after a failed coverage/liveness check. Exact bindings
    /// take priority; nonexact queries use a singleton resource bucket (or a
    /// singleton binding map for a checked alias).
    fn bound_view_candidate(&self, required: &ResourceFact) -> Option<ResourceOccurrenceId> {
        if self.state.map.is_empty() {
            return None;
        }
        if let Some(exact) = self.state.by_view.get(required) {
            return exact.iter().next().copied();
        }
        if let Some(bucket) = self.state.by_key.get(&BoundViewKey::of(required)) {
            return (bucket.len() == 1).then(|| *bucket.iter().next().unwrap());
        }
        (self.state.map.len() == 1).then(|| *self.state.map.iter().next().unwrap().0)
    }

    fn select_bound_view(
        &self,
        required: &ResourceFact,
        resources: &ResourceContext,
        assumptions: &PureFactContext,
    ) -> Option<ResourceOccurrenceId> {
        if self.state.map.is_empty() {
            return None;
        }
        let Some(occurrence) = self.bound_view_candidate(required) else {
            // Loop construction can retain metadata for earlier occurrences
            // beside a fresh live view. With no metadata nominee, select one
            // live view through the resource index and read its binding.
            // This is not a retry after a failed candidate check.
            let occurrence = resources.indexed_view_witness(required, assumptions)?;
            return self.get(&occurrence).map(|_| occurrence);
        };
        let held = resources.view_fact_for_occurrence(occurrence)?;
        // Binding metadata alone cannot turn an owned composite or an absent
        // occurrence into a view. Check only the nominated held occurrence.
        bound_view_covers_requirement(held, None, required, assumptions).then_some(occurrence)
    }

    /// Attach inherited authority to the occurrences just constructed by a
    /// resource producer. Neither context is enumerated to rediscover them.
    pub(crate) fn attach_to_inserted_views(
        &self,
        source: &ResourceContext,
        mut destination: ResourceContext,
        inserted: &[(ResourceFact, ResourceOccurrenceId)],
        assumptions: &PureFactContext,
    ) -> ResourceContext {
        if self.state.map.is_empty() {
            return destination;
        }
        for (fact, occurrence) in inserted {
            crate::instrumentation::record_deterministic_work(1);
            if fact.is_view()
                && let Some(source_occurrence) = self.select_bound_view(fact, source, assumptions)
                && let Some(binding) = self.get(&source_occurrence)
            {
                destination = destination.with_loan_dependency(*occurrence, binding.clone());
            }
        }
        destination
    }

    pub(crate) fn with_inserted(
        &self,
        occurrence: ResourceOccurrenceId,
        binding: LoanViewBinding,
    ) -> Self {
        if self.state.map.get(&occurrence) == Some(&binding) {
            return self.clone();
        }
        Self {
            state: self.state.updated(
                self.state.map.with_inserted(occurrence, binding),
                [occurrence],
            ),
        }
    }

    pub(crate) fn without(&self, occurrence: ResourceOccurrenceId) -> Self {
        if !self.state.map.contains_key(&occurrence) {
            return self.clone();
        }
        Self {
            state: self
                .state
                .updated(self.state.map.without_key(&occurrence), [occurrence]),
        }
    }
}

/// The dyadic index nodes under which a loan *stores* its memory range, or
/// `None` for a range the ledger keeps per block and compares by proven
/// overlap. Queries still use their own concrete interval nodes; every query
/// alias also checks its block's per-block ranges. A range based
/// on a pointer read from memory is kept that way even at constant bounds:
/// its constant displacement says nothing about where it lies relative to
/// another block, so an unproved separation from it is not a conflict, as for
/// any symbolic view (docs/internals/stable-views.md, "Footprints").
fn ledger_interval_nodes(range: &MemoryRange) -> Option<Vec<ResourceMemoryIntervalNode>> {
    if matches!(range.base().block, PointerBlock::LoadedPointer(_)) {
        return None;
    }
    memory_interval_nodes(range)
}

fn update_active_memory_index(
    index: &PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    range: &MemoryRange,
    loan: LoanId,
    insert: bool,
) -> Result<PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>, LoanRefusal> {
    let nodes = ledger_interval_nodes(range).ok_or(LoanRefusal::UnsupportedPartition)?;
    let mut index = index.clone();
    for node in nodes {
        let key_set = index.get(&node).cloned().unwrap_or_default();
        let key_set = if insert {
            key_set.with_value(loan)
        } else {
            key_set.without_value(&loan)
        };
        index = if key_set.is_empty() {
            index.without_key(&node)
        } else {
            index.with_inserted(node, key_set)
        };
    }
    Ok(index)
}

fn update_active_memory_subtree(
    subtree: &PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    range: &MemoryRange,
    loan: LoanId,
    insert: bool,
) -> Result<PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>, LoanRefusal> {
    let nodes = ledger_interval_nodes(range).ok_or(LoanRefusal::UnsupportedPartition)?;
    let mut subtree = subtree.clone();
    for node in nodes {
        for ancestor in memory_interval_ancestors(&node) {
            let key_set = subtree.get(&ancestor).cloned().unwrap_or_default();
            let key_set = if insert {
                key_set.with_value(loan)
            } else {
                key_set.without_value(&loan)
            };
            subtree = if key_set.is_empty() {
                subtree.without_key(&ancestor)
            } else {
                subtree.with_inserted(ancestor, key_set)
            };
        }
    }
    Ok(subtree)
}

fn symbolic_memory_ranges(ranges: &[MemoryRange]) -> Vec<MemoryRange> {
    ranges
        .iter()
        .filter(|range| ledger_interval_nodes(range).is_none())
        .cloned()
        .collect()
}

fn with_unindexed_memory(
    map: &PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<MemoryRange>>>,
    loan: LoanId,
    ranges: &[MemoryRange],
) -> PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<MemoryRange>>> {
    let mut map = map.clone();
    let mut by_block: BTreeMap<PointerBlock, Vec<MemoryRange>> = BTreeMap::new();
    for range in ranges {
        by_block
            .entry(range.base().block.clone())
            .or_default()
            .push(range.clone());
    }
    for (block, ranges) in by_block {
        let bucket = map.get(&block).cloned().unwrap_or_default();
        map = map.with_inserted(block, bucket.with_inserted(loan, ranges));
    }
    map
}

fn without_unindexed_memory(
    map: &PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<MemoryRange>>>,
    loan: LoanId,
    ranges: &[MemoryRange],
) -> PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<MemoryRange>>> {
    let mut map = map.clone();
    for range in ranges {
        let block = &range.base().block;
        let Some(bucket) = map.get(block) else {
            continue;
        };
        let bucket = bucket.without_key(&loan);
        map = if bucket.is_empty() {
            map.without_key(block)
        } else {
            map.with_inserted(block.clone(), bucket)
        };
    }
    map
}

/// Whether a range names no storage at all, which is the one shape the write
/// barrier may skip without looking at a single loan.
///
/// A backwards range is how a range says it is empty, and both endpoints are
/// read as the signed `int32` values they are. Read through
/// `MachineTerm::as_const`, a start of `-1` arrives as `4294967295` and
/// every range beginning below its base — `r[-1..3]` under a callee's
/// `mutable r[s..e]` called at `-1, 3` — claimed to be empty and took the
/// barrier's exit: no interval lookup, no symbolic comparison, no refusal,
/// for a range naming four real elements.
///
/// Undecided is not empty. A symbolic endpoint answers `false` here and goes
/// on to the barrier proper, which is where a range the index cannot hold is
/// refused rather than waved through.
fn memory_range_is_empty(range: &MemoryRange) -> bool {
    matches!(
        (
            range.signed_constant_start(),
            range.signed_constant_end(),
        ),
        (Some(start), Some(end)) if start >= end
    )
}

fn memory_range_aliases(range: &MemoryRange, assumptions: &PureFactContext) -> Vec<MemoryRange> {
    crate::kernel::search::ProofSearch::<LoanLedger>::loan_aliases(range, assumptions)
}

/// Whether a query range provably touches a protected range, compared
/// bytewise so that differing element widths cannot hide an overlap.
///
/// The polarity is deliberate and matches the rest of the resource algebra:
/// two symbolic ranges are separate unless they are proven to overlap. A
/// write reaches this check only with owned authority for its range, and
/// under stable-view semantics every caller must establish its owned and
/// viewed inputs as a partition before a call, so an owner-authorized write
/// inside the body is separate from every contract input view by the same
/// contract meaning that keeps two owners separate. The check therefore
/// refuses the writes that no partition can license: a store through the
/// viewed pointer itself, through a pointer assumed equal to it, or into a
/// concretely overlapping offset of the same object.
pub(crate) fn protected_range_proven_overlapping(
    query: &MemoryRange,
    protected: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    protected_range_proven_overlapping_with_separation(query, protected, assumptions, true)
}

pub(crate) fn protected_range_proven_overlapping_ignoring_separation(
    query: &MemoryRange,
    protected: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    protected_range_proven_overlapping_with_separation(query, protected, assumptions, false)
}

fn protected_range_proven_overlapping_with_separation(
    query: &MemoryRange,
    protected: &MemoryRange,
    assumptions: &PureFactContext,
    use_separation: bool,
) -> bool {
    let queries = memory_range_aliases(query, assumptions);
    let protected_ranges = memory_range_aliases(protected, assumptions);
    // Exact aliases can settle the whole comparison without initializing any
    // arithmetic search over unrelated facts, including when they are adjacent.
    let mut separated = false;
    for (query_index, query) in queries.iter().enumerate() {
        for (protected_index, protected) in protected_ranges.iter().enumerate() {
            // The original range comparison is charged by the loan query;
            // each additional alias is extra work for this check.
            if query_index != 0 || protected_index != 0 {
                crate::instrumentation::record_deterministic_work(1);
            }
            match protected_ranges_constant_overlap(query, protected) {
                Some(true) => return true,
                Some(false) => separated = true,
                None => {}
            }
        }
    }
    if separated {
        return false;
    }
    let byte_range = |range: &MemoryRange| {
        let (base, bytes) = range.byte_footprint();
        MemoryRange::new_with_element_width(base, MachineTerm::constant(0), bytes, 1)
    };
    queries.iter().any(|query| {
        protected_ranges.iter().any(|protected| {
            // A wide range has no 32-bit byte footprint. Its overlap is
            // decided on its own 64-bit bounds, and an explicit separation
            // vetoes it last, as in the byte comparison.
            if query.wide_bounds().is_some() || protected.wide_bounds().is_some() {
                return super::primitives::wide_memory_ranges_proven_overlapping(
                    query,
                    protected,
                    assumptions,
                ) && (!use_separation
                    || !assumptions
                        .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                            query, protected,
                        ));
            }
            let (query, protected) = (byte_range(query), byte_range(protected));
            let overlapping = if use_separation {
                memory_ranges_proven_overlapping
            } else {
                super::primitives::memory_ranges_proven_overlapping_ignoring_separation
            };
            overlapping(&query, &protected, assumptions)
                || overlapping(&protected, &query, assumptions)
        })
    })
}

fn protected_ranges_constant_overlap(query: &MemoryRange, protected: &MemoryRange) -> Option<bool> {
    // Compare concrete intervals in exact byte arithmetic. Negative offsets
    // and large widths must not wrap through a 32-bit byte-count term.
    let byte_bounds = |range: &MemoryRange| {
        let width = i64::from(range.element_width());
        let start = range.signed_constant_start()?;
        let end = range.signed_constant_end()?;
        (start < end).then_some(())?;
        Some((start.checked_mul(width)?, end.checked_mul(width)?))
    };
    let (query_start, query_end) = byte_bounds(query)?;
    let (protected_start, protected_end) = byte_bounds(protected)?;
    let delta = protected
        .base()
        .exact_element_delta_from_base(query.base(), 1, None)?;
    if !delta.is_constant() {
        return None;
    }
    let start = protected_start.checked_add(delta.constant)?;
    let end = protected_end.checked_add(delta.constant)?;
    Some(query_start < end && start < query_end)
}

/// Whether an active loan protects memory: any byte-backed loan, and any
/// loan of a composite head, whose body is memory whether or not the
/// one-level frontier enumerated any of it. The fail-closed barriers
/// (unknown loop write sets, branch joins) consult this count.
fn loan_protects_memory(memory_backing: &[MemoryRange], permitted: &[ResourceFact]) -> bool {
    !memory_backing.is_empty()
        || permitted
            .iter()
            .any(|fact| matches!(fact.resource(), Resource::Composite { .. }))
}

/// The authority a reborrow inherits from its parent loan. One description,
/// `viewed`, authorized the transition, so the child loan permits that
/// description alone and protects only the parent backing that lies within
/// it (docs/internals/stable-views.md):
///
/// - a memory view narrows to the viewed range itself, which the parent
///   already protects through a backing piece or through the escrowed head
///   the projection that exposed it was checked against;
/// - the head the parent's backing was checked against - always its first
///   permitted description - keeps that checked one-level frontier;
/// - any other description, in particular a projected nested composite
///   child, brings no byte backing of its own. Its bytes stay protected by
///   the parent entry, which remains live for the whole child scope because
///   the reborrow pins the parent's share.
///
/// The child therefore never protects bytes outside the parent's footprint,
/// and its own barrier registrations are the ones its end removes.
fn reborrowed_authority(
    parent: &LoanRecord,
    viewed: &ResourceFact,
) -> (Vec<ResourceFact>, Vec<MemoryRange>) {
    let memory_backing = if let Some(range) = viewed.memory_range() {
        vec![range.clone()]
    } else if parent.permitted.first() == Some(viewed) {
        parent.memory_backing.clone()
    } else {
        Vec::new()
    };
    (vec![viewed.clone()], memory_backing)
}

/// A read derived from ownership in the current context. This is useful for
/// checking the owner's own computation, but it is not transferable loan
/// authority and contains no loan identity.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OwnedResourceObservation {
    support: ResourceOccurrenceId,
    viewed: ResourceFact,
}

impl OwnedResourceObservation {
    #[cfg(test)]
    pub(crate) fn new(support: ResourceOccurrenceId, owned: &ResourceFact) -> Option<Self> {
        owned.is_own().then(|| Self {
            support,
            viewed: ResourceFact::View(owned.resource().clone()),
        })
    }

    #[cfg(test)]
    pub(crate) fn support(&self) -> ResourceOccurrenceId {
        self.support
    }

    #[cfg(test)]
    pub(crate) fn viewed(&self) -> &ResourceFact {
        &self.viewed
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanScopeRecord {
    loan: LoanId,
    root: LoanShareId,
    /// The participant allowed to end this scope. A borrowed contract input
    /// has no local close right: its lender lives outside the modular proof.
    close_right: Option<LoanParticipantId>,
    active: bool,
    parent: Option<LoanScopeId>,
    parent_share: Option<LoanShareId>,
    dependencies: crate::persistent::PersistentSet<LoanScopeId>,
    /// Holds placed by folded borrowing composites; `End` refuses while any
    /// remain.
    holds: crate::persistent::PersistentSet<LoanHoldId>,
}

fn origin_kind(origin: &LoanOrigin) -> LoanOriginKind {
    match origin {
        LoanOrigin::Escrowed(_) => LoanOriginKind::LentOwner,
        LoanOrigin::Reborrowed => LoanOriginKind::Reborrow,
        LoanOrigin::BorrowedContractInput => LoanOriginKind::ContractInputView,
        LoanOrigin::LocalStorage(_) => LoanOriginKind::LocalStorage,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LoanOrigin {
    /// Ownership was placed in this ledger's escrow and may be recovered by
    /// exactly this participant after the scope closes.
    Escrowed(LoanParticipantId),
    /// A checked child scope pins an already-live parent share.
    Reborrowed,
    /// Modular verification began with a caller-supplied shared borrow. The
    /// caller and its ownership escrow are deliberately outside this ledger.
    BorrowedContractInput,
    /// A live local object backs a read loan without manufacturing an owned
    /// resource. Closing it restores implicit access, not an escrowed fact.
    LocalStorage(LoanParticipantId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanRecord {
    scope: LoanScopeId,
    /// Direct anchor to the escrowed or caller-assumed mutex identity. Child scopes carry
    /// this identity, never an owner copy or a walk through ancestor scopes.
    mutex_root: Option<LoanId>,
    /// Identity promised by a modular input; this is never recoverable escrow.
    assumed_mutex: Option<ResourceFact>,
    assumed_mutex_protected: Option<ResourceDescription>,
    support: ResourceOccurrenceId,
    escrow: Option<ResourceFact>,
    /// Every checked viewed projection authorized by this loan.  A composite
    /// loan keeps its folded head plus all primitive body views here so a
    /// child binding cannot be minted from the head alone.
    permitted: Vec<ResourceFact>,
    origin: LoanOrigin,
    recovered: bool,
    /// Primitive body pieces whose memory remains protected while a
    /// composite head is lent.  The head is retained as the restoration
    /// recipe, while this checked list supplies the actual write footprint.
    memory_backing: Vec<MemoryRange>,
}

impl LoanRecord {
    fn mutex_identity_description(&self) -> Option<&ResourceFact> {
        match self.origin {
            LoanOrigin::Escrowed(_) if self.assumed_mutex.is_none() => self
                .escrow
                .as_ref()
                .filter(|owner| is_mutex_lifetime_owner(owner)),
            LoanOrigin::BorrowedContractInput if self.escrow.is_none() => {
                self.assumed_mutex.as_ref().filter(|owner| {
                    matches!(owner,
                    ResourceFact::Own(Resource::MutexLive(identity), quantity)
                    if identity.epoch.is_some() && quantity.as_const() == Some(1))
                })
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanShareRecord {
    scope: LoanScopeId,
    parent: Option<LoanShareId>,
    children: Option<(LoanShareId, LoanShareId)>,
    holder: Option<LoanParticipantId>,
    pinned_by: Option<LoanScopeId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanLedgerData {
    arena: u64,
    exclusive_calls: PersistentMap<ExclusiveCallId, ExclusiveCallRecord>,
    exclusive_holders: PersistentMap<LoanParticipantId, ExclusiveCallId>,
    local_references: PersistentMap<LocalReferenceId, LocalReferenceRecord>,
    local_reference_roots: PersistentMap<ResourceOccurrenceId, LocalReferenceId>,
    local_reference_holders: PersistentMap<LoanParticipantId, u64>,
    source_local_references:
        PersistentMap<(LoanParticipantId, crate::kernel::ScalarReferencePlanKey), LocalReferenceId>,
    local_reference_scope: Option<Arc<local_references::scopes::LocalReferenceScope>>,
    next_scope: u64,
    next_loan: u64,
    next_share: u64,
    next_hold: u64,
    /// Every live hold, with the scope it restricts and the participant that
    /// placed it and may release it.
    holds: PersistentMap<LoanHoldId, (LoanScopeId, LoanParticipantId)>,
    scopes: PersistentMap<LoanScopeId, LoanScopeRecord>,
    loans: PersistentMap<LoanId, LoanRecord>,
    shares: PersistentMap<LoanShareId, LoanShareRecord>,
    active_memory_index: PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    active_memory_subtree: PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    /// Counted from the same live ranges as the interval index. A symbolic
    /// external argument can only skip that index when every indexed loan
    /// protects fresh function-local storage.
    active_nonlocal_indexed_ranges: usize,
    active_memory_loans: usize,
    active_footprint: active_footprint::ActiveFootprint,
    /// Exact coordinate origins, including symbolic pointers. Constant byte
    /// intervals support cache retention without searching the symbolic loans.
    cache_memory_index: CacheProtectionIndex,
    cache_memory_subtree: CacheProtectionIndex,
    /// Protected ranges whose bounds are not concrete, keyed by the block
    /// they lie in. Contract input views over parameter memory live here: a
    /// parameter pointer has a symbolic offset in the shared external block,
    /// so the dyadic index cannot hold it. A write query consults only the
    /// entries in its own block, and the entries are bounded by the active
    /// loans with symbolic footprints, which a modular proof creates only
    /// from its contract's explicit view clauses and its own calls.
    unindexed_memory: PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<MemoryRange>>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanLedgerStorage {
    state: LoanLedgerStateId,
    data: LoanLedgerData,
}

type CacheProtectionIndex =
    PersistentMap<(Pointer, ResourceMemoryIntervalNode), PersistentSet<LoanId>>;

fn cache_protection_nodes(
    range: &MemoryRange,
) -> Option<(Pointer, Vec<ResourceMemoryIntervalNode>)> {
    let (origin, start, end) = super::primitives::constant_memory_coordinates(range)?;
    let nodes = super::primitives::memory_interval_nodes_for_coordinates(
        &origin.block,
        i64::try_from(start).ok()?,
        i64::try_from(end).ok()?,
    )?;
    Some((origin, nodes))
}

fn update_cache_protection_bucket(
    index: &mut CacheProtectionIndex,
    key: (Pointer, ResourceMemoryIntervalNode),
    loan: LoanId,
    insert: bool,
) {
    let bucket = index.get(&key).cloned().unwrap_or_default();
    let bucket = if insert {
        bucket.with_value(loan)
    } else {
        bucket.without_value(&loan)
    };
    *index = if bucket.is_empty() {
        index.without_key(&key)
    } else {
        index.with_inserted(key, bucket)
    };
}

fn update_cache_protection(
    data: &mut LoanLedgerData,
    range: &MemoryRange,
    loan: LoanId,
    insert: bool,
) {
    // Charge one explicit backing-range update, as with the write-barrier
    // interval index. Its fixed 32-bit decomposition is bounded independently
    // of the ledger and does not enumerate the range's cells.
    crate::instrumentation::record_deterministic_work(1);
    let Some((origin, nodes)) = cache_protection_nodes(range) else {
        return;
    };
    for node in nodes {
        for ancestor in memory_interval_ancestors(&node) {
            update_cache_protection_bucket(
                &mut data.cache_memory_subtree,
                (origin.clone(), ancestor),
                loan,
                insert,
            );
        }
        update_cache_protection_bucket(
            &mut data.cache_memory_index,
            (origin.clone(), node),
            loan,
            insert,
        );
    }
}

fn update_indexed_memory_range(
    data: &mut LoanLedgerData,
    range: &MemoryRange,
    loan: LoanId,
    insert: bool,
) -> Result<(), LoanRefusal> {
    update_cache_protection(data, range, loan, insert);
    if ledger_interval_nodes(range).is_none() {
        return Ok(());
    }
    let index = update_active_memory_index(&data.active_memory_index, range, loan, insert)?;
    let subtree = update_active_memory_subtree(&data.active_memory_subtree, range, loan, insert)?;
    let nonlocal = if range.base().block.is_local_block() {
        data.active_nonlocal_indexed_ranges
    } else if insert {
        data.active_nonlocal_indexed_ranges
            .checked_add(1)
            .ok_or(LoanRefusal::IdentitySpaceExhausted)?
    } else {
        data.active_nonlocal_indexed_ranges
            .checked_sub(1)
            .ok_or(LoanRefusal::InvalidEvidence)?
    };
    data.active_memory_index = index;
    data.active_memory_subtree = subtree;
    data.active_nonlocal_indexed_ranges = nonlocal;
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct LoanLedgerStateId(u64);

impl LoanLedgerStateId {
    fn fresh() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        Self(NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
    }
}

#[derive(Clone)]
pub(crate) struct LoanLedger {
    storage: Arc<LoanLedgerStorage>,
}

impl std::fmt::Debug for LoanLedger {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("LoanLedger")
            .field("state", &self.storage.state)
            .field("arena", &self.storage.data.arena)
            .finish_non_exhaustive()
    }
}

impl PartialEq for LoanLedger {
    fn eq(&self, other: &Self) -> bool {
        self.storage.state == other.storage.state
    }
}

impl Eq for LoanLedger {}

impl Hash for LoanLedger {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.storage.state.hash(state);
    }
}

impl PartialOrd for LoanLedger {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LoanLedger {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.state.cmp(&other.storage.state)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoanRefusalCategory {
    ProvenOverlap,
    SeparationUnproved,
    WrongHolder,
    WrongArena,
    WrongScope,
    ActiveDependency,
    StalePredecessor,
    Recovery,
    Lifetime,
    Unsupported,
    Missing,
    InvalidEvidence,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoanRefusalOperation {
    Validate,
    Plan,
    Entry,
    Recovery,
    Transition,
    MemoryAccess,
}

/// Where the authority a loan protects came from. A refusal names it so the
/// reader knows which declaration to look at: a contract's own `views`
/// clause, live local storage, an owner lent for a call, or a nested reborrow.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoanOriginKind {
    LocalStorage,
    ContractInputView,
    LentOwner,
    Reborrow,
}

/// One bounded local subject for a refusal. A diagnostic may retain either
/// the selected resource fact or its concrete memory range, the one other
/// fact the refusal is a conflict with, and the small identity needed to
/// explain a loan transition. It never retains a ledger, resource frame, or
/// transition history.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LoanRefusalSubject {
    resource: Option<ResourceFact>,
    /// Boxed for the same reason as `conflicting`: a refusal that names a
    /// range and a fact must stay within the bounded payload size.
    range: Option<Box<MemoryRange>>,
    /// The fact on the other side of a conflict: the resource a live loan
    /// protects for a refused access, or the owned entry that already
    /// supports a contract input view at entry. Boxed so that naming both
    /// sides keeps the diagnostic within its bounded payload size.
    conflicting: Option<Box<ResourceFact>>,
    origin: Option<LoanOriginKind>,
    loan: Option<(u64, u64)>,
    scope: Option<(u64, u64)>,
    share: Option<(u64, u64)>,
    support: Option<(u64, u64)>,
}

impl LoanRefusalSubject {
    fn none() -> Self {
        Self {
            resource: None,
            range: None,
            conflicting: None,
            origin: None,
            loan: None,
            scope: None,
            share: None,
            support: None,
        }
    }

    /// The attempted range, the protected resource it overlaps, and the loan
    /// that protects it: the D13 shape for a refused write, free, or
    /// reallocation.
    pub(crate) fn for_memory_conflict(
        attempted: MemoryRange,
        protected: ResourceFact,
        loan: LoanId,
        origin: LoanOriginKind,
    ) -> Self {
        Self {
            range: Some(Box::new(attempted)),
            conflicting: Some(Box::new(protected)),
            origin: Some(origin),
            loan: Some((loan.arena, loan.ordinal)),
            ..Self::none()
        }
    }

    pub(crate) fn for_conflicting_resources(
        resource: ResourceFact,
        conflicting: ResourceFact,
    ) -> Self {
        Self {
            resource: Some(resource),
            conflicting: Some(Box::new(conflicting)),
            ..Self::none()
        }
    }

    /// A contract input view and the owned entry in the same contract that
    /// already supports it.
    pub(crate) fn for_supported_view(
        viewed: ResourceFact,
        owner: ResourceFact,
        support: ResourceOccurrenceId,
    ) -> Self {
        Self {
            resource: Some(viewed),
            conflicting: Some(Box::new(owner)),
            support: Some((support.arena(), support.ordinal())),
            ..Self::none()
        }
    }

    fn resource(resource: ResourceFact) -> Self {
        Self {
            resource: Some(resource),
            ..Self::none()
        }
    }

    pub(crate) fn for_resource(resource: ResourceFact) -> Self {
        Self::resource(resource)
    }
    fn range(range: MemoryRange) -> Self {
        Self {
            range: Some(Box::new(range)),
            ..Self::none()
        }
    }

    pub(crate) fn with_range(range: MemoryRange) -> Self {
        Self::range(range)
    }

    #[cfg(test)]
    pub(crate) fn for_range(range: MemoryRange) -> Self {
        Self::with_range(range)
    }

    fn with_loan_id(loan: LoanId) -> Self {
        Self {
            loan: Some((loan.arena, loan.ordinal)),
            ..Self::none()
        }
    }

    fn with_scope_id(scope: LoanScopeId) -> Self {
        Self {
            scope: Some((scope.arena, scope.ordinal)),
            ..Self::none()
        }
    }

    fn with_share_id(share: LoanShareId) -> Self {
        Self {
            share: Some((share.arena, share.ordinal)),
            ..Self::none()
        }
    }

    pub(crate) fn with_support_id(support: ResourceOccurrenceId) -> Self {
        Self {
            support: Some((support.arena(), support.ordinal())),
            ..Self::none()
        }
    }

    pub fn resource_fact(&self) -> Option<&ResourceFact> {
        self.resource.as_ref()
    }

    pub fn memory_range(&self) -> Option<&MemoryRange> {
        self.range.as_deref()
    }

    pub fn conflicting_resource_fact(&self) -> Option<&ResourceFact> {
        self.conflicting.as_deref()
    }

    pub fn origin(&self) -> Option<LoanOriginKind> {
        self.origin
    }

    pub fn loan_id(&self) -> Option<(u64, u64)> {
        self.loan
    }

    pub fn scope_id(&self) -> Option<(u64, u64)> {
        self.scope
    }

    pub fn share_id(&self) -> Option<(u64, u64)> {
        self.share
    }

    pub fn support_id(&self) -> Option<(u64, u64)> {
        self.support
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoanOverlapStatus {
    NotApplicable,
    ProvenOverlap,
    SeparationUnproved,
}

/// Compact, bounded semantic payload for a rejected loan operation. It is
/// deliberately retains at most one selected subject; callers must never
/// format a ledger or resource frame to explain a refusal.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LoanRefusalDiagnostic {
    pub(crate) refusal: LoanRefusal,
    pub(crate) category: LoanRefusalCategory,
    pub(crate) operation: LoanRefusalOperation,
    pub(crate) subject: LoanRefusalSubject,
    pub(crate) overlap: LoanOverlapStatus,
    pub(crate) source_clause: Option<u32>,
    pub(crate) source_step: Option<u32>,
}

impl LoanRefusalDiagnostic {
    pub fn category(&self) -> LoanRefusalCategory {
        self.category
    }

    pub fn operation(&self) -> LoanRefusalOperation {
        self.operation
    }

    pub fn overlap(&self) -> LoanOverlapStatus {
        self.overlap
    }

    pub fn subject(&self) -> LoanRefusalSubject {
        self.subject.clone()
    }

    /// The source clause and step are populated by callers that have source
    /// provenance at the point where the kernel refusal is surfaced. They are
    /// intentionally numeric and optional so diagnostics cannot retain source
    /// text or an unbounded proof trace.
    pub fn source_clause(&self) -> Option<u32> {
        self.source_clause
    }

    pub fn source_step(&self) -> Option<u32> {
        self.source_step
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum LoanRefusal {
    NotOwnership,
    WrongArena,
    MissingLoan,
    MissingScope,
    MissingShare,
    WrongHolder,
    WrongScope,
    ScopeEnded,
    ScopeStillActive,
    ShareStillSplit,
    NotSiblings,
    AlreadyRecovered,
    StalePredecessor,
    InvalidEvidence,
    UnsupportedResource,
    UnsupportedPartition,
    ActiveDependency,
    MissingBacking,
    MissingLoanBinding,
    IdentitySpaceExhausted,
}

/// A refusal's reason as a sentence fragment, for a kernel message that has
/// no subject to name. A refusal with one goes through
/// [`LoanRefusal::diagnostic_with_subject`] and the surface renderer instead.
impl std::fmt::Display for LoanRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::NotOwnership => "the lent resource is not an ownership fact",
            Self::WrongArena => "the loan evidence belongs to a different authority arena",
            Self::MissingLoan => "the loan is not recorded in the ledger",
            Self::MissingScope => "the loan scope is not recorded in the ledger",
            Self::MissingShare => "the loan share is not recorded in the ledger",
            Self::WrongHolder => "the loan evidence names the wrong participant",
            Self::WrongScope => "the loan evidence names the wrong scope",
            Self::ScopeEnded => "the loan scope has already ended",
            Self::ScopeStillActive => "the loan scope is still active",
            Self::ShareStillSplit => "the loan share is still split",
            Self::NotSiblings => "the loan shares are not siblings",
            Self::AlreadyRecovered => "the loan was already recovered",
            Self::StalePredecessor => "the loan evidence uses a stale predecessor state",
            Self::InvalidEvidence => "the loan evidence is invalid",
            Self::UnsupportedResource => "this resource shape is outside stable-view support",
            Self::UnsupportedPartition => {
                "the verifier could not prove the access separate from the live borrowed footprint"
            }
            Self::ActiveDependency => "the access overlaps a live borrowed footprint",
            Self::MissingBacking => "the required loan backing is missing",
            Self::MissingLoanBinding => "the required loan binding is missing",
            Self::IdentitySpaceExhausted => "the loan identity space is exhausted",
        })
    }
}

impl LoanRefusal {
    pub(crate) fn diagnostic(self, operation: LoanRefusalOperation) -> LoanRefusalDiagnostic {
        self.diagnostic_with_subject(operation, LoanRefusalSubject::none())
    }

    pub(crate) fn diagnostic_with_subject(
        self,
        operation: LoanRefusalOperation,
        selected_subject: LoanRefusalSubject,
    ) -> LoanRefusalDiagnostic {
        let (category, default_subject, overlap) = match self {
            Self::ActiveDependency => (
                LoanRefusalCategory::ActiveDependency,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::ProvenOverlap,
            ),
            Self::UnsupportedPartition => (
                LoanRefusalCategory::SeparationUnproved,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::SeparationUnproved,
            ),
            Self::WrongHolder => (
                LoanRefusalCategory::WrongHolder,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::WrongArena => (
                LoanRefusalCategory::WrongArena,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::WrongScope | Self::MissingScope => (
                LoanRefusalCategory::WrongScope,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::StalePredecessor => (
                LoanRefusalCategory::StalePredecessor,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::AlreadyRecovered | Self::ShareStillSplit => (
                LoanRefusalCategory::Recovery,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::ScopeEnded | Self::ScopeStillActive => (
                LoanRefusalCategory::Lifetime,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::UnsupportedResource | Self::IdentitySpaceExhausted => (
                LoanRefusalCategory::Unsupported,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::MissingLoan
            | Self::MissingShare
            | Self::MissingBacking
            | Self::MissingLoanBinding => (
                LoanRefusalCategory::Missing,
                LoanRefusalSubject::none(),
                LoanOverlapStatus::NotApplicable,
            ),
            Self::InvalidEvidence | Self::NotOwnership | Self::NotSiblings => {
                let category = match operation {
                    LoanRefusalOperation::Recovery => LoanRefusalCategory::Recovery,
                    _ => LoanRefusalCategory::InvalidEvidence,
                };
                (
                    category,
                    LoanRefusalSubject::none(),
                    LoanOverlapStatus::NotApplicable,
                )
            }
        };
        LoanRefusalDiagnostic {
            refusal: self,
            category,
            operation,
            subject: if selected_subject.resource.is_some()
                || selected_subject.range.is_some()
                || selected_subject.conflicting.is_some()
                || selected_subject.loan.is_some()
                || selected_subject.scope.is_some()
                || selected_subject.share.is_some()
                || selected_subject.support.is_some()
            {
                selected_subject
            } else {
                default_subject
            },
            overlap,
            source_clause: None,
            source_step: None,
        }
    }

    pub(crate) fn proven_overlap_diagnostic(
        self,
        operation: LoanRefusalOperation,
        subject: LoanRefusalSubject,
    ) -> LoanRefusalDiagnostic {
        let mut diagnostic = self.diagnostic_with_subject(operation, subject);
        diagnostic.category = LoanRefusalCategory::ProvenOverlap;
        diagnostic.overlap = LoanOverlapStatus::ProvenOverlap;
        diagnostic
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LoanTransitionEvidence {
    RegisterLocalReference(LocalReferenceBinding),
    BorrowLocalReference(LocalReferenceBinding),
    RecoverLocalReference(LocalReferenceBinding),
    RetireLocalReferenceRoot(LocalReferenceBinding),
    OpenExclusiveCall(ExclusiveCallBinding),
    ReturnExclusiveCall {
        binding: ExclusiveCallBinding,
        holder: LoanParticipantId,
    },
    Lend {
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: ResourceFact,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    LendComposite {
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        support_fact: ResourceFact,
        escrow: ResourceFact,
        backing: Vec<ResourceFact>,
        adapted: Vec<ResourceFact>,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    BorrowedMutexUseRoot {
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        mutex: super::Pointer,
        protected: Option<ResourceDescription>,
        initialization: super::mutexes::MutexInitializationId,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    BorrowedRoot {
        local: Option<(LoanParticipantId, LocalViewBacking)>,
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        viewed: ResourceFact,
        backing: Vec<ResourceFact>,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    Reborrow {
        parent: ReborrowBinding,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    Split {
        share: LoanShareId,
        holder: LoanParticipantId,
        left_holder: LoanParticipantId,
        right_holder: LoanParticipantId,
        left: LoanShareId,
        right: LoanShareId,
    },
    Transfer {
        share: LoanShareId,
        from: LoanParticipantId,
        to: LoanParticipantId,
    },
    Join {
        left: LoanShareId,
        right: LoanShareId,
        holder: LoanParticipantId,
    },
    Hold {
        binding: LoanAuthorityBinding,
        holder: LoanParticipantId,
        hold: LoanHoldId,
    },
    Release {
        hold: LoanHoldId,
        scope: LoanScopeId,
        holder: LoanParticipantId,
    },
    End {
        scope: LoanScopeId,
        holder: LoanParticipantId,
    },
    Recover {
        loan: LoanId,
        holder: LoanParticipantId,
    },
    #[cfg_attr(not(test), allow(dead_code))]
    RegisterDependency {
        parent: LoanScopeId,
        child: LoanScopeId,
        holder: LoanParticipantId,
    },
}

/// Kernel-issued evidence for one exact ledger transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CheckedLoanTransition {
    before_state: LoanLedgerStateId,
    after_state: LoanLedgerStateId,
    checked_after_state: LoanLedgerStateId,
    evidence: LoanTransitionEvidence,
    /// A structural seal over the bounded operation payload. A second opaque
    /// copy avoids probabilistic hashing and avoids comparing whole ledgers.
    checked_evidence: LoanTransitionEvidence,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoanOpening {
    pub(crate) scope: LoanScopeId,
    pub(crate) loan: LoanId,
    pub(crate) root_share: LoanShareId,
    pub(crate) description: StableViewDescription,
    pub(crate) transition: CheckedLoanTransition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PlannedStableView {
    pub(crate) requirement: CheckedResourceFact,
    pub(crate) support: ResourceOccurrenceId,
    pub(crate) loan: LoanId,
    pub(crate) scope: LoanScopeId,
    pub(crate) share: LoanShareId,
    pub(crate) description: StableViewDescription,
}

/// A definition-checked primitive frontier for one folded composite head.
/// Construction is intentionally restricted to the kernel's expansion
/// boundary; the ledger never accepts an untyped list of alleged backing
/// resources.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompositeLoanBacking {
    support: ResourceOccurrenceId,
    head: ResourceFact,
    pieces: Vec<ResourceFact>,
    /// Extra viewed composite descriptions this loan permits beside its own
    /// head: the owned-interface-to-viewed-implementation adapter, where the
    /// caller escrows `head` and the callee's clause names a different
    /// composite whose checked frontier `pieces` already covers.
    adapted: Vec<ResourceFact>,
    /// What recovery hands back instead of `head`. Empty for an ordinary
    /// lend, where the escrowed head is the restoration recipe; the exact
    /// owned facts the planner consumed when the head itself was
    /// materialized for the call.
    restored: Vec<ResourceFact>,
}

/// Definition-checked primitive footprint for an externally supplied folded
/// view. The surface initializer is the only producer; the transition stores
/// the checked pieces so later rechecks need no definition lookup. Recursive
/// children are deliberately excluded until the ledger has an opaque
/// capability that protects their complete footprint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BorrowedContractInputBacking {
    support: ResourceOccurrenceId,
    head: ResourceFact,
    pieces: Vec<ResourceFact>,
}

/// A definition-checked one-level expansion of one viewed composite: the
/// head a loan already permits, and the only children a projection of that
/// head may add to it. Construction is restricted to the kernel's expansion
/// boundary, exactly like the two backings above, so `project` re-checks the
/// containment premise itself instead of trusting the caller's child list
/// (D2 law 10).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompositeProjectionEvidence {
    head: ResourceFact,
    children: Vec<ResourceFact>,
}

impl CompositeProjectionEvidence {
    pub(crate) fn from_checked_expansion(
        head: ResourceFact,
        children: Vec<ResourceFact>,
    ) -> Option<Self> {
        // A projection is read-only authority derived from a viewed
        // composite, so the head is a composite view and every admissible
        // child is a view. An exclusive instance cannot be viewed (D12).
        (head.is_view()
            && matches!(head.resource(), Resource::Composite { .. })
            && children
                .iter()
                .all(|child| child.is_view() && !matches!(child.resource(), Resource::Instance(_))))
        .then_some(Self { head, children })
    }

    fn contains_child(&self, child: &ResourceFact) -> bool {
        // Evidence-local structural entailment has no ambient premises.
        let assumptions = &PureFactContext::default();
        self.children.iter().any(|piece| {
            piece == child
                || ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(piece.clone())
                    .satisfies_fact(child, assumptions)
        })
    }
}

impl BorrowedContractInputBacking {
    pub(crate) fn from_checked_expansion(
        support: ResourceOccurrenceId,
        head: ResourceFact,
        pieces: Vec<ResourceFact>,
    ) -> Option<Self> {
        // A nested composite child is a read-only description under the
        // same loan with no byte backing of its own: the head's escrow, or
        // the contract's partition at a root, protects everything under it.
        // An exclusive instance cannot be viewed (D12).
        (head.is_view()
            && matches!(head.resource(), Resource::Composite { .. })
            && pieces
                .iter()
                .all(|piece| piece.is_view() && !matches!(piece.resource(), Resource::Instance(_))))
        .then_some(Self {
            support,
            head,
            pieces,
        })
    }
}

impl CompositeLoanBacking {
    /// The ordinary same-composite lend: the caller owns the very composite
    /// the callee views, so the escrowed head is also the only description
    /// the loan permits and the exact restoration recipe.
    #[cfg(test)]
    pub(crate) fn from_checked_expansion(
        support: ResourceOccurrenceId,
        head: ResourceFact,
        pieces: Vec<ResourceFact>,
    ) -> Option<Self> {
        Self::from_checked_adapter(support, head, pieces, Vec::new(), Vec::new())
    }

    /// The adapter form (docs/internals/stable-views.md). `adapted` are the viewed
    /// composite descriptions this loan permits beside its own head, and
    /// `restored` are the owned facts recovery hands back in place of the
    /// head. Both are empty for an ordinary same-composite lend, which is
    /// what the test-only `CompositeLoanBacking::from_checked_expansion`
    /// builds.
    pub(crate) fn from_checked_adapter(
        support: ResourceOccurrenceId,
        head: ResourceFact,
        pieces: Vec<ResourceFact>,
        adapted: Vec<ResourceFact>,
        restored: Vec<ResourceFact>,
    ) -> Option<Self> {
        // A nested composite child stays folded inside the escrowed head; it
        // enters the loan as a permitted description with no byte backing.
        // So does a viewed piece of a borrowing composite: the head packages
        // a description its hold keeps stable, and there is no owner here to
        // escrow for it. An exclusive instance cannot be viewed (D12).
        (head.is_own()
            && matches!(head.resource(), Resource::Composite { .. })
            && pieces
                .iter()
                .all(|piece| !matches!(piece.resource(), Resource::Instance(_)))
            // An adapted description is read-only authority over the same
            // escrow, so it is a composite view; it never names an exclusive
            // instance (D12) and never carries ownership.
            && adapted.iter().all(|description| {
                description.is_view() && matches!(description.resource(), Resource::Composite { .. })
            })
            // A restoration is what the caller gets back, so it is owned
            // authority. An instance is not restorable this way.
            && restored.iter().all(|fact| {
                fact.is_own() && !matches!(fact.resource(), Resource::Instance(_))
            }))
        .then_some(Self {
            support,
            head,
            pieces,
            adapted,
            restored,
        })
    }

    /// Whether this backing was checked to permit `description` beside its
    /// own head.
    pub(crate) fn adapts(&self, description: &ResourceFact) -> bool {
        self.adapted.contains(description)
    }
}

/// Checked backing for a view of live automatic storage. Retain the memory
/// state whose allocation bounds and lifetime were checked. The loan ledger
/// enforces the lifetime restriction; fields are private to this module.
#[derive(Clone, Debug, Eq, PartialEq)]
struct LocalViewBacking {
    memory: super::Memory,
    viewed: ResourceFact,
}

impl LocalViewBacking {
    fn check(
        memory: &super::Memory,
        viewed: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let range = viewed.memory_range()?;
        if !viewed.is_view()
            || !range.base().block.is_local_block()
            || !memory.has_block(&range.base().block)
            || memory.is_ended_local_address(range.base())
        {
            return None;
        }
        let bytes = memory.block_size(&range.base().block)?.clone();
        let entire = MemoryRange::new_with_element_width(
            super::Pointer {
                block: range.base().block.clone(),
                offset: super::PointerOffsetTerm::Constant(0),
            },
            0.into(),
            bytes,
            1,
        );
        if !ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_fact(ResourceFact::own_memory(entire))
            .satisfies_fact(viewed, assumptions)
        {
            return None;
        }
        Some(Self {
            memory: memory.clone(),
            viewed: viewed.clone(),
        })
    }
}

/// One body-independent partition of a call's resource requirements.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewTransferPlan {
    pub(crate) caller_resources_after_requirements: ResourceContext,
    pub(crate) callee_resources: ResourceContext,
    pub(crate) transferred_ownership: Vec<CheckedResourceFact>,
    exclusive_call: Option<ExclusiveCallBinding>,
    /// Caller spellings for transferred ownership. A partial memory borrow
    /// retains its supplier's carrier on only the requested slice; it never
    /// returns the supplier's larger footprint.
    pub(crate) canonical_transferred_ownership: Vec<Option<ResourceFact>>,
    pub(crate) stable_views: Vec<PlannedStableView>,
    pub(crate) memory_effects: Vec<MemoryRange>,
    /// The owned occurrence each reserved requirement in
    /// `transferred_ownership` was taken out of. This is the provenance the
    /// call-site effect check reads: a valid resource context is a partition,
    /// so an effect reserved from one owned occurrence and a view lent from a
    /// different one are bytewise disjoint by construction, and only an
    /// effect and a view drawn from the same occurrence still need an
    /// arithmetic separation proof (step 4, D8). A composite requirement is
    /// recorded here too, since the effects projected from it are the bytes
    /// of that one occurrence.
    pub(crate) reserved_ownership_supports: Vec<(ResourceFact, ResourceOccurrenceId)>,
    pub(crate) ledger: LoanLedger,
    pub(crate) entry_transitions: Vec<CheckedLoanTransition>,
    pub(crate) mutex_uses: Vec<mutex_calls::MutexUseCallTransfer>,
    pub(crate) mutex_use_requirements: BTreeMap<ResourceFact, ResourceFact>,
    callee_view_bindings: LoanViewBindings,
    parent_view_bindings: LoanViewBindings,
    parent_ledger: LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    loan_roots: Vec<(LoanScopeId, LoanId, LoanShareId, ResourceOccurrenceId, bool)>,
    /// The owned facts this plan escrowed and will hand back at recovery.
    /// A lend empties them out of the caller residual, so a check that reads
    /// the residual alone would not see what the caller still holds across
    /// the call.
    escrowed_owners: Vec<ResourceFact>,
    /// The hold bindings of escrowed borrowing composites, by escrow fact.
    /// The head leaves the caller residual for the call, but its hold stays
    /// in the ledger, and recovery hands the binding back to the restored
    /// head (step 7).
    escrowed_holds: Vec<(ResourceFact, LoanViewBinding)>,
    /// Owned requirements whose caller occurrence carried a hold binding: the
    /// composite went to the callee together with its borrow. Recovery
    /// re-binds it if the callee returned it and releases the hold if the
    /// callee consumed it (step 7).
    pub(crate) transferred_holds: Vec<(ResourceFact, LoanViewBinding)>,
    /// For a view lent as a child of the caller's own binding: that parent
    /// binding, which an escaping borrow holds after the child ends.
    pub(crate) rebound_parents: BTreeMap<LoanId, LoanViewBinding>,
    /// Reborrows whose parent share was split for a suspended worker.
    suspended_split_reborrows: BTreeMap<LoanId, (ResourceOccurrenceId, LoanShareId)>,
    /// Implicit stack roots retained by the parent while modeled workers read.
    suspended_local_parents: BTreeMap<ResourceFact, LoanViewBinding>,
    suspended_local_reborrows: BTreeMap<LoanId, (ResourceFact, LoanShareId)>,
    /// For an adapter lend whose escrowed head was materialized for the call
    /// out of owned facts the caller already held: exactly those facts, which
    /// recovery hands back in place of the head (docs/internals/stable-views.md). The
    /// escrow stays the head in the ledger, so the loan still protects the
    /// whole frontier; only what the caller gets back differs.
    adapter_restorations: BTreeMap<LoanId, Vec<ResourceFact>>,
}

/// What a call leaves behind for a borrowing composite it produced or
/// returned: the loan the composite keeps open and the binding, carrying the
/// hold, that its occurrence in the caller must carry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EscapedHold {
    pub(crate) head: ResourceFact,
    pub(crate) binding: LoanViewBinding,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewRecovery {
    pub(crate) ledger: LoanLedger,
    pub(crate) terminal_ledger: LoanLedger,
    /// The canonical predecessor on which escaped composite holds are added.
    pub(crate) hold_base_ledger: LoanLedger,
    /// Exact hold transitions after the terminal recovery path is selected.
    pub(crate) hold_transitions: Vec<CheckedLoanTransition>,
    pub(crate) resources: ResourceContext,
    /// The escrowed owners recovery handed back, in recovery order, each
    /// with the hold binding its occurrence carried before the call.
    pub(crate) recovered_escrows: Vec<(ResourceFact, Option<LoanViewBinding>)>,
    pub(crate) mutex_authority_updates: Vec<mutex_calls::MutexAuthorityUpdate>,
    /// The holds this call's produced borrowing composites now carry.
    pub(crate) escaped_holds: Vec<EscapedHold>,
    pub(crate) view_bindings: LoanViewBindings,
    /// A completed local reader either advances its parent's share or closes
    /// the implicit root after the final sibling returns.
    pub(crate) local_view_updates: BTreeMap<ResourceFact, Option<LoanViewBinding>>,
    pub(crate) transitions: Vec<CheckedLoanTransition>,
}

impl StableViewRecovery {
    pub(crate) fn diagnostic_subject(&self) -> LoanRefusalSubject {
        self.transitions
            .last()
            .map(|transition| match &transition.evidence {
                LoanTransitionEvidence::RegisterLocalReference(_)
                | LoanTransitionEvidence::BorrowLocalReference(_)
                | LoanTransitionEvidence::RecoverLocalReference(_)
                | LoanTransitionEvidence::RetireLocalReferenceRoot(_)
                | LoanTransitionEvidence::OpenExclusiveCall(_)
                | LoanTransitionEvidence::ReturnExclusiveCall { .. } => LoanRefusalSubject::none(),
                LoanTransitionEvidence::Lend {
                    scope,
                    loan,
                    root,
                    support,
                    ..
                }
                | LoanTransitionEvidence::LendComposite {
                    scope,
                    loan,
                    root,
                    support,
                    ..
                }
                | LoanTransitionEvidence::BorrowedMutexUseRoot {
                    scope,
                    loan,
                    root,
                    support,
                    ..
                }
                | LoanTransitionEvidence::BorrowedRoot {
                    scope,
                    loan,
                    root,
                    support,
                    ..
                } => LoanRefusalSubject {
                    loan: Some((loan.arena, loan.ordinal)),
                    scope: Some((scope.arena, scope.ordinal)),
                    share: Some((root.arena, root.ordinal)),
                    support: Some((support.arena(), support.ordinal())),
                    ..LoanRefusalSubject::none()
                },
                LoanTransitionEvidence::Recover { loan, .. } => {
                    LoanRefusalSubject::with_loan_id(*loan)
                }
                LoanTransitionEvidence::End { scope, .. }
                | LoanTransitionEvidence::RegisterDependency { parent: scope, .. } => {
                    LoanRefusalSubject::with_scope_id(*scope)
                }
                LoanTransitionEvidence::Split { share, .. }
                | LoanTransitionEvidence::Transfer { share, .. } => {
                    LoanRefusalSubject::with_share_id(*share)
                }
                LoanTransitionEvidence::Join { left, .. } => {
                    LoanRefusalSubject::with_share_id(*left)
                }
                LoanTransitionEvidence::Hold { binding, .. } => LoanRefusalSubject {
                    loan: Some((binding.loan.arena, binding.loan.ordinal)),
                    scope: Some((binding.scope.arena, binding.scope.ordinal)),
                    ..LoanRefusalSubject::none()
                },
                LoanTransitionEvidence::Release { scope, .. } => {
                    LoanRefusalSubject::with_scope_id(*scope)
                }
                LoanTransitionEvidence::Reborrow {
                    scope, loan, root, ..
                } => LoanRefusalSubject {
                    loan: Some((loan.arena, loan.ordinal)),
                    scope: Some((scope.arena, scope.ordinal)),
                    share: Some((root.arena, root.ordinal)),
                    ..LoanRefusalSubject::none()
                },
            })
            .unwrap_or_else(LoanRefusalSubject::none)
    }
}

/// Checked evidence for one complete stable-view call transition.
///
/// The entry and recovery lists are bounded by the scopes and shares created
/// by this call.  They are retained separately from the resulting ledger
/// roots so artifact reuse cannot treat an equal final state as proof that a
/// different predecessor or transition history was valid.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CheckedLoanCallEvidence {
    pub(crate) entry: StableViewTransferPlan,
    pub(crate) recovered_ledger: LoanLedger,
    pub(crate) recovery_terminal_ledger: LoanLedger,
    pub(crate) recovery_transitions: Vec<CheckedLoanTransition>,
    /// Holds are applied to either the exact caller predecessor or the
    /// terminal recovery successor, and retain their own checked identities.
    pub(crate) recovery_hold_base: LoanLedger,
    pub(crate) recovery_hold_transitions: Vec<CheckedLoanTransition>,
}

/// The part of a call-evidence trace that is needed by the artifact boundary.
///
/// Call evidence is checked when it enters the persistent trace.  Keeping the
/// resulting outer-state index beside the trace means a later artifact check
/// can ask for the one caller root it owns instead of materializing and
/// rechecking every completed call on the path.  The maps are persistent so a
/// branch or a repeated call copies only the update path.
#[derive(Clone)]
struct CheckedLoanCallEvidenceSummary {
    valid: bool,
    recovered_by_caller: PersistentMap<(u64, LoanParticipantId), LoanLedger>,
    last_pristine_recovered: Option<(LoanParticipantId, LoanLedger)>,
    chain_origin: Option<(u64, LoanParticipantId)>,
    last_recovered: Option<(LoanParticipantId, LoanLedger)>,
}

impl Default for CheckedLoanCallEvidenceSummary {
    fn default() -> Self {
        Self {
            valid: true,
            recovered_by_caller: PersistentMap::default(),
            last_pristine_recovered: None,
            chain_origin: None,
            last_recovered: None,
        }
    }
}

impl CheckedLoanCallEvidenceSummary {
    fn append(&self, evidence: &CheckedLoanCallEvidence) -> CheckedLoanCallEvidenceSummary {
        let caller_ledger = evidence.entry.caller_ledger();
        let caller_participant = evidence.entry.caller_participant();
        let valid = self.valid
            && evidence
                .recheck(
                    caller_ledger,
                    Some(caller_participant),
                    &evidence.entry.ledger,
                    Some(evidence.entry.callee_participant()),
                )
                .is_ok();
        let key = (caller_ledger.state_identity(), caller_participant);
        let continues_chain = self
            .last_recovered
            .as_ref()
            .is_some_and(|(participant, ledger)| {
                *participant == caller_participant && ledger == caller_ledger
            });
        let chain_origin = if continues_chain {
            self.chain_origin.unwrap_or(key)
        } else {
            key
        };
        let recovered_by_caller = self
            .recovered_by_caller
            .with_inserted(key, evidence.recovered_ledger.clone())
            .with_inserted(chain_origin, evidence.recovered_ledger.clone());
        let continues_pristine_chain =
            self.last_pristine_recovered
                .as_ref()
                .is_some_and(|(participant, ledger)| {
                    *participant == caller_participant && ledger == caller_ledger
                });
        let last_pristine_recovered = if caller_ledger.is_pristine() || continues_pristine_chain {
            Some((caller_participant, evidence.recovered_ledger.clone()))
        } else {
            self.last_pristine_recovered.clone()
        };
        CheckedLoanCallEvidenceSummary {
            valid,
            recovered_by_caller,
            last_pristine_recovered,
            chain_origin: Some(chain_origin),
            last_recovered: Some((caller_participant, evidence.recovered_ledger.clone())),
        }
    }
}

#[derive(Clone)]
enum CheckedLoanCallEvidenceSequenceNode {
    Empty,
    Append {
        prefix: Arc<CheckedLoanCallEvidenceSequenceNode>,
        evidence: Arc<CheckedLoanCallEvidence>,
    },
}

#[derive(Clone)]
pub(crate) struct CheckedLoanCallEvidenceSequence {
    node: Arc<CheckedLoanCallEvidenceSequenceNode>,
    len: usize,
    summary: Arc<CheckedLoanCallEvidenceSummary>,
}

pub(crate) fn empty_checked_loan_evidence_sequence() -> CheckedLoanCallEvidenceSequence {
    CheckedLoanCallEvidenceSequence {
        node: Arc::new(CheckedLoanCallEvidenceSequenceNode::Empty),
        len: 0,
        summary: Arc::new(CheckedLoanCallEvidenceSummary::default()),
    }
}

pub(crate) fn append_checked_loan_evidence(
    sequence: &CheckedLoanCallEvidenceSequence,
    evidence: Option<Arc<CheckedLoanCallEvidence>>,
) -> CheckedLoanCallEvidenceSequence {
    let Some(evidence) = evidence else {
        return sequence.clone();
    };
    let summary = Arc::new(sequence.summary.append(&evidence));
    CheckedLoanCallEvidenceSequence {
        node: Arc::new(CheckedLoanCallEvidenceSequenceNode::Append {
            prefix: sequence.node.clone(),
            evidence,
        }),
        len: sequence.len + 1,
        summary,
    }
}

pub(crate) fn concat_checked_loan_evidence(
    prefix: &CheckedLoanCallEvidenceSequence,
    suffix: &CheckedLoanCallEvidenceSequence,
) -> CheckedLoanCallEvidenceSequence {
    if prefix.is_empty() {
        return suffix.clone();
    }
    if suffix.is_empty() {
        return prefix.clone();
    }
    suffix
        .to_vec()
        .into_iter()
        .fold(prefix.clone(), |sequence, evidence| {
            append_checked_loan_evidence(&sequence, Some(evidence))
        })
}

impl CheckedLoanCallEvidenceSequence {
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub(crate) fn is_valid(&self) -> bool {
        self.summary.valid
    }

    pub(crate) fn recovered_ledger_for(
        &self,
        caller_ledger: &LoanLedger,
        caller_participant: LoanParticipantId,
        pristine_start: bool,
    ) -> Option<LoanLedger> {
        if pristine_start {
            self.summary
                .last_pristine_recovered
                .as_ref()
                .and_then(|(participant, ledger)| {
                    (*participant == caller_participant).then(|| ledger.clone())
                })
        } else {
            self.summary
                .recovered_by_caller
                .get(&(caller_ledger.state_identity(), caller_participant))
                .cloned()
        }
    }

    pub(crate) fn pristine_recovery(&self) -> (Option<LoanParticipantId>, Option<LoanLedger>) {
        self.summary
            .last_pristine_recovered
            .as_ref()
            .map_or((None, None), |(participant, ledger)| {
                (Some(*participant), Some(ledger.clone()))
            })
    }

    /// Returns the persistent suffix after `prefix`, when this sequence was
    /// derived from that exact prefix. Walking only the appended evidence
    /// keeps branch-join work proportional to the path delta.
    pub(crate) fn suffix_since(
        &self,
        prefix: &CheckedLoanCallEvidenceSequence,
    ) -> Option<CheckedLoanCallEvidenceSequence> {
        if self.len < prefix.len {
            return None;
        }
        if self.len == prefix.len {
            return (self.len == 0 || Arc::ptr_eq(&self.node, &prefix.node))
                .then(empty_checked_loan_evidence_sequence);
        }
        let mut node = self.node.clone();
        let mut remaining = self.len;
        let mut suffix = Vec::with_capacity(self.len - prefix.len);
        while remaining > prefix.len {
            let CheckedLoanCallEvidenceSequenceNode::Append {
                prefix: predecessor,
                evidence,
            } = &*node
            else {
                return None;
            };
            suffix.push(evidence.clone());
            node = predecessor.clone();
            remaining -= 1;
        }
        if !Arc::ptr_eq(&node, &prefix.node) {
            return None;
        }
        suffix.reverse();
        Some(suffix.into_iter().fold(
            empty_checked_loan_evidence_sequence(),
            |sequence, evidence| append_checked_loan_evidence(&sequence, Some(evidence)),
        ))
    }

    /// Materialize only at an artifact boundary or diagnostic/test boundary.
    /// Hot-path path forks clone the immutable node root instead.
    pub(crate) fn to_vec(&self) -> Vec<Arc<CheckedLoanCallEvidence>> {
        let mut result = Vec::with_capacity(self.len);
        let mut node = &*self.node;
        while let CheckedLoanCallEvidenceSequenceNode::Append { prefix, evidence } = node {
            result.push(evidence.clone());
            node = prefix;
        }
        result.reverse();
        result
    }
}

impl PartialEq for CheckedLoanCallEvidenceSequence {
    fn eq(&self, other: &Self) -> bool {
        // Cloned proof paths retain the exact persistent node identity.  This
        // is the common artifact-comparison case and must not revisit the
        // completed call history.  Separately-built histories still take the
        // exact evidence-by-evidence fallback below.
        if Arc::ptr_eq(&self.node, &other.node) {
            return true;
        }
        if self.len != other.len {
            return false;
        }
        let mut left = &*self.node;
        let mut right = &*other.node;
        loop {
            match (left, right) {
                (
                    CheckedLoanCallEvidenceSequenceNode::Empty,
                    CheckedLoanCallEvidenceSequenceNode::Empty,
                ) => return true,
                (
                    CheckedLoanCallEvidenceSequenceNode::Append {
                        prefix: left_prefix,
                        evidence: left_evidence,
                    },
                    CheckedLoanCallEvidenceSequenceNode::Append {
                        prefix: right_prefix,
                        evidence: right_evidence,
                    },
                ) => {
                    if left_evidence != right_evidence {
                        return false;
                    }
                    left = left_prefix;
                    right = right_prefix;
                }
                _ => return false,
            }
        }
    }
}

impl Eq for CheckedLoanCallEvidenceSequence {}

impl std::fmt::Debug for CheckedLoanCallEvidenceSequence {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut recent = Vec::new();
        let mut node = &*self.node;
        while recent.len() < 3 {
            let CheckedLoanCallEvidenceSequenceNode::Append { prefix, evidence } = node else {
                break;
            };
            recent.push((evidence.entry.caller, evidence.entry.callee));
            node = prefix;
        }
        formatter
            .debug_struct("CheckedLoanCallEvidenceSequence")
            .field("len", &self.len)
            .field("recent_call_participants", &recent)
            .finish()
    }
}

impl Drop for CheckedLoanCallEvidenceSequence {
    fn drop(&mut self) {
        let mut node = std::mem::replace(
            &mut self.node,
            Arc::new(CheckedLoanCallEvidenceSequenceNode::Empty),
        );
        loop {
            if Arc::strong_count(&node) != 1 {
                break;
            }
            let Ok(unwrapped) = Arc::try_unwrap(node) else {
                break;
            };
            match unwrapped {
                CheckedLoanCallEvidenceSequenceNode::Empty => break,
                CheckedLoanCallEvidenceSequenceNode::Append { prefix, evidence } => {
                    drop(evidence);
                    node = prefix;
                }
            }
        }
    }
}

impl CheckedLoanCallEvidence {
    /// A modeled runtime call retains its participant and transfers no
    /// resource clauses. Its only loan effect is one checked hold or release.
    pub(crate) fn runtime_mutex_transition(
        before: &LoanLedger,
        holder: LoanParticipantId,
        transition: CheckedLoanTransition,
        after: &LoanLedger,
    ) -> Result<Self, LoanRefusal> {
        let is_hold = match &transition.evidence {
            LoanTransitionEvidence::Hold { holder: actual, .. } if *actual == holder => true,
            LoanTransitionEvidence::Release { holder: actual, .. } if *actual == holder => false,
            _ => return Err(LoanRefusal::InvalidEvidence),
        };
        let entry = plan_stable_view_transfer(
            &ResourceContext::new(),
            &[],
            &PureFactContext::new(),
            before,
            holder,
            holder,
        )
        .map_err(|_| LoanRefusal::InvalidEvidence)?;
        let evidence = if is_hold {
            Self::new(
                entry,
                after.clone(),
                before.clone(),
                vec![],
                before.clone(),
                vec![transition],
            )
        } else {
            Self::new(
                entry,
                after.clone(),
                after.clone(),
                vec![transition],
                after.clone(),
                vec![],
            )
        };
        evidence.recheck(before, Some(holder), before, Some(holder))?;
        // The general call checker permits restoring its predecessor. A
        // runtime operation must instead publish this exact successor.
        let checked = if is_hold {
            &evidence.recovery_hold_transitions[0]
        } else {
            &evidence.recovery_transitions[0]
        };
        if before.apply(checked)? != *after {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(evidence)
    }

    pub(crate) fn new(
        entry: StableViewTransferPlan,
        recovered_ledger: LoanLedger,
        recovery_terminal_ledger: LoanLedger,
        recovery_transitions: Vec<CheckedLoanTransition>,
        recovery_hold_base: LoanLedger,
        recovery_hold_transitions: Vec<CheckedLoanTransition>,
    ) -> Self {
        Self {
            entry,
            recovered_ledger,
            recovery_terminal_ledger,
            recovery_transitions,
            recovery_hold_base,
            recovery_hold_transitions,
        }
    }

    /// Rechecks both halves of the call boundary against the exact roots and
    /// participants that the states publish.  Ledger equality is only the
    /// final identity check; every retained transition is applied first.
    pub(crate) fn recheck(
        &self,
        caller_ledger: &LoanLedger,
        caller_participant: Option<LoanParticipantId>,
        callee_ledger: &LoanLedger,
        callee_participant: Option<LoanParticipantId>,
    ) -> Result<(), LoanRefusal> {
        if caller_participant != Some(self.entry.caller)
            || callee_participant != Some(self.entry.callee)
        {
            return Err(LoanRefusal::WrongHolder);
        }
        let entry_successor = self.entry.recheck_entry(caller_ledger)?;
        if entry_successor != *callee_ledger {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let mut recovery_successor = callee_ledger.clone();
        for transition in &self.recovery_transitions {
            match &transition.evidence {
                LoanTransitionEvidence::Hold { .. } => {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                LoanTransitionEvidence::Release { holder, .. } if *holder != self.entry.caller => {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                _ => {}
            }
            crate::instrumentation::record_deterministic_work(1);
            recovery_successor = recovery_successor.apply(transition)?;
        }
        if let Some(binding) = &self.entry.exclusive_call {
            recovery_successor.validate_returned_exclusive_call(binding)?;
        }
        if recovery_successor != self.recovery_terminal_ledger {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if self.recovery_hold_base != *caller_ledger
            && self.recovery_hold_base != self.recovery_terminal_ledger
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let mut hold_successor = self.recovery_hold_base.clone();
        for transition in &self.recovery_hold_transitions {
            match &transition.evidence {
                LoanTransitionEvidence::Hold { holder, .. } if *holder == self.entry.caller => {}
                _ => return Err(LoanRefusal::InvalidEvidence),
            }
            crate::instrumentation::record_deterministic_work(1);
            hold_successor = hold_successor.apply(transition)?;
        }
        // The caller resumes at the exact predecessor, at the checked terminal
        // successor, or at that predecessor/terminal with the recorded escaped
        // holds applied. Nothing else is a valid continuation.
        if self.recovered_ledger != *caller_ledger
            && self.recovered_ledger != self.recovery_terminal_ledger
            && self.recovered_ledger != hold_successor
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(())
    }
}

impl StableViewRecovery {
    /// Rechecks the ordered recovery evidence from the exact entry ledger.
    /// Applying each item performs the kernel's predecessor and payload checks;
    /// callers can retain the returned historical successor separately from
    /// the canonical predecessor stored in `ledger`.
    pub(crate) fn recheck_transitions(
        &self,
        predecessor: &LoanLedger,
        caller: LoanParticipantId,
    ) -> Result<LoanLedger, LoanRefusal> {
        let mut current = predecessor.clone();
        for transition in &self.transitions {
            match &transition.evidence {
                LoanTransitionEvidence::Hold { .. } => {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                LoanTransitionEvidence::Release { holder, .. } if *holder != caller => {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                _ => {}
            }
            crate::instrumentation::record_deterministic_work(1);
            current = current.apply(transition)?;
        }
        Ok(current)
    }
}

/// Whether a loan's lent view covers what a callee requires of it.
///
/// The lent view covers the requirement directly, or through the view the
/// caller holds under the loan: a loop that took `views chunk[0..n]` out of
/// `views bytes[0..length]` holds the smaller view under the same loan, and
/// a requirement inside `chunk[0..n]` is inside `bytes[0..length]` because
/// the held view is. Both steps are checked here; neither is assumed from
/// how the held view came to be bound.
fn bound_view_covers_requirement(
    viewed: &ResourceFact,
    held: Option<&ResourceFact>,
    requirement: &ResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    let covers = |available: &ResourceFact, required: &ResourceFact| {
        ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_fact(available.clone())
            .satisfies_fact(required, assumptions)
    };
    covers(viewed, requirement)
        || held.is_some_and(|held| covers(viewed, held) && covers(held, requirement))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StableViewPlanError {
    InvalidRequirement,
    MissingResource(ResourceFact),
    ConflictingRequirement(ResourceFact),
    Loan(LoanRefusal),
    InvalidResidual,
    UnsupportedPartition,
}

/// The plan error for a resource that could not join a context: an owned
/// resource that the context already holds, or that overlaps one it holds,
/// is a conflicting requirement naming that resource.
fn composition_conflict(
    error: crate::kernel::primitives::ResourceContextValidityError,
    composed: &ResourceFact,
) -> StableViewPlanError {
    use crate::kernel::primitives::ResourceContextValidityError as Invalid;
    match error {
        Invalid::DuplicateOwnedResourceFact(_)
        | Invalid::OverlappingOwnedMemoryResources { .. } => {
            StableViewPlanError::ConflictingRequirement(composed.clone())
        }
        Invalid::InvalidExclusiveAccess(_) => StableViewPlanError::InvalidResidual,
    }
}

impl StableViewPlanError {
    pub(crate) fn loan_diagnostic(
        &self,
        operation: LoanRefusalOperation,
    ) -> Option<LoanRefusalDiagnostic> {
        match self {
            Self::Loan(refusal) => Some(refusal.diagnostic(operation)),
            Self::MissingResource(resource) => {
                Some(LoanRefusal::MissingBacking.diagnostic_with_subject(
                    operation,
                    LoanRefusalSubject::resource(resource.clone()),
                ))
            }
            Self::ConflictingRequirement(resource) => Some(LoanRefusalDiagnostic {
                refusal: LoanRefusal::ActiveDependency,
                category: LoanRefusalCategory::ProvenOverlap,
                operation,
                subject: LoanRefusalSubject::resource(resource.clone()),
                overlap: LoanOverlapStatus::ProvenOverlap,
                source_clause: None,
                source_step: None,
            }),
            Self::InvalidRequirement => {
                Some(LoanRefusal::UnsupportedResource.diagnostic(operation))
            }
            Self::InvalidResidual => Some(LoanRefusal::InvalidEvidence.diagnostic(operation)),
            Self::UnsupportedPartition => {
                Some(LoanRefusal::UnsupportedPartition.diagnostic(operation))
            }
        }
    }
}

impl From<LoanRefusal> for StableViewPlanError {
    fn from(error: LoanRefusal) -> Self {
        Self::Loan(error)
    }
}

/// Jointly plans all requirements from a normalized contract interface.
///
/// Ownership requirements are reserved before any view is created, so input
/// order cannot decide whether a mutable transfer and a shared loan overlap.
/// Equal or overlapping views supported by the same owned occurrence reuse
/// one escrow and one root share.
pub(crate) fn plan_stable_view_transfer(
    caller_resources: &ResourceContext,
    requirements: &[CheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
) -> Result<StableViewTransferPlan, StableViewPlanError> {
    plan_stable_view_transfer_with_bindings(
        caller_resources,
        requirements,
        assumptions,
        ledger,
        caller,
        callee,
        &LoanViewBindings::default(),
    )
}

pub(crate) fn plan_stable_view_transfer_with_bindings(
    caller_resources: &ResourceContext,
    requirements: &[CheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    parent_view_bindings: &LoanViewBindings,
) -> Result<StableViewTransferPlan, StableViewPlanError> {
    plan_stable_view_transfer_with_bindings_and_composites(
        caller_resources,
        requirements,
        assumptions,
        ledger,
        caller,
        callee,
        parent_view_bindings,
        &BTreeMap::new(),
    )
}

pub(crate) fn plan_stable_view_transfer_with_bindings_and_composites(
    caller_resources: &ResourceContext,
    requirements: &[CheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    parent_view_bindings: &LoanViewBindings,
    composite_backings: &BTreeMap<ResourceOccurrenceId, CompositeLoanBacking>,
) -> Result<StableViewTransferPlan, StableViewPlanError> {
    plan_stable_view_transfer_with_bindings_and_composites_for_worker(
        caller_resources,
        requirements,
        assumptions,
        ledger,
        caller,
        callee,
        parent_view_bindings,
        composite_backings,
        false,
    )
}

/// Suspend one owned memory piece under a parent-held root, then lend a
/// sibling share to this worker. The parent receives a genuine checked view
/// of the escrowed piece, so later workers use the ordinary split/reborrow
/// path. The view is removed when the final join recovers the exact escrow.
fn lend_owned_view_to_suspended_worker(
    ledger: &mut LoanLedger,
    transitions: &mut Vec<CheckedLoanTransition>,
    residual: &mut ResourceContext,
    split_origins: &mut MemorySplitOrigins,
    parent_bindings: &mut LoanViewBindings,
    split_reborrows: &mut BTreeMap<LoanId, (ResourceOccurrenceId, LoanShareId)>,
    selected: &ResourceFact,
    support: ResourceOccurrenceId,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    assumptions: &PureFactContext,
) -> Result<LoanOpening, StableViewPlanError> {
    let range = selected
        .memory_own_range()
        .cloned()
        .ok_or(StableViewPlanError::UnsupportedPartition)?;
    let root = ledger.lend(caller, caller, support, selected.clone())?;
    *ledger = ledger.apply(&root.transition)?;
    transitions.push(root.transition);
    *residual = residual
        .clone()
        .without_selected_fact_with_origins(support, selected, assumptions, split_origins)
        .ok_or_else(|| StableViewPlanError::MissingResource(selected.clone()))?;
    let viewed = ResourceFact::view_memory(range);
    let (next_residual, occurrence) = residual
        .clone()
        .try_compose_with_fact_with_occurrence(viewed.clone(), assumptions)
        .map_err(|error| composition_conflict(error, &viewed))?;
    let occurrence = occurrence.ok_or(StableViewPlanError::InvalidResidual)?;
    let (split, retained, worker) = ledger.split(root.root_share, caller, caller, caller)?;
    *ledger = ledger.apply(&split)?;
    transitions.push(split);
    let binding = LoanViewBinding {
        loan: root.loan,
        scope: root.scope,
        share: retained,
        support,
        viewed,
        hold: None,
    };
    *residual = next_residual.with_loan_dependency(occurrence, binding.clone());
    *parent_bindings = parent_bindings.with_inserted(occurrence, binding.clone());
    let worker_binding = LoanViewBinding {
        share: worker,
        ..binding
    };
    let child = ledger.reborrow(worker_binding, caller, callee)?;
    *ledger = ledger.apply(&child.transition)?;
    transitions.push(child.transition.clone());
    split_reborrows.insert(child.loan, (occurrence, worker));
    Ok(child)
}

/// The caller's context at the moment one call's exclusive reservation found
/// no owner for a requirement: what earlier requirements of the same call had
/// already reserved, and what remained of the caller's partition. A refusal
/// naming the missing owner reads this so it can say what was compared, not
/// the caller's context before any reservation (which may well cover the
/// requirement, as it does when two requirements name one cell).
///
/// Diagnostic only. Every plan clears it on entry and sets it on this one
/// refusal, so it describes the latest plan, and a reader matches the missing
/// fact before trusting it.
#[derive(Clone, Debug)]
pub(crate) struct OwnedReservationMiss {
    pub(crate) missing: ResourceFact,
    pub(crate) reserved: Vec<ResourceFact>,
    pub(crate) remaining: Vec<ResourceFact>,
}

thread_local! {
    static LAST_OWNED_RESERVATION_MISS: std::cell::RefCell<Option<OwnedReservationMiss>> =
        const { std::cell::RefCell::new(None) };
}

/// The reservation state behind the latest plan's missing owner `missing`,
/// if the latest plan refused exactly that requirement.
pub(crate) fn owned_reservation_miss_for(missing: &ResourceFact) -> Option<OwnedReservationMiss> {
    LAST_OWNED_RESERVATION_MISS.with(|miss| {
        miss.borrow()
            .as_ref()
            .filter(|miss| &miss.missing == missing)
            .cloned()
    })
}

pub(crate) fn plan_stable_view_transfer_with_bindings_and_composites_for_worker(
    caller_resources: &ResourceContext,
    requirements: &[CheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    parent_view_bindings: &LoanViewBindings,
    composite_backings: &BTreeMap<ResourceOccurrenceId, CompositeLoanBacking>,
    split_reborrowed_views: bool,
) -> Result<StableViewTransferPlan, StableViewPlanError> {
    plan_stable_view_transfer_with_protocol_effect(
        caller_resources,
        requirements,
        assumptions,
        ledger,
        caller,
        callee,
        parent_view_bindings,
        composite_backings,
        split_reborrowed_views,
        false,
    )
}

pub(crate) fn plan_stable_view_transfer_with_protocol_effect(
    caller_resources: &ResourceContext,
    requirements: &[CheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    parent_view_bindings: &LoanViewBindings,
    composite_backings: &BTreeMap<ResourceOccurrenceId, CompositeLoanBacking>,
    split_reborrowed_views: bool,
    same_thread_protocol_effect: bool,
) -> Result<StableViewTransferPlan, StableViewPlanError> {
    if ledger.holder_has_local_references(caller) {
        return Err(StableViewPlanError::InvalidRequirement);
    }
    if same_thread_protocol_effect && split_reborrowed_views {
        return Err(StableViewPlanError::InvalidRequirement);
    }
    if requirements.iter().any(|requirement| {
        requirement.state_source == ResourceStateSource::Post
            || requirement.role == ResourceTransferRole::Produce
            || (requirement.fact.is_view() && requirement.role != ResourceTransferRole::Borrow)
    }) {
        return Err(StableViewPlanError::InvalidRequirement);
    }

    LAST_OWNED_RESERVATION_MISS.with(|miss| *miss.borrow_mut() = None);
    let mut residual = caller_resources.clone();
    let mut split_origins = MemorySplitOrigins::default();
    let mut parent_view_bindings = parent_view_bindings.clone();
    let mut callee_resources = ResourceContext::new_with_equalities(assumptions);
    let mut transferred_ownership = Vec::new();
    let mut transferred_holds = Vec::new();
    let mut rebound_parents = BTreeMap::new();
    let mut suspended_split_reborrows = BTreeMap::new();
    let mut stable_views = Vec::new();
    let mut callee_view_bindings = LoanViewBindings::default();
    let mut memory_effects = Vec::new();
    // Several clauses naming one token or composite are a single demand for
    // their combined count. Reservation stays clause by clause -- one entry
    // must directly entail each -- but a refusal has to name the whole
    // demand, the way the definitional route does when it consumes the
    // normalized requirement context: `consume_two(cb, cb)` needs quantity
    // two of `can_complete(cb)`, and reporting the second unit alone would
    // name a fact the caller does hold. Only constant counts add up; anything
    // else reports its own clause.
    let mut demanded_own_quantities = BTreeMap::<Resource, Option<u32>>::new();
    for requirement in requirements
        .iter()
        .filter(|requirement| requirement.fact.is_own())
    {
        let clause = match requirement.fact.owned_quantity_term() {
            Some(bits32_constant!(quantity)) => Some(constant_u32(*quantity)),
            _ => None,
        };
        let total = demanded_own_quantities
            .entry(requirement.fact.resource().clone())
            .or_insert(Some(0));
        *total = match (*total, clause) {
            (Some(total), Some(clause)) => total.checked_add(clause),
            _ => None,
        };
    }
    let missing_own_requirement = |fact: &ResourceFact| {
        let demanded = demanded_own_quantities
            .get(fact.resource())
            .copied()
            .flatten();
        match (demanded, fact.owned_quantity_term()) {
            (Some(demanded), Some(bits32_constant!(clause)))
                if demanded > constant_u32(*clause) =>
            {
                StableViewPlanError::MissingResource(ResourceFact::Own(
                    fact.resource().clone(),
                    Box::new(MachineTerm::constant(demanded)),
                ))
            }
            _ => StableViewPlanError::MissingResource(fact.clone()),
        }
    };
    let mut reserved_ownership_supports = Vec::new();
    let mut exclusive_supports = Vec::new();
    let mut canonical_transferred_ownership = Vec::new();
    let mut planned_ledger = ledger.clone();
    let mut entry_transitions = Vec::new();
    let mut mutex_uses = Vec::new();
    let mut mutex_use_requirements = BTreeMap::new();
    // Reserve exclusive requirements first. This makes the partition stable
    // under source reordering and prevents a view from hiding a later write.
    for requirement in requirements
        .iter()
        .filter(|requirement| requirement.fact.is_own())
    {
        if let Resource::MutexUse(identity) = requirement.fact.resource()
            && !same_thread_protocol_effect
        {
            if requirement.role != ResourceTransferRole::Borrow {
                return Err(StableViewPlanError::InvalidRequirement);
            }
            let source = if let Some(selected) = &requirement.selected_mutex_source {
                let selected_source = &selected.1;
                let (selected_mutex, selected_initialization) = match selected_source.resource() {
                    Resource::MutexLive(identity) => (&identity.mutex, identity.epoch),
                    Resource::MutexUse(identity) => (&identity.mutex, identity.initialization),
                    _ => {
                        return Err(StableViewPlanError::MissingResource(
                            requirement.fact.clone(),
                        ));
                    }
                };
                if selected_mutex != &identity.mutex
                    || selected_initialization.is_none()
                    || identity
                        .initialization
                        .is_some_and(|generation| selected_initialization != Some(generation))
                    || residual
                        .unique_owned_occurrence_for_fact(selected_source)
                        .is_none()
                {
                    return Err(StableViewPlanError::MissingResource(
                        requirement.fact.clone(),
                    ));
                }
                selected_source.clone()
            } else {
                residual
                    .mutex_use_candidate_at(&identity.mutex)
                    .cloned()
                    .or_else(|| residual.mutex_live_at(&identity.mutex).cloned())
                    .ok_or_else(|| StableViewPlanError::MissingResource(requirement.fact.clone()))?
            };
            // Evaluating a typed requirement preserves its selected use binding
            // but supplies the requested protected type. Concrete roots retain
            // that type in their authenticated protocol interface, not in the
            // loan atom, so compare occurrence identity here and validate the
            // protected assertion against the interface after planning.
            if requirement.selected_mutex_source.is_none()
                && identity.binding.is_some()
                && !matches!(source.resource(), Resource::MutexUse(actual)
                    if actual.binding == identity.binding
                        && actual.initialization == identity.initialization
                        && actual.mutex == identity.mutex)
            {
                return Err(StableViewPlanError::MissingResource(
                    requirement.fact.clone(),
                ));
            }
            let prepare = if split_reborrowed_views {
                mutex_calls::MutexUseCallTransfer::prepare_suspended
            } else {
                mutex_calls::MutexUseCallTransfer::prepare
            };
            let mut use_plan = prepare(
                &planned_ledger,
                caller,
                callee,
                &residual,
                &source,
                assumptions,
            )
            .map_err(|error| match error {
                mutex_calls::MutexUseCallError::Loan(error) => StableViewPlanError::Loan(error),
                _ => StableViewPlanError::MissingResource(requirement.fact.clone()),
            })?;
            use_plan = use_plan.with_required_type(identity.protected.clone());
            if let Some(selected) = &requirement.selected_mutex_source {
                use_plan = use_plan.with_selected_alias(selected.0);
            }
            let fact = use_plan.ledger.mutex_use_resource(use_plan.usage, callee)?;
            callee_resources = callee_resources
                .try_compose_with_fact(fact.clone(), assumptions)
                .map_err(|error| composition_conflict(error, &fact))?;
            mutex_use_requirements.insert(requirement.fact.clone(), fact.clone());
            let mut checked = requirement.clone();
            checked.fact = fact;
            transferred_ownership.push(checked);
            canonical_transferred_ownership.push(None);
            residual = use_plan.caller_resources.clone();
            planned_ledger = use_plan.ledger.clone();
            entry_transitions.extend(use_plan.entry_transitions.iter().cloned());
            mutex_uses.push(use_plan);
            continue;
        }
        // The occurrence this reservation is taken out of, read before the
        // removal below: the transferred hold and the effect provenance both
        // name the residual entry that actually supplied the requirement, not
        // an equal-looking owner elsewhere in the caller's partition.
        // A concrete owned footprint is reserved directly from indexed live
        // fragments before any general support lookup. Returned pointer
        // aliases must not turn this join into a scan of the parent's block.
        let fragment_reservation = residual
            .clone()
            .reserve_owned_memory_fragments_with_origins(
                &requirement.fact,
                assumptions,
                &split_origins,
            );
        if let Some((remaining, supports, origins)) = &fragment_reservation
            && supports.len() > 1
        {
            // Bare memory may be joined, but a hold-bearing owner cannot
            // lose its authenticated binding through an implicit join.
            if supports.iter().any(|support| {
                parent_view_bindings
                    .get(support)
                    .is_some_and(|binding| binding.hold.is_some())
            }) {
                return Err(StableViewPlanError::UnsupportedPartition);
            }
            callee_resources = callee_resources
                .try_compose_with_fact(requirement.fact.clone(), assumptions)
                .map_err(|error| composition_conflict(error, &requirement.fact))?;
            memory_effects.push(
                requirement
                    .fact
                    .memory_own_range()
                    .expect("fragment reservation is memory")
                    .clone(),
            );
            reserved_ownership_supports.extend(
                supports
                    .iter()
                    .copied()
                    .map(|support| (requirement.fact.clone(), support)),
            );
            if requirement.role == ResourceTransferRole::Borrow {
                exclusive_supports.extend(
                    supports
                        .iter()
                        .copied()
                        .map(|support| (requirement.fact.clone(), support)),
                );
            }
            canonical_transferred_ownership.push(None);
            transferred_ownership.push(requirement.clone());
            residual = remaining.clone();
            split_origins = origins.clone();
            continue;
        }
        let direct = fragment_reservation
            .as_ref()
            .filter(|(_, supports, _)| supports.len() == 1)
            .and_then(|(_, supports, _)| {
                residual
                    .owned_fact_for_occurrence(supports[0])
                    .map(|fact| (supports[0], fact))
            })
            .or_else(|| residual.directly_supporting_owned_entry(&requirement.fact, assumptions));
        let Some((occurrence, caller_fact)) = direct else {
            let error = missing_own_requirement(&requirement.fact);
            if let StableViewPlanError::MissingResource(missing) = &error
                && !reserved_ownership_supports.is_empty()
            {
                let reserved = reserved_ownership_supports
                    .iter()
                    .map(|(fact, _): &(ResourceFact, _)| fact.clone())
                    .collect();
                let miss = OwnedReservationMiss {
                    missing: missing.clone(),
                    reserved,
                    remaining: residual.facts().to_vec(),
                };
                LAST_OWNED_RESERVATION_MISS.with(|last| *last.borrow_mut() = Some(miss));
            }
            return Err(error);
        };
        let same_memory_extent = match (requirement.fact.resource(), caller_fact.resource()) {
            (Resource::Memory(required), Resource::Memory(caller)) => {
                match (required.wide_bounds(), caller.wide_bounds()) {
                    (None, None) => {
                        let (_, required_bytes) = required.byte_footprint();
                        let (_, caller_bytes) = caller.byte_footprint();
                        assumptions
                            .bitvector_terms_equal_for_transport(&required_bytes, &caller_bytes)
                    }
                    // Two wide ranges have one extent when their widths and
                    // 64-bit bounds agree.
                    (Some((required_start, required_end)), Some((caller_start, caller_end))) => {
                        let same = |left: &MachineTerm, right: &MachineTerm| {
                            left == right
                                || assumptions.decide(&crate::kernel::ConditionTerm::uint64_equal(
                                    left.clone(),
                                    right.clone(),
                                )) == Some(true)
                        };
                        required.element_width() == caller.element_width()
                            && same(required_start, caller_start)
                            && same(required_end, caller_end)
                    }
                    _ => false,
                }
            }
            _ => false,
        };
        let canonical_caller_fact = if !same_memory_extent
            && requirement.role == ResourceTransferRole::Borrow
            && let (
                ResourceFact::Own(Resource::Memory(required), quantity),
                ResourceFact::Own(Resource::Memory(caller), _),
            ) = (&requirement.fact, caller_fact)
        {
            // Reservation selected and consumed this caller's bytes. Return
            // exactly that slice with its original pointer domain, rather
            // than replacing the domain with the callee's selected view.
            Some(ResourceFact::Own(
                Resource::Memory(required.clone().with_carrier_of(caller)),
                quantity.clone(),
            ))
        } else {
            (same_memory_extent
                || ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(requirement.fact.clone())
                    .satisfies_fact(caller_fact, assumptions))
            .then(|| caller_fact.clone())
        };
        if let Some(binding) = parent_view_bindings.get(&occurrence)
            && binding.hold.is_some()
        {
            transferred_holds.push((requirement.fact.clone(), binding.clone()));
        }
        residual = match fragment_reservation {
            Some((remaining, supports, origins)) if supports.len() == 1 => {
                split_origins = origins;
                remaining
            }
            _ => residual
                .without_fact_incrementally_with_origins(
                    &requirement.fact,
                    assumptions,
                    &mut split_origins,
                )
                .ok_or_else(|| missing_own_requirement(&requirement.fact))?,
        };
        callee_resources = callee_resources
            .try_compose_with_fact(requirement.fact.clone(), assumptions)
            .map_err(|error| composition_conflict(error, &requirement.fact))?;
        if let Some(range) = requirement.fact.memory_own_range() {
            memory_effects.push(range.clone());
        }
        if requirement.role == ResourceTransferRole::Borrow
            && requirement.fact.memory_own_range().is_some()
        {
            exclusive_supports.push((requirement.fact.clone(), occurrence));
        }
        reserved_ownership_supports.push((requirement.fact.clone(), occurrence));
        canonical_transferred_ownership.push(canonical_caller_fact);
        transferred_ownership.push(requirement.clone());
    }

    let mut loan_roots = Vec::new();
    let mut adapter_restorations = BTreeMap::<LoanId, Vec<ResourceFact>>::new();
    let mut escrowed_owners = Vec::new();
    let mut escrowed_holds = Vec::new();
    let mut grouped = BTreeMap::<ResourceOccurrenceId, Vec<(usize, CheckedResourceFact)>>::new();
    let mut rebound = BTreeMap::<
        LoanViewBinding,
        (ResourceOccurrenceId, Vec<(usize, CheckedResourceFact)>),
    >::new();
    // The checked adapter entry that permits a viewed composite beside a
    // different escrowed head (docs/internals/stable-views.md). Only a backing the caller
    // built at the kernel's expansion boundary can answer here, and only for
    // the exact description it was checked against, so this is one indexed
    // lookup over this call's own backings rather than a search.
    let adapter_support = |required: &ResourceFact| {
        composite_backings
            .iter()
            .find(|(support, backing)| backing.support == **support && backing.adapts(required))
            .map(|(support, backing)| (*support, backing.head.clone()))
    };
    // Owner occurrences that must back a view whose byte bounds are not
    // concrete.  The concrete sweep below cannot order such a range, so the
    // covering owner itself becomes the single lent backing for everything
    // grouped under it.  See `symbolic_covering_owner`.
    let mut symbolic_covering_owner = BTreeMap::<ResourceOccurrenceId, ResourceFact>::new();
    for (index, requirement) in requirements.iter().enumerate() {
        if !requirement.fact.is_view() {
            continue;
        }
        // Equal endpoints describe no cells. The resource algebra already
        // entails this view from an empty context; there is no backing to
        // escrow, binding to reborrow, or memory to protect.
        if requirement
            .fact
            .memory_range()
            .is_some_and(|range| memory_range_is_proven_empty(range, assumptions))
        {
            continue;
        }
        let bound_occurrence = parent_view_bindings
            .select_bound_view(&requirement.fact, caller_resources, assumptions)
            .map(|occurrence| {
                (
                    occurrence,
                    parent_view_bindings.get(&occurrence).unwrap().clone(),
                )
            });
        if bound_occurrence.is_none()
            && caller_resources.has_indexed_view_witness(&requirement.fact, assumptions)
            && caller_resources
                .directly_supporting_owned_entry(&requirement.fact, assumptions)
                .is_none()
        {
            // A view description with no live loan binding carries no
            // authority (law 4), so it can neither be reborrowed nor stand in
            // for backing that the caller does not hold.
            return Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding));
        }
        if let Some((parent_occurrence, binding)) = bound_occurrence {
            ledger.validate_view_binding(binding.clone(), caller)?;
            if !bound_view_covers_requirement(
                &binding.viewed,
                caller_resources.view_fact_for_occurrence(parent_occurrence),
                &requirement.fact,
                assumptions,
            ) {
                return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
            }
            let grouped = rebound
                .entry(binding)
                .or_insert_with(|| (parent_occurrence, Vec::new()));
            if grouped.0 != parent_occurrence {
                return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
            }
            grouped.1.push((index, requirement.clone()));
            continue;
        }
        let direct = caller_resources
            .directly_supporting_owned_entry(&requirement.fact, assumptions)
            .map(|(support, owned)| (support, owned.clone()));
        let Some((support, owned)) = direct.or_else(|| adapter_support(&requirement.fact)) else {
            return Err(StableViewPlanError::MissingResource(
                requirement.fact.clone(),
            ));
        };
        let owned = &owned;
        match owned.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                continue;
            }
            Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_) => {
                return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
            }
            Resource::Composite { .. } => {
                if caller_resources.owned_occurrences_for_fact(owned).len() != 1
                    || !composite_backings
                        .get(&support)
                        .is_some_and(|backing| backing.support == support && backing.head == *owned)
                {
                    return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
                }
            }
            Resource::Memory(_) | Resource::Token { .. } => {}
        }
        if requirement
            .fact
            .memory_range()
            .is_some_and(|range| range.constant_start().is_none() || range.constant_end().is_none())
        {
            // A symbolic view range is plannable exactly when one owned
            // occurrence already covers it: the entailment above is the
            // checked coverage witness, and the whole covering owner becomes
            // the loan backing.  Law 8 forbids inferring anything else here,
            // so no residual split and no separation from a sibling
            // requirement is assumed; every requirement grouped under this
            // owner shares the one loan.
            let Resource::Memory(_) = owned.resource() else {
                return Err(StableViewPlanError::UnsupportedPartition);
            };
            symbolic_covering_owner.insert(support, owned.clone());
        }
        grouped
            .entry(support)
            .or_default()
            .push((index, requirement.clone()));
    }

    let mut planned_views = Vec::<(usize, PlannedStableView)>::new();
    for (origin_support, group) in grouped {
        // A group that must serve a symbolic range is lent whole: one loan
        // for the covering owner, one cluster holding every requirement it
        // supports.  Clustering by proven overlap is unavailable here, and
        // guessing that two symbolic ranges are separate would create two
        // escrows for bytes that unknown aliasing can share (law 8).  The
        // owner's authority is fully suspended, so nothing is left writable.
        if let Some(covering) = symbolic_covering_owner.get(&origin_support) {
            let cluster = group;
            let selected = covering.clone();
            let (support, owned) = residual
                .clone()
                .directly_supporting_owned_entry(&selected, assumptions)
                .map(|(support, owned)| (support, owned.clone()))
                .ok_or_else(|| StableViewPlanError::ConflictingRequirement(selected.clone()))?;
            if support != origin_support {
                // The exclusive reservations above already took this owner,
                // or an equal-looking occurrence would be lent instead of the
                // one the coverage was checked against.
                return Err(StableViewPlanError::ConflictingRequirement(selected));
            }
            let opening = if split_reborrowed_views {
                lend_owned_view_to_suspended_worker(
                    &mut planned_ledger,
                    &mut entry_transitions,
                    &mut residual,
                    &mut split_origins,
                    &mut parent_view_bindings,
                    &mut suspended_split_reborrows,
                    &selected,
                    support,
                    caller,
                    callee,
                    assumptions,
                )?
            } else {
                let opening = planned_ledger.lend(caller, callee, support, selected.clone())?;
                entry_transitions.push(opening.transition.clone());
                planned_ledger = planned_ledger.apply(&opening.transition)?;
                residual = residual
                    .without_selected_fact_with_origins(
                        support,
                        &selected,
                        assumptions,
                        &mut split_origins,
                    )
                    .ok_or_else(|| StableViewPlanError::MissingResource(owned.clone()))?;
                opening
            };
            loan_roots.push((
                opening.scope,
                opening.loan,
                opening.root_share,
                support,
                !split_reborrowed_views,
            ));
            escrowed_owners.push(selected.clone());
            if let Some(binding) = parent_view_bindings.get(&support)
                && binding.hold.is_some()
            {
                escrowed_holds.push((selected.clone(), binding.clone()));
            }
            let mut owner_occurrences = BTreeMap::<LoanViewBinding, ResourceOccurrenceId>::new();
            for (index, requirement) in cluster {
                let description = planned_ledger
                    .describe_view(opening.loan, requirement.fact.clone(), assumptions)
                    .map_err(|_| {
                        StableViewPlanError::ConflictingRequirement(requirement.fact.clone())
                    })?;
                let binding = LoanViewBinding {
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    support,
                    viewed: requirement.fact.clone(),
                    hold: None,
                };
                let (next_resources, occurrence) = callee_resources
                    .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                    .map_err(|error| composition_conflict(error, &requirement.fact))?;
                let occurrence = occurrence
                    .or_else(|| owner_occurrences.get(&binding).copied())
                    .or_else(|| {
                        callee_view_bindings
                            .select_bound_view(&requirement.fact, &next_resources, assumptions)
                            .filter(|occurrence| {
                                callee_view_bindings.get(occurrence) == Some(&binding)
                            })
                    })
                    .ok_or(StableViewPlanError::InvalidResidual)?;
                // Record the dependency on the occurrence itself, not just in
                // the sidecar: normalization must not merge two adjacent bound
                // views into one fact whose occurrence no requirement can then
                // find again.
                callee_resources = next_resources.with_loan_dependency(occurrence, binding.clone());
                owner_occurrences.insert(binding.clone(), occurrence);
                callee_view_bindings = callee_view_bindings.with_inserted(occurrence, binding);
                planned_views.push((
                    index,
                    PlannedStableView {
                        requirement,
                        support,
                        loan: opening.loan,
                        scope: opening.scope,
                        share: opening.root_share,
                        description,
                    },
                ));
            }
            continue;
        }
        let mut clusters: Vec<Vec<(usize, CheckedResourceFact)>> = Vec::new();
        // Keep the union beside each memory cluster.  Recomputing it by
        // walking the whole cluster on every merge made a chain of
        // overlapping views quadratic in the number of clauses.
        let mut cluster_unions: Vec<Option<MemoryRange>> = Vec::new();
        let mut memory_items = Vec::new();
        let mut non_memory_clusters = BTreeMap::<Resource, usize>::new();
        for item in group {
            if let Resource::Composite { .. } = item.1.fact.resource() {
                let resource = item.1.fact.resource().clone();
                let cluster_index = *non_memory_clusters.entry(resource).or_insert_with(|| {
                    clusters.push(Vec::new());
                    cluster_unions.push(None);
                    clusters.len() - 1
                });
                clusters[cluster_index].push(item);
                continue;
            }
            let Some(range) = item.1.fact.memory_range().cloned() else {
                if !matches!(item.1.fact.resource(), Resource::Token { .. }) {
                    return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
                }
                let resource = item.1.fact.resource().clone();
                let cluster_index = *non_memory_clusters.entry(resource).or_insert_with(|| {
                    clusters.push(Vec::new());
                    cluster_unions.push(None);
                    clusters.len() - 1
                });
                clusters[cluster_index].push(item);
                continue;
            };
            if range.constant_start().is_none() || range.constant_end().is_none() {
                return Err(StableViewPlanError::UnsupportedPartition);
            }
            memory_items.push((item, range));
        }

        // Connected components of concrete ranges can be found by sorting
        // each base/element-width family once and extending only the latest
        // component.  This avoids comparing every new view with every old
        // cluster while preserving transitive overlap decisions.
        memory_items.sort_by(|(_, left), (_, right)| {
            left.base()
                .cmp(right.base())
                .then_with(|| left.element_width().cmp(&right.element_width()))
                .then_with(|| left.constant_start().cmp(&right.constant_start()))
                .then_with(|| left.constant_end().cmp(&right.constant_end()))
        });
        for (item, range) in memory_items {
            let can_extend = cluster_unions
                .last()
                .and_then(Option::as_ref)
                .and_then(|union| concrete_memory_union(union, &range));
            if let Some(union) = can_extend {
                clusters
                    .last_mut()
                    .expect("memory cluster exists")
                    .push(item);
                *cluster_unions.last_mut().expect("memory union exists") = Some(union);
            } else {
                clusters.push(vec![item]);
                cluster_unions.push(Some(range));
            }
        }

        for (cluster, cluster_union) in clusters.into_iter().zip(cluster_unions) {
            let selected = if cluster
                .first()
                .and_then(|(_, item)| item.fact.memory_range())
                .is_some()
            {
                let union = cluster_union.ok_or(StableViewPlanError::UnsupportedPartition)?;
                ResourceFact::own_memory(union)
            } else if cluster
                .first()
                .is_some_and(|(_, item)| matches!(item.fact.resource(), Resource::Composite { .. }))
            {
                let required = cluster
                    .first()
                    .map(|(_, item)| &item.fact)
                    .ok_or(StableViewPlanError::UnsupportedPartition)?;
                let residual_for_selection = residual.clone();
                // The adapter's head is a different composite from the
                // clause, so select it by the checked backing and then take
                // the residual's own occurrence of that head.
                let head = adapter_support(required)
                    .map(|(_, head)| head)
                    .unwrap_or_else(|| required.clone());
                let (support, owned) = residual_for_selection
                    .directly_supporting_owned_entry(&head, assumptions)
                    .ok_or_else(|| StableViewPlanError::ConflictingRequirement(required.clone()))?;
                if matches!(owned.resource(), Resource::Composite { .. })
                    && residual_for_selection
                        .owned_occurrences_for_fact(owned)
                        .len()
                        != 1
                {
                    return Err(StableViewPlanError::ConflictingRequirement(owned.clone()));
                }
                let Some(backing) = composite_backings.get(&support) else {
                    return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
                };
                if backing.support != support || backing.head != *owned {
                    return Err(StableViewPlanError::InvalidResidual);
                }
                owned.clone()
            } else {
                let resource = cluster
                    .first()
                    .map(|(_, item)| item.fact.resource().clone())
                    .ok_or(StableViewPlanError::UnsupportedPartition)?;
                ResourceFact::own(Resource::Token {
                    name: match resource {
                        Resource::Token { ref name, .. } => name.clone(),
                        _ => return Err(StableViewPlanError::UnsupportedPartition),
                    },
                    arguments: match resource {
                        Resource::Token { arguments, .. } => arguments,
                        _ => return Err(StableViewPlanError::UnsupportedPartition),
                    },
                })
            };
            let Some((support, owned)) = residual
                .clone()
                .directly_supporting_owned_entry(&selected, assumptions)
                .map(|(support, owned)| (support, owned.clone()))
            else {
                return Err(StableViewPlanError::ConflictingRequirement(selected));
            };
            // Splitting constructs this relation while creating each residual.
            // Do not infer it from coverage or absence of another supplier.
            if split_origins.origin_of(support) != origin_support {
                return Err(StableViewPlanError::ConflictingRequirement(selected));
            }
            // The checked supplier owns this slice in its original pointer
            // domain. Keep that domain in escrow; the callee's view may have
            // selected a known member extent instead.
            let selected = match (selected, owned.memory_own_range()) {
                (ResourceFact::Own(Resource::Memory(range), quantity), Some(source)) => {
                    ResourceFact::Own(Resource::Memory(range.with_carrier_of(source)), quantity)
                }
                (selected, _) => selected,
            };
            let suspended_owned_reader =
                split_reborrowed_views && selected.memory_own_range().is_some();
            let opening = if suspended_owned_reader {
                lend_owned_view_to_suspended_worker(
                    &mut planned_ledger,
                    &mut entry_transitions,
                    &mut residual,
                    &mut split_origins,
                    &mut parent_view_bindings,
                    &mut suspended_split_reborrows,
                    &selected,
                    support,
                    caller,
                    callee,
                    assumptions,
                )?
            } else if let Some(backing) = composite_backings.get(&support) {
                let remaining = residual
                    .clone()
                    .without_selected_fact_with_origins(
                        support,
                        &selected,
                        assumptions,
                        &mut split_origins,
                    )
                    .ok_or(StableViewPlanError::MissingResource(selected.clone()))?;
                // The exclusive requirements were reserved out of `residual`
                // before any view was planned, so the residual alone cannot
                // see a callee contract that asks to own bytes its own viewed
                // composite covers.  Put the reserved owners back beside the
                // frontier: this is the caller's partition as the contract
                // actually demands it, and a self-overlapping contract is
                // refused here rather than handing the callee an owner and a
                // view of the same authority (law 1, law 8).
                let protected = remaining
                    .clone()
                    .unchecked_with_facts(
                        transferred_ownership
                            .iter()
                            .map(|requirement| requirement.fact.clone()),
                    )
                    .unchecked_with_facts(backing.pieces.clone());
                if protected.validity_error(assumptions).is_some() {
                    return Err(StableViewPlanError::ConflictingRequirement(selected));
                }
                planned_ledger.lend_composite(
                    caller,
                    callee,
                    support,
                    selected.clone(),
                    backing.clone(),
                )?
            } else {
                planned_ledger.lend(caller, callee, support, selected.clone())?
            };
            if !suspended_owned_reader {
                entry_transitions.push(opening.transition.clone());
                planned_ledger = planned_ledger.apply(&opening.transition)?;
                residual = residual
                    .without_selected_fact_with_origins(
                        support,
                        &selected,
                        assumptions,
                        &mut split_origins,
                    )
                    .ok_or_else(|| StableViewPlanError::MissingResource(owned.clone()))?;
            }
            loan_roots.push((
                opening.scope,
                opening.loan,
                opening.root_share,
                support,
                !suspended_owned_reader,
            ));
            // What the caller actually holds across the call: for an adapter
            // lend the head is a name the planner gave to owned facts the
            // caller had, so those facts are the honest escrow record and
            // what recovery hands back.
            match composite_backings
                .get(&support)
                .filter(|backing| !backing.restored.is_empty())
            {
                Some(backing) => {
                    escrowed_owners.extend(backing.restored.iter().cloned());
                    adapter_restorations.insert(opening.loan, backing.restored.clone());
                }
                None => escrowed_owners.push(selected.clone()),
            }
            if let Some(binding) = parent_view_bindings.get(&support)
                && binding.hold.is_some()
            {
                escrowed_holds.push((selected.clone(), binding.clone()));
            }
            let mut owner_occurrences = BTreeMap::<LoanViewBinding, ResourceOccurrenceId>::new();
            for (index, requirement) in cluster {
                let description = planned_ledger
                    .describe_view(opening.loan, requirement.fact.clone(), assumptions)
                    .map_err(|_| {
                        StableViewPlanError::ConflictingRequirement(requirement.fact.clone())
                    })?;
                let binding = LoanViewBinding {
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    support,
                    viewed: requirement.fact.clone(),
                    hold: None,
                };
                let (next_resources, occurrence) = callee_resources
                    .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                    .map_err(|error| composition_conflict(error, &requirement.fact))?;
                let occurrence = occurrence
                    .or_else(|| owner_occurrences.get(&binding).copied())
                    .or_else(|| {
                        callee_view_bindings
                            .select_bound_view(&requirement.fact, &next_resources, assumptions)
                            .filter(|occurrence| {
                                callee_view_bindings.get(occurrence) == Some(&binding)
                            })
                    })
                    .ok_or(StableViewPlanError::InvalidResidual)?;
                // Record the dependency on the occurrence itself, not just in
                // the sidecar: normalization must not merge two adjacent bound
                // views into one fact whose occurrence no requirement can then
                // find again.
                callee_resources = next_resources.with_loan_dependency(occurrence, binding.clone());
                owner_occurrences.insert(binding.clone(), occurrence);
                callee_view_bindings = callee_view_bindings.with_inserted(occurrence, binding);
                planned_views.push((
                    index,
                    PlannedStableView {
                        requirement,
                        support,
                        loan: opening.loan,
                        scope: opening.scope,
                        share: opening.root_share,
                        description,
                    },
                ));
            }
        }
    }
    for (binding, (parent_occurrence, group)) in rebound {
        let worker_binding = if split_reborrowed_views {
            let (split, retained, worker) =
                planned_ledger.split(binding.share, caller, caller, caller)?;
            planned_ledger = planned_ledger.apply(&split)?;
            entry_transitions.push(split);
            let retained_binding = LoanViewBinding {
                share: retained,
                ..binding.clone()
            };
            parent_view_bindings =
                parent_view_bindings.with_inserted(parent_occurrence, retained_binding.clone());
            residual = residual.with_loan_dependency(parent_occurrence, retained_binding);
            LoanViewBinding {
                share: worker,
                ..binding.clone()
            }
        } else {
            binding.clone()
        };
        let opening = planned_ledger.reborrow(worker_binding.clone(), caller, callee)?;
        entry_transitions.push(opening.transition.clone());
        planned_ledger = planned_ledger.apply(&opening.transition)?;
        let child_binding = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: binding.support,
            viewed: binding.viewed.clone(),
            hold: None,
        };
        loan_roots.push((
            opening.scope,
            opening.loan,
            opening.root_share,
            binding.support,
            false,
        ));
        rebound_parents.insert(opening.loan, binding.clone());
        if split_reborrowed_views {
            suspended_split_reborrows
                .insert(opening.loan, (parent_occurrence, worker_binding.share));
        }
        let mut child_occurrence = None;
        for (index, requirement) in group {
            // Membership in this group already carries the coverage checked
            // against this exact parent binding above. Reborrow preserves that
            // permitted view, so its child description keeps the same checked
            // restriction without asking the resource algebra again.
            let (next_resources, occurrence) = callee_resources
                .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                .map_err(|error| composition_conflict(error, &requirement.fact))?;
            let occurrence = occurrence
                .or(child_occurrence)
                .or_else(|| {
                    callee_view_bindings
                        .select_bound_view(&requirement.fact, &next_resources, assumptions)
                        .filter(|occurrence| {
                            callee_view_bindings.get(occurrence) == Some(&child_binding)
                        })
                })
                .ok_or(StableViewPlanError::InvalidResidual)?;
            callee_resources =
                next_resources.with_loan_dependency(occurrence, child_binding.clone());
            child_occurrence = Some(occurrence);
            callee_view_bindings =
                callee_view_bindings.with_inserted(occurrence, child_binding.clone());
            let description = StableViewDescription {
                viewed: requirement.fact.clone(),
                ..opening.description.clone()
            };
            planned_views.push((
                index,
                PlannedStableView {
                    requirement,
                    support: binding.support,
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    description,
                },
            ));
        }
    }
    planned_views.sort_by_key(|(index, _)| *index);
    stable_views.extend(planned_views.into_iter().map(|(_, view)| view));

    let exclusive_call = if exclusive_supports.is_empty() || split_reborrowed_views {
        None
    } else {
        let (binding, transition) =
            planned_ledger.open_exclusive_call(caller, callee, exclusive_supports)?;
        planned_ledger = planned_ledger.apply(&transition)?;
        entry_transitions.push(transition);
        Some(binding)
    };
    Ok(StableViewTransferPlan {
        exclusive_call,
        caller_resources_after_requirements: residual,
        callee_resources,
        transferred_ownership,
        canonical_transferred_ownership,
        stable_views,
        memory_effects,
        reserved_ownership_supports,
        ledger: planned_ledger,
        entry_transitions,
        mutex_uses,
        mutex_use_requirements,
        callee_view_bindings,
        parent_view_bindings: parent_view_bindings.clone(),
        parent_ledger: ledger.clone(),
        caller,
        callee,
        loan_roots,
        escrowed_owners,
        escrowed_holds,
        transferred_holds,
        rebound_parents,
        suspended_split_reborrows,
        suspended_local_parents: BTreeMap::new(),
        suspended_local_reborrows: BTreeMap::new(),
        adapter_restorations,
    })
}

impl StableViewTransferPlan {
    /// Add the call's implicit local views to the same checked entry trace as
    /// explicit resources. No owned fact is inserted into either context.
    #[cfg(test)]
    pub(crate) fn lend_local_views(
        &mut self,
        memory: &super::Memory,
        requirements: &[CheckedResourceFact],
        assumptions: &PureFactContext,
    ) -> Result<(), StableViewPlanError> {
        self.lend_local_views_with_worker_shares(memory, requirements, assumptions, None)
    }

    pub(crate) fn lend_local_views_with_worker_shares(
        &mut self,
        memory: &super::Memory,
        requirements: &[CheckedResourceFact],
        assumptions: &PureFactContext,
        existing: Option<&BTreeMap<ResourceFact, LoanViewBinding>>,
    ) -> Result<(), StableViewPlanError> {
        let mut seen = std::collections::BTreeSet::new();
        for requirement in requirements {
            crate::instrumentation::record_deterministic_work(1);
            if !seen.insert(requirement.fact.clone()) {
                continue;
            }
            let backing = LocalViewBacking::check(memory, &requirement.fact, assumptions)
                .ok_or_else(|| StableViewPlanError::MissingResource(requirement.fact.clone()))?;
            let range = requirement
                .fact
                .memory_range()
                .expect("checked memory view");
            let (resources, occurrence) = self
                .callee_resources
                .clone()
                .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                .map_err(|error| composition_conflict(error, &requirement.fact))?;
            let support = occurrence.ok_or(StableViewPlanError::InvalidResidual)?;
            if let Some(existing) = existing {
                let parent = if let Some(binding) = existing.get(&requirement.fact) {
                    self.ledger
                        .validate_view_binding(binding.clone(), self.caller)?;
                    binding.clone()
                } else {
                    // Only the first worker opens the local root. The parent
                    // keeps its close right and a share, without receiving an
                    // owned or viewed resource fact.
                    self.ledger
                        .permits_memory_access_with_assumptions(range, assumptions)?;
                    let opening = self.ledger.open_borrowed_root(
                        self.caller,
                        support,
                        requirement.fact.clone(),
                        None,
                        Some((self.caller, backing)),
                    )?;
                    self.ledger = self.ledger.apply(&opening.transition)?;
                    self.entry_transitions.push(opening.transition);
                    LoanViewBinding {
                        loan: opening.loan,
                        scope: opening.scope,
                        share: opening.root_share,
                        support,
                        viewed: requirement.fact.clone(),
                        hold: None,
                    }
                };
                let (split, retained, worker) =
                    self.ledger
                        .split(parent.share, self.caller, self.caller, self.caller)?;
                self.ledger = self.ledger.apply(&split)?;
                self.entry_transitions.push(split);
                let worker_binding = LoanViewBinding {
                    share: worker,
                    ..parent.clone()
                };
                let opening = self
                    .ledger
                    .reborrow(worker_binding, self.caller, self.callee)?;
                self.ledger = self.ledger.apply(&opening.transition)?;
                self.entry_transitions.push(opening.transition);
                let child_binding = LoanViewBinding {
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    support: parent.support,
                    viewed: requirement.fact.clone(),
                    hold: None,
                };
                self.callee_resources =
                    resources.with_loan_dependency(support, child_binding.clone());
                self.callee_view_bindings = self
                    .callee_view_bindings
                    .with_inserted(support, child_binding);
                self.loan_roots.push((
                    opening.scope,
                    opening.loan,
                    opening.root_share,
                    support,
                    false,
                ));
                self.stable_views.push(PlannedStableView {
                    requirement: requirement.clone(),
                    support,
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    description: opening.description,
                });
                self.suspended_local_parents.insert(
                    requirement.fact.clone(),
                    LoanViewBinding {
                        share: retained,
                        ..parent
                    },
                );
                self.suspended_local_reborrows
                    .insert(opening.loan, (requirement.fact.clone(), worker));
                continue;
            }
            // An ordinary local loan closes with its call. New local
            // authority cannot bypass an existing loan.
            self.parent_ledger
                .permits_memory_access_with_assumptions(range, assumptions)?;
            let opening = self.ledger.open_borrowed_root(
                self.callee,
                support,
                requirement.fact.clone(),
                None,
                Some((self.caller, backing)),
            )?;
            self.ledger = self.ledger.apply(&opening.transition)?;
            self.entry_transitions.push(opening.transition);
            let binding = LoanViewBinding {
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                support,
                viewed: requirement.fact.clone(),
                hold: None,
            };
            self.callee_resources = resources.with_loan_dependency(support, binding.clone());
            self.callee_view_bindings = self.callee_view_bindings.with_inserted(support, binding);
            self.loan_roots.push((
                opening.scope,
                opening.loan,
                opening.root_share,
                support,
                false,
            ));
            self.stable_views.push(PlannedStableView {
                requirement: requirement.clone(),
                support,
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                description: opening.description,
            });
        }
        Ok(())
    }

    pub(crate) fn caller_ledger(&self) -> &LoanLedger {
        &self.parent_ledger
    }

    pub(crate) fn suspended_local_parents(&self) -> &BTreeMap<ResourceFact, LoanViewBinding> {
        &self.suspended_local_parents
    }

    pub(crate) fn caller_participant(&self) -> LoanParticipantId {
        self.caller
    }

    pub(crate) fn caller_view_bindings_after_requirements(&self) -> &LoanViewBindings {
        &self.parent_view_bindings
    }

    pub(crate) fn callee_participant(&self) -> LoanParticipantId {
        self.callee
    }

    pub(crate) fn has_stable_views(&self) -> bool {
        !self.stable_views.is_empty()
    }

    pub(crate) fn stable_views(&self) -> &[PlannedStableView] {
        &self.stable_views
    }

    /// The owned facts a lend escrowed out of the caller residual. Recovery
    /// composes each one back, so a caller-side check on the residual has to
    /// read them too or it will treat lent ownership as gone.
    pub(crate) fn escrowed_owners(&self) -> &[ResourceFact] {
        &self.escrowed_owners
    }

    pub(crate) fn callee_view_bindings(&self) -> &LoanViewBindings {
        &self.callee_view_bindings
    }

    /// Closes every unmodified root share and returns the exact escrowed
    /// ownership to the residual caller context.
    /// Recovers the call's loans. `escaping` names the loans a produced
    /// borrowing composite keeps open, with that composite's head fact; such
    /// a loan is not ended (an escrowed owner stays escrowed) and the caller
    /// receives a hold binding for the head instead. `consumed_holds` are the
    /// hold bindings of owned composites the callee consumed without
    /// returning: their holds are released, and a root the caller can then
    /// close is ended and its owner recovered (step 7).
    pub(crate) fn recover_stable_views(
        self,
        assumptions: &PureFactContext,
        escaping: &BTreeMap<LoanId, Vec<ResourceFact>>,
        consumed_holds: &[LoanViewBinding],
    ) -> Result<StableViewRecovery, StableViewPlanError> {
        self.recover_stable_views_impl(assumptions, escaping, consumed_holds, false)
    }

    pub(crate) fn supports_suspended_memory_recovery(&self) -> bool {
        self.transferred_holds.is_empty()
            && self.escrowed_holds.is_empty()
            && self.adapter_restorations.is_empty()
    }

    /// Recover only this suspended call's loans against the parent's current
    /// context. Other children may have opened loans since entry, so recovery
    /// must keep the checked terminal ledger, never restore the entry state.
    pub(crate) fn recover_suspended_views(
        mut self,
        ledger: LoanLedger,
        resources: ResourceContext,
        bindings: LoanViewBindings,
        local_bindings: BTreeMap<ResourceFact, LoanViewBinding>,
        assumptions: &PureFactContext,
    ) -> Result<StableViewRecovery, StableViewPlanError> {
        self.ledger = ledger;
        self.caller_resources_after_requirements = resources;
        self.parent_view_bindings = bindings;
        self.suspended_local_parents = local_bindings;
        self.recover_stable_views_impl(assumptions, &BTreeMap::new(), &[], true)
    }

    fn recover_stable_views_impl(
        self,
        assumptions: &PureFactContext,
        escaping: &BTreeMap<LoanId, Vec<ResourceFact>>,
        consumed_holds: &[LoanViewBinding],
        mut keep_terminal: bool,
    ) -> Result<StableViewRecovery, StableViewPlanError> {
        // Recovery changes only this call's escrow. Normalizing the ambient
        // frame would rebuild unrelated resource indexes at every child join.
        let restore_resource = |resources: ResourceContext, fact: &ResourceFact| {
            resources
                .try_compose_into_valid_context_delaying_normalization(
                    std::iter::once(fact.clone()),
                    assumptions,
                )
                .map_err(|error| composition_conflict(error, fact))
        };
        self.validate_exclusive_reservation()?;
        let parent_ledger = self.parent_ledger;
        let stable_views = self.stable_views.clone();
        let loan_roots = self.loan_roots.clone();
        let mut ledger = self.ledger;
        let mut resources = self.caller_resources_after_requirements;
        let mut view_bindings = self.parent_view_bindings.clone();
        let mut local_view_updates = BTreeMap::new();
        let mut transitions = Vec::new();
        let mut recovered_escrows = Vec::new();
        let mut mutex_authority_updates = Vec::new();
        let mut pending_holds: Vec<(Vec<ResourceFact>, LoanViewBinding)> = Vec::new();
        for (scope, loan, root, support, recoverable) in loan_roots.into_iter().rev() {
            let transfer = ledger.transfer(root, self.callee, self.caller)?;
            ledger = ledger.apply(&transfer)?;
            transitions.push(transfer);
            if let Some(heads) = escaping.get(&loan) {
                if recoverable {
                    // The owner stays escrowed: the produced composite now
                    // describes it, and the caller's binding to this open
                    // loan is what the composite's hold rests on.
                    let viewed = stable_views
                        .iter()
                        .find(|view| view.loan == loan)
                        .map(|view| view.requirement.fact.clone())
                        .ok_or(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))?;
                    pending_holds.push((
                        heads.clone(),
                        LoanViewBinding {
                            loan,
                            scope,
                            share: root,
                            support,
                            viewed,
                            hold: None,
                        },
                    ));
                    keep_terminal = true;
                    continue;
                }
                // The caller lent a view of its own: the child ends as usual
                // and the composite holds the caller's parent binding.
                let end = ledger.end(scope, self.caller)?;
                ledger = ledger.apply(&end)?;
                transitions.push(end);
                let parent = self
                    .rebound_parents
                    .get(&loan)
                    .cloned()
                    .ok_or(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))?;
                pending_holds.push((heads.clone(), parent));
                continue;
            }
            let end = ledger.end(scope, self.caller)?;
            ledger = ledger.apply(&end)?;
            transitions.push(end);
            if let Some((fact, worker_share)) = self.suspended_local_reborrows.get(&loan) {
                let binding = self
                    .suspended_local_parents
                    .get(fact)
                    .cloned()
                    .ok_or(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))?;
                ledger.validate_view_binding(binding.clone(), self.caller)?;
                let (joined, merged_share, joins) =
                    ledger.join_available_share_ancestors(*worker_share, self.caller)?;
                ledger = joined;
                transitions.extend(joins);
                let updated = if ledger.scope_can_end(binding.scope, self.caller) {
                    let close = ledger.end(binding.scope, self.caller)?;
                    ledger = ledger.apply(&close)?;
                    transitions.push(close);
                    None
                } else if ledger
                    .validate_view_binding(binding.clone(), self.caller)
                    .is_ok()
                {
                    Some(binding)
                } else {
                    let updated = LoanViewBinding {
                        share: merged_share,
                        ..binding
                    };
                    ledger.validate_view_binding(updated.clone(), self.caller)?;
                    Some(updated)
                };
                local_view_updates.insert(fact.clone(), updated);
            }
            if let Some((occurrence, worker_share)) = self.suspended_split_reborrows.get(&loan) {
                let binding = view_bindings
                    .get(occurrence)
                    .cloned()
                    .ok_or(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))?;
                ledger.validate_view_binding(binding.clone(), self.caller)?;
                let (joined, merged_share, joins) =
                    ledger.join_available_share_ancestors(*worker_share, self.caller)?;
                ledger = joined;
                transitions.extend(joins);
                if ledger.loan_is_recoverable_by(binding.loan, self.caller)
                    && ledger.scope_can_end(binding.scope, self.caller)
                {
                    let close = ledger.end(binding.scope, self.caller)?;
                    ledger = ledger.apply(&close)?;
                    transitions.push(close);
                    let (recover, escrow, recovered_support) =
                        ledger.recover(binding.loan, self.caller)?;
                    ledger = ledger.apply(&recover)?;
                    transitions.push(recover);
                    if recovered_support != binding.support {
                        return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
                    }
                    resources = resources
                        .without_bound_view_occurrence(*occurrence, &binding)
                        .ok_or(StableViewPlanError::InvalidResidual)?;
                    view_bindings = view_bindings.without(*occurrence);
                    resources = restore_resource(resources, &escrow)?;
                    recovered_escrows.push((escrow, None));
                } else if ledger
                    .validate_view_binding(binding.clone(), self.caller)
                    .is_err()
                {
                    let binding = LoanViewBinding {
                        share: merged_share,
                        ..binding
                    };
                    ledger.validate_view_binding(binding.clone(), self.caller)?;
                    view_bindings = view_bindings.with_inserted(*occurrence, binding.clone());
                    resources = resources.with_loan_dependency(*occurrence, binding);
                }
            }
            if recoverable {
                let (recover, escrow, recovered_support) = ledger.recover(loan, self.caller)?;
                ledger = ledger.apply(&recover)?;
                transitions.push(recover);
                if recovered_support != support {
                    return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
                }
                // An adapter lend escrowed a head the planner materialized
                // for this call. Recovery restores exactly the owned facts it
                // was materialized from, so a `views` requirement leaves the
                // caller's own packaging exactly as it found it.
                if let Some(restored) = self.adapter_restorations.get(&loan) {
                    for fact in restored {
                        resources = restore_resource(resources, fact)?;
                        recovered_escrows.push((fact.clone(), None));
                    }
                    continue;
                }
                resources = restore_resource(resources, &escrow)?;
                let hold_binding = self
                    .escrowed_holds
                    .iter()
                    .find(|(held, _)| *held == escrow)
                    .map(|(_, binding)| binding.clone());
                recovered_escrows.push((escrow, hold_binding));
            }
        }
        // A composite the callee consumed took its borrow with it: release
        // the hold, and if that leaves a root this caller may close, close it
        // and recover the owner, as the fold's mirror image.
        for binding in consumed_holds {
            let Some(hold) = binding.hold else {
                continue;
            };
            let (released, transition) = ledger.release_with_transition(hold, self.caller)?;
            ledger = released;
            transitions.push(transition);
            keep_terminal = true;
            if !ledger.scope_can_end(binding.scope, self.caller) {
                continue;
            }
            let end = ledger.end(binding.scope, self.caller)?;
            ledger = ledger.apply(&end)?;
            transitions.push(end);
            if ledger.loan_is_recoverable_by(binding.loan, self.caller) {
                let (recover, escrow, _) = ledger.recover(binding.loan, self.caller)?;
                ledger = ledger.apply(&recover)?;
                transitions.push(recover);
                resources = restore_resource(resources, &escrow)?;
                recovered_escrows.push((escrow, None));
            }
        }
        for use_plan in self.mutex_uses.iter().rev() {
            if use_plan.is_suspended() {
                let returned = use_plan
                    .finish_suspended_checked_ledger(
                        ledger,
                        resources,
                        &use_plan.callee_resources,
                        assumptions,
                    )
                    .map_err(|error| match error {
                        mutex_calls::MutexUseCallError::Loan(error) => {
                            StableViewPlanError::Loan(error)
                        }
                        _ => StableViewPlanError::InvalidResidual,
                    })?;
                ledger = returned.ledger;
                resources = returned.caller_resources;
                mutex_authority_updates.extend(returned.authority_updates);
                transitions.extend(returned.exit_transitions);
                keep_terminal = true;
            } else {
                let returned = use_plan
                    .finish_checked_ledger(ledger, &use_plan.callee_resources, assumptions)
                    .map_err(|error| match error {
                        mutex_calls::MutexUseCallError::Loan(error) => {
                            StableViewPlanError::Loan(error)
                        }
                        _ => StableViewPlanError::InvalidResidual,
                    })?;
                ledger = returned.ledger;
                transitions.extend(returned.exit_transitions);
                let source = use_plan.source_resource().clone();
                resources = restore_resource(resources, &source)?;
                recovered_escrows.push((source, None));
            }
        }
        // Every scope in loan_roots that this plan ended has just passed End
        // and Recover. End checks its indexed dependency set, so a registered
        // child would have refused before this checkpoint. When nothing
        // survives the call, the plan rolls back to the exact predecessor
        // root without a whole-ledger quiescence scan; a surviving (escaping)
        // loan or a released hold keeps the terminal ledger, since the call
        // changed authority.
        if let Some(binding) = &self.exclusive_call {
            let transition = ledger.return_exclusive_call(binding, self.caller)?;
            ledger = ledger.apply(&transition)?;
            transitions.push(transition);
        }
        let terminal_ledger = ledger.clone();
        ledger = if keep_terminal { ledger } else { parent_ledger };
        let hold_base_ledger = ledger.clone();
        let mut hold_transitions = Vec::new();
        let mut escaped_holds = Vec::new();
        for (heads, binding) in pending_holds {
            let (held, hold, transition) = ledger.hold_with_transition(&binding, self.caller)?;
            ledger = held;
            hold_transitions.push(transition);
            let binding = LoanViewBinding {
                hold: Some(hold),
                ..binding
            };
            for head in heads {
                escaped_holds.push(EscapedHold {
                    head,
                    binding: binding.clone(),
                });
            }
        }
        Ok(StableViewRecovery {
            ledger,
            terminal_ledger,
            hold_base_ledger,
            hold_transitions,
            resources,
            recovered_escrows,
            mutex_authority_updates,
            escaped_holds,
            view_bindings,
            local_view_updates,
            transitions,
        })
    }

    fn validate_exclusive_reservation(&self) -> Result<(), LoanRefusal> {
        let recorded = self.ledger.storage.data.exclusive_holders.get(&self.callee);
        match &self.exclusive_call {
            None if recorded.is_none() => Ok(()),
            Some(binding) => {
                self.ledger.validate_exclusive_call(binding, self.callee)?;
                let reserved: BTreeSet<_> = self.reserved_ownership_supports.iter().collect();
                for reservation in binding.supports.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if !reserved.contains(reservation)
                        || !self
                            .callee_resources
                            .satisfies_fact(&reservation.0, &PureFactContext::new())
                    {
                        return Err(LoanRefusal::InvalidEvidence);
                    }
                }
                Ok(())
            }
            _ => Err(LoanRefusal::InvalidEvidence),
        }
    }

    pub(crate) fn recheck_entry(
        &self,
        predecessor: &LoanLedger,
    ) -> Result<LoanLedger, LoanRefusal> {
        self.validate_exclusive_reservation()?;
        let mut current = predecessor.clone();
        for transition in &self.entry_transitions {
            crate::instrumentation::record_deterministic_work(1);
            current = current.apply(transition)?;
        }
        (current == self.ledger)
            .then_some(current)
            .ok_or(LoanRefusal::InvalidEvidence)
    }
}

fn concrete_memory_union(left: &MemoryRange, right: &MemoryRange) -> Option<MemoryRange> {
    // Every overlap decision is a named unit of planner work.  In
    // particular, the scaling gate must see candidate comparisons rather
    // than only the final number of clusters.
    crate::instrumentation::record_deterministic_work(1);
    if left.base() != right.base() || left.element_width() != right.element_width() {
        return None;
    }
    let left_start = left.constant_start()?;
    let left_end = left.constant_end()?;
    let right_start = right.constant_start()?;
    let right_end = right.constant_end()?;
    if left_start > left_end || right_start > right_end {
        return None;
    }
    if left_end < right_start || right_end < left_start {
        return None;
    }
    Some(MemoryRange::new_with_element_width(
        left.base().clone(),
        left_start.min(right_start).into(),
        left_end.max(right_end).into(),
        left.element_width(),
    ))
}

fn is_mutex_lifetime_owner(fact: &ResourceFact) -> bool {
    matches!(fact, ResourceFact::Own(Resource::MutexLive(_), quantity)
        if quantity.as_const() == Some(1))
}

impl LoanLedger {
    pub(crate) fn new() -> Self {
        static NEXT_ARENA: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let arena = NEXT_ARENA.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Self {
            storage: Arc::new(LoanLedgerStorage {
                state: LoanLedgerStateId::fresh(),
                data: LoanLedgerData {
                    arena,
                    exclusive_calls: PersistentMap::default(),
                    exclusive_holders: PersistentMap::default(),
                    local_references: PersistentMap::default(),
                    local_reference_roots: PersistentMap::default(),
                    local_reference_holders: PersistentMap::default(),
                    source_local_references: PersistentMap::default(),
                    local_reference_scope: None,
                    next_scope: 0,
                    next_loan: 0,
                    next_share: 0,
                    next_hold: 0,
                    holds: PersistentMap::default(),
                    scopes: PersistentMap::default(),
                    loans: PersistentMap::default(),
                    shares: PersistentMap::default(),
                    active_memory_index: PersistentMap::default(),
                    active_memory_subtree: PersistentMap::default(),
                    active_nonlocal_indexed_ranges: 0,
                    active_memory_loans: 0,
                    active_footprint: Default::default(),
                    cache_memory_index: PersistentMap::default(),
                    cache_memory_subtree: PersistentMap::default(),
                    unindexed_memory: PersistentMap::default(),
                },
            }),
        }
    }

    pub(crate) fn fresh_participant(&self) -> Result<LoanParticipantId, LoanRefusal> {
        static NEXT_PARTICIPANT: std::sync::atomic::AtomicU64 =
            std::sync::atomic::AtomicU64::new(0);
        let participant = LoanParticipantId {
            arena: self.storage.data.arena,
            ordinal: NEXT_PARTICIPANT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        };
        Ok(participant)
    }

    pub(crate) fn is_pristine(&self) -> bool {
        let data = &self.storage.data;
        if data.local_reference_scope.is_some()
            || !data.exclusive_calls.is_empty()
            || !data.exclusive_holders.is_empty()
            || !data.local_references.is_empty()
            || !data.local_reference_roots.is_empty()
            || !data.local_reference_holders.is_empty()
            || !data.source_local_references.is_empty()
        {
            return false;
        }
        data.next_scope == 0
            && data.next_loan == 0
            && data.next_share == 0
            && data.scopes.is_empty()
            && data.loans.is_empty()
            && data.shares.is_empty()
    }

    /// Stable identity for indexed evidence summaries.  The identity is
    /// opaque outside this module; it is only used to look up the exact
    /// predecessor root that a checked call named.
    pub(crate) fn state_identity(&self) -> u64 {
        self.storage.state.0
    }

    pub(crate) fn contains_participant(&self, participant: LoanParticipantId) -> bool {
        self.storage.data.arena == participant.arena
    }

    pub(crate) fn lend(
        &self,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: ResourceFact,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.require_participant(lender)?;
        self.require_participant(borrower)?;
        if support == ResourceOccurrenceId::default() {
            return Err(LoanRefusal::MissingBacking);
        }
        if !escrow.is_own() {
            return Err(LoanRefusal::NotOwnership);
        }
        if !matches!(
            escrow.resource(),
            Resource::Memory(_) | Resource::Token { .. }
        ) {
            return Err(LoanRefusal::UnsupportedResource);
        }
        let scope = LoanScopeId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let evidence = LoanTransitionEvidence::Lend {
            lender,
            borrower,
            support,
            escrow: escrow.clone(),
            scope,
            loan,
            root,
        };
        Ok(LoanOpening {
            scope,
            loan,
            root_share: root,
            description: StableViewDescription {
                loan,
                support,
                viewed: ResourceFact::View(escrow.resource().clone()),
            },
            transition: self.issue(evidence)?,
        })
    }

    /// The mutex adapter consumes the actual resource occurrence before
    /// installing this successor. This opening grants lifetime use only;
    /// ordinary `lend` deliberately continues to reject mutex owners.
    #[cfg(test)]
    pub(crate) fn lend_mutex_use(
        &self,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: ResourceFact,
    ) -> Result<(Self, MutexUseLoan), LoanRefusal> {
        let (ledger, loan, _) =
            self.lend_mutex_use_with_transition(lender, borrower, support, escrow)?;
        Ok((ledger, loan))
    }

    pub(crate) fn lend_mutex_use_with_transition(
        &self,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: ResourceFact,
    ) -> Result<(Self, MutexUseLoan, CheckedLoanTransition), LoanRefusal> {
        if !is_mutex_lifetime_owner(&escrow) {
            return Err(LoanRefusal::UnsupportedResource);
        }
        let scope = LoanScopeId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let transition = self.issue(LoanTransitionEvidence::Lend {
            lender,
            borrower,
            support,
            escrow,
            scope,
            loan,
            root,
        })?;
        Ok((
            self.apply(&transition)?,
            MutexUseLoan {
                scope,
                loan,
                usage: MutexUseBinding(LoanAuthorityBinding {
                    loan,
                    scope,
                    share: root,
                    support,
                }),
            },
            transition,
        ))
    }

    /// Check possession of this scope, then consult the original escrow or
    /// modular input description by its indexed identity. Root shares may be
    /// pinned: the root's *scope*
    /// must remain live, but its holder need not be the current borrower.
    fn mutex_use_identity_description(
        &self,
        usage: MutexUseBinding,
        holder: LoanParticipantId,
    ) -> Result<&ResourceFact, LoanRefusal> {
        let record = self.validate_authority_binding(usage.0, holder)?;
        let root_id = record.mutex_root.ok_or(LoanRefusal::MissingLoanBinding)?;
        let root = self
            .storage
            .data
            .loans
            .get(&root_id)
            .ok_or(LoanRefusal::MissingLoan)?;
        if !record.permitted.is_empty()
            || !record.memory_backing.is_empty()
            || root.mutex_root != Some(root_id)
            || root.support != record.support
            || root.recovered
            || !self
                .storage
                .data
                .scopes
                .get(&root.scope)
                .is_some_and(|scope| scope.active)
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        root.mutex_identity_description()
            .ok_or(LoanRefusal::MissingLoanBinding)
    }

    /// Only the authenticated root's type is visible through reborrows.
    /// A bare address or a caller's requested type cannot augment this promise.
    pub(crate) fn mutex_use_protected_type(
        &self,
        usage: MutexUseBinding,
        holder: LoanParticipantId,
    ) -> Result<Option<&ResourceDescription>, LoanRefusal> {
        self.mutex_use_identity_description(usage, holder)?;
        let record = self.validate_authority_binding(usage.0, holder)?;
        let root = self
            .storage
            .data
            .loans
            .get(&record.mutex_root.ok_or(LoanRefusal::MissingLoanBinding)?)
            .ok_or(LoanRefusal::MissingLoan)?;
        Ok(root.assumed_mutex_protected.as_ref())
    }

    /// Describing the occurrence grants no ownership. The mutex adapter must
    /// insert or consume it as part of the checked loan/state exchange.
    pub(crate) fn mutex_use_resource(
        &self,
        usage: MutexUseBinding,
        holder: LoanParticipantId,
    ) -> Result<ResourceFact, LoanRefusal> {
        let owner = self.mutex_use_identity_description(usage, holder)?;
        let Resource::MutexLive(identity) = owner.resource() else {
            return Err(LoanRefusal::MissingLoanBinding);
        };
        Ok(ResourceFact::own(Resource::MutexUse(
            super::MutexUseIdentity {
                binding: Some(usage),
                protected: self.mutex_use_protected_type(usage, holder)?.cloned(),
                initialization: identity.epoch,
                mutex: identity.mutex.clone(),
            },
        )))
    }

    /// End first, then describe the exact parent share the End transition
    /// restored. Neither the child receipt nor an equal pointer selects it.
    #[cfg(test)]
    pub(crate) fn end_mutex_reborrow_with_parent(
        &self,
        opening: &MutexUseLoan,
        holder: LoanParticipantId,
    ) -> Result<(Self, ResourceFact), LoanRefusal> {
        let ended = self.end_mutex_reborrow(opening, holder)?;
        let child = self
            .storage
            .data
            .scopes
            .get(&opening.scope)
            .ok_or(LoanRefusal::MissingScope)?;
        let parent_scope = child.parent.ok_or(LoanRefusal::MissingScope)?;
        let parent = self
            .storage
            .data
            .scopes
            .get(&parent_scope)
            .ok_or(LoanRefusal::MissingScope)?;
        let record = self
            .storage
            .data
            .loans
            .get(&parent.loan)
            .ok_or(LoanRefusal::MissingLoan)?;
        let usage = MutexUseBinding(LoanAuthorityBinding {
            loan: parent.loan,
            scope: parent_scope,
            share: child.parent_share.ok_or(LoanRefusal::MissingShare)?,
            support: record.support,
        });
        let resource = ended.mutex_use_resource(usage, holder)?;
        Ok((ended, resource))
    }

    /// Modular proof-entry assumption only: the caller guarantees this
    /// initialization's lifetime, but retains all closing and recovery rights.
    /// Call sites must lend/reborrow instead. The entry builder supplies the
    /// principal clause occurrence and installs the resulting use resource.
    #[cfg(test)]
    pub(crate) fn borrowed_mutex_use_input(
        &self,
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        mutex: super::Pointer,
    ) -> Result<(Self, MutexUseContractInput), LoanRefusal> {
        self.borrowed_mutex_use_input_with_protected(holder, support, mutex, None)
    }

    pub(crate) fn borrowed_mutex_use_input_with_protected(
        &self,
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        mutex: super::Pointer,
        protected: Option<ResourceDescription>,
    ) -> Result<(Self, MutexUseContractInput), LoanRefusal> {
        let arena = self.storage.data.arena;
        let scope = LoanScopeId {
            arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena,
            ordinal: self.storage.data.next_share,
        };
        let transition = self.issue(LoanTransitionEvidence::BorrowedMutexUseRoot {
            holder,
            support,
            mutex,
            protected,
            initialization: super::mutexes::MutexInitializationId::fresh()
                .map_err(|_| LoanRefusal::IdentitySpaceExhausted)?,
            scope,
            loan,
            root,
        })?;
        Ok((
            self.apply(&transition)?,
            MutexUseContractInput {
                holder,
                usage: MutexUseBinding(LoanAuthorityBinding {
                    loan,
                    scope,
                    share: root,
                    support,
                }),
            },
        ))
    }

    /// The selected share must be held and unpinned, with no guard hold in
    /// its scope. A child reborrow pins only its own share; siblings remain
    /// usable. Modular return separately requires every child to have ended.
    pub(crate) fn check_mutex_use_available(
        &self,
        usage: MutexUseBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<(), LoanRefusal> {
        let fact = self.mutex_use_resource(usage, holder)?;
        let scope = self
            .storage
            .data
            .scopes
            .get(&usage.0.scope)
            .ok_or(LoanRefusal::MissingScope)?;
        if !scope.holds.is_empty() {
            return Err(LoanRefusal::ActiveDependency);
        }
        if resources.unique_owned_occurrence_for_fact(&fact).is_none() {
            return Err(LoanRefusal::MissingBacking);
        }
        Ok(())
    }

    pub(crate) fn check_assumed_mutex_use_return(
        &self,
        usage: MutexUseBinding,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<(), LoanRefusal> {
        self.check_mutex_use_input_return(
            &MutexUseContractInput { usage, holder },
            holder,
            resources,
        )
    }

    /// A preserving helper must return the exact input occurrence, with its
    /// complete share and no escaping child or guard. It cannot close the root.
    pub(crate) fn check_mutex_use_input_return(
        &self,
        input: &MutexUseContractInput,
        holder: LoanParticipantId,
        resources: &ResourceContext,
    ) -> Result<(), LoanRefusal> {
        if input.holder != holder {
            return Err(LoanRefusal::WrongHolder);
        }
        let fact = self.mutex_use_resource(input.usage, holder)?;
        let record = self
            .storage
            .data
            .loans
            .get(&input.usage.0.loan)
            .ok_or(LoanRefusal::MissingLoan)?;
        let scope = self
            .storage
            .data
            .scopes
            .get(&record.scope)
            .ok_or(LoanRefusal::MissingScope)?;
        if record.origin != LoanOrigin::BorrowedContractInput
            || record.assumed_mutex.is_none()
            || record.mutex_root != Some(input.usage.0.loan)
            || scope.root != input.usage.0.share
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        if !scope.dependencies.is_empty() || !scope.holds.is_empty() {
            return Err(LoanRefusal::ActiveDependency);
        }
        if resources.unique_owned_occurrence_for_fact(&fact).is_none() {
            return Err(LoanRefusal::MissingBacking);
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn reborrow_mutex_use(
        &self,
        parent: MutexUseBinding,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
    ) -> Result<(Self, MutexUseLoan), LoanRefusal> {
        let (ledger, loan, _) =
            self.reborrow_mutex_use_with_transition(parent, lender, borrower)?;
        Ok((ledger, loan))
    }

    pub(crate) fn reborrow_mutex_use_with_transition(
        &self,
        parent: MutexUseBinding,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
    ) -> Result<(Self, MutexUseLoan, CheckedLoanTransition), LoanRefusal> {
        let scope = LoanScopeId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let transition = self.issue(LoanTransitionEvidence::Reborrow {
            parent: ReborrowBinding::MutexUse(parent),
            lender,
            borrower,
            scope,
            loan,
            root,
        })?;
        Ok((
            self.apply(&transition)?,
            MutexUseLoan {
                scope,
                loan,
                usage: MutexUseBinding(LoanAuthorityBinding {
                    loan,
                    scope,
                    share: root,
                    support: parent.0.support,
                }),
            },
            transition,
        ))
    }

    /// Closing a child restores its pinned parent share through the ordinary
    /// End transition. A child has no escrow and cannot recover ownership.
    #[cfg(test)]
    pub(crate) fn end_mutex_reborrow(
        &self,
        opening: &MutexUseLoan,
        holder: LoanParticipantId,
    ) -> Result<Self, LoanRefusal> {
        self.mutex_use_identity_description(opening.usage, holder)?;
        let authority = opening.usage.0;
        let record = self
            .storage
            .data
            .loans
            .get(&authority.loan)
            .ok_or(LoanRefusal::MissingLoan)?;
        if opening.scope != authority.scope
            || opening.loan != authority.loan
            || record.origin != LoanOrigin::Reborrowed
            || record.escrow.is_some()
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        self.apply(&self.end(opening.scope, holder)?)
    }

    #[cfg(test)]
    pub(crate) fn recover_mutex_use(
        &self,
        opening: &MutexUseLoan,
        holder: LoanParticipantId,
    ) -> Result<(Self, ResourceFact), LoanRefusal> {
        let authority = opening.usage.0;
        let record = self.validate_authority_binding(authority, holder)?;
        if opening.scope != authority.scope
            || opening.loan != authority.loan
            || record.mutex_root != Some(opening.loan)
            || !record.escrow.as_ref().is_some_and(is_mutex_lifetime_owner)
            || !record.permitted.is_empty()
            || !record.memory_backing.is_empty()
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        let closed = self.apply(&self.end(opening.scope, holder)?)?;
        let (recovery, owner, _) = closed.recover(opening.loan, holder)?;
        Ok((closed.apply(&recovery)?, owner))
    }

    #[cfg(test)]
    pub(crate) fn hold_mutex_use(
        &self,
        usage: MutexUseBinding,
        owner: &ResourceFact,
        holder: LoanParticipantId,
    ) -> Result<(Self, LoanHoldId), LoanRefusal> {
        let (held, hold, _) = self.hold_mutex_use_with_transition(usage, owner, holder)?;
        Ok((held, hold))
    }

    pub(crate) fn hold_mutex_use_with_transition(
        &self,
        usage: MutexUseBinding,
        owner: &ResourceFact,
        holder: LoanParticipantId,
    ) -> Result<(Self, LoanHoldId, CheckedLoanTransition), LoanRefusal> {
        if self.mutex_use_identity_description(usage, holder)? != owner {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        self.hold_authority_with_transition(usage.0, holder)
    }

    /// Establish the shared authority supplied by a modular function
    /// contract. Unlike [`Self::lend`], this transition consumes no ownership
    /// and creates no recovery or close right: the unknown caller retains
    /// both outside the proof. The exact resource occurrence is the only
    /// supported anchor, so an equal-looking fact cannot reuse this root.
    pub(crate) fn borrowed_contract_input(
        &self,
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        viewed: ResourceFact,
        backing: Option<BorrowedContractInputBacking>,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.open_borrowed_root(holder, support, viewed, backing, None)
    }

    fn open_borrowed_root(
        &self,
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        viewed: ResourceFact,
        backing: Option<BorrowedContractInputBacking>,
        local: Option<(LoanParticipantId, LocalViewBacking)>,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.require_participant(holder)?;
        if support == ResourceOccurrenceId::default() {
            return Err(LoanRefusal::MissingBacking);
        }
        if !viewed.is_view() {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let backing = match (viewed.resource(), backing) {
            (Resource::Memory(_) | Resource::Token { .. }, None) => Vec::new(),
            (Resource::Composite { .. }, Some(backing))
                if backing.support == support && backing.head == viewed =>
            {
                backing.pieces
            }
            _ => return Err(LoanRefusal::UnsupportedResource),
        };
        let scope = LoanScopeId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let evidence = LoanTransitionEvidence::BorrowedRoot {
            local,
            holder,
            support,
            viewed: viewed.clone(),
            backing,
            scope,
            loan,
            root,
        };
        Ok(LoanOpening {
            scope,
            loan,
            root_share: root,
            description: StableViewDescription {
                loan,
                support,
                viewed,
            },
            transition: self.issue(evidence)?,
        })
    }

    /// Lend a folded composite only when its primitive body frontier has
    /// already been checked by the caller.  The composite head is the exact
    /// restoration recipe; the primitive backing facts are what populate the
    /// active memory protection index.  This keeps composite escrow distinct
    /// from opaque token escrow and refuses hidden writable memory.
    pub(crate) fn lend_composite(
        &self,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: ResourceFact,
        backing: CompositeLoanBacking,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.require_participant(lender)?;
        self.require_participant(borrower)?;
        if support == ResourceOccurrenceId::default() {
            return Err(LoanRefusal::MissingBacking);
        }
        if !matches!(escrow.resource(), Resource::Composite { .. })
            || !escrow.is_own()
            || backing.support != support
            || backing.head != escrow
        {
            return Err(LoanRefusal::UnsupportedResource);
        }
        if backing
            .pieces
            .iter()
            .any(|fact| matches!(fact.resource(), Resource::Instance(_)))
        {
            return Err(LoanRefusal::UnsupportedResource);
        }
        let scope = LoanScopeId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let evidence = LoanTransitionEvidence::LendComposite {
            lender,
            borrower,
            support,
            support_fact: escrow.clone(),
            escrow: escrow.clone(),
            backing: backing.pieces,
            adapted: backing.adapted,
            scope,
            loan,
            root,
        };
        Ok(LoanOpening {
            scope,
            loan,
            root_share: root,
            description: StableViewDescription {
                loan,
                support,
                viewed: ResourceFact::View(escrow.resource().clone()),
            },
            transition: self.issue(evidence)?,
        })
    }

    /// Extend a loan's permitted descriptions by one checked child
    /// projection of a composite description it already permits.
    ///
    /// `evidence` is the kernel's own one-level expansion of `parent`, built
    /// at the expansion boundary by the checked `unfold`, `observe`, or
    /// `open` that calls this. The ledger re-checks both premises of the
    /// transition rather than delegating them to its caller (D2 law 10): the
    /// evidence must describe the very parent the loan permits, and the
    /// child must be one the expansion contains.
    ///
    /// **Identity rule.** A projection keeps the ledger identity, so two
    /// ledgers that compare equal can differ in derived `permitted` entries,
    /// and the branch join, the loop backedge,
    /// `recover_candidate_stable_view_resources`, and `recheck_entry` cannot
    /// see a projection difference. With containment checked here that is
    /// safe: every projected description is re-derivable from its parent by
    /// a checked expansion of the same state, so it is derived read-only
    /// authority over memory the loan already protects. It mints no share,
    /// no scope, and no recovery right, and no transition is possible from a
    /// projected description alone. Ledger identity tracks
    /// authority-changing transitions only, and a certificate that re-runs
    /// the same checked rewrites re-derives the same projections.
    pub(crate) fn project(
        &self,
        holder: LoanParticipantId,
        loan: LoanId,
        parent: &ResourceFact,
        evidence: &CompositeProjectionEvidence,
        child: ResourceFact,
    ) -> Result<Self, LoanRefusal> {
        self.require_arena(loan.arena)?;
        self.require_participant(holder)?;
        let record = self
            .storage
            .data
            .loans
            .get(&loan)
            .cloned()
            .ok_or(LoanRefusal::MissingLoan)?;
        let scope = self
            .storage
            .data
            .scopes
            .get(&record.scope)
            .ok_or(LoanRefusal::MissingScope)?;
        if !scope.active || record.recovered {
            return Err(LoanRefusal::ScopeEnded);
        }
        // Binding identity is checked without importing ambient equality facts.
        let assumptions = &PureFactContext::default();
        if !parent.is_view()
            || !matches!(parent.resource(), Resource::Composite { .. })
            || !record.permitted.iter().any(|permitted| {
                ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(permitted.clone())
                    .satisfies_fact(parent, assumptions)
            })
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        if evidence.head != *parent {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if !child.is_view() || matches!(child.resource(), Resource::Instance(_)) {
            return Err(LoanRefusal::UnsupportedResource);
        }
        if !evidence.contains_child(&child) {
            return Err(LoanRefusal::MissingBacking);
        }
        if record.permitted.contains(&child) {
            return Ok(self.clone());
        }
        let mut permitted = record.permitted;
        permitted.push(child);
        let mut data = self.storage.data.clone();
        data.loans = data.loans.with_inserted(
            loan,
            LoanRecord {
                permitted,
                ..record
            },
        );
        Ok(Self {
            storage: Arc::new(LoanLedgerStorage {
                state: self.storage.state,
                data,
            }),
        })
    }

    /// Places a hold on the scope of the binding's loan for a folded
    /// borrowing composite. While the hold exists, End refuses, so the owner
    /// behind the loan cannot be recovered and written while the composite
    /// still describes it and carries its body facts.
    ///
    /// A hold changes the scope's ability to end. The kernel records it as a
    /// checked transition with its own successor identity, and recovery keeps
    /// that transition so later checks use the same endpoint.
    /// The composite occurrence carries the hold binding, which is released
    /// when that occurrence is consumed by a call that does not return it.
    #[cfg(test)]
    pub(crate) fn hold(
        &self,
        binding: &LoanViewBinding,
        holder: LoanParticipantId,
    ) -> Result<(Self, LoanHoldId), LoanRefusal> {
        let (ledger, hold, _) = self.hold_with_transition(binding, holder)?;
        Ok((ledger, hold))
    }

    pub(crate) fn hold_with_transition(
        &self,
        binding: &LoanViewBinding,
        holder: LoanParticipantId,
    ) -> Result<(Self, LoanHoldId, CheckedLoanTransition), LoanRefusal> {
        self.validate_view_binding(binding.clone(), holder)?;
        self.hold_authority_with_transition(binding.authority(), holder)
    }

    /// The successor of a proof `fold` that packages a loan-backed view into
    /// an owned borrowing composite: `transition` must be exactly the hold
    /// `holder` placed on the loan `binding` names, and `binding.hold` must
    /// name that hold, so the folded head carries the hold that keeps its
    /// loan's scope from ending. Applying it rechecks the exact predecessor
    /// and that `holder` still holds the live authority. Anything else, a
    /// different transition or a hold the head does not carry, is refused.
    pub(crate) fn apply_borrowing_fold_hold(
        &self,
        transition: &CheckedLoanTransition,
        binding: &LoanViewBinding,
        holder: LoanParticipantId,
    ) -> Result<Self, LoanRefusal> {
        match &transition.evidence {
            LoanTransitionEvidence::Hold {
                binding: held,
                holder: placed_by,
                hold,
            } if *held == binding.authority()
                && *placed_by == holder
                && binding.hold == Some(*hold) =>
            {
                self.apply(transition)
            }
            _ => Err(LoanRefusal::InvalidEvidence),
        }
    }

    /// Lifetime holds need possession, not a stable-read description. The
    /// view adapter above must still check its description before delegating.
    fn hold_authority_with_transition(
        &self,
        binding: LoanAuthorityBinding,
        holder: LoanParticipantId,
    ) -> Result<(Self, LoanHoldId, CheckedLoanTransition), LoanRefusal> {
        self.validate_authority_binding(binding, holder)?;
        let hold = LoanHoldId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_hold,
        };
        self.storage
            .data
            .next_hold
            .checked_add(1)
            .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
        let transition = self.issue(LoanTransitionEvidence::Hold {
            binding,
            holder,
            hold,
        })?;
        let ledger = self.apply(&transition)?;
        Ok((ledger, hold, transition))
    }

    /// Removes a hold placed by its holder. Releasing restores the scope's
    /// ability to end, so it also receives a checked successor identity.
    #[cfg(test)]
    pub(crate) fn release(
        &self,
        hold: LoanHoldId,
        holder: LoanParticipantId,
    ) -> Result<Self, LoanRefusal> {
        let (ledger, _) = self.release_with_transition(hold, holder)?;
        Ok(ledger)
    }

    pub(crate) fn release_mutex_use_hold_with_transition(
        &self,
        usage: MutexUseBinding,
        owner: &ResourceFact,
        hold: LoanHoldId,
        holder: LoanParticipantId,
    ) -> Result<(Self, CheckedLoanTransition), LoanRefusal> {
        if self.mutex_use_identity_description(usage, holder)? != owner
            || self.storage.data.holds.get(&hold) != Some(&(usage.0.scope, holder))
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        self.release_with_transition(hold, holder)
    }

    pub(crate) fn release_with_transition(
        &self,
        hold: LoanHoldId,
        holder: LoanParticipantId,
    ) -> Result<(Self, CheckedLoanTransition), LoanRefusal> {
        self.require_arena(hold.arena)?;
        self.require_participant(holder)?;
        let (scope, placed_by) = self
            .storage
            .data
            .holds
            .get(&hold)
            .copied()
            .ok_or(LoanRefusal::MissingScope)?;
        if placed_by != holder {
            return Err(LoanRefusal::WrongHolder);
        }
        let transition = self.issue(LoanTransitionEvidence::Release {
            hold,
            scope,
            holder,
        })?;
        let ledger = self.apply(&transition)?;
        Ok((ledger, transition))
    }

    /// The descriptions a live loan authorizes, or none for an ended or
    /// unknown loan.
    pub(crate) fn permitted_descriptions(&self, loan: LoanId) -> Vec<ResourceFact> {
        let data = &self.storage.data;
        data.loans
            .get(&loan)
            .filter(|record| {
                !record.recovered
                    && data
                        .scopes
                        .get(&record.scope)
                        .is_some_and(|scope| scope.active)
            })
            .map(|record| record.permitted.clone())
            .unwrap_or_default()
    }

    /// The scope a live hold restricts, if the hold exists.
    #[cfg(test)]
    pub(crate) fn held_scope(&self, hold: LoanHoldId) -> Option<LoanScopeId> {
        self.storage.data.holds.get(&hold).map(|(scope, _)| *scope)
    }

    /// Whether `holder` could end `scope` now: it holds the close right and
    /// the whole root share, and nothing depends on or holds the scope.
    pub(crate) fn scope_can_end(&self, scope: LoanScopeId, holder: LoanParticipantId) -> bool {
        let data = &self.storage.data;
        data.scopes.get(&scope).is_some_and(|record| {
            record.active
                && record.close_right == Some(holder)
                && record.dependencies.is_empty()
                && record.holds.is_empty()
                && data
                    .shares
                    .get(&record.root)
                    .is_some_and(|root| root.holder == Some(holder))
        })
    }

    /// Whether `holder` is the recovery right of an escrowed, unrecovered
    /// loan.
    pub(crate) fn loan_is_recoverable_by(&self, loan: LoanId, holder: LoanParticipantId) -> bool {
        self.storage.data.loans.get(&loan).is_some_and(|record| {
            !record.recovered && record.origin == LoanOrigin::Escrowed(holder)
        })
    }

    fn validate_authority_binding(
        &self,
        binding: LoanAuthorityBinding,
        holder: LoanParticipantId,
    ) -> Result<&LoanRecord, LoanRefusal> {
        self.require_participant(holder)?;
        let loan = self
            .storage
            .data
            .loans
            .get(&binding.loan)
            .ok_or(LoanRefusal::MissingLoan)?;
        let scope = self
            .storage
            .data
            .scopes
            .get(&binding.scope)
            .ok_or(LoanRefusal::MissingScope)?;
        let share = self
            .storage
            .data
            .shares
            .get(&binding.share)
            .ok_or(LoanRefusal::MissingShare)?;
        if loan.scope != binding.scope
            || scope.loan != binding.loan
            || loan.support != binding.support
            || !scope.active
            || loan.recovered
            || share.scope != binding.scope
            || share.holder != Some(holder)
            || share.pinned_by.is_some()
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        Ok(loan)
    }

    pub(crate) fn validate_view_binding(
        &self,
        binding: LoanViewBinding,
        holder: LoanParticipantId,
    ) -> Result<(), LoanRefusal> {
        let loan = self.validate_authority_binding(binding.authority(), holder)?;
        // Binding identity is checked without importing ambient equality facts.
        let assumptions = &PureFactContext::default();
        if !binding.viewed.is_view()
            || !loan.permitted.iter().any(|permitted| {
                ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(permitted.clone())
                    .satisfies_fact(&binding.viewed, assumptions)
            })
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        Ok(())
    }

    pub(crate) fn reborrow(
        &self,
        parent: LoanViewBinding,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.validate_view_binding(parent.clone(), lender)?;
        self.require_participant(borrower)?;
        let scope = LoanScopeId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_scope,
        };
        let loan = LoanId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_loan,
        };
        let root = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let evidence = LoanTransitionEvidence::Reborrow {
            parent: ReborrowBinding::View(parent.clone()),
            lender,
            borrower,
            scope,
            loan,
            root,
        };
        Ok(LoanOpening {
            scope,
            loan,
            root_share: root,
            description: StableViewDescription {
                loan,
                support: parent.support,
                viewed: parent.viewed,
            },
            transition: self.issue(evidence)?,
        })
    }

    pub(crate) fn split(
        &self,
        share: LoanShareId,
        holder: LoanParticipantId,
        left_holder: LoanParticipantId,
        right_holder: LoanParticipantId,
    ) -> Result<(CheckedLoanTransition, LoanShareId, LoanShareId), LoanRefusal> {
        self.require_arena(share.arena)?;
        self.require_participant(holder)?;
        self.require_participant(left_holder)?;
        self.require_participant(right_holder)?;
        let left = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self.storage.data.next_share,
        };
        let right = LoanShareId {
            arena: self.storage.data.arena,
            ordinal: self
                .storage
                .data
                .next_share
                .checked_add(1)
                .ok_or(LoanRefusal::IdentitySpaceExhausted)?,
        };
        let transition = self.issue(LoanTransitionEvidence::Split {
            share,
            holder,
            left_holder,
            right_holder,
            left,
            right,
        })?;
        Ok((transition, left, right))
    }

    pub(crate) fn transfer(
        &self,
        share: LoanShareId,
        from: LoanParticipantId,
        to: LoanParticipantId,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.require_arena(share.arena)?;
        self.require_participant(from)?;
        self.require_participant(to)?;
        self.issue(LoanTransitionEvidence::Transfer { share, from, to })
    }

    pub(crate) fn join(
        &self,
        left: LoanShareId,
        right: LoanShareId,
        holder: LoanParticipantId,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.require_arena(left.arena)?;
        self.require_arena(right.arena)?;
        self.require_participant(holder)?;
        self.issue(LoanTransitionEvidence::Join {
            left,
            right,
            holder,
        })
    }

    /// Recombine only siblings already returned to this holder. A live
    /// worker's pinned share stops the climb; joining that worker later can
    /// resume from its own returned share. Work is proportional to the
    /// affected branch of the explicit share tree.
    pub(crate) fn join_available_share_ancestors(
        &self,
        share: LoanShareId,
        holder: LoanParticipantId,
    ) -> Result<(Self, LoanShareId, Vec<CheckedLoanTransition>), LoanRefusal> {
        let mut ledger = self.clone();
        let mut current = share;
        let mut transitions = Vec::new();
        loop {
            let record = ledger
                .storage
                .data
                .shares
                .get(&current)
                .ok_or(LoanRefusal::MissingShare)?;
            if record.holder != Some(holder) || record.pinned_by.is_some() {
                return Err(LoanRefusal::WrongHolder);
            }
            let Some(parent) = record.parent else {
                break;
            };
            let Some((left, right)) = ledger
                .storage
                .data
                .shares
                .get(&parent)
                .and_then(|record| record.children)
            else {
                return Err(LoanRefusal::NotSiblings);
            };
            let sibling = match current {
                current if current == left => right,
                current if current == right => left,
                _ => return Err(LoanRefusal::NotSiblings),
            };
            if !ledger
                .storage
                .data
                .shares
                .get(&sibling)
                .is_some_and(|record| record.holder == Some(holder) && record.pinned_by.is_none())
            {
                break;
            }
            let join = ledger.join(left, right, holder)?;
            ledger = ledger.apply(&join)?;
            transitions.push(join);
            current = parent;
        }
        Ok((ledger, current, transitions))
    }

    pub(crate) fn end(
        &self,
        scope: LoanScopeId,
        holder: LoanParticipantId,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.require_arena(scope.arena)?;
        self.require_participant(holder)?;
        self.issue(LoanTransitionEvidence::End { scope, holder })
    }

    #[cfg(test)]
    pub(crate) fn register_dependency(
        &self,
        parent: LoanScopeId,
        child: LoanScopeId,
        holder: LoanParticipantId,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.require_arena(parent.arena)?;
        self.require_arena(child.arena)?;
        self.require_participant(holder)?;
        self.issue(LoanTransitionEvidence::RegisterDependency {
            parent,
            child,
            holder,
        })
    }

    pub(crate) fn recover(
        &self,
        loan: LoanId,
        holder: LoanParticipantId,
    ) -> Result<(CheckedLoanTransition, ResourceFact, ResourceOccurrenceId), LoanRefusal> {
        self.require_arena(loan.arena)?;
        self.require_participant(holder)?;
        let record = self
            .storage
            .data
            .loans
            .get(&loan)
            .ok_or(LoanRefusal::MissingLoan)?;
        if !matches!(record.origin, LoanOrigin::Escrowed(right) if right == holder) {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let escrow = record.escrow.clone().ok_or(LoanRefusal::MissingBacking)?;
        let support = record.support;
        Ok((
            self.issue(LoanTransitionEvidence::Recover { loan, holder })?,
            escrow,
            support,
        ))
    }

    pub(crate) fn permits_view(
        &self,
        holder: LoanParticipantId,
        description: &StableViewDescription,
        share: LoanShareId,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(loan) = self.storage.data.loans.get(&description.loan) else {
            return false;
        };
        self.validate_authority_binding(
            LoanAuthorityBinding {
                loan: description.loan,
                scope: loan.scope,
                share,
                support: description.support,
            },
            holder,
        )
        .is_ok()
            && description.viewed.is_view()
            && loan.permitted.iter().any(|permitted| {
                ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(permitted.clone())
                    .satisfies_fact(&description.viewed, assumptions)
            })
    }

    pub(crate) fn authorizes_bindings(
        &self,
        holder: LoanParticipantId,
        bindings: &LoanViewBindings,
        assumptions: &PureFactContext,
    ) -> bool {
        bindings.iter().all(|(_, binding)| {
            self.storage
                .data
                .loans
                .get(&binding.loan)
                .is_some_and(|loan| loan.scope == binding.scope)
                && self.permits_view(
                    holder,
                    &StableViewDescription {
                        loan: binding.loan,
                        support: binding.support,
                        viewed: binding.viewed.clone(),
                    },
                    binding.share,
                    assumptions,
                )
        })
    }

    pub(crate) fn describe_view(
        &self,
        loan: LoanId,
        viewed: ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<StableViewDescription, LoanRefusal> {
        self.describe_view_through(loan, viewed, None, assumptions)
    }

    /// [`Self::describe_view`] for a view reached through one the holder
    /// already has under the loan: `held` lies in what the loan permits and
    /// `viewed` lies in `held`, both checked here, so `viewed` lies in what
    /// the loan permits. A requirement inside a chunk taken from a lent
    /// range is described this way, where its position in the whole range
    /// is two offsets deep.
    pub(crate) fn describe_view_through(
        &self,
        loan: LoanId,
        viewed: ResourceFact,
        held: Option<&ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<StableViewDescription, LoanRefusal> {
        self.require_arena(loan.arena)?;
        let record = self
            .storage
            .data
            .loans
            .get(&loan)
            .ok_or(LoanRefusal::MissingLoan)?;
        if record.recovered
            || !self
                .storage
                .data
                .scopes
                .get(&record.scope)
                .is_some_and(|scope| scope.active)
        {
            return Err(LoanRefusal::ScopeEnded);
        }
        let covers = |available: &ResourceFact, required: &ResourceFact| {
            ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(available.clone())
                .satisfies_fact(required, assumptions)
        };
        if !viewed.is_view()
            || !record.permitted.iter().any(|permitted| {
                covers(permitted, &viewed)
                    || held.is_some_and(|held| {
                        held.is_view() && covers(permitted, held) && covers(held, &viewed)
                    })
            })
        {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(StableViewDescription {
            loan,
            support: record.support,
            viewed,
        })
    }

    pub(crate) fn apply(&self, transition: &CheckedLoanTransition) -> Result<Self, LoanRefusal> {
        if self.storage.state != transition.before_state {
            return Err(LoanRefusal::StalePredecessor);
        }
        if transition.evidence != transition.checked_evidence {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if transition.after_state != transition.checked_after_state {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let data = self.apply_evidence(&transition.evidence)?;
        Ok(Self {
            storage: Arc::new(LoanLedgerStorage {
                state: transition.after_state,
                data,
            }),
        })
    }

    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.storage, &other.storage)
    }

    /// Select the least conflicting loan ID from the concrete write index.
    /// Each fixed-width dyadic bucket contributes only its first member;
    /// selecting the minimum preserves the diagnostic's existing loan choice.
    fn first_active_memory_overlap(
        &self,
        range: &MemoryRange,
    ) -> Result<Option<LoanId>, LoanRefusal> {
        if memory_range_is_empty(range) {
            return Ok(None);
        }
        let Some(nodes) = memory_interval_nodes(range) else {
            return if self.storage.data.active_memory_loans == 0 {
                Ok(None)
            } else {
                Err(LoanRefusal::UnsupportedPartition)
            };
        };
        let mut selected: Option<LoanId> = None;
        let mut consider = |bucket: Option<&PersistentSet<LoanId>>| {
            crate::instrumentation::record_deterministic_work(1);
            // PersistentSet's iterator descends to the least key lazily.
            // Taking one member does not enumerate or collect the bucket.
            if let Some(loan) = bucket.and_then(|bucket| bucket.iter().next()).copied() {
                selected = Some(selected.map_or(loan, |previous| previous.min(loan)));
            }
        };
        for node in nodes {
            for ancestor in memory_interval_ancestors(&node) {
                consider(self.storage.data.active_memory_index.get(&ancestor));
            }
            consider(self.storage.data.active_memory_subtree.get(&node));
        }
        Ok(selected)
    }

    /// Return active memory loans whose concrete byte footprints overlap the
    /// query. The dyadic index visits logarithmically many buckets plus the
    /// returned loan IDs; it never scans the ledger.
    #[cfg(test)]
    pub(crate) fn active_memory_overlaps(
        &self,
        range: &MemoryRange,
    ) -> Result<Vec<LoanId>, LoanRefusal> {
        if memory_range_is_empty(range) {
            return Ok(Vec::new());
        }
        let Some(query_nodes) = memory_interval_nodes(range) else {
            return if self.storage.data.active_memory_loans == 0 {
                Ok(Vec::new())
            } else {
                Err(LoanRefusal::UnsupportedPartition)
            };
        };
        let mut loans = PersistentSet::default();
        for query in query_nodes {
            crate::instrumentation::record_deterministic_work(1);
            for ancestor in memory_interval_ancestors(&query) {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(bucket) = self.storage.data.active_memory_index.get(&ancestor) {
                    for loan in bucket.iter() {
                        crate::instrumentation::record_deterministic_work(1);
                        loans = loans.with_value(*loan);
                    }
                }
            }
            if let Some(bucket) = self.storage.data.active_memory_subtree.get(&query) {
                for loan in bucket.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    loans = loans.with_value(*loan);
                }
            }
        }
        Ok(loans.iter().copied().collect())
    }

    fn first_active_memory_overlap_with_assumptions(
        &self,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Result<Option<LoanId>, LoanRefusal> {
        let mut selected: Option<LoanId> = None;
        for alias in memory_range_aliases(range, assumptions) {
            if memory_interval_nodes(&alias).is_some()
                && let Some(loan) = self.first_active_memory_overlap(&alias)?
            {
                selected = Some(selected.map_or(loan, |previous| previous.min(loan)));
            }
        }
        Ok(selected)
    }

    /// Whether a write, free, or havoc of `range` is compatible with every
    /// active loan. Concrete ranges and concrete aliases use the dyadic
    /// index. A symbolic query cannot be looked up there, so it is refused
    /// while an indexed loan might alias it. An external input cannot alias a
    /// fresh function-local block; that exact case is allowed when all
    /// indexed loans are local. Remaining symbolic loans are compared in the
    /// buckets for the query and its exact pointer aliases with
    /// [`protected_range_proven_overlapping`], whose polarity is documented
    /// there.
    pub(crate) fn permits_memory_access_with_assumptions(
        &self,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Result<(), LoanRefusal> {
        // An empty barrier is a fast decision, not a search invocation.
        if !self.has_active_memory_loans() || memory_range_is_empty(range) {
            return Ok(());
        }
        crate::kernel::search::ProofSearch::<LoanLedger>::loan_access(self, range, assumptions)
    }

    /// The write's complete loan condition, retained as an ordinary resource
    /// proposition. Building it never visits the protected ranges or aliases.
    pub(crate) fn memory_access_requirement(
        &self,
        range: &MemoryRange,
    ) -> Option<super::Proposition> {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("loan access requirement");
        let footprint = self.storage.data.active_footprint.resource();
        if matches!(footprint, Resource::Emp) || memory_range_is_empty(range) {
            return None;
        }
        Some(super::Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range.clone())),
            right: Box::new(footprint),
        })
    }

    /// Explain a refused access in the D13 shape: the loan that refused it,
    /// where that loan came from, the range it protects, and the range the
    /// operation attempted. Only the refusal path pays for the explanation,
    /// and it revisits the same index buckets the check itself used, so a
    /// permitted access costs nothing and a refused one never walks the
    /// ledger.
    pub(crate) fn memory_access_refusal(
        &self,
        range: &MemoryRange,
        assumptions: &PureFactContext,
        operation: LoanRefusalOperation,
    ) -> Option<LoanRefusalDiagnostic> {
        let refusal = self
            .permits_memory_access_with_assumptions(range, assumptions)
            .err()?;
        let subject = match self.conflicting_memory_loan(range, assumptions) {
            Some((loan, protected, origin)) => LoanRefusalSubject::for_memory_conflict(
                range.clone(),
                ResourceFact::view_memory(protected),
                loan,
                origin,
            ),
            None => LoanRefusalSubject::with_range(range.clone()),
        };
        Some(refusal.diagnostic_with_subject(operation, subject))
    }

    /// The first active loan whose protected footprint explains a refusal of
    /// `range`, with the protected range and the loan's origin.
    fn conflicting_memory_loan(
        &self,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<(LoanId, MemoryRange, LoanOriginKind)> {
        let described = |loan: LoanId, protected: &MemoryRange| {
            let record = self.storage.data.loans.get(&loan)?;
            Some((loan, protected.clone(), origin_kind(&record.origin)))
        };
        if let Ok(Some(loan)) =
            self.first_active_memory_overlap_with_assumptions(range, assumptions)
            && let Some(record) = self.storage.data.loans.get(&loan)
        {
            let protected = record
                .memory_backing
                .iter()
                .find(|protected| protected_range_proven_overlapping(range, protected, assumptions))
                .or_else(|| record.memory_backing.first());
            if let Some(protected) = protected {
                return described(loan, protected);
            }
        }
        let mut checked_blocks = BTreeSet::new();
        for alias in memory_range_aliases(range, assumptions) {
            if !checked_blocks.insert(alias.base().block.clone()) {
                continue;
            }
            let Some(block) = self.storage.data.unindexed_memory.get(&alias.base().block) else {
                continue;
            };
            for (loan, protected_ranges) in block.iter() {
                for protected in protected_ranges {
                    if protected_range_proven_overlapping(range, protected, assumptions) {
                        return described(*loan, protected);
                    }
                }
            }
        }
        None
    }

    /// [`Self::permits_memory_access_with_assumptions`] without path
    /// assumptions, for write-authority callers that have none. Cache
    /// retention instead uses `has_indexed_memory_overlap` and never searches
    /// the symbolic buckets. Fewer assumptions prove fewer overlaps, so this is the
    /// more permissive form; the ordinary owned-authority check remains the
    /// primary guard on every write.
    pub(crate) fn permits_memory_access(&self, range: &MemoryRange) -> Result<(), LoanRefusal> {
        self.permits_memory_access_with_assumptions(range, &PureFactContext::default())
    }

    /// Positive protection evidence for cache preservation. Unknown relative
    /// bounds forget the value; they never grant permission to write.
    /// Unlike the write barrier, this optional retention query does not search
    /// other coordinate origins, and it asks only whether an interval bucket is occupied.
    pub(crate) fn has_indexed_memory_overlap(&self, range: &MemoryRange) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if self.storage.data.cache_memory_index.is_empty()
            && self.storage.data.cache_memory_subtree.is_empty()
        {
            return false;
        }
        let Some((origin, nodes)) = cache_protection_nodes(range) else {
            return false;
        };
        let root = ResourceMemoryIntervalNode {
            block: origin.block.clone(),
            level: 32,
            start: 0,
        };
        if !self
            .storage
            .data
            .cache_memory_subtree
            .contains_key(&(origin.clone(), root))
        {
            return false;
        }
        for node in nodes {
            for ancestor in memory_interval_ancestors(&node) {
                crate::instrumentation::record_deterministic_work(1);
                if self
                    .storage
                    .data
                    .cache_memory_index
                    .get(&(origin.clone(), ancestor))
                    .is_some_and(|bucket| !bucket.is_empty())
                {
                    return true;
                }
            }
            crate::instrumentation::record_deterministic_work(1);
            if self
                .storage
                .data
                .cache_memory_subtree
                .get(&(origin.clone(), node))
                .is_some_and(|bucket| !bucket.is_empty())
            {
                return true;
            }
        }
        false
    }

    /// Whether an active loan may protect memory, including composite loans
    /// whose one-level frontier enumerated no bytes.
    ///
    /// A zero count skips write-barrier alias discovery. Loop and branch havoc
    /// also need this fail-closed answer when no checked write set is available.
    /// Read the maintained count; do not rediscover it from loans or scopes.
    pub(crate) fn has_active_memory_loans(&self) -> bool {
        self.storage.data.active_memory_loans != 0
    }

    fn issue(
        &self,
        evidence: LoanTransitionEvidence,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        // Validate at issue time; applying repeats the same local transition
        // check against the exact predecessor.
        self.apply_evidence(&evidence)?;
        let after_state = LoanLedgerStateId::fresh();
        Ok(CheckedLoanTransition {
            before_state: self.storage.state,
            after_state,
            checked_after_state: after_state,
            checked_evidence: evidence.clone(),
            evidence,
        })
    }

    fn require_arena(&self, arena: u64) -> Result<(), LoanRefusal> {
        (arena == self.storage.data.arena)
            .then_some(())
            .ok_or(LoanRefusal::WrongArena)
    }

    fn require_participant(&self, participant: LoanParticipantId) -> Result<(), LoanRefusal> {
        (participant.arena == self.storage.data.arena)
            .then_some(())
            .ok_or(LoanRefusal::WrongArena)
    }

    fn apply_evidence(
        &self,
        evidence: &LoanTransitionEvidence,
    ) -> Result<LoanLedgerData, LoanRefusal> {
        crate::instrumentation::record_deterministic_work(1);
        let mut data = self.storage.data.clone();
        self.advance_local_reference_scope(&mut data, evidence)?;
        match evidence {
            LoanTransitionEvidence::RegisterLocalReference(binding) => {
                self.apply_local_reference_registration(&mut data, binding)?
            }
            LoanTransitionEvidence::BorrowLocalReference(binding) => {
                self.apply_local_reference_borrow(&mut data, binding)?
            }
            LoanTransitionEvidence::RecoverLocalReference(binding) => {
                self.apply_local_reference_recovery(&mut data, binding)?
            }
            LoanTransitionEvidence::RetireLocalReferenceRoot(binding) => {
                self.apply_local_reference_retirement(&mut data, binding)?
            }
            LoanTransitionEvidence::OpenExclusiveCall(binding) => {
                self.apply_exclusive_open(&mut data, binding)?
            }
            LoanTransitionEvidence::ReturnExclusiveCall { binding, holder } => {
                self.apply_exclusive_return(&mut data, binding, *holder)?
            }
            LoanTransitionEvidence::Lend {
                lender,
                borrower,
                support,
                escrow,
                scope,
                loan,
                root,
            } => {
                if !escrow.is_own() {
                    return Err(LoanRefusal::NotOwnership);
                }
                if *support == ResourceOccurrenceId::default() {
                    return Err(LoanRefusal::MissingBacking);
                }
                self.require_participant(*lender)?;
                self.require_participant(*borrower)?;
                if !matches!(
                    escrow.resource(),
                    Resource::Memory(_) | Resource::Token { .. }
                ) && !is_mutex_lifetime_owner(escrow)
                {
                    return Err(LoanRefusal::UnsupportedResource);
                }
                if scope.arena != data.arena || loan.arena != data.arena || root.arena != data.arena
                {
                    return Err(LoanRefusal::WrongArena);
                }
                if scope.ordinal != data.next_scope
                    || loan.ordinal != data.next_loan
                    || root.ordinal != data.next_share
                {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                let memory_backing = match escrow.resource() {
                    Resource::Footprint(_)
                    | Resource::Parameter(_)
                    | Resource::Emp
                    | Resource::Star(_) => {
                        return Err(LoanRefusal::InvalidEvidence);
                    }
                    Resource::Memory(range) => vec![range.clone()],
                    Resource::Token { .. } | Resource::MutexLive(_) => Vec::new(),
                    Resource::Composite { .. }
                    | Resource::PopulationAuthority(_)
                    | Resource::Instance(_)
                    | Resource::MutexGuard(_)
                    | Resource::MutexUse(_)
                    | Resource::Publication(_)
                    | Resource::Iterated(_) => {
                        return Err(LoanRefusal::UnsupportedResource);
                    }
                };
                let protects_memory = !memory_backing.is_empty();
                data.next_scope = data
                    .next_scope
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_loan = data
                    .next_loan
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_share = data
                    .next_share
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        loan: *loan,
                        root: *root,
                        close_right: Some(*lender),
                        active: true,
                        parent: None,
                        parent_share: None,
                        dependencies: crate::persistent::PersistentSet::default(),
                        holds: crate::persistent::PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        mutex_root: is_mutex_lifetime_owner(escrow).then_some(*loan),
                        assumed_mutex: None,
                        assumed_mutex_protected: None,
                        support: *support,
                        escrow: Some(escrow.clone()),
                        permitted: if is_mutex_lifetime_owner(escrow) {
                            Vec::new()
                        } else {
                            vec![ResourceFact::View(escrow.resource().clone())]
                        },
                        origin: LoanOrigin::Escrowed(*lender),
                        recovered: false,
                        memory_backing: memory_backing.clone(),
                    },
                );
                data.shares = data.shares.with_inserted(
                    *root,
                    LoanShareRecord {
                        scope: *scope,
                        parent: None,
                        children: None,
                        holder: Some(*borrower),
                        pinned_by: None,
                    },
                );
                data.active_footprint = data.active_footprint.with_loan(*loan, &memory_backing);
                for range in &memory_backing {
                    update_indexed_memory_range(&mut data, range, *loan, true)?;
                }
                data.unindexed_memory = with_unindexed_memory(
                    &data.unindexed_memory,
                    *loan,
                    &symbolic_memory_ranges(&memory_backing),
                );
                if protects_memory {
                    data.active_memory_loans = data
                        .active_memory_loans
                        .checked_add(1)
                        .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                }
            }
            LoanTransitionEvidence::LendComposite {
                lender,
                borrower,
                support,
                support_fact,
                escrow,
                backing,
                adapted,
                scope,
                loan,
                root,
            } => {
                if !escrow.is_own()
                    || support_fact != escrow
                    || !matches!(escrow.resource(), Resource::Composite { .. })
                {
                    return Err(LoanRefusal::UnsupportedResource);
                }
                if *support == ResourceOccurrenceId::default() {
                    return Err(LoanRefusal::MissingBacking);
                }
                self.require_participant(*lender)?;
                self.require_participant(*borrower)?;
                if backing
                    .iter()
                    .any(|fact| matches!(fact.resource(), Resource::Instance(_)))
                {
                    return Err(LoanRefusal::UnsupportedResource);
                }
                // An adapted description is another name for the very bytes
                // this escrow suspends, never a second authority: it is a
                // composite view and it carries no backing of its own.
                if adapted.iter().any(|description| {
                    !description.is_view()
                        || !matches!(description.resource(), Resource::Composite { .. })
                }) {
                    return Err(LoanRefusal::UnsupportedResource);
                }
                if scope.arena != data.arena
                    || loan.arena != data.arena
                    || root.arena != data.arena
                    || scope.ordinal != data.next_scope
                    || loan.ordinal != data.next_loan
                    || root.ordinal != data.next_share
                {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                let memory_backing = backing
                    .iter()
                    .filter_map(ResourceFact::memory_own_range)
                    .cloned()
                    .collect::<Vec<_>>();
                // A composite head is memory whether or not its one-level
                // frontier enumerated any of it.
                let protects_memory = true;
                data.next_scope = data
                    .next_scope
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_loan = data
                    .next_loan
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_share = data
                    .next_share
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        loan: *loan,
                        root: *root,
                        close_right: Some(*lender),
                        active: true,
                        parent: None,
                        parent_share: None,
                        dependencies: crate::persistent::PersistentSet::default(),
                        holds: crate::persistent::PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        mutex_root: None,
                        assumed_mutex: None,
                        assumed_mutex_protected: None,
                        support: *support,
                        escrow: Some(escrow.clone()),
                        permitted: std::iter::once(ResourceFact::View(escrow.resource().clone()))
                            .chain(
                                backing
                                    .iter()
                                    .map(|fact| ResourceFact::View(fact.resource().clone())),
                            )
                            .chain(adapted.iter().cloned())
                            .collect(),
                        origin: LoanOrigin::Escrowed(*lender),
                        recovered: false,
                        memory_backing: memory_backing.clone(),
                    },
                );
                data.shares = data.shares.with_inserted(
                    *root,
                    LoanShareRecord {
                        scope: *scope,
                        parent: None,
                        children: None,
                        holder: Some(*borrower),
                        pinned_by: None,
                    },
                );
                data.active_footprint = data.active_footprint.with_loan(*loan, &memory_backing);
                for range in &memory_backing {
                    update_indexed_memory_range(&mut data, range, *loan, true)?;
                }
                data.unindexed_memory = with_unindexed_memory(
                    &data.unindexed_memory,
                    *loan,
                    &symbolic_memory_ranges(&memory_backing),
                );
                if protects_memory {
                    data.active_memory_loans = data
                        .active_memory_loans
                        .checked_add(1)
                        .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                }
            }
            LoanTransitionEvidence::BorrowedMutexUseRoot {
                holder,
                support,
                mutex,
                protected,
                initialization,
                scope,
                loan,
                root,
            } => {
                self.require_participant(*holder)?;
                if *support == ResourceOccurrenceId::default() {
                    return Err(LoanRefusal::MissingBacking);
                }
                if scope.arena != data.arena
                    || loan.arena != data.arena
                    || root.arena != data.arena
                    || scope.ordinal != data.next_scope
                    || loan.ordinal != data.next_loan
                    || root.ordinal != data.next_share
                {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                data.next_scope = data
                    .next_scope
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_loan = data
                    .next_loan
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_share = data
                    .next_share
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        loan: *loan,
                        root: *root,
                        close_right: None,
                        active: true,
                        parent: None,
                        parent_share: None,
                        dependencies: PersistentSet::default(),
                        holds: PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        mutex_root: Some(*loan),
                        support: *support,
                        assumed_mutex: Some(initialization.description(mutex)),
                        assumed_mutex_protected: protected.clone(),
                        escrow: None,
                        permitted: Vec::new(),
                        origin: LoanOrigin::BorrowedContractInput,
                        recovered: false,
                        memory_backing: Vec::new(),
                    },
                );
                data.shares = data.shares.with_inserted(
                    *root,
                    LoanShareRecord {
                        scope: *scope,
                        parent: None,
                        children: None,
                        holder: Some(*holder),
                        pinned_by: None,
                    },
                );
            }
            LoanTransitionEvidence::BorrowedRoot {
                local,
                holder,
                support,
                viewed,
                backing,
                scope,
                loan,
                root,
            } => {
                self.require_participant(*holder)?;
                if let Some((lender, backing)) = local {
                    self.require_participant(*lender)?;
                    if backing.viewed != *viewed {
                        return Err(LoanRefusal::InvalidEvidence);
                    }
                }
                if *support == ResourceOccurrenceId::default() {
                    return Err(LoanRefusal::MissingBacking);
                }
                let valid_backing = match viewed.resource() {
                    Resource::Memory(_) | Resource::Token { .. } => backing.is_empty(),
                    Resource::Composite { .. } => backing.iter().all(|piece| {
                        piece.is_view() && !matches!(piece.resource(), Resource::Instance(_))
                    }),
                    _ => false,
                };
                if !viewed.is_view() || !valid_backing {
                    return Err(LoanRefusal::UnsupportedResource);
                }
                if scope.arena != data.arena
                    || loan.arena != data.arena
                    || root.arena != data.arena
                    || scope.ordinal != data.next_scope
                    || loan.ordinal != data.next_loan
                    || root.ordinal != data.next_share
                {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                let mut permitted = vec![viewed.clone()];
                permitted.extend(backing.iter().cloned());
                let memory_backing = permitted
                    .iter()
                    .filter_map(ResourceFact::memory_range)
                    .cloned()
                    .collect::<Vec<_>>();
                let protects_memory = loan_protects_memory(&memory_backing, &permitted);
                data.next_scope = data
                    .next_scope
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_loan = data
                    .next_loan
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_share = data
                    .next_share
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        loan: *loan,
                        root: *root,
                        close_right: local.as_ref().map(|(lender, _)| *lender),
                        active: true,
                        parent: None,
                        parent_share: None,
                        dependencies: crate::persistent::PersistentSet::default(),
                        holds: crate::persistent::PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        mutex_root: None,
                        assumed_mutex: None,
                        assumed_mutex_protected: None,
                        support: *support,
                        escrow: None,
                        permitted,
                        origin: local
                            .as_ref()
                            .map_or(LoanOrigin::BorrowedContractInput, |(lender, _)| {
                                LoanOrigin::LocalStorage(*lender)
                            }),
                        recovered: false,
                        memory_backing: memory_backing.clone(),
                    },
                );
                data.shares = data.shares.with_inserted(
                    *root,
                    LoanShareRecord {
                        scope: *scope,
                        parent: None,
                        children: None,
                        holder: Some(*holder),
                        pinned_by: None,
                    },
                );
                data.active_footprint = data.active_footprint.with_loan(*loan, &memory_backing);
                for range in &memory_backing {
                    update_indexed_memory_range(&mut data, range, *loan, true)?;
                }
                data.unindexed_memory = with_unindexed_memory(
                    &data.unindexed_memory,
                    *loan,
                    &symbolic_memory_ranges(&memory_backing),
                );
                if protects_memory {
                    data.active_memory_loans = data
                        .active_memory_loans
                        .checked_add(1)
                        .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                }
            }
            LoanTransitionEvidence::Reborrow {
                parent,
                lender,
                borrower,
                scope,
                loan,
                root,
            } => {
                let (permitted, memory_backing, mutex_root) = match parent {
                    ReborrowBinding::View(binding) => {
                        self.validate_view_binding(binding.clone(), *lender)?;
                        let record = self
                            .storage
                            .data
                            .loans
                            .get(&binding.loan)
                            .ok_or(LoanRefusal::MissingLoan)?;
                        let (permitted, backing) = reborrowed_authority(record, &binding.viewed);
                        (permitted, backing, None)
                    }
                    ReborrowBinding::MutexUse(binding) => {
                        self.mutex_use_identity_description(*binding, *lender)?;
                        let record = self
                            .storage
                            .data
                            .loans
                            .get(&binding.0.loan)
                            .ok_or(LoanRefusal::MissingLoan)?;
                        (Vec::new(), Vec::new(), record.mutex_root)
                    }
                };
                let parent = parent.authority();
                self.require_participant(*lender)?;
                self.require_participant(*borrower)?;
                let parent_scope = data
                    .scopes
                    .get(&parent.scope)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                let parent_share = data
                    .shares
                    .get(&parent.share)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                if scope.arena != data.arena
                    || loan.arena != data.arena
                    || root.arena != data.arena
                    || scope.ordinal != data.next_scope
                    || loan.ordinal != data.next_loan
                    || root.ordinal != data.next_share
                {
                    return Err(LoanRefusal::MissingLoanBinding);
                }
                data.next_scope = data
                    .next_scope
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_loan = data
                    .next_loan
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.next_share = data
                    .next_share
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.scopes = data.scopes.with_inserted(
                    parent.scope,
                    LoanScopeRecord {
                        dependencies: parent_scope.dependencies.with_value(*scope),
                        ..parent_scope
                    },
                );
                data.shares = data.shares.with_inserted(
                    parent.share,
                    LoanShareRecord {
                        holder: None,
                        pinned_by: Some(*scope),
                        ..parent_share
                    },
                );
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        loan: *loan,
                        root: *root,
                        close_right: Some(*lender),
                        active: true,
                        parent: Some(parent.scope),
                        parent_share: Some(parent.share),
                        dependencies: crate::persistent::PersistentSet::default(),
                        holds: crate::persistent::PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        mutex_root,
                        assumed_mutex: None,
                        assumed_mutex_protected: None,
                        support: parent.support,
                        escrow: None,
                        permitted: permitted.clone(),
                        origin: LoanOrigin::Reborrowed,
                        recovered: false,
                        memory_backing: memory_backing.clone(),
                    },
                );
                data.shares = data.shares.with_inserted(
                    *root,
                    LoanShareRecord {
                        scope: *scope,
                        parent: None,
                        children: None,
                        holder: Some(*borrower),
                        pinned_by: None,
                    },
                );
                data.active_footprint = data.active_footprint.with_loan(*loan, &memory_backing);
                for range in &memory_backing {
                    // A symbolic parent range stays protected by the parent
                    // entry, which remains active while its share is pinned.
                    update_indexed_memory_range(&mut data, range, *loan, true)?;
                }
                // Counted by the same predicate `End` decrements with, over
                // the narrowed authority this child actually holds, so a
                // reborrow of a byte-less composite loan is conserved.
                if loan_protects_memory(&memory_backing, &permitted) {
                    data.active_memory_loans = data
                        .active_memory_loans
                        .checked_add(1)
                        .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                }
            }
            LoanTransitionEvidence::Split {
                share,
                holder,
                left_holder,
                right_holder,
                left,
                right,
            } => {
                let parent = data
                    .shares
                    .get(share)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                if parent.holder != Some(*holder) {
                    return Err(LoanRefusal::WrongHolder);
                }
                if !data
                    .scopes
                    .get(&parent.scope)
                    .is_some_and(|scope| scope.active)
                {
                    return Err(LoanRefusal::ScopeEnded);
                }
                let expected_right = data
                    .next_share
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                if left.arena != data.arena
                    || right.arena != data.arena
                    || left.ordinal != data.next_share
                    || right.ordinal != expected_right
                {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                data.next_share = data
                    .next_share
                    .checked_add(2)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.shares = data.shares.with_inserted(
                    *share,
                    LoanShareRecord {
                        holder: None,
                        children: Some((*left, *right)),
                        ..parent.clone()
                    },
                );
                for (child, child_holder) in [(*left, *left_holder), (*right, *right_holder)] {
                    data.shares = data.shares.with_inserted(
                        child,
                        LoanShareRecord {
                            scope: parent.scope,
                            parent: Some(*share),
                            children: None,
                            holder: Some(child_holder),
                            pinned_by: None,
                        },
                    );
                }
            }
            LoanTransitionEvidence::Transfer { share, from, to } => {
                let record = data
                    .shares
                    .get(share)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                if record.holder != Some(*from) {
                    return Err(LoanRefusal::WrongHolder);
                }
                data.shares = data.shares.with_inserted(
                    *share,
                    LoanShareRecord {
                        holder: Some(*to),
                        ..record
                    },
                );
            }
            LoanTransitionEvidence::Join {
                left,
                right,
                holder,
            } => {
                let left_record = data
                    .shares
                    .get(left)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                let right_record = data
                    .shares
                    .get(right)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                if left_record.holder != Some(*holder) || right_record.holder != Some(*holder) {
                    return Err(LoanRefusal::WrongHolder);
                }
                if left_record.scope != right_record.scope {
                    return Err(LoanRefusal::WrongScope);
                }
                let parent = left_record.parent.ok_or(LoanRefusal::NotSiblings)?;
                if right_record.parent != Some(parent)
                    || data.shares.get(&parent).and_then(|record| record.children)
                        != Some((*left, *right))
                {
                    return Err(LoanRefusal::NotSiblings);
                }
                for child in [*left, *right] {
                    let record = data.shares.get(&child).cloned().expect("checked child");
                    data.shares = data.shares.with_inserted(
                        child,
                        LoanShareRecord {
                            holder: None,
                            ..record
                        },
                    );
                }
                let parent_record = data
                    .shares
                    .get(&parent)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                data.shares = data.shares.with_inserted(
                    parent,
                    LoanShareRecord {
                        holder: Some(*holder),
                        ..parent_record
                    },
                );
            }
            LoanTransitionEvidence::Hold {
                binding,
                holder,
                hold,
            } => {
                self.validate_authority_binding(*binding, *holder)?;
                let scope_record = data
                    .scopes
                    .get(&binding.scope)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                if hold.arena != data.arena || hold.ordinal != data.next_hold {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                data.next_hold = data
                    .next_hold
                    .checked_add(1)
                    .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
                data.holds = data.holds.with_inserted(*hold, (binding.scope, *holder));
                data.scopes = data.scopes.with_inserted(
                    binding.scope,
                    LoanScopeRecord {
                        holds: scope_record.holds.with_value(*hold),
                        ..scope_record
                    },
                );
            }
            LoanTransitionEvidence::Release {
                hold,
                scope,
                holder,
            } => {
                if hold.arena != data.arena || holder.arena != data.arena {
                    return Err(LoanRefusal::WrongArena);
                }
                let (actual_scope, placed_by) = data
                    .holds
                    .get(hold)
                    .copied()
                    .ok_or(LoanRefusal::MissingScope)?;
                if actual_scope != *scope {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                if placed_by != *holder {
                    return Err(LoanRefusal::WrongHolder);
                }
                let scope_record = data
                    .scopes
                    .get(scope)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                data.holds = data.holds.without_key(hold);
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        holds: scope_record.holds.without_value(hold),
                        ..scope_record
                    },
                );
            }
            LoanTransitionEvidence::End { scope, holder } => {
                let scope_record = data
                    .scopes
                    .get(scope)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                if !scope_record.active {
                    return Err(LoanRefusal::ScopeEnded);
                }
                if scope_record.close_right != Some(*holder) {
                    return Err(LoanRefusal::WrongHolder);
                }
                if !scope_record.dependencies.is_empty() || !scope_record.holds.is_empty() {
                    return Err(LoanRefusal::ActiveDependency);
                }
                let root = data
                    .shares
                    .get(&scope_record.root)
                    .cloned()
                    .ok_or(LoanRefusal::MissingShare)?;
                if root.holder != Some(*holder) {
                    return Err(LoanRefusal::ShareStillSplit);
                }
                data.shares = data.shares.with_inserted(
                    scope_record.root,
                    LoanShareRecord {
                        holder: None,
                        ..root
                    },
                );
                data.scopes = data.scopes.with_inserted(
                    *scope,
                    LoanScopeRecord {
                        active: false,
                        ..scope_record
                    },
                );
                if let Some(record) = data.loans.get(&scope_record.loan).cloned() {
                    data.active_footprint = data.active_footprint.without_loan(scope_record.loan);
                    data.unindexed_memory = without_unindexed_memory(
                        &data.unindexed_memory,
                        scope_record.loan,
                        &symbolic_memory_ranges(&record.memory_backing),
                    );
                    for range in &record.memory_backing {
                        update_indexed_memory_range(&mut data, range, scope_record.loan, false)?;
                    }
                    if loan_protects_memory(&record.memory_backing, &record.permitted) {
                        data.active_memory_loans = data
                            .active_memory_loans
                            .checked_sub(1)
                            .ok_or(LoanRefusal::InvalidEvidence)?;
                    }
                }
                if let Some(parent) = data.scopes.get(scope).and_then(|record| record.parent) {
                    let parent_record = data
                        .scopes
                        .get(&parent)
                        .cloned()
                        .ok_or(LoanRefusal::MissingScope)?;
                    data.scopes = data.scopes.with_inserted(
                        parent,
                        LoanScopeRecord {
                            dependencies: parent_record.dependencies.without_value(scope),
                            ..parent_record
                        },
                    );
                    if let Some(parent_share) = scope_record.parent_share {
                        let pinned = data
                            .shares
                            .get(&parent_share)
                            .cloned()
                            .ok_or(LoanRefusal::MissingShare)?;
                        if pinned.pinned_by != Some(*scope) || pinned.holder.is_some() {
                            return Err(LoanRefusal::InvalidEvidence);
                        }
                        data.shares = data.shares.with_inserted(
                            parent_share,
                            LoanShareRecord {
                                holder: Some(
                                    scope_record
                                        .close_right
                                        .ok_or(LoanRefusal::InvalidEvidence)?,
                                ),
                                pinned_by: None,
                                ..pinned
                            },
                        );
                    }
                }
            }
            LoanTransitionEvidence::Recover { loan, holder } => {
                let record = data
                    .loans
                    .get(loan)
                    .cloned()
                    .ok_or(LoanRefusal::MissingLoan)?;
                let LoanOrigin::Escrowed(recovery_right) = record.origin else {
                    return Err(LoanRefusal::InvalidEvidence);
                };
                if recovery_right != *holder {
                    return Err(LoanRefusal::WrongHolder);
                }
                if record.recovered {
                    return Err(LoanRefusal::AlreadyRecovered);
                }
                if data
                    .scopes
                    .get(&record.scope)
                    .is_some_and(|scope| scope.active)
                {
                    return Err(LoanRefusal::ScopeStillActive);
                }
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        recovered: true,
                        ..record
                    },
                );
            }
            LoanTransitionEvidence::RegisterDependency {
                parent,
                child,
                holder,
            } => {
                if parent == child {
                    return Err(LoanRefusal::InvalidEvidence);
                }
                let parent_record = data
                    .scopes
                    .get(parent)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                let child_record = data
                    .scopes
                    .get(child)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                if !parent_record.active || !child_record.active {
                    return Err(LoanRefusal::ScopeEnded);
                }
                if parent_record.close_right != Some(*holder) || child_record.parent.is_some() {
                    return Err(LoanRefusal::WrongHolder);
                }
                let parent_share = data
                    .shares
                    .get(&parent_record.root)
                    .ok_or(LoanRefusal::MissingShare)?;
                if parent_share.holder != Some(*holder) {
                    return Err(LoanRefusal::WrongHolder);
                }
                data.scopes = data.scopes.with_inserted(
                    *parent,
                    LoanScopeRecord {
                        dependencies: parent_record.dependencies.with_value(*child),
                        ..parent_record
                    },
                );
                data.scopes = data.scopes.with_inserted(
                    *child,
                    LoanScopeRecord {
                        parent: Some(*parent),
                        ..child_record
                    },
                );
            }
        }
        Ok(data)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn invariant_holds(&self) -> bool {
        if !self.exclusive_calls_invariant() || !self.local_references_invariant() {
            return false;
        }
        let data = &self.storage.data;
        let mut expected_cache_index = CacheProtectionIndex::default();
        let mut expected_cache_subtree = CacheProtectionIndex::default();
        for (loan, record) in data.loans.iter() {
            if !data
                .scopes
                .get(&record.scope)
                .is_some_and(|scope| scope.active)
            {
                continue;
            }
            for range in &record.memory_backing {
                if let Some((origin, nodes)) = cache_protection_nodes(range) {
                    for node in nodes {
                        for ancestor in memory_interval_ancestors(&node) {
                            update_cache_protection_bucket(
                                &mut expected_cache_subtree,
                                (origin.clone(), ancestor),
                                *loan,
                                true,
                            );
                        }
                        update_cache_protection_bucket(
                            &mut expected_cache_index,
                            (origin.clone(), node),
                            *loan,
                            true,
                        );
                    }
                }
            }
        }
        if !expected_cache_index
            .iter()
            .eq(data.cache_memory_index.iter())
            || !expected_cache_subtree
                .iter()
                .eq(data.cache_memory_subtree.iter())
        {
            return false;
        }
        let mut expected_unindexed = BTreeMap::new();
        for (loan_id, loan) in data.loans.iter() {
            if matches!(loan.origin, LoanOrigin::Reborrowed)
                || !data
                    .scopes
                    .get(&loan.scope)
                    .is_some_and(|scope| scope.active)
            {
                continue;
            }
            for range in symbolic_memory_ranges(&loan.memory_backing) {
                expected_unindexed
                    .entry((range.base().block.clone(), *loan_id))
                    .or_insert_with(Vec::new)
                    .push(range);
            }
        }
        let mut actual_unindexed = BTreeMap::new();
        for (block, bucket) in data.unindexed_memory.iter() {
            if bucket.is_empty() {
                return false;
            }
            for (loan_id, ranges) in bucket.iter() {
                if ranges.is_empty() || ranges.iter().any(|range| &range.base().block != block) {
                    return false;
                }
                actual_unindexed.insert((block.clone(), *loan_id), ranges.clone());
            }
        }
        if expected_unindexed != actual_unindexed {
            return false;
        }
        // The fail-closed barrier counter is exactly the number of live loans
        // that protect memory, whether or not they enumerated any bytes.
        let expected_active_memory_loans = data
            .loans
            .iter()
            .filter(|(_, loan)| {
                data.scopes
                    .get(&loan.scope)
                    .is_some_and(|scope| scope.active)
                    && loan_protects_memory(&loan.memory_backing, &loan.permitted)
            })
            .count();
        if data.active_memory_loans != expected_active_memory_loans {
            return false;
        }
        let expected_nonlocal_indexed_ranges = data
            .loans
            .iter()
            .filter(|(_, loan)| {
                data.scopes
                    .get(&loan.scope)
                    .is_some_and(|scope| scope.active)
            })
            .flat_map(|(_, loan)| &loan.memory_backing)
            .filter(|range| {
                !range.base().block.is_local_block() && ledger_interval_nodes(range).is_some()
            })
            .count();
        if data.active_nonlocal_indexed_ranges != expected_nonlocal_indexed_ranges {
            return false;
        }
        for (loan_id, loan) in data.loans.iter() {
            if loan_id.arena != data.arena {
                return false;
            }
            let Some(scope) = data.scopes.get(&loan.scope) else {
                return false;
            };
            if loan.recovered && scope.active {
                return false;
            }
            if loan.assumed_mutex_protected.is_some() && loan.assumed_mutex.is_none() {
                return false;
            }
            if loan.assumed_mutex.is_some()
                && (loan.origin != LoanOrigin::BorrowedContractInput
                    || loan.mutex_root != Some(*loan_id))
            {
                return false;
            }
            if let Some(root_id) = loan.mutex_root {
                let Some(root) = data.loans.get(&root_id) else {
                    return false;
                };
                if root.mutex_root != Some(root_id)
                    || root.support != loan.support
                    || root.mutex_identity_description().is_none()
                    || !loan.permitted.is_empty()
                    || !loan.memory_backing.is_empty()
                    || (scope.active
                        && (root.recovered
                            || !data.scopes.get(&root.scope).is_some_and(|s| s.active)))
                    || (root_id != *loan_id
                        && (loan.escrow.is_some()
                            || loan.assumed_mutex.is_some()
                            || loan.origin != LoanOrigin::Reborrowed))
                {
                    return false;
                }
            }
            let origin_is_valid = match &loan.origin {
                LoanOrigin::Escrowed(recovery_right) => {
                    loan.escrow.as_ref().is_some_and(ResourceFact::is_own)
                        && scope.close_right == Some(*recovery_right)
                        && scope.parent.is_none()
                }
                LoanOrigin::Reborrowed => {
                    loan.escrow.is_none()
                        && scope.close_right.is_some()
                        && scope.parent.is_some()
                        && !loan.recovered
                }
                LoanOrigin::LocalStorage(lender) => {
                    loan.escrow.is_none()
                        && scope.close_right == Some(*lender)
                        && scope.parent.is_none()
                        && !loan.recovered
                        && loan.support != ResourceOccurrenceId::default()
                        && loan
                            .permitted
                            .iter()
                            .all(|fact| fact.is_view() && fact.memory_range().is_some())
                }
                LoanOrigin::BorrowedContractInput => {
                    loan.escrow.is_none()
                        && scope.close_right.is_none()
                        && scope.parent.is_none()
                        && !loan.recovered
                        && loan.support != ResourceOccurrenceId::default()
                        && loan.permitted.iter().all(ResourceFact::is_view)
                }
            };
            if !origin_is_valid {
                return false;
            }
        }
        for (hold, (scope, _)) in data.holds.iter() {
            if hold.arena != data.arena
                || !data
                    .scopes
                    .get(scope)
                    .is_some_and(|record| record.active && record.holds.contains(hold))
            {
                return false;
            }
        }
        for (scope_id, scope) in data.scopes.iter() {
            if scope_id.arena != data.arena || scope.root.arena != data.arena {
                return false;
            }
            if scope
                .holds
                .iter()
                .any(|hold| data.holds.get(hold).map(|(held, _)| held) != Some(scope_id))
            {
                return false;
            }
            let Some(active_leaves) = self.conserved_active_leaves(*scope_id, scope.root) else {
                return false;
            };
            if scope.active != (active_leaves > 0) {
                return false;
            }
        }
        data.shares
            .iter()
            .all(|(share, record)| share.arena == data.arena && record.scope.arena == data.arena)
    }

    #[cfg(test)]
    fn conserved_active_leaves(&self, scope: LoanScopeId, share: LoanShareId) -> Option<usize> {
        let record = self.storage.data.shares.get(&share)?;
        if record.scope != scope {
            return None;
        }
        if record.holder.is_some() {
            return (!self.descendant_is_active(record)).then_some(1);
        }
        if let Some(pinning_scope) = record.pinned_by {
            // A leaf pinned under a child scope is still one conserved
            // share: the child holds it until that scope ends.
            return self
                .storage
                .data
                .scopes
                .get(&pinning_scope)
                .is_some_and(|scope| scope.active && scope.parent == Some(record.scope))
                .then_some(1);
        }
        match record.children {
            Some((left, right)) => Some(
                self.conserved_active_leaves(scope, left)?
                    + self.conserved_active_leaves(scope, right)?,
            ),
            None => Some(0),
        }
    }

    #[cfg(test)]
    fn descendant_is_active(&self, record: &LoanShareRecord) -> bool {
        let Some((left, right)) = record.children else {
            return false;
        };
        [left, right].into_iter().any(|child| {
            self.storage
                .data
                .shares
                .get(&child)
                .is_some_and(|record| record.holder.is_some() || self.descendant_is_active(record))
        })
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod local_storage_tests;

#[cfg(test)]
mod hold_identity_tests;

mod legacy_search;
