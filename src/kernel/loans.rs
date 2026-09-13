//! Stable shared-loan authority for resource views.
//!
//! A [`LoanLedger`] is immutable. Every update returns opaque checked
//! evidence tied to the exact predecessor state identity. The ledger deliberately
//! contains no C call-stack policy: ordinary calls, named contracts, and
//! future language frontends must all use the same transitions.

use super::functions::CCheckedResourceFact;
use super::{
    CMemoryRange, CResource, CResourceFact, CResourceSnapshot, CResourceTransferRole,
    PureFactContext, ResourceContext, ResourceOccurrenceId,
};
use crate::persistent::PersistentMap;
use std::cmp::Ordering;
use std::collections::BTreeMap;
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewDescription {
    loan: LoanId,
    support: ResourceOccurrenceId,
    viewed: CResourceFact,
}

impl StableViewDescription {
    pub(crate) fn loan(&self) -> LoanId {
        self.loan
    }

    pub(crate) fn viewed(&self) -> &CResourceFact {
        &self.viewed
    }

    pub(crate) fn support(&self) -> ResourceOccurrenceId {
        self.support
    }
}

/// A read derived from ownership in the current context. This is useful for
/// checking the owner's own computation, but it is not transferable loan
/// authority and contains no loan identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OwnedResourceObservation {
    support: ResourceOccurrenceId,
    viewed: CResourceFact,
}

impl OwnedResourceObservation {
    pub(crate) fn new(support: ResourceOccurrenceId, owned: &CResourceFact) -> Option<Self> {
        owned.is_own().then(|| Self {
            support,
            viewed: CResourceFact::View(owned.resource().clone()),
        })
    }

    pub(crate) fn support(&self) -> ResourceOccurrenceId {
        self.support
    }

    pub(crate) fn viewed(&self) -> &CResourceFact {
        &self.viewed
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanScopeRecord {
    root: LoanShareId,
    close_right: LoanParticipantId,
    active: bool,
    parent: Option<LoanScopeId>,
    dependencies: crate::persistent::PersistentSet<LoanScopeId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanRecord {
    scope: LoanScopeId,
    support: ResourceOccurrenceId,
    escrow: CResourceFact,
    recovery_right: LoanParticipantId,
    recovered: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanShareRecord {
    scope: LoanScopeId,
    parent: Option<LoanShareId>,
    children: Option<(LoanShareId, LoanShareId)>,
    holder: Option<LoanParticipantId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanLedgerData {
    arena: u64,
    next_scope: u64,
    next_loan: u64,
    next_share: u64,
    scopes: PersistentMap<LoanScopeId, LoanScopeRecord>,
    loans: PersistentMap<LoanId, LoanRecord>,
    shares: PersistentMap<LoanShareId, LoanShareRecord>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanLedgerStorage {
    state: LoanLedgerStateId,
    data: LoanLedgerData,
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

#[derive(Clone, Debug, Eq, PartialEq)]
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
    IdentitySpaceExhausted,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LoanTransitionEvidence {
    Lend {
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: CResourceFact,
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
    End {
        scope: LoanScopeId,
        holder: LoanParticipantId,
    },
    Recover {
        loan: LoanId,
        holder: LoanParticipantId,
    },
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
    pub(crate) requirement: CCheckedResourceFact,
    pub(crate) support: ResourceOccurrenceId,
    pub(crate) loan: LoanId,
    pub(crate) scope: LoanScopeId,
    pub(crate) share: LoanShareId,
    pub(crate) description: StableViewDescription,
}

/// One body-independent partition of a call's resource requirements.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewTransferPlan {
    pub(crate) caller_resources_after_requirements: ResourceContext,
    pub(crate) callee_resources: ResourceContext,
    pub(crate) transferred_ownership: Vec<CCheckedResourceFact>,
    pub(crate) stable_views: Vec<PlannedStableView>,
    pub(crate) memory_effects: Vec<CMemoryRange>,
    pub(crate) ledger: LoanLedger,
    pub(crate) entry_transitions: Vec<CheckedLoanTransition>,
    parent_ledger: LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    loan_roots: Vec<(LoanScopeId, LoanId, LoanShareId, ResourceOccurrenceId)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewRecovery {
    pub(crate) ledger: LoanLedger,
    pub(crate) resources: ResourceContext,
    pub(crate) transitions: Vec<CheckedLoanTransition>,
}

impl StableViewRecovery {
    /// Replays the ordered recovery evidence from the exact entry ledger.
    /// Applying each item performs the kernel's predecessor and payload checks;
    /// callers can retain the returned historical successor separately from
    /// the canonical predecessor stored in `ledger`.
    pub(crate) fn replay_transitions(
        &self,
        predecessor: &LoanLedger,
    ) -> Result<LoanLedger, LoanRefusal> {
        let mut current = predecessor.clone();
        for transition in &self.transitions {
            current = current.apply(transition)?;
        }
        Ok(current)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StableViewPlanError {
    InvalidRequirement,
    MissingResource(CResourceFact),
    ConflictingRequirement(CResourceFact),
    Loan(LoanRefusal),
    InvalidResidual,
    UnsupportedPartition,
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
    requirements: &[CCheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
) -> Result<StableViewTransferPlan, StableViewPlanError> {
    if requirements.iter().any(|requirement| {
        requirement.snapshot == CResourceSnapshot::Post
            || requirement.role == CResourceTransferRole::Produce
            || (requirement.fact.is_view() && requirement.role != CResourceTransferRole::Borrow)
    }) {
        return Err(StableViewPlanError::InvalidRequirement);
    }

    let mut residual = caller_resources.clone();
    let mut callee_resources = ResourceContext::new();
    let mut transferred_ownership = Vec::new();
    let mut stable_views = Vec::new();
    let mut memory_effects = Vec::new();
    // Reserve exclusive requirements first. This makes the partition stable
    // under source reordering and prevents a view from hiding a later write.
    for requirement in requirements
        .iter()
        .filter(|requirement| requirement.fact.is_own())
    {
        if residual
            .directly_supporting_owned_entry(&requirement.fact, assumptions)
            .is_none()
        {
            return Err(StableViewPlanError::MissingResource(
                requirement.fact.clone(),
            ));
        }
        residual = residual
            .without_fact_incrementally(&requirement.fact, assumptions)
            .ok_or_else(|| StableViewPlanError::MissingResource(requirement.fact.clone()))?;
        callee_resources = callee_resources
            .try_compose_with_fact(requirement.fact.clone(), assumptions)
            .map_err(|_| StableViewPlanError::InvalidResidual)?;
        if let Some(range) = requirement.fact.memory_own_range() {
            memory_effects.push(range.clone());
        }
        transferred_ownership.push(requirement.clone());
    }

    let mut loan_roots = Vec::new();
    let mut planned_ledger = ledger.clone();
    let mut entry_transitions = Vec::new();
    let mut grouped = BTreeMap::<ResourceOccurrenceId, Vec<(usize, CCheckedResourceFact)>>::new();
    for (index, requirement) in requirements.iter().enumerate() {
        if !requirement.fact.is_view() {
            continue;
        }
        if let Some(range) = requirement.fact.memory_range()
            && (range.start().as_const().is_none() || range.end().as_const().is_none())
        {
            return Err(StableViewPlanError::UnsupportedPartition);
        }
        let Some((support, owned)) =
            caller_resources.directly_supporting_owned_entry(&requirement.fact, assumptions)
        else {
            return Err(StableViewPlanError::MissingResource(
                requirement.fact.clone(),
            ));
        };
        if matches!(
            owned.resource(),
            CResource::Composite { .. } | CResource::Instance(_)
        ) {
            return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
        }
        grouped
            .entry(support)
            .or_default()
            .push((index, requirement.clone()));
    }

    let mut planned_views = Vec::<(usize, PlannedStableView)>::new();
    for (_origin_support, group) in grouped {
        let mut clusters: Vec<Vec<(usize, CCheckedResourceFact)>> = Vec::new();
        for item in group {
            let Some(range) = item.1.fact.memory_range().cloned() else {
                if !matches!(item.1.fact.resource(), CResource::Token { .. }) {
                    return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
                }
                if let Some(token_cluster) = clusters.iter_mut().find(|cluster| {
                    cluster
                        .first()
                        .is_some_and(|(_, requirement)| requirement.fact.memory_range().is_none())
                }) {
                    token_cluster.push(item);
                } else {
                    clusters.push(vec![item]);
                }
                continue;
            };
            if range.start().as_const().is_none() || range.end().as_const().is_none() {
                return Err(StableViewPlanError::UnsupportedPartition);
            }
            let mut pending = vec![item];
            let mut pending_union = range;
            let mut cluster_index = 0;
            while cluster_index < clusters.len() {
                let Some(existing_union) = concrete_memory_cluster_union(&clusters[cluster_index])
                else {
                    cluster_index += 1;
                    continue;
                };
                let Some(union) = concrete_memory_union(&existing_union, &pending_union) else {
                    cluster_index += 1;
                    continue;
                };
                pending_union = union;
                pending.extend(clusters.remove(cluster_index));
                // Expanding the pending interval can make it overlap a
                // cluster that was previously disjoint, so restart the
                // indexed merge walk after each removal.
                cluster_index = 0;
            }
            clusters.push(pending);
        }

        for cluster in clusters {
            let selected = if cluster
                .first()
                .and_then(|(_, item)| item.fact.memory_range())
                .is_some()
            {
                let mut union = cluster
                    .first()
                    .and_then(|(_, item)| item.fact.memory_range())
                    .cloned()
                    .ok_or(StableViewPlanError::UnsupportedPartition)?;
                for (_, item) in cluster.iter().skip(1) {
                    let range = item
                        .fact
                        .memory_range()
                        .ok_or(StableViewPlanError::UnsupportedPartition)?;
                    union = concrete_memory_union(&union, range)
                        .ok_or(StableViewPlanError::UnsupportedPartition)?;
                }
                CResourceFact::own_memory(union)
            } else {
                let resource = cluster
                    .first()
                    .map(|(_, item)| item.fact.resource().clone())
                    .ok_or(StableViewPlanError::UnsupportedPartition)?;
                CResourceFact::own(CResource::Token {
                    name: match resource {
                        CResource::Token { ref name, .. } => name.clone(),
                        _ => return Err(StableViewPlanError::UnsupportedPartition),
                    },
                    arguments: match resource {
                        CResource::Token { arguments, .. } => arguments,
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
            let opening = planned_ledger.lend(caller, callee, support, selected.clone())?;
            entry_transitions.push(opening.transition.clone());
            planned_ledger = planned_ledger.apply(&opening.transition)?;
            residual = residual
                .without_fact_incrementally(&selected, assumptions)
                .ok_or_else(|| StableViewPlanError::MissingResource(owned.clone()))?;
            let root_index = loan_roots.len();
            loan_roots.push((opening.scope, opening.loan, opening.root_share, support));
            for (index, requirement) in cluster {
                let description = planned_ledger
                    .describe_view(opening.loan, requirement.fact.clone(), assumptions)
                    .map_err(|_| {
                        StableViewPlanError::ConflictingRequirement(requirement.fact.clone())
                    })?;
                callee_resources = callee_resources
                    .try_compose_with_fact(requirement.fact.clone(), assumptions)
                    .map_err(|_| StableViewPlanError::InvalidResidual)?;
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
            let _ = root_index;
        }
    }
    planned_views.sort_by_key(|(index, _)| *index);
    stable_views.extend(planned_views.into_iter().map(|(_, view)| view));

    Ok(StableViewTransferPlan {
        caller_resources_after_requirements: residual,
        callee_resources,
        transferred_ownership,
        stable_views,
        memory_effects,
        ledger: planned_ledger,
        entry_transitions,
        parent_ledger: ledger.clone(),
        caller,
        callee,
        loan_roots,
    })
}

impl StableViewTransferPlan {
    pub(crate) fn caller_participant(&self) -> LoanParticipantId {
        self.caller
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

    /// Closes every unmodified root share and returns the exact escrowed
    /// ownership to the residual caller context.
    pub(crate) fn recover_stable_views(
        self,
        assumptions: &PureFactContext,
    ) -> Result<StableViewRecovery, StableViewPlanError> {
        let parent_ledger = self.parent_ledger;
        let stable_views = self.stable_views.clone();
        let loan_roots = self.loan_roots.clone();
        let mut ledger = self.ledger;
        let mut resources = self.caller_resources_after_requirements;
        let mut transitions = Vec::new();
        for (scope, loan, root, _) in loan_roots.into_iter().rev() {
            let transfer = ledger.transfer(root, self.callee, self.caller)?;
            ledger = ledger.apply(&transfer)?;
            transitions.push(transfer);
            let end = ledger.end(scope, self.caller)?;
            ledger = ledger.apply(&end)?;
            transitions.push(end);
            let (recover, escrow, support) = ledger.recover(loan, self.caller)?;
            ledger = ledger.apply(&recover)?;
            transitions.push(recover);
            if support
                != stable_views
                    .iter()
                    .find(|view| view.loan == loan)
                    .map(|view| view.support)
                    .unwrap_or(support)
            {
                return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
            }
            resources = resources
                .try_compose_with_fact(escrow, assumptions)
                .map_err(|_| StableViewPlanError::InvalidResidual)?;
        }
        // Every scope in loan_roots was created by this plan and has just
        // passed End and Recover. End checks its indexed dependency set, so a
        // registered child would have refused before this checkpoint. The
        // plan can therefore roll back directly to the exact predecessor
        // root without a whole-ledger quiescence scan.
        ledger = parent_ledger;
        Ok(StableViewRecovery {
            ledger,
            resources,
            transitions,
        })
    }

    pub(crate) fn replay_entry(&self, predecessor: &LoanLedger) -> Result<LoanLedger, LoanRefusal> {
        let mut current = predecessor.clone();
        for transition in &self.entry_transitions {
            current = current.apply(transition)?;
        }
        (current == self.ledger)
            .then_some(current)
            .ok_or(LoanRefusal::InvalidEvidence)
    }
}

fn concrete_memory_union(left: &CMemoryRange, right: &CMemoryRange) -> Option<CMemoryRange> {
    if left.base() != right.base() || left.element_width() != right.element_width() {
        return None;
    }
    let left_start = left.start().as_const()?;
    let left_end = left.end().as_const()?;
    let right_start = right.start().as_const()?;
    let right_end = right.end().as_const()?;
    if left_start > left_end || right_start > right_end {
        return None;
    }
    if left_end < right_start || right_end < left_start {
        return None;
    }
    Some(CMemoryRange::new_with_element_width(
        left.base().clone(),
        left_start.min(right_start).into(),
        left_end.max(right_end).into(),
        left.element_width(),
    ))
}

fn concrete_memory_cluster_union(
    cluster: &[(usize, CCheckedResourceFact)],
) -> Option<CMemoryRange> {
    let mut union = cluster.first()?.1.fact.memory_range()?.clone();
    for (_, requirement) in cluster.iter().skip(1) {
        union = concrete_memory_union(&union, requirement.fact.memory_range()?)?;
    }
    Some(union)
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
                    next_scope: 0,
                    next_loan: 0,
                    next_share: 0,
                    scopes: PersistentMap::default(),
                    loans: PersistentMap::default(),
                    shares: PersistentMap::default(),
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

    pub(crate) fn lend(
        &self,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: CResourceFact,
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
            CResource::Memory(_) | CResource::Token { .. }
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
                viewed: CResourceFact::View(escrow.resource().clone()),
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

    pub(crate) fn end(
        &self,
        scope: LoanScopeId,
        holder: LoanParticipantId,
    ) -> Result<CheckedLoanTransition, LoanRefusal> {
        self.require_arena(scope.arena)?;
        self.require_participant(holder)?;
        self.issue(LoanTransitionEvidence::End { scope, holder })
    }

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
    ) -> Result<(CheckedLoanTransition, CResourceFact, ResourceOccurrenceId), LoanRefusal> {
        self.require_arena(loan.arena)?;
        self.require_participant(holder)?;
        let escrow = self
            .storage
            .data
            .loans
            .get(&loan)
            .ok_or(LoanRefusal::MissingLoan)?
            .escrow
            .clone();
        let support = self
            .storage
            .data
            .loans
            .get(&loan)
            .ok_or(LoanRefusal::MissingLoan)?
            .support;
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
        let Some(scope) = self.storage.data.scopes.get(&loan.scope) else {
            return false;
        };
        let Some(share) = self.storage.data.shares.get(&share) else {
            return false;
        };
        scope.active
            && !loan.recovered
            && share.scope == loan.scope
            && share.holder == Some(holder)
            && description.viewed.is_view()
            && ResourceContext::new()
                .unchecked_with_fact(loan.escrow.clone())
                .satisfies_fact(&description.viewed, assumptions)
    }

    pub(crate) fn describe_view(
        &self,
        loan: LoanId,
        viewed: CResourceFact,
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
        if !viewed.is_view()
            || !ResourceContext::new()
                .unchecked_with_fact(record.escrow.clone())
                .satisfies_fact(&viewed, assumptions)
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

    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.storage, &other.storage)
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
        let mut data = self.storage.data.clone();
        match evidence {
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
                    CResource::Memory(_) | CResource::Token { .. }
                ) {
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
                        root: *root,
                        close_right: *lender,
                        active: true,
                        parent: None,
                        dependencies: crate::persistent::PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        support: *support,
                        escrow: escrow.clone(),
                        recovery_right: *lender,
                        recovered: false,
                    },
                );
                data.shares = data.shares.with_inserted(
                    *root,
                    LoanShareRecord {
                        scope: *scope,
                        parent: None,
                        children: None,
                        holder: Some(*borrower),
                    },
                );
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
            LoanTransitionEvidence::End { scope, holder } => {
                let scope_record = data
                    .scopes
                    .get(scope)
                    .cloned()
                    .ok_or(LoanRefusal::MissingScope)?;
                if !scope_record.active {
                    return Err(LoanRefusal::ScopeEnded);
                }
                if scope_record.close_right != *holder {
                    return Err(LoanRefusal::WrongHolder);
                }
                if !scope_record.dependencies.is_empty() {
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
                }
            }
            LoanTransitionEvidence::Recover { loan, holder } => {
                let record = data
                    .loans
                    .get(loan)
                    .cloned()
                    .ok_or(LoanRefusal::MissingLoan)?;
                if record.recovery_right != *holder {
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
                if parent_record.close_right != *holder || child_record.parent.is_some() {
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
    fn invariant_holds(&self) -> bool {
        let data = &self.storage.data;
        for (loan_id, loan) in data.loans.iter() {
            if loan_id.arena != data.arena || !loan.escrow.is_own() {
                return false;
            }
            let Some(scope) = data.scopes.get(&loan.scope) else {
                return false;
            };
            if loan.recovered && scope.active {
                return false;
            }
        }
        for (scope_id, scope) in data.scopes.iter() {
            if scope_id.arena != data.arena || scope.root.arena != data.arena {
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
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, CResource, CResourceFact, Variable};

    fn owned(name: &str) -> CResourceFact {
        CResourceFact::own(CResource::Token {
            name: name.to_string(),
            arguments: Vec::new().into(),
        })
    }

    fn backing(fact: &CResourceFact) -> ResourceOccurrenceId {
        ResourceContext::new()
            .unchecked_with_fact(fact.clone())
            .unique_owned_occurrence_for_fact(fact)
            .unwrap()
            .0
    }

    fn lend_test(
        ledger: &LoanLedger,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        escrow: CResourceFact,
    ) -> LoanOpening {
        ledger
            .lend(lender, borrower, backing(&escrow), escrow)
            .unwrap()
    }

    fn participants() -> (LoanLedger, LoanParticipantId, LoanParticipantId) {
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        (ledger, owner, reader)
    }

    #[test]
    fn checked_two_reader_lifecycle_recovers_exact_escrow_once() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let escrow = owned("cell");
        let opening = lend_test(&ledger, owner, owner, escrow.clone());
        let ledger = ledger.apply(&opening.transition).unwrap();
        let (split, left, right) = ledger
            .split(opening.root_share, owner, owner, reader)
            .unwrap();
        let ledger = ledger.apply(&split).unwrap();
        assert!(ledger.permits_view(owner, &opening.description, left, &assumptions));
        assert!(ledger.permits_view(reader, &opening.description, right, &assumptions));
        assert_eq!(
            ledger.end(opening.scope, owner),
            Err(LoanRefusal::ShareStillSplit)
        );
        let transfer = ledger.transfer(right, reader, owner).unwrap();
        let ledger = ledger.apply(&transfer).unwrap();
        let join = ledger.join(left, right, owner).unwrap();
        let ledger = ledger.apply(&join).unwrap();
        let end = ledger.end(opening.scope, owner).unwrap();
        let ledger = ledger.apply(&end).unwrap();
        assert!(!ledger.permits_view(
            owner,
            &opening.description,
            opening.root_share,
            &assumptions
        ));
        let (recover, recovered, support) = ledger.recover(opening.loan, owner).unwrap();
        assert_eq!(recovered, escrow);
        assert_eq!(support, opening.description.support());
        let ledger = ledger.apply(&recover).unwrap();
        assert!(ledger.invariant_holds());
        assert_eq!(
            ledger.recover(opening.loan, owner),
            Err(LoanRefusal::AlreadyRecovered)
        );
    }

    #[test]
    fn transitions_are_bound_to_their_exact_predecessor() {
        let (ledger, owner, reader) = participants();
        let opening = lend_test(&ledger, owner, reader, owned("cell"));
        let advanced = ledger.apply(&opening.transition).unwrap();
        assert_eq!(
            advanced.apply(&opening.transition),
            Err(LoanRefusal::StalePredecessor)
        );
        let unrelated = LoanLedger::new();
        assert_eq!(
            unrelated.apply(&opening.transition),
            Err(LoanRefusal::StalePredecessor)
        );
    }

    #[test]
    fn divergent_successors_have_distinct_state_identities() {
        let (ledger, owner, reader) = participants();
        let first = lend_test(&ledger, owner, reader, owned("first"));
        let second = lend_test(&ledger, owner, reader, owned("second"));
        let first = ledger.apply(&first.transition).unwrap();
        let second = ledger.apply(&second.transition).unwrap();
        assert_ne!(first, second);
        assert!(!first.shares_storage_with(&second));
    }

    #[test]
    fn hostile_transition_payload_is_rechecked() {
        let (ledger, owner, reader) = participants();
        let mut opening = lend_test(&ledger, owner, reader, owned("cell"));
        let LoanTransitionEvidence::Lend { borrower, .. } = &mut opening.transition.evidence else {
            panic!("lend evidence")
        };
        *borrower = owner;
        assert_eq!(
            ledger.apply(&opening.transition),
            Err(LoanRefusal::InvalidEvidence)
        );
    }

    #[test]
    fn snapshots_share_storage_and_updates_do_not_mutate_predecessors() {
        let (ledger, owner, reader) = participants();
        let clone = ledger.clone();
        assert!(ledger.shares_storage_with(&clone));
        let opening = lend_test(&ledger, owner, reader, owned("cell"));
        let advanced = ledger.apply(&opening.transition).unwrap();
        assert!(!ledger.shares_storage_with(&advanced));
        assert!(ledger.storage.data.loans.is_empty());
        assert_eq!(advanced.storage.data.loans.len(), 1);
    }

    #[test]
    fn nested_reborrow_must_rejoin_each_parent_before_scope_end() {
        let (ledger, owner, reader) = participants();
        let opening = lend_test(&ledger, owner, owner, owned("cell"));
        let ledger = ledger.apply(&opening.transition).unwrap();
        let (outer_split, retained, reborrowed) = ledger
            .split(opening.root_share, owner, owner, reader)
            .unwrap();
        let ledger = ledger.apply(&outer_split).unwrap();
        let (nested_split, nested_left, nested_right) =
            ledger.split(reborrowed, reader, reader, reader).unwrap();
        let ledger = ledger.apply(&nested_split).unwrap();
        assert_eq!(
            ledger.join(retained, reborrowed, owner),
            Err(LoanRefusal::WrongHolder)
        );
        let nested_join = ledger.join(nested_left, nested_right, reader).unwrap();
        let ledger = ledger.apply(&nested_join).unwrap();
        let return_child = ledger.transfer(reborrowed, reader, owner).unwrap();
        let ledger = ledger.apply(&return_child).unwrap();
        let outer_join = ledger.join(retained, reborrowed, owner).unwrap();
        let ledger = ledger.apply(&outer_join).unwrap();
        assert!(ledger.end(opening.scope, owner).is_ok());
        assert!(ledger.invariant_holds());
    }

    #[test]
    fn owner_observation_is_not_a_stable_view_description() {
        let resources = crate::kernel::ResourceContext::new().unchecked_with_fact(owned("cell"));
        let fact = resources.facts()[0].clone();
        let (occurrence, _) = resources.unique_owned_occurrence_for_fact(&fact).unwrap();
        let observation = OwnedResourceObservation::new(occurrence, &fact).unwrap();
        assert_eq!(observation.support(), occurrence);
        assert_eq!(
            observation.viewed(),
            &CResourceFact::View(fact.resource().clone())
        );
        let (_ledger, _owner, _reader) = participants();
        // Only `lend` creates a `StableViewDescription`; an observation has
        // no loan or scope identity to transfer to another participant.
        assert!(observation.viewed().is_view());
    }

    #[test]
    fn participants_and_scope_ids_cannot_cross_ledger_arenas() {
        let (first, first_owner, _) = participants();
        let (_second, second_owner, second_reader) = participants();
        let cell = owned("cell");
        assert_eq!(
            first.lend(second_owner, second_reader, backing(&cell), cell.clone()),
            Err(LoanRefusal::WrongArena)
        );
        let opening = lend_test(&first, first_owner, first_owner, cell);
        let first = first.apply(&opening.transition).unwrap();
        assert_eq!(
            first.transfer(opening.root_share, second_owner, first_owner),
            Err(LoanRefusal::WrongArena)
        );
    }

    #[test]
    fn first_loan_family_boundary_rejects_composites() {
        let (ledger, owner, reader) = participants();
        let composite = CResourceFact::own_composite("cell".to_string(), Vec::new());
        assert_eq!(
            ledger.lend(owner, reader, backing(&composite), composite),
            Err(LoanRefusal::UnsupportedResource)
        );
    }

    #[test]
    fn local_ledger_updates_allocate_logarithmically() {
        for size in [16_usize, 64, 256, 1024] {
            let (mut ledger, owner, reader) = participants();
            for index in 0..size {
                let cell = owned(&format!("cell_{index}"));
                let opening = ledger.lend(owner, reader, backing(&cell), cell).unwrap();
                ledger = ledger.apply(&opening.transition).unwrap();
            }
            let ancestor = ledger.clone();
            assert!(ledger.shares_storage_with(&ancestor));
            let before = crate::persistent::persistent_node_allocations();
            let target = owned("target");
            let opening = ledger
                .lend(owner, reader, backing(&target), target)
                .unwrap();
            let successor = ledger.apply(&opening.transition).unwrap();
            let allocations = crate::persistent::persistent_node_allocations() - before;
            let logarithmic_height = usize::BITS as usize - size.leading_zeros() as usize;
            let allocation_bound = 64 * logarithmic_height + 64;
            assert!(
                allocations <= allocation_bound,
                "size {size} loan update allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(ancestor.storage.data.loans.len(), size);
            assert_eq!(successor.storage.data.loans.len(), size + 1);
        }
    }

    fn checked(fact: CResourceFact) -> CCheckedResourceFact {
        CCheckedResourceFact {
            fact,
            role: CResourceTransferRole::Borrow,
            snapshot: CResourceSnapshot::Entry,
            clause_position: None,
        }
    }

    fn memory(start: u32, end: u32, own: bool) -> CResourceFact {
        let range = crate::kernel::CMemoryRange::new(
            crate::kernel::Pointer {
                block: "buffer".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            },
            crate::kernel::Bitvector32Term::Constant(start),
            crate::kernel::Bitvector32Term::Constant(end),
        );
        if own {
            CResourceFact::own_memory(range)
        } else {
            CResourceFact::view_memory(range)
        }
    }

    fn symbolic_memory(start: Bitvector32Term, end: Bitvector32Term, own: bool) -> CResourceFact {
        let range = crate::kernel::CMemoryRange::new(
            crate::kernel::Pointer {
                block: "buffer".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            },
            start,
            end,
        );
        if own {
            CResourceFact::own_memory(range)
        } else {
            CResourceFact::view_memory(range)
        }
    }

    #[test]
    fn joint_planner_uses_one_escrow_for_overlapping_views_and_recovers_it() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 9, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[
                checked(memory(0, 6, false)),
                checked(memory(2, 8, false)),
                checked(memory(7, 9, false)),
            ],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        assert_eq!(plan.stable_views.len(), 3);
        assert_eq!(plan.stable_views[0].loan, plan.stable_views[1].loan);
        assert_eq!(plan.stable_views[0].share, plan.stable_views[1].share);
        assert!(
            !plan
                .caller_resources_after_requirements
                .satisfies_fact(&owner, &assumptions)
        );
        for planned in &plan.stable_views {
            assert!(plan.ledger.permits_view(
                callee,
                &planned.description,
                planned.share,
                &assumptions
            ));
        }
        let planned_ledger = plan.ledger.clone();
        let replayed = plan.replay_entry(&ledger).unwrap();
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
        assert_eq!(recovery.transitions.len(), 3);
        assert_eq!(recovery.ledger, ledger);
        assert_eq!(replayed, planned_ledger);
        assert!(recovery.replay_transitions(&planned_ledger).is_ok());
    }

    #[test]
    fn joint_planner_returns_disjoint_residual_ranges_and_exact_backing() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(2, 4, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let planned = &plan.stable_views[0];
        let (support, _) = caller_resources
            .directly_supporting_owned_entry(&owner, &assumptions)
            .unwrap();
        assert_eq!(planned.support, support);
        assert_eq!(planned.description.support(), support);
        assert!(
            plan.caller_resources_after_requirements
                .satisfies_fact(&memory(0, 2, true), &assumptions)
        );
        assert!(
            plan.caller_resources_after_requirements
                .satisfies_fact(&memory(4, 8, true), &assumptions)
        );
        assert!(
            !plan
                .caller_resources_after_requirements
                .satisfies_fact(&owner, &assumptions)
        );
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
        assert_eq!(recovery.ledger, ledger);
    }

    #[test]
    fn joint_planner_replays_two_disjoint_entry_loans_by_exact_state_chain() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 2, false)), checked(memory(6, 8, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        assert_eq!(plan.entry_transitions.len(), 2);
        assert_ne!(plan.stable_views[0].support, plan.stable_views[1].support);
        let planned_ledger = plan.ledger.clone();
        assert_eq!(plan.replay_entry(&ledger).unwrap(), planned_ledger);
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert_eq!(recovery.ledger, ledger);
        assert_eq!(recovery.transitions.len(), 6);
        assert!(recovery.replay_transitions(&planned_ledger).is_ok());
    }

    #[test]
    fn joint_planner_refuses_symbolic_partition_without_consuming_state() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let before = ledger.clone();
        let symbolic = symbolic_memory(
            Bitvector32Term::Variable(Variable(71_001)),
            Bitvector32Term::Constant(4),
            false,
        );
        assert_eq!(
            plan_stable_view_transfer(
                &caller_resources,
                &[checked(symbolic)],
                &assumptions,
                &ledger,
                caller,
                callee,
            ),
            Err(StableViewPlanError::UnsupportedPartition)
        );
        assert!(ledger.shares_storage_with(&before));
    }

    #[test]
    fn active_child_dependency_blocks_parent_close_until_child_ends() {
        let (ledger, owner, reader) = participants();
        let parent = lend_test(&ledger, owner, owner, owned("parent"));
        let ledger = ledger.apply(&parent.transition).unwrap();
        let child = lend_test(&ledger, owner, reader, owned("child"));
        let ledger = ledger.apply(&child.transition).unwrap();
        let dependency = ledger
            .register_dependency(parent.scope, child.scope, owner)
            .unwrap();
        let ledger = ledger.apply(&dependency).unwrap();
        assert_eq!(
            ledger.end(parent.scope, owner),
            Err(LoanRefusal::ActiveDependency)
        );
        let child_return = ledger.transfer(child.root_share, reader, owner).unwrap();
        let ledger = ledger.apply(&child_return).unwrap();
        let child_end = ledger.end(child.scope, owner).unwrap();
        let ledger = ledger.apply(&child_end).unwrap();
        assert!(ledger.end(parent.scope, owner).is_ok());
    }

    #[test]
    fn joint_planner_rejects_view_and_mutable_transfer_of_same_authority() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let requirements = [
            checked(memory(0, 4, false)),
            CCheckedResourceFact {
                fact: owner,
                role: CResourceTransferRole::Consume,
                snapshot: CResourceSnapshot::Entry,
                clause_position: None,
            },
        ];
        assert!(matches!(
            plan_stable_view_transfer(
                &caller_resources,
                &requirements,
                &assumptions,
                &ledger,
                caller,
                callee,
            ),
            Err(StableViewPlanError::ConflictingRequirement(_))
        ));
    }

    #[test]
    fn joint_planner_partitions_disjoint_write_and_view_ranges_in_any_clause_order() {
        let assumptions = PureFactContext::new();
        let caller_resources = ResourceContext::new().unchecked_with_fact(memory(0, 8, true));
        let (ledger, caller, callee) = participants();
        let write = CCheckedResourceFact {
            fact: memory(4, 8, true),
            role: CResourceTransferRole::Consume,
            snapshot: CResourceSnapshot::Entry,
            clause_position: None,
        };
        let read = checked(memory(0, 4, false));
        let left = plan_stable_view_transfer(
            &caller_resources,
            &[write.clone(), read.clone()],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let right = plan_stable_view_transfer(
            &caller_resources,
            &[read.clone(), write.clone()],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        for plan in [&left, &right] {
            assert!(
                plan.callee_resources
                    .satisfies_fact(&write.fact, &assumptions)
            );
            assert!(
                plan.callee_resources
                    .satisfies_fact(&read.fact, &assumptions)
            );
            assert_eq!(
                plan.memory_effects,
                vec![write.fact.memory_own_range().unwrap().clone()]
            );
            assert_eq!(plan.stable_views.len(), 1);
        }
        assert_eq!(left.callee_resources, right.callee_resources);
        assert_eq!(left.memory_effects, right.memory_effects);
    }

    #[test]
    fn rejected_joint_plan_leaves_caller_resources_and_ledger_unchanged() {
        let assumptions = PureFactContext::new();
        let owned = memory(0, 4, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owned.clone());
        let resources_before = caller_resources.clone();
        let (ledger, caller, callee) = participants();
        let ledger_before = ledger.clone();
        let missing = CResourceFact::own_token("missing".to_string(), Vec::new());
        let requirements = [
            checked(memory(0, 4, false)),
            CCheckedResourceFact {
                fact: missing.clone(),
                role: CResourceTransferRole::Consume,
                snapshot: CResourceSnapshot::Entry,
                clause_position: None,
            },
        ];
        assert_eq!(
            plan_stable_view_transfer(
                &caller_resources,
                &requirements,
                &assumptions,
                &ledger,
                caller,
                callee,
            ),
            Err(StableViewPlanError::MissingResource(missing))
        );
        assert_eq!(caller_resources, resources_before);
        assert!(ledger.shares_storage_with(&ledger_before));
        assert!(caller_resources.satisfies_fact(&owned, &assumptions));
    }

    #[test]
    fn joint_planner_refuses_an_independent_view_without_owned_support() {
        let assumptions = PureFactContext::new();
        let view = memory(0, 4, false);
        let caller_resources = ResourceContext::new().unchecked_with_fact(view.clone());
        let (ledger, caller, callee) = participants();
        assert_eq!(
            plan_stable_view_transfer(
                &caller_resources,
                &[checked(view.clone())],
                &assumptions,
                &ledger,
                caller,
                callee,
            ),
            Err(StableViewPlanError::MissingResource(view))
        );
    }
}
