//! Stable shared-loan authority for resource views.
//!
//! A [`LoanLedger`] is immutable. Every update returns opaque checked
//! evidence tied to the exact predecessor version. The ledger deliberately
//! contains no C call-stack policy: ordinary calls, named contracts, and
//! future language frontends must all use the same transitions.

use super::functions::CCheckedResourceFact;
use super::{
    CMemoryRange, CResource, CResourceFact, CResourceSnapshot, CResourceTransferRole,
    PureFactContext, ResourceContext, ResourceOccurrenceId,
};
use crate::persistent::PersistentMap;
use std::collections::BTreeMap;
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
    viewed: CResourceFact,
}

impl StableViewDescription {
    pub(crate) fn loan(&self) -> LoanId {
        self.loan
    }

    pub(crate) fn viewed(&self) -> &CResourceFact {
        &self.viewed
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanRecord {
    scope: LoanScopeId,
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
    next_participant: u64,
    next_scope: u64,
    next_loan: u64,
    next_share: u64,
    scopes: PersistentMap<LoanScopeId, LoanScopeRecord>,
    loans: PersistentMap<LoanId, LoanRecord>,
    shares: PersistentMap<LoanShareId, LoanShareRecord>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanLedgerStorage {
    version: u64,
    data: LoanLedgerData,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoanLedger {
    storage: Arc<LoanLedgerStorage>,
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
    IdentitySpaceExhausted,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LoanTransitionEvidence {
    Lend {
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
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
}

/// Kernel-issued evidence for one exact ledger transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CheckedLoanTransition {
    before_arena: u64,
    before_version: u64,
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
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    loan_roots: Vec<(LoanScopeId, LoanId, LoanShareId, ResourceOccurrenceId)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StableViewPlanError {
    InvalidRequirement,
    MissingResource(CResourceFact),
    ConflictingRequirement(CResourceFact),
    Loan(LoanRefusal),
    InvalidResidual,
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

    let mut loans_by_origin = BTreeMap::<ResourceOccurrenceId, usize>::new();
    let mut loan_roots = Vec::new();
    let mut planned_ledger = ledger.clone();
    for requirement in requirements
        .iter()
        .filter(|requirement| requirement.fact.is_view())
    {
        let Some((origin_support, _)) =
            caller_resources.directly_supporting_owned_entry(&requirement.fact, assumptions)
        else {
            return Err(StableViewPlanError::MissingResource(
                requirement.fact.clone(),
            ));
        };

        let root_index = if let Some(index) = loans_by_origin.get(&origin_support) {
            *index
        } else {
            let Some((support, owned)) =
                residual.directly_supporting_owned_entry(&requirement.fact, assumptions)
            else {
                return Err(StableViewPlanError::ConflictingRequirement(
                    requirement.fact.clone(),
                ));
            };
            let owned = owned.clone();
            let opening = planned_ledger.lend(caller, callee, owned.clone())?;
            planned_ledger = planned_ledger.apply(&opening.transition)?;
            residual = residual
                .without_exact_representation_for_occurrence(support)
                .ok_or_else(|| StableViewPlanError::MissingResource(owned.clone()))?;
            let index = loan_roots.len();
            loan_roots.push((opening.scope, opening.loan, opening.root_share, support));
            loans_by_origin.insert(origin_support, index);
            index
        };
        let (scope, loan, share, support) = loan_roots[root_index];
        let description = planned_ledger
            .describe_view(loan, requirement.fact.clone(), assumptions)
            .map_err(|_| StableViewPlanError::ConflictingRequirement(requirement.fact.clone()))?;
        callee_resources = callee_resources
            .try_compose_with_fact(requirement.fact.clone(), assumptions)
            .map_err(|_| StableViewPlanError::InvalidResidual)?;
        stable_views.push(PlannedStableView {
            requirement: requirement.clone(),
            support,
            loan,
            scope,
            share,
            description,
        });
    }

    Ok(StableViewTransferPlan {
        caller_resources_after_requirements: residual,
        callee_resources,
        transferred_ownership,
        stable_views,
        memory_effects,
        ledger: planned_ledger,
        caller,
        callee,
        loan_roots,
    })
}

impl StableViewTransferPlan {
    /// Closes every unmodified root share and returns the exact escrowed
    /// ownership to the residual caller context.
    pub(crate) fn recover_stable_views(
        self,
        assumptions: &PureFactContext,
    ) -> Result<(LoanLedger, ResourceContext), StableViewPlanError> {
        let mut ledger = self.ledger;
        let mut resources = self.caller_resources_after_requirements;
        for (scope, loan, root, _) in self.loan_roots.into_iter().rev() {
            let transfer = ledger.transfer(root, self.callee, self.caller)?;
            ledger = ledger.apply(&transfer)?;
            let end = ledger.end(scope, self.caller)?;
            ledger = ledger.apply(&end)?;
            let (recover, escrow) = ledger.recover(loan, self.caller)?;
            ledger = ledger.apply(&recover)?;
            resources = resources
                .try_compose_with_fact(escrow, assumptions)
                .map_err(|_| StableViewPlanError::InvalidResidual)?;
        }
        Ok((ledger, resources))
    }
}

impl LoanLedger {
    pub(crate) fn new() -> Self {
        static NEXT_ARENA: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let arena = NEXT_ARENA.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Self {
            storage: Arc::new(LoanLedgerStorage {
                version: 0,
                data: LoanLedgerData {
                    arena,
                    next_participant: 0,
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

    pub(crate) fn fresh_participant(&self) -> Result<(Self, LoanParticipantId), LoanRefusal> {
        let mut data = self.storage.data.clone();
        let participant = LoanParticipantId {
            arena: data.arena,
            ordinal: data.next_participant,
        };
        data.next_participant = data
            .next_participant
            .checked_add(1)
            .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
        Ok((self.with_data(data)?, participant))
    }

    pub(crate) fn lend(
        &self,
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        escrow: CResourceFact,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.require_participant(lender)?;
        self.require_participant(borrower)?;
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

    pub(crate) fn recover(
        &self,
        loan: LoanId,
        holder: LoanParticipantId,
    ) -> Result<(CheckedLoanTransition, CResourceFact), LoanRefusal> {
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
        Ok((
            self.issue(LoanTransitionEvidence::Recover { loan, holder })?,
            escrow,
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
        Ok(StableViewDescription { loan, viewed })
    }

    pub(crate) fn apply(&self, transition: &CheckedLoanTransition) -> Result<Self, LoanRefusal> {
        if self.storage.data.arena != transition.before_arena
            || self.storage.version != transition.before_version
        {
            return Err(LoanRefusal::StalePredecessor);
        }
        if transition.evidence != transition.checked_evidence {
            return Err(LoanRefusal::InvalidEvidence);
        }
        self.with_data(self.apply_evidence(&transition.evidence)?)
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
        Ok(CheckedLoanTransition {
            before_arena: self.storage.data.arena,
            before_version: self.storage.version,
            checked_evidence: evidence.clone(),
            evidence,
        })
    }

    fn with_data(&self, data: LoanLedgerData) -> Result<Self, LoanRefusal> {
        let version = self
            .storage
            .version
            .checked_add(1)
            .ok_or(LoanRefusal::IdentitySpaceExhausted)?;
        Ok(Self {
            storage: Arc::new(LoanLedgerStorage { version, data }),
        })
    }

    fn require_arena(&self, arena: u64) -> Result<(), LoanRefusal> {
        (arena == self.storage.data.arena)
            .then_some(())
            .ok_or(LoanRefusal::WrongArena)
    }

    fn require_participant(&self, participant: LoanParticipantId) -> Result<(), LoanRefusal> {
        (participant.arena == self.storage.data.arena
            && participant.ordinal < self.storage.data.next_participant)
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
                escrow,
                scope,
                loan,
                root,
            } => {
                if !escrow.is_own() {
                    return Err(LoanRefusal::NotOwnership);
                }
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
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
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
    use crate::kernel::{CResource, CResourceFact};

    fn owned(name: &str) -> CResourceFact {
        CResourceFact::own(CResource::Token {
            name: name.to_string(),
            arguments: Vec::new().into(),
        })
    }

    fn participants() -> (LoanLedger, LoanParticipantId, LoanParticipantId) {
        let ledger = LoanLedger::new();
        let (ledger, owner) = ledger.fresh_participant().unwrap();
        let (ledger, reader) = ledger.fresh_participant().unwrap();
        (ledger, owner, reader)
    }

    #[test]
    fn checked_two_reader_lifecycle_recovers_exact_escrow_once() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let escrow = owned("cell");
        let opening = ledger.lend(owner, owner, escrow.clone()).unwrap();
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
        let (recover, recovered) = ledger.recover(opening.loan, owner).unwrap();
        assert_eq!(recovered, escrow);
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
        let opening = ledger.lend(owner, reader, owned("cell")).unwrap();
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
    fn hostile_transition_payload_is_rechecked() {
        let (ledger, owner, reader) = participants();
        let mut opening = ledger.lend(owner, reader, owned("cell")).unwrap();
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
        let opening = ledger.lend(owner, reader, owned("cell")).unwrap();
        let advanced = ledger.apply(&opening.transition).unwrap();
        assert!(!ledger.shares_storage_with(&advanced));
        assert!(ledger.storage.data.loans.is_empty());
        assert_eq!(advanced.storage.data.loans.len(), 1);
    }

    #[test]
    fn nested_reborrow_must_rejoin_each_parent_before_scope_end() {
        let (ledger, owner, reader) = participants();
        let opening = ledger.lend(owner, owner, owned("cell")).unwrap();
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
        assert_eq!(
            first.lend(second_owner, second_reader, owned("cell")),
            Err(LoanRefusal::WrongArena)
        );
        let opening = first.lend(first_owner, first_owner, owned("cell")).unwrap();
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
            ledger.lend(owner, reader, composite),
            Err(LoanRefusal::UnsupportedResource)
        );
    }

    #[test]
    fn local_ledger_updates_allocate_logarithmically() {
        for size in [16_usize, 64, 256, 1024] {
            let (mut ledger, owner, reader) = participants();
            for index in 0..size {
                let opening = ledger
                    .lend(owner, reader, owned(&format!("cell_{index}")))
                    .unwrap();
                ledger = ledger.apply(&opening.transition).unwrap();
            }
            let ancestor = ledger.clone();
            assert!(ledger.shares_storage_with(&ancestor));
            let before = crate::persistent::persistent_node_allocations();
            let opening = ledger.lend(owner, reader, owned("target")).unwrap();
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

    #[test]
    fn joint_planner_uses_one_escrow_for_overlapping_views_and_recovers_it() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 6, false)), checked(memory(2, 8, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        assert_eq!(plan.stable_views.len(), 2);
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
        let (_ledger, recovered) = plan.recover_stable_views(&assumptions).unwrap();
        assert!(recovered.satisfies_fact(&owner, &assumptions));
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
