//! Stable shared-loan authority for resource views.
//!
//! A [`LoanLedger`] is immutable. Every update returns opaque checked
//! evidence tied to the exact predecessor state identity. The ledger deliberately
//! contains no C call-stack policy: ordinary calls, named contracts, and
//! future language frontends must all use the same transitions.

use super::functions::CCheckedResourceFact;
use super::primitives::{
    PointerBlock, ResourceMemoryIntervalNode, memory_interval_ancestors, memory_interval_nodes,
    memory_ranges_proven_overlapping,
};
use super::{
    Bitvector32Term, CMemoryRange, CResource, CResourceFact, CResourceSnapshot,
    CResourceTransferRole, PureFactContext, ResourceContext, ResourceOccurrenceId,
};
use crate::persistent::{PersistentMap, PersistentSet};
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

/// Exact binding from a resource occurrence to the live loan/share that
/// authorizes reading it. This is carried by checked state, never inferred by
/// searching the ambient ledger or resource frame.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoanViewBinding {
    pub(crate) loan: LoanId,
    pub(crate) scope: LoanScopeId,
    pub(crate) share: LoanShareId,
    pub(crate) support: ResourceOccurrenceId,
    pub(crate) viewed: CResourceFact,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LoanViewBindings {
    state: Arc<LoanViewBindingsState>,
}

#[derive(Debug, Default)]
pub(crate) struct LoanViewBindingsState {
    pub(crate) identity: u64,
    pub(crate) map: PersistentMap<ResourceOccurrenceId, LoanViewBinding>,
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

    pub(crate) fn with_inserted(
        &self,
        occurrence: ResourceOccurrenceId,
        binding: LoanViewBinding,
    ) -> Self {
        if self.state.map.get(&occurrence) == Some(&binding) {
            return self.clone();
        }
        Self {
            state: Arc::new(LoanViewBindingsState {
                identity: next_loan_binding_identity(),
                map: self.state.map.with_inserted(occurrence, binding),
            }),
        }
    }
}

fn update_active_memory_index(
    index: &PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    range: &CMemoryRange,
    loan: LoanId,
    insert: bool,
) -> Result<PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>, LoanRefusal> {
    let nodes = memory_interval_nodes(range).ok_or(LoanRefusal::UnsupportedPartition)?;
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
    range: &CMemoryRange,
    loan: LoanId,
    insert: bool,
) -> Result<PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>, LoanRefusal> {
    let nodes = memory_interval_nodes(range).ok_or(LoanRefusal::UnsupportedPartition)?;
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

fn symbolic_memory_ranges(ranges: &[CMemoryRange]) -> Vec<CMemoryRange> {
    ranges
        .iter()
        .filter(|range| memory_interval_nodes(range).is_none())
        .cloned()
        .collect()
}

fn with_unindexed_memory(
    map: &PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<CMemoryRange>>>,
    loan: LoanId,
    ranges: &[CMemoryRange],
) -> PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<CMemoryRange>>> {
    let mut map = map.clone();
    let mut by_block: BTreeMap<PointerBlock, Vec<CMemoryRange>> = BTreeMap::new();
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
    map: &PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<CMemoryRange>>>,
    loan: LoanId,
    ranges: &[CMemoryRange],
) -> PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<CMemoryRange>>> {
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
    query: &CMemoryRange,
    protected: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if query.base() == protected.base() {
        // One object at one base term: element offsets scaled to bytes are
        // enough, and the kernel's arithmetic decides them exactly.
        let byte_bounds = |range: &CMemoryRange| {
            let width = i64::from(range.element_width());
            Some((
                i64::from(range.start().as_const()?).checked_mul(width)?,
                i64::from(range.end().as_const()?).checked_mul(width)?,
            ))
        };
        if let (Some((query_start, query_end)), Some((protected_start, protected_end))) =
            (byte_bounds(query), byte_bounds(protected))
        {
            return query_start < protected_end && protected_start < query_end;
        }
    }
    let byte_range = |range: &CMemoryRange| {
        let (base, bytes) = range.byte_footprint();
        CMemoryRange::new_with_element_width(base, Bitvector32Term::Constant(0), bytes, 1)
    };
    let (query, protected) = (byte_range(query), byte_range(protected));
    // The kernel oracle relates the second base to the first syntactically,
    // so ask in both orders; overlap itself is symmetric.
    memory_ranges_proven_overlapping(&query, &protected, assumptions)
        || memory_ranges_proven_overlapping(&protected, &query, assumptions)
}

/// Whether an active loan protects memory: any byte-backed loan, and any
/// loan of a composite head, whose body is memory whether or not the
/// one-level frontier enumerated any of it. The fail-closed barriers
/// (unknown loop write sets, branch joins) consult this count.
fn loan_protects_memory(memory_backing: &[CMemoryRange], permitted: &[CResourceFact]) -> bool {
    !memory_backing.is_empty()
        || permitted
            .iter()
            .any(|fact| matches!(fact.resource(), CResource::Composite { .. }))
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
    loan: LoanId,
    root: LoanShareId,
    /// The participant allowed to end this scope. A borrowed contract input
    /// has no local close right: its lender lives outside the modular proof.
    close_right: Option<LoanParticipantId>,
    active: bool,
    parent: Option<LoanScopeId>,
    parent_share: Option<LoanShareId>,
    dependencies: crate::persistent::PersistentSet<LoanScopeId>,
}

fn origin_kind(origin: &LoanOrigin) -> LoanOriginKind {
    match origin {
        LoanOrigin::Escrowed(_) => LoanOriginKind::LentOwner,
        LoanOrigin::Reborrowed => LoanOriginKind::Reborrow,
        LoanOrigin::BorrowedContractInput => LoanOriginKind::ContractInputView,
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoanRecord {
    scope: LoanScopeId,
    support: ResourceOccurrenceId,
    escrow: Option<CResourceFact>,
    /// Every checked viewed projection authorized by this loan.  A composite
    /// loan keeps its folded head plus all primitive body views here so a
    /// child binding cannot be minted from the head alone.
    permitted: Vec<CResourceFact>,
    origin: LoanOrigin,
    recovered: bool,
    /// Primitive body pieces whose memory remains protected while a
    /// composite head is lent.  The head is retained as the restoration
    /// recipe, while this checked list supplies the actual write footprint.
    memory_backing: Vec<CMemoryRange>,
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
    next_scope: u64,
    next_loan: u64,
    next_share: u64,
    scopes: PersistentMap<LoanScopeId, LoanScopeRecord>,
    loans: PersistentMap<LoanId, LoanRecord>,
    shares: PersistentMap<LoanShareId, LoanShareRecord>,
    active_memory_index: PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    active_memory_subtree: PersistentMap<ResourceMemoryIntervalNode, PersistentSet<LoanId>>,
    active_memory_loans: usize,
    /// Protected ranges whose bounds are not concrete, keyed by the block
    /// they lie in. Contract input views over parameter memory live here: a
    /// parameter pointer has a symbolic offset in the shared external block,
    /// so the dyadic index cannot hold it. A write query consults only the
    /// entries in its own block, and the entries are bounded by the active
    /// loans with symbolic footprints, which a modular proof creates only
    /// from its contract's explicit view clauses and its own calls.
    unindexed_memory: PersistentMap<PointerBlock, PersistentMap<LoanId, Vec<CMemoryRange>>>,
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
/// clause, an owner lent for a call, or a nested reborrow of a live loan.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoanOriginKind {
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
    resource: Option<CResourceFact>,
    /// Boxed for the same reason as `conflicting`: a refusal that names a
    /// range and a fact must stay within the bounded payload size.
    range: Option<Box<CMemoryRange>>,
    /// The fact on the other side of a conflict: the resource a live loan
    /// protects for a refused access, or the owned entry that already
    /// supports a contract input view at entry. Boxed so that naming both
    /// sides keeps the diagnostic within its bounded payload size.
    conflicting: Option<Box<CResourceFact>>,
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
        attempted: CMemoryRange,
        protected: CResourceFact,
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

    /// A contract input view and the owned entry in the same contract that
    /// already supports it.
    pub(crate) fn for_supported_view(
        viewed: CResourceFact,
        owner: CResourceFact,
        support: ResourceOccurrenceId,
    ) -> Self {
        Self {
            resource: Some(viewed),
            conflicting: Some(Box::new(owner)),
            support: Some((support.arena(), support.ordinal())),
            ..Self::none()
        }
    }

    fn resource(resource: CResourceFact) -> Self {
        Self {
            resource: Some(resource),
            ..Self::none()
        }
    }

    pub(crate) fn for_resource(resource: CResourceFact) -> Self {
        Self::resource(resource)
    }

    #[allow(dead_code)]
    fn range(range: CMemoryRange) -> Self {
        Self {
            range: Some(Box::new(range)),
            ..Self::none()
        }
    }

    pub(crate) fn with_range(range: CMemoryRange) -> Self {
        Self::range(range)
    }

    #[cfg(test)]
    pub(crate) fn for_range(range: CMemoryRange) -> Self {
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

    pub fn resource_fact(&self) -> Option<&CResourceFact> {
        self.resource.as_ref()
    }

    pub fn memory_range(&self) -> Option<&CMemoryRange> {
        self.range.as_deref()
    }

    pub fn conflicting_resource_fact(&self) -> Option<&CResourceFact> {
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
    Lend {
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        escrow: CResourceFact,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    LendComposite {
        lender: LoanParticipantId,
        borrower: LoanParticipantId,
        support: ResourceOccurrenceId,
        support_fact: CResourceFact,
        escrow: CResourceFact,
        backing: Vec<CResourceFact>,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    BorrowedContractInput {
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        viewed: CResourceFact,
        backing: Vec<CResourceFact>,
        scope: LoanScopeId,
        loan: LoanId,
        root: LoanShareId,
    },
    Reborrow {
        parent: LoanViewBinding,
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

/// A definition-checked primitive frontier for one folded composite head.
/// Construction is intentionally restricted to the kernel's expansion
/// boundary; the ledger never accepts an untyped list of alleged backing
/// resources.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompositeLoanBacking {
    support: ResourceOccurrenceId,
    head: CResourceFact,
    pieces: Vec<CResourceFact>,
}

/// Definition-checked primitive footprint for an externally supplied folded
/// view. The surface initializer is the only producer; the transition stores
/// the checked pieces so later rechecks need no definition lookup. Recursive
/// children are deliberately excluded until the ledger has an opaque
/// capability that protects their complete footprint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BorrowedContractInputBacking {
    support: ResourceOccurrenceId,
    head: CResourceFact,
    pieces: Vec<CResourceFact>,
}

impl BorrowedContractInputBacking {
    pub(crate) fn from_checked_expansion(
        support: ResourceOccurrenceId,
        head: CResourceFact,
        pieces: Vec<CResourceFact>,
    ) -> Option<Self> {
        // A nested composite child is a read-only description under the
        // same loan with no byte backing of its own: the head's escrow, or
        // the contract's partition at a root, protects everything under it.
        // An exclusive instance cannot be viewed (D12).
        (head.is_view()
            && matches!(head.resource(), CResource::Composite { .. })
            && pieces.iter().all(|piece| {
                piece.is_view() && !matches!(piece.resource(), CResource::Instance(_))
            }))
        .then_some(Self {
            support,
            head,
            pieces,
        })
    }
}

impl CompositeLoanBacking {
    pub(crate) fn from_checked_expansion(
        support: ResourceOccurrenceId,
        head: CResourceFact,
        pieces: Vec<CResourceFact>,
    ) -> Option<Self> {
        // A nested composite child stays folded inside the escrowed head; it
        // enters the loan as a permitted description with no byte backing.
        // An exclusive instance cannot be viewed (D12).
        (head.is_own()
            && matches!(head.resource(), CResource::Composite { .. })
            && pieces
                .iter()
                .all(|piece| piece.is_own() && !matches!(piece.resource(), CResource::Instance(_))))
        .then_some(Self {
            support,
            head,
            pieces,
        })
    }
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
    callee_view_bindings: LoanViewBindings,
    parent_view_bindings: LoanViewBindings,
    parent_ledger: LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    loan_roots: Vec<(LoanScopeId, LoanId, LoanShareId, ResourceOccurrenceId, bool)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StableViewRecovery {
    pub(crate) ledger: LoanLedger,
    pub(crate) terminal_ledger: LoanLedger,
    pub(crate) resources: ResourceContext,
    pub(crate) view_bindings: LoanViewBindings,
    pub(crate) transitions: Vec<CheckedLoanTransition>,
}

impl StableViewRecovery {
    pub(crate) fn diagnostic_subject(&self) -> LoanRefusalSubject {
        self.transitions
            .last()
            .map(|transition| match &transition.evidence {
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
                | LoanTransitionEvidence::BorrowedContractInput {
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
}

impl Default for CheckedLoanCallEvidenceSummary {
    fn default() -> Self {
        Self {
            valid: true,
            recovered_by_caller: PersistentMap::default(),
            last_pristine_recovered: None,
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
        let recovered_by_caller = self
            .recovered_by_caller
            .with_inserted(key, evidence.recovered_ledger.clone());
        let last_pristine_recovered = if caller_ledger.is_pristine() {
            Some((caller_participant, evidence.recovered_ledger.clone()))
        } else {
            self.last_pristine_recovered.clone()
        };
        CheckedLoanCallEvidenceSummary {
            valid,
            recovered_by_caller,
            last_pristine_recovered,
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
    pub(crate) fn new(
        entry: StableViewTransferPlan,
        recovered_ledger: LoanLedger,
        recovery_terminal_ledger: LoanLedger,
        recovery_transitions: Vec<CheckedLoanTransition>,
    ) -> Self {
        Self {
            entry,
            recovered_ledger,
            recovery_terminal_ledger,
            recovery_transitions,
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
            crate::instrumentation::record_deterministic_work(1);
            recovery_successor = recovery_successor.apply(transition)?;
        }
        if recovery_successor != self.recovery_terminal_ledger {
            return Err(LoanRefusal::InvalidEvidence);
        }
        if self.recovered_ledger != *caller_ledger {
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
    ) -> Result<LoanLedger, LoanRefusal> {
        let mut current = predecessor.clone();
        for transition in &self.transitions {
            crate::instrumentation::record_deterministic_work(1);
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
    requirements: &[CCheckedResourceFact],
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
    requirements: &[CCheckedResourceFact],
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
    requirements: &[CCheckedResourceFact],
    assumptions: &PureFactContext,
    ledger: &LoanLedger,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
    parent_view_bindings: &LoanViewBindings,
    composite_backings: &BTreeMap<ResourceOccurrenceId, CompositeLoanBacking>,
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
    let mut callee_view_bindings = LoanViewBindings::default();
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
    let mut rebound = BTreeMap::<LoanViewBinding, Vec<(usize, CCheckedResourceFact)>>::new();
    // Owner occurrences that must back a view whose byte bounds are not
    // concrete.  The concrete sweep below cannot order such a range, so the
    // covering owner itself becomes the single lent backing for everything
    // grouped under it.  See `symbolic_covering_owner`.
    let mut symbolic_covering_owner = BTreeMap::<ResourceOccurrenceId, CResourceFact>::new();
    for (index, requirement) in requirements.iter().enumerate() {
        if !requirement.fact.is_view() {
            continue;
        }
        let view_occurrences =
            caller_resources.view_occurrences_for_fact(&requirement.fact, assumptions);
        let binding = view_occurrences
            .iter()
            .find_map(|occurrence| parent_view_bindings.get(occurrence).cloned());
        if binding.is_none()
            && !view_occurrences.is_empty()
            && caller_resources
                .directly_supporting_owned_entry(&requirement.fact, assumptions)
                .is_none()
        {
            // A view description with no live loan binding carries no
            // authority (law 4), so it can neither be reborrowed nor stand in
            // for backing that the caller does not hold.
            return Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding));
        }
        if let Some(binding) = binding {
            ledger.validate_view_binding(binding.clone(), caller)?;
            if !ResourceContext::new()
                .unchecked_with_fact(binding.viewed.clone())
                .satisfies_fact(&requirement.fact, assumptions)
            {
                return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
            }
            rebound
                .entry(binding)
                .or_default()
                .push((index, requirement.clone()));
            continue;
        }
        let Some((support, owned)) =
            caller_resources.directly_supporting_owned_entry(&requirement.fact, assumptions)
        else {
            return Err(StableViewPlanError::MissingResource(
                requirement.fact.clone(),
            ));
        };
        match owned.resource() {
            CResource::Instance(_) => {
                return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
            }
            CResource::Composite { .. } => {
                if caller_resources.owned_occurrences_for_fact(owned).len() != 1
                    || !composite_backings
                        .get(&support)
                        .is_some_and(|backing| backing.support == support && backing.head == *owned)
                {
                    return Err(StableViewPlanError::Loan(LoanRefusal::UnsupportedResource));
                }
            }
            CResource::Memory(_) | CResource::Token { .. } => {}
        }
        if requirement.fact.memory_range().is_some_and(|range| {
            range.start().as_const().is_none() || range.end().as_const().is_none()
        }) {
            // A symbolic view range is plannable exactly when one owned
            // occurrence already covers it: the entailment above is the
            // checked coverage witness, and the whole covering owner becomes
            // the loan backing.  Law 8 forbids inferring anything else here,
            // so no residual split and no separation from a sibling
            // requirement is assumed; every requirement grouped under this
            // owner shares the one loan.
            let CResource::Memory(_) = owned.resource() else {
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
            let opening = planned_ledger.lend(caller, callee, support, selected.clone())?;
            entry_transitions.push(opening.transition.clone());
            planned_ledger = planned_ledger.apply(&opening.transition)?;
            residual = residual
                .without_fact_incrementally(&selected, assumptions)
                .ok_or_else(|| StableViewPlanError::MissingResource(owned.clone()))?;
            loan_roots.push((
                opening.scope,
                opening.loan,
                opening.root_share,
                support,
                true,
            ));
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
                };
                let (next_resources, occurrence) = callee_resources
                    .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                    .map_err(|_| StableViewPlanError::InvalidResidual)?;
                let occurrence = occurrence
                    .or_else(|| owner_occurrences.get(&binding).copied())
                    .or_else(|| {
                        next_resources
                            .view_occurrences_for_fact(&requirement.fact, assumptions)
                            .into_iter()
                            .find(|occurrence| {
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
        let mut clusters: Vec<Vec<(usize, CCheckedResourceFact)>> = Vec::new();
        // Keep the union beside each memory cluster.  Recomputing it by
        // walking the whole cluster on every merge made a chain of
        // overlapping views quadratic in the number of clauses.
        let mut cluster_unions: Vec<Option<CMemoryRange>> = Vec::new();
        let mut memory_items = Vec::new();
        let mut non_memory_clusters = BTreeMap::<CResource, usize>::new();
        for item in group {
            if let CResource::Composite { .. } = item.1.fact.resource() {
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
                if !matches!(item.1.fact.resource(), CResource::Token { .. }) {
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
            if range.start().as_const().is_none() || range.end().as_const().is_none() {
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
                .then_with(|| left.start().as_const().cmp(&right.start().as_const()))
                .then_with(|| left.end().as_const().cmp(&right.end().as_const()))
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
                CResourceFact::own_memory(union)
            } else if cluster.first().is_some_and(|(_, item)| {
                matches!(item.fact.resource(), CResource::Composite { .. })
            }) {
                let required = cluster
                    .first()
                    .map(|(_, item)| &item.fact)
                    .ok_or(StableViewPlanError::UnsupportedPartition)?;
                let residual_for_selection = residual.clone();
                let (support, owned) = residual_for_selection
                    .directly_supporting_owned_entry(required, assumptions)
                    .ok_or_else(|| StableViewPlanError::ConflictingRequirement(required.clone()))?;
                if matches!(owned.resource(), CResource::Composite { .. })
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
            let opening = if let Some(backing) = composite_backings.get(&support) {
                let remaining = residual
                    .clone()
                    .without_fact_incrementally(&selected, assumptions)
                    .ok_or(StableViewPlanError::MissingResource(selected.clone()))?;
                let protected = remaining
                    .clone()
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
            entry_transitions.push(opening.transition.clone());
            planned_ledger = planned_ledger.apply(&opening.transition)?;
            residual = residual
                .without_fact_incrementally(&selected, assumptions)
                .ok_or_else(|| StableViewPlanError::MissingResource(owned.clone()))?;
            let root_index = loan_roots.len();
            loan_roots.push((
                opening.scope,
                opening.loan,
                opening.root_share,
                support,
                true,
            ));
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
                };
                let (next_resources, occurrence) = callee_resources
                    .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                    .map_err(|_| StableViewPlanError::InvalidResidual)?;
                let occurrence = occurrence
                    .or_else(|| owner_occurrences.get(&binding).copied())
                    .or_else(|| {
                        next_resources
                            .view_occurrences_for_fact(&requirement.fact, assumptions)
                            .into_iter()
                            .find(|occurrence| {
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
            let _ = root_index;
        }
    }
    for (binding, group) in rebound {
        let opening = planned_ledger.reborrow(binding.clone(), caller, callee)?;
        entry_transitions.push(opening.transition.clone());
        planned_ledger = planned_ledger.apply(&opening.transition)?;
        let child_binding = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: binding.support,
            viewed: binding.viewed.clone(),
        };
        loan_roots.push((
            opening.scope,
            opening.loan,
            opening.root_share,
            binding.support,
            false,
        ));
        let mut child_occurrence = None;
        for (index, requirement) in group {
            if !ResourceContext::new()
                .unchecked_with_fact(binding.viewed.clone())
                .satisfies_fact(&requirement.fact, assumptions)
            {
                return Err(StableViewPlanError::Loan(LoanRefusal::InvalidEvidence));
            }
            let (next_resources, occurrence) = callee_resources
                .try_compose_with_fact_with_occurrence(requirement.fact.clone(), assumptions)
                .map_err(|_| StableViewPlanError::InvalidResidual)?;
            let occurrence = occurrence
                .or(child_occurrence)
                .or_else(|| {
                    next_resources
                        .view_occurrences_for_fact(&requirement.fact, assumptions)
                        .into_iter()
                        .find(|occurrence| {
                            callee_view_bindings.get(occurrence) == Some(&child_binding)
                        })
                })
                .ok_or(StableViewPlanError::InvalidResidual)?;
            callee_resources =
                next_resources.with_loan_dependency(occurrence, child_binding.clone());
            child_occurrence = Some(occurrence);
            callee_view_bindings =
                callee_view_bindings.with_inserted(occurrence, child_binding.clone());
            let description = planned_ledger
                .describe_view(opening.loan, requirement.fact.clone(), assumptions)
                .map_err(|_| {
                    StableViewPlanError::ConflictingRequirement(requirement.fact.clone())
                })?;
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

    Ok(StableViewTransferPlan {
        caller_resources_after_requirements: residual,
        callee_resources,
        transferred_ownership,
        stable_views,
        memory_effects,
        ledger: planned_ledger,
        entry_transitions,
        callee_view_bindings,
        parent_view_bindings: parent_view_bindings.clone(),
        parent_ledger: ledger.clone(),
        caller,
        callee,
        loan_roots,
    })
}

impl StableViewTransferPlan {
    pub(crate) fn caller_ledger(&self) -> &LoanLedger {
        &self.parent_ledger
    }

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

    pub(crate) fn callee_view_bindings(&self) -> &LoanViewBindings {
        &self.callee_view_bindings
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
        for (scope, loan, root, _, recoverable) in loan_roots.into_iter().rev() {
            let transfer = ledger.transfer(root, self.callee, self.caller)?;
            ledger = ledger.apply(&transfer)?;
            transitions.push(transfer);
            let end = ledger.end(scope, self.caller)?;
            ledger = ledger.apply(&end)?;
            transitions.push(end);
            if recoverable {
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
        }
        // Every scope in loan_roots was created by this plan and has just
        // passed End and Recover. End checks its indexed dependency set, so a
        // registered child would have refused before this checkpoint. The
        // plan can therefore roll back directly to the exact predecessor
        // root without a whole-ledger quiescence scan.
        let terminal_ledger = ledger;
        ledger = parent_ledger;
        Ok(StableViewRecovery {
            ledger,
            terminal_ledger,
            resources,
            view_bindings: self.parent_view_bindings,
            transitions,
        })
    }

    pub(crate) fn recheck_entry(
        &self,
        predecessor: &LoanLedger,
    ) -> Result<LoanLedger, LoanRefusal> {
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

fn concrete_memory_union(left: &CMemoryRange, right: &CMemoryRange) -> Option<CMemoryRange> {
    // Every overlap decision is a named unit of planner work.  In
    // particular, the scaling gate must see candidate comparisons rather
    // than only the final number of clusters.
    crate::instrumentation::record_deterministic_work(1);
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
                    active_memory_index: PersistentMap::default(),
                    active_memory_subtree: PersistentMap::default(),
                    active_memory_loans: 0,
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

    /// Establish the shared authority supplied by a modular function
    /// contract. Unlike [`Self::lend`], this transition consumes no ownership
    /// and creates no recovery or close right: the unknown caller retains
    /// both outside the proof. The exact resource occurrence is the only
    /// supported anchor, so an equal-looking fact cannot reuse this root.
    pub(crate) fn borrowed_contract_input(
        &self,
        holder: LoanParticipantId,
        support: ResourceOccurrenceId,
        viewed: CResourceFact,
        backing: Option<BorrowedContractInputBacking>,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.require_participant(holder)?;
        if support == ResourceOccurrenceId::default() {
            return Err(LoanRefusal::MissingBacking);
        }
        if !viewed.is_view() {
            return Err(LoanRefusal::InvalidEvidence);
        }
        let backing = match (viewed.resource(), backing) {
            (CResource::Memory(_) | CResource::Token { .. }, None) => Vec::new(),
            (CResource::Composite { .. }, Some(backing))
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
        let evidence = LoanTransitionEvidence::BorrowedContractInput {
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
        escrow: CResourceFact,
        backing: CompositeLoanBacking,
    ) -> Result<LoanOpening, LoanRefusal> {
        self.require_participant(lender)?;
        self.require_participant(borrower)?;
        if support == ResourceOccurrenceId::default() {
            return Err(LoanRefusal::MissingBacking);
        }
        if !matches!(escrow.resource(), CResource::Composite { .. })
            || !escrow.is_own()
            || backing.support != support
            || backing.head != escrow
        {
            return Err(LoanRefusal::UnsupportedResource);
        }
        if backing
            .pieces
            .iter()
            .any(|fact| !fact.is_own() || matches!(fact.resource(), CResource::Instance(_)))
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

    /// Extend a loan's permitted descriptions by one checked child
    /// projection of a composite description it already permits.
    ///
    /// The child comes from the kernel's expansion of `parent` in the
    /// current state, performed by the checked `unfold`, `observe`, or
    /// `open` that calls this. A projection is derived, read-only authority
    /// over memory the loan already protects, so it is not a transition:
    /// the ledger keeps its state identity, which tracks authority-changing
    /// operations only, and a certificate that re-runs the same checked
    /// rewrites re-derives the same projections.
    pub(crate) fn project(
        &self,
        holder: LoanParticipantId,
        loan: LoanId,
        parent: &CResourceFact,
        child: CResourceFact,
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
        if !parent.is_view()
            || !matches!(parent.resource(), CResource::Composite { .. })
            || !record.permitted.iter().any(|permitted| {
                ResourceContext::new()
                    .unchecked_with_fact(permitted.clone())
                    .satisfies_fact(parent, &PureFactContext::default())
            })
        {
            return Err(LoanRefusal::MissingLoanBinding);
        }
        if !child.is_view() || matches!(child.resource(), CResource::Instance(_)) {
            return Err(LoanRefusal::UnsupportedResource);
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

    pub(crate) fn validate_view_binding(
        &self,
        binding: LoanViewBinding,
        holder: LoanParticipantId,
    ) -> Result<(), LoanRefusal> {
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
            || loan.support != binding.support
            || !scope.active
            || loan.recovered
            || share.scope != binding.scope
            || share.holder != Some(holder)
            || share.pinned_by.is_some()
            || !binding.viewed.is_view()
            || !loan.permitted.iter().any(|permitted| {
                ResourceContext::new()
                    .unchecked_with_fact(permitted.clone())
                    .satisfies_fact(&binding.viewed, &PureFactContext::default())
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
            parent: parent.clone(),
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
        let Some(scope) = self.storage.data.scopes.get(&loan.scope) else {
            return false;
        };
        let Some(share) = self.storage.data.shares.get(&share) else {
            return false;
        };
        scope.active
            && !loan.recovered
            && description.support == loan.support
            && share.scope == loan.scope
            && share.holder == Some(holder)
            && share.pinned_by.is_none()
            && description.viewed.is_view()
            && loan.permitted.iter().any(|permitted| {
                ResourceContext::new()
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
            || !record.permitted.iter().any(|permitted| {
                ResourceContext::new()
                    .unchecked_with_fact(permitted.clone())
                    .satisfies_fact(&viewed, assumptions)
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

    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.storage, &other.storage)
    }

    /// Return active memory loans whose concrete byte footprints overlap the
    /// query. The dyadic index visits logarithmically many buckets plus the
    /// returned loan IDs; it never scans the ledger.
    pub(crate) fn active_memory_overlaps(
        &self,
        range: &CMemoryRange,
    ) -> Result<Vec<LoanId>, LoanRefusal> {
        if let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const())
            && start >= end
        {
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

    /// Whether a write, free, or havoc of `range` is compatible with every
    /// active loan. Concrete ranges use the dyadic index. A symbolic query
    /// cannot be looked up there, so it is refused outright while any
    /// indexed loan is active; otherwise it is compared against the
    /// symbolic entries of its own block with
    /// [`protected_range_proven_overlapping`], whose polarity is documented
    /// there.
    pub(crate) fn permits_memory_access_with_assumptions(
        &self,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Result<(), LoanRefusal> {
        if let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const())
            && start >= end
        {
            return Ok(());
        }
        if memory_interval_nodes(range).is_some() {
            if !self.active_memory_overlaps(range)?.is_empty() {
                return Err(LoanRefusal::ActiveDependency);
            }
        } else if !self.storage.data.active_memory_index.is_empty() {
            return Err(LoanRefusal::UnsupportedPartition);
        }
        let Some(protected) = self.storage.data.unindexed_memory.get(&range.base().block) else {
            return Ok(());
        };
        for (_, ranges) in protected.iter() {
            for protected in ranges {
                crate::instrumentation::record_deterministic_work(1);
                if protected_range_proven_overlapping(range, protected, assumptions) {
                    return Err(LoanRefusal::ActiveDependency);
                }
            }
        }
        Ok(())
    }

    /// Explain a refused access in the D13 shape: the loan that refused it,
    /// where that loan came from, the range it protects, and the range the
    /// operation attempted. Only the refusal path pays for the explanation,
    /// and it revisits the same index buckets the check itself used, so a
    /// permitted access costs nothing and a refused one never walks the
    /// ledger.
    pub(crate) fn memory_access_refusal(
        &self,
        range: &CMemoryRange,
        assumptions: &PureFactContext,
        operation: LoanRefusalOperation,
    ) -> Option<LoanRefusalDiagnostic> {
        let refusal = self
            .permits_memory_access_with_assumptions(range, assumptions)
            .err()?;
        let subject = match self.conflicting_memory_loan(range, assumptions) {
            Some((loan, protected, origin)) => LoanRefusalSubject::for_memory_conflict(
                range.clone(),
                CResourceFact::view_memory(protected),
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
        range: &CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<(LoanId, CMemoryRange, LoanOriginKind)> {
        let described = |loan: LoanId, protected: &CMemoryRange| {
            let record = self.storage.data.loans.get(&loan)?;
            Some((loan, protected.clone(), origin_kind(&record.origin)))
        };
        if let Ok(loans) = self.active_memory_overlaps(range) {
            for loan in loans {
                let Some(record) = self.storage.data.loans.get(&loan) else {
                    continue;
                };
                let protected = record
                    .memory_backing
                    .iter()
                    .find(|protected| {
                        protected_range_proven_overlapping(range, protected, assumptions)
                    })
                    .or_else(|| record.memory_backing.first());
                if let Some(protected) = protected {
                    return described(loan, protected);
                }
            }
        }
        let block = self
            .storage
            .data
            .unindexed_memory
            .get(&range.base().block)?;
        for (loan, protected_ranges) in block.iter() {
            for protected in protected_ranges {
                if protected_range_proven_overlapping(range, protected, assumptions) {
                    return described(*loan, protected);
                }
            }
        }
        None
    }

    /// [`Self::permits_memory_access_with_assumptions`] without path
    /// assumptions, for callers such as branch joins and memory havoc that
    /// have none. Fewer assumptions prove fewer overlaps, so this is the
    /// more permissive form; the ordinary owned-authority check remains the
    /// primary guard on every write.
    pub(crate) fn permits_memory_access(&self, range: &CMemoryRange) -> Result<(), LoanRefusal> {
        self.permits_memory_access_with_assumptions(range, &PureFactContext::default())
    }

    /// Whether any active memory loan contributes a footprint to this ledger.
    ///
    /// Loop and branch havoc need a fail-closed answer when no checked write
    /// set is available.  Reading the maintained count keeps that barrier
    /// constant time and avoids turning the check into an ambient ledger scan.
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
                let memory_backing = match escrow.resource() {
                    CResource::Memory(range) => vec![range.clone()],
                    CResource::Token { .. } => Vec::new(),
                    CResource::Composite { .. } | CResource::Instance(_) => {
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
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        support: *support,
                        escrow: Some(escrow.clone()),
                        permitted: vec![CResourceFact::View(escrow.resource().clone())],
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
                for range in &memory_backing {
                    if memory_interval_nodes(range).is_none() {
                        continue;
                    }
                    data.active_memory_index =
                        update_active_memory_index(&data.active_memory_index, range, *loan, true)?;
                    data.active_memory_subtree = update_active_memory_subtree(
                        &data.active_memory_subtree,
                        range,
                        *loan,
                        true,
                    )?;
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
                scope,
                loan,
                root,
            } => {
                if !escrow.is_own()
                    || support_fact != escrow
                    || !matches!(escrow.resource(), CResource::Composite { .. })
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
                    .any(|fact| !fact.is_own() || matches!(fact.resource(), CResource::Instance(_)))
                {
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
                    .filter_map(CResourceFact::memory_own_range)
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
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        support: *support,
                        escrow: Some(escrow.clone()),
                        permitted: std::iter::once(CResourceFact::View(escrow.resource().clone()))
                            .chain(
                                backing
                                    .iter()
                                    .map(|fact| CResourceFact::View(fact.resource().clone())),
                            )
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
                for range in &memory_backing {
                    if memory_interval_nodes(range).is_none() {
                        continue;
                    }
                    data.active_memory_index =
                        update_active_memory_index(&data.active_memory_index, range, *loan, true)?;
                    data.active_memory_subtree = update_active_memory_subtree(
                        &data.active_memory_subtree,
                        range,
                        *loan,
                        true,
                    )?;
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
            LoanTransitionEvidence::BorrowedContractInput {
                holder,
                support,
                viewed,
                backing,
                scope,
                loan,
                root,
            } => {
                self.require_participant(*holder)?;
                if *support == ResourceOccurrenceId::default() {
                    return Err(LoanRefusal::MissingBacking);
                }
                let valid_backing = match viewed.resource() {
                    CResource::Memory(_) | CResource::Token { .. } => backing.is_empty(),
                    CResource::Composite { .. } => backing.iter().all(|piece| {
                        piece.is_view() && !matches!(piece.resource(), CResource::Instance(_))
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
                    .filter_map(CResourceFact::memory_range)
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
                        close_right: None,
                        active: true,
                        parent: None,
                        parent_share: None,
                        dependencies: crate::persistent::PersistentSet::default(),
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        support: *support,
                        escrow: None,
                        permitted,
                        origin: LoanOrigin::BorrowedContractInput,
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
                for range in &memory_backing {
                    if memory_interval_nodes(range).is_none() {
                        continue;
                    }
                    data.active_memory_index =
                        update_active_memory_index(&data.active_memory_index, range, *loan, true)?;
                    data.active_memory_subtree = update_active_memory_subtree(
                        &data.active_memory_subtree,
                        range,
                        *loan,
                        true,
                    )?;
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
                self.require_participant(*lender)?;
                self.require_participant(*borrower)?;
                let parent_loan = data
                    .loans
                    .get(&parent.loan)
                    .cloned()
                    .ok_or(LoanRefusal::MissingLoan)?;
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
                if parent_loan.scope != parent.scope
                    || parent_loan.support != parent.support
                    || !parent_scope.active
                    || parent_loan.recovered
                    || parent_share.scope != parent.scope
                    || parent_share.holder != Some(*lender)
                    || parent_share.pinned_by.is_some()
                    || !parent.viewed.is_view()
                    || !parent_loan.permitted.iter().any(|permitted| {
                        ResourceContext::new()
                            .unchecked_with_fact(permitted.clone())
                            .satisfies_fact(&parent.viewed, &PureFactContext::default())
                    })
                    || scope.arena != data.arena
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
                    },
                );
                data.loans = data.loans.with_inserted(
                    *loan,
                    LoanRecord {
                        scope: *scope,
                        support: parent.support,
                        escrow: None,
                        permitted: parent_loan.permitted.clone(),
                        origin: LoanOrigin::Reborrowed,
                        recovered: false,
                        memory_backing: parent_loan.memory_backing.clone(),
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
                for range in &parent_loan.memory_backing {
                    // A symbolic parent range stays protected by the parent
                    // entry, which remains active while its share is pinned.
                    if memory_interval_nodes(range).is_none() {
                        continue;
                    }
                    data.active_memory_index =
                        update_active_memory_index(&data.active_memory_index, range, *loan, true)?;
                    data.active_memory_subtree = update_active_memory_subtree(
                        &data.active_memory_subtree,
                        range,
                        *loan,
                        true,
                    )?;
                }
                // Counted by the same predicate `End` decrements with, so a
                // reborrow of a byte-less composite loan is conserved.
                if loan_protects_memory(&parent_loan.memory_backing, &parent_loan.permitted) {
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
                if let Some(record) = data.loans.get(&scope_record.loan).cloned() {
                    data.unindexed_memory = without_unindexed_memory(
                        &data.unindexed_memory,
                        scope_record.loan,
                        &symbolic_memory_ranges(&record.memory_backing),
                    );
                    for range in &record.memory_backing {
                        if memory_interval_nodes(range).is_none() {
                            continue;
                        }
                        data.active_memory_index = update_active_memory_index(
                            &data.active_memory_index,
                            range,
                            scope_record.loan,
                            false,
                        )?;
                        data.active_memory_subtree = update_active_memory_subtree(
                            &data.active_memory_subtree,
                            range,
                            scope_record.loan,
                            false,
                        )?;
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
    fn invariant_holds(&self) -> bool {
        let data = &self.storage.data;
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
            let origin_is_valid = match &loan.origin {
                LoanOrigin::Escrowed(recovery_right) => {
                    loan.escrow.as_ref().is_some_and(CResourceFact::is_own)
                        && scope.close_right == Some(*recovery_right)
                        && scope.parent.is_none()
                }
                LoanOrigin::Reborrowed => {
                    loan.escrow.is_none()
                        && scope.close_right.is_some()
                        && scope.parent.is_some()
                        && !loan.recovered
                }
                LoanOrigin::BorrowedContractInput => {
                    loan.escrow.is_none()
                        && scope.close_right.is_none()
                        && scope.parent.is_none()
                        && !loan.recovered
                        && loan.support != ResourceOccurrenceId::default()
                        && loan.permitted.iter().all(CResourceFact::is_view)
                }
            };
            if !origin_is_valid {
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
mod tests {
    use super::*;
    use crate::kernel::{CResource, CResourceFact, Variable};

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
    fn borrowed_contract_input_is_read_only_and_cannot_be_closed_or_recovered() {
        let (ledger, holder, _) = participants();
        let assumptions = PureFactContext::new();
        let viewed = memory(0, 4, false);
        let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
        let support = resources.occurrences_for_fact(&viewed)[0];
        let opening = ledger
            .borrowed_contract_input(holder, support, viewed.clone(), None)
            .expect("checked contract input");
        let ledger = ledger.apply(&opening.transition).expect("apply input root");

        assert!(ledger.invariant_holds());
        assert!(ledger.permits_view(
            holder,
            &opening.description,
            opening.root_share,
            &assumptions,
        ));
        assert_eq!(
            ledger.permits_memory_access(viewed.memory_range().unwrap()),
            Err(LoanRefusal::ActiveDependency)
        );
        assert_eq!(
            ledger.end(opening.scope, holder),
            Err(LoanRefusal::WrongHolder)
        );
        assert_eq!(
            ledger.recover(opening.loan, holder),
            Err(LoanRefusal::InvalidEvidence)
        );
    }

    fn parameter_range(variable: u64, start: u32, end: u32, width: u32) -> CMemoryRange {
        CMemoryRange::new_with_element_width(
            crate::kernel::Pointer {
                block: PointerBlock::ExternalArgument,
                offset: crate::kernel::PointerOffsetTerm::Variable(Variable(variable)),
            },
            Bitvector32Term::Constant(start),
            Bitvector32Term::Constant(end),
            width,
        )
    }

    fn rooted_parameter_view(
        variable: u64,
    ) -> (LoanLedger, LoanParticipantId, LoanOpening, CResourceFact) {
        let (ledger, holder, _) = participants();
        let viewed = CResourceFact::view_memory(parameter_range(variable, 0, 1, 4));
        let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
        let support = resources.occurrences_for_fact(&viewed)[0];
        let opening = ledger
            .borrowed_contract_input(holder, support, viewed.clone(), None)
            .expect("checked symbolic contract input");
        let ledger = ledger
            .apply(&opening.transition)
            .expect("apply symbolic root");
        (ledger, holder, opening, viewed)
    }

    /// A contract input over parameter memory has a symbolic base offset, so
    /// it cannot enter the concrete index; it is still a live loan that
    /// refuses writes proven to touch it and rejects closure and recovery.
    #[test]
    fn symbolic_borrowed_contract_input_is_live_outside_the_concrete_index() {
        let assumptions = PureFactContext::new();
        let (ledger, holder, opening, _) = rooted_parameter_view(41);
        assert!(ledger.invariant_holds());
        assert!(ledger.has_active_memory_loans());
        assert!(ledger.permits_view(
            holder,
            &opening.description,
            opening.root_share,
            &assumptions,
        ));
        // The viewed cell itself, at any element width that touches it.
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                &parameter_range(41, 0, 1, 4),
                &assumptions
            ),
            Err(LoanRefusal::ActiveDependency)
        );
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                &parameter_range(41, 3, 4, 1),
                &assumptions
            ),
            Err(LoanRefusal::ActiveDependency)
        );
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                &parameter_range(41, 0, 8, 1),
                &assumptions
            ),
            Err(LoanRefusal::ActiveDependency)
        );
        // A concretely disjoint offset of the same object.
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                &parameter_range(41, 1, 2, 4),
                &assumptions
            ),
            Ok(())
        );
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                &parameter_range(41, 4, 8, 1),
                &assumptions
            ),
            Ok(())
        );
        // Another parameter, separate by the contract partition unless the
        // path proves otherwise; and storage this activation declared.
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                &parameter_range(42, 0, 1, 4),
                &assumptions
            ),
            Ok(())
        );
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(
                memory(0, 1, true).memory_range().unwrap(),
                &assumptions
            ),
            Ok(())
        );
        assert_eq!(
            ledger.end(opening.scope, holder),
            Err(LoanRefusal::WrongHolder)
        );
        assert_eq!(
            ledger.recover(opening.loan, holder),
            Err(LoanRefusal::InvalidEvidence)
        );
    }

    /// A concrete query is refused while a symbolic loan on its block is
    /// live only when the overlap is proven; a symbolic query is refused
    /// outright while any concrete loan is indexed, because the index cannot
    /// answer it.
    #[test]
    fn symbolic_and_concrete_loans_fail_closed_across_the_index_boundary() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let concrete = lend_test(&ledger, owner, reader, memory(0, 4, true));
        let ledger = ledger.apply(&concrete.transition).unwrap();
        assert_eq!(
            ledger
                .permits_memory_access_with_assumptions(&parameter_range(7, 0, 1, 4), &assumptions),
            Err(LoanRefusal::UnsupportedPartition)
        );
        let ended = ledger
            .transfer(concrete.root_share, reader, owner)
            .and_then(|transfer| ledger.apply(&transfer))
            .and_then(|ledger| ledger.end(concrete.scope, owner).map(|end| (ledger, end)))
            .and_then(|(ledger, end)| ledger.apply(&end))
            .expect("close the concrete loan");
        assert!(ended.invariant_holds());
        assert_eq!(
            ended
                .permits_memory_access_with_assumptions(&parameter_range(7, 0, 1, 4), &assumptions),
            Ok(())
        );
    }

    /// Ending a child scope over a symbolic root leaves the root's
    /// protection in place, and the invariant tracks the symbolic entries.
    #[test]
    fn child_reborrow_of_a_symbolic_root_keeps_the_root_protected() {
        let (ledger, holder, _) = participants();
        let reader = ledger.fresh_participant().unwrap();
        let assumptions = PureFactContext::new();
        let viewed = CResourceFact::view_memory(parameter_range(9, 0, 1, 4));
        let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
        let support = resources.occurrences_for_fact(&viewed)[0];
        let opening = ledger
            .borrowed_contract_input(holder, support, viewed.clone(), None)
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let parent = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
        };
        let child = ledger.reborrow(parent, holder, reader).unwrap();
        let ledger = ledger.apply(&child.transition).unwrap();
        assert!(ledger.invariant_holds());
        assert_eq!(
            ledger
                .permits_memory_access_with_assumptions(&parameter_range(9, 0, 1, 4), &assumptions),
            Err(LoanRefusal::ActiveDependency)
        );
        let transfer = ledger.transfer(child.root_share, reader, holder).unwrap();
        let ledger = ledger.apply(&transfer).unwrap();
        let end = ledger.end(child.scope, holder).unwrap();
        let ledger = ledger.apply(&end).unwrap();
        assert!(ledger.invariant_holds());
        assert!(ledger.has_active_memory_loans());
        assert_eq!(
            ledger
                .permits_memory_access_with_assumptions(&parameter_range(9, 0, 1, 4), &assumptions),
            Err(LoanRefusal::ActiveDependency)
        );
    }

    /// Projection extends a composite loan's permitted descriptions by a
    /// checked child without changing the ledger's identity; it needs a
    /// permitted composite parent and a live scope, and never admits an
    /// exclusive instance.
    #[test]
    fn projection_extends_permitted_descriptions_without_a_transition() {
        let (ledger, owner, reader) = participants();
        let head = composite("cell", true);
        let support = backing(&head);
        let nested = composite("nested", true);
        let backing_pieces =
            CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![nested])
                .unwrap();
        let opening = ledger
            .lend_composite(owner, reader, support, head, backing_pieces)
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let assumptions = PureFactContext::new();
        let nested_view = composite("nested", false);
        let deep = CResourceFact::view_memory(memory(0, 1, true).memory_range().unwrap().clone());
        let describe = |viewed: CResourceFact| StableViewDescription {
            loan: opening.loan,
            support,
            viewed,
        };
        assert!(ledger.permits_view(
            reader,
            &describe(nested_view.clone()),
            opening.root_share,
            &assumptions
        ));
        assert!(!ledger.permits_view(
            reader,
            &describe(deep.clone()),
            opening.root_share,
            &assumptions
        ));
        let projected = ledger
            .project(reader, opening.loan, &nested_view, deep.clone())
            .expect("a child of a permitted composite view projects");
        assert_eq!(projected, ledger, "projection keeps the ledger identity");
        assert!(projected.permits_view(
            reader,
            &describe(deep.clone()),
            opening.root_share,
            &assumptions
        ));
        assert!(projected.invariant_holds());
        // Not a permitted parent, an owned child, and an ended scope.
        assert_eq!(
            projected.project(
                reader,
                opening.loan,
                &composite("other", false),
                deep.clone()
            ),
            Err(LoanRefusal::MissingLoanBinding)
        );
        assert_eq!(
            projected.project(reader, opening.loan, &nested_view, memory(0, 1, true)),
            Err(LoanRefusal::UnsupportedResource)
        );
        let transfer = projected
            .transfer(opening.root_share, reader, owner)
            .unwrap();
        let projected = projected.apply(&transfer).unwrap();
        let end = projected.end(opening.scope, owner).unwrap();
        let ended = projected.apply(&end).unwrap();
        assert_eq!(
            ended.project(owner, opening.loan, &nested_view, deep),
            Err(LoanRefusal::ScopeEnded)
        );
    }

    /// A reborrow of a byte-less composite loan is counted and uncounted by
    /// the same predicate, so ending the child leaves the parent's
    /// contribution to the fail-closed barrier in place (F2 in fix-views).
    #[test]
    fn ending_a_reborrow_of_a_byteless_composite_loan_keeps_the_barrier_armed() {
        let (ledger, owner, reader) = participants();
        let head = CResourceFact::own(CResource::Composite {
            name: "box".to_string(),
            arguments: Vec::new().into(),
        });
        let piece = owned("box_token");
        let support = backing(&head);
        let backing =
            CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece])
                .expect("a token-only frontier is a checked expansion");
        let opening = ledger
            .lend_composite(owner, reader, support, head.clone(), backing)
            .expect("composite lend");
        let ledger = ledger.apply(&opening.transition).unwrap();
        assert!(ledger.has_active_memory_loans());
        assert!(ledger.invariant_holds());
        let parent = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: CResourceFact::view_composite("box".to_string(), Vec::new()),
        };
        let child = ledger.reborrow(parent, reader, owner).unwrap();
        let ledger = ledger.apply(&child.transition).unwrap();
        assert!(ledger.has_active_memory_loans());
        assert!(ledger.invariant_holds());
        let transfer = ledger.transfer(child.root_share, owner, reader).unwrap();
        let ledger = ledger.apply(&transfer).unwrap();
        let end = ledger.end(child.scope, reader).unwrap();
        let ledger = ledger.apply(&end).unwrap();
        assert!(
            ledger.has_active_memory_loans(),
            "the parent composite loan is still live"
        );
        assert!(ledger.invariant_holds());
        let transfer = ledger.transfer(opening.root_share, reader, owner).unwrap();
        let ledger = ledger.apply(&transfer).unwrap();
        let end = ledger.end(opening.scope, owner).unwrap();
        let ledger = ledger.apply(&end).unwrap();
        assert!(!ledger.has_active_memory_loans());
        assert!(ledger.invariant_holds());
    }

    /// A composite loan is a memory loan whether or not its one-level
    /// frontier enumerated any bytes: the head is memory.
    #[test]
    fn composite_lend_counts_as_a_memory_loan_without_byte_backing() {
        let (ledger, owner, reader) = participants();
        let head = CResourceFact::own(CResource::Composite {
            name: "box".to_string(),
            arguments: Vec::new().into(),
        });
        let piece = owned("box_token");
        let support = backing(&head);
        let backing =
            CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece])
                .expect("a token-only frontier is a checked expansion");
        let opening = ledger
            .lend_composite(owner, reader, support, head, backing)
            .expect("composite lend");
        let ledger = ledger.apply(&opening.transition).unwrap();
        assert!(ledger.has_active_memory_loans());
        assert!(ledger.invariant_holds());
        let transfer = ledger.transfer(opening.root_share, reader, owner).unwrap();
        let ledger = ledger.apply(&transfer).unwrap();
        let end = ledger.end(opening.scope, owner).unwrap();
        let ledger = ledger.apply(&end).unwrap();
        assert!(!ledger.has_active_memory_loans());
        assert!(ledger.invariant_holds());
    }

    #[test]
    fn nested_reborrow_restores_a_borrowed_contract_input_root() {
        let (ledger, holder, reader) = participants();
        let assumptions = PureFactContext::new();
        let viewed = memory(0, 4, false);
        let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
        let support = resources.occurrences_for_fact(&viewed)[0];
        let opening = ledger
            .borrowed_contract_input(holder, support, viewed.clone(), None)
            .expect("checked contract input");
        let ledger = ledger.apply(&opening.transition).expect("apply input root");
        let parent = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
        };
        let child = ledger
            .reborrow(parent, holder, reader)
            .expect("checked child reborrow");
        let ledger = ledger.apply(&child.transition).expect("apply child");
        assert!(!ledger.permits_view(
            holder,
            &opening.description,
            opening.root_share,
            &assumptions,
        ));
        let transfer = ledger
            .transfer(child.root_share, reader, holder)
            .expect("return child share");
        let ledger = ledger.apply(&transfer).expect("apply return");
        let end = ledger
            .end(child.scope, holder)
            .expect("close child scope only");
        let ledger = ledger.apply(&end).expect("apply child close");

        assert!(ledger.invariant_holds());
        assert!(ledger.permits_view(
            holder,
            &opening.description,
            opening.root_share,
            &assumptions,
        ));
        assert_eq!(
            ledger.recover(child.loan, holder),
            Err(LoanRefusal::InvalidEvidence)
        );
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
        let lifetime = ledger
            .end(opening.scope, owner)
            .expect_err("an ended scope cannot be ended again");
        assert_eq!(
            lifetime
                .diagnostic(LoanRefusalOperation::Transition)
                .category(),
            LoanRefusalCategory::Lifetime
        );
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
        let duplicate = ledger
            .recover(opening.loan, owner)
            .expect_err("a loan cannot be recovered twice");
        assert_eq!(
            duplicate
                .diagnostic(LoanRefusalOperation::Recovery)
                .category(),
            LoanRefusalCategory::Recovery
        );
    }

    #[test]
    fn transitions_are_bound_to_their_exact_predecessor() {
        let (ledger, owner, reader) = participants();
        let opening = lend_test(&ledger, owner, reader, owned("cell"));
        let advanced = ledger.apply(&opening.transition).unwrap();
        let stale = advanced
            .apply(&opening.transition)
            .expect_err("a transition cannot be applied twice");
        assert_eq!(
            stale
                .diagnostic(LoanRefusalOperation::Transition)
                .category(),
            LoanRefusalCategory::StalePredecessor
        );
        let unrelated = LoanLedger::new();
        let stale = unrelated
            .apply(&opening.transition)
            .expect_err("a transition cannot cross ledger histories");
        assert_eq!(
            stale
                .diagnostic(LoanRefusalOperation::Transition)
                .category(),
            LoanRefusalCategory::StalePredecessor
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
        let invalid = ledger
            .apply(&opening.transition)
            .expect_err("tampered participant evidence must be refused");
        assert_eq!(
            invalid
                .diagnostic(LoanRefusalOperation::Transition)
                .category(),
            LoanRefusalCategory::InvalidEvidence
        );
    }

    #[test]
    fn checked_call_evidence_rejects_stale_or_swapped_recovery() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 4, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 2, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let planned_ledger = plan.ledger.clone();
        let recovery = plan.clone().recover_stable_views(&assumptions).unwrap();
        let recovery_subject = recovery.diagnostic_subject();
        assert!(
            recovery_subject.loan_id().is_some()
                || recovery_subject.scope_id().is_some()
                || recovery_subject.share_id().is_some()
                || recovery_subject.support_id().is_some()
        );
        let evidence = CheckedLoanCallEvidence::new(
            plan,
            recovery.ledger.clone(),
            recovery.terminal_ledger.clone(),
            recovery.transitions.clone(),
        );
        assert!(
            evidence
                .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
                .is_ok()
        );

        let mut stale = evidence.clone();
        stale.recovery_transitions.reverse();
        let stale_error = stale
            .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
            .expect_err("reordered recovery must be refused");
        assert_eq!(
            stale_error
                .diagnostic(LoanRefusalOperation::Recovery)
                .category(),
            LoanRefusalCategory::StalePredecessor
        );

        let mut truncated = evidence.clone();
        truncated.recovery_transitions.pop();
        let truncated_error = truncated
            .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
            .expect_err("truncated recovery must be refused");
        assert_eq!(
            truncated_error
                .diagnostic(LoanRefusalOperation::Recovery)
                .category(),
            LoanRefusalCategory::Recovery
        );

        let unrelated = LoanLedger::new();
        let unrelated_error = evidence
            .recheck(&unrelated, Some(caller), &planned_ledger, Some(callee))
            .expect_err("a cross-call predecessor must be refused");
        assert_eq!(
            unrelated_error
                .diagnostic(LoanRefusalOperation::Recovery)
                .category(),
            LoanRefusalCategory::StalePredecessor
        );
    }

    #[test]
    fn checked_evidence_sequence_scales_with_shared_immutable_history() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 4, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 2, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let recovery = plan.clone().recover_stable_views(&assumptions).unwrap();
        let evidence = Arc::new(CheckedLoanCallEvidence::new(
            plan,
            recovery.ledger,
            recovery.terminal_ledger,
            recovery.transitions,
        ));
        let mut sequence = empty_checked_loan_evidence_sequence();
        let mut midpoint = None;
        for index in 0..2048 {
            let previous = sequence.clone();
            sequence = append_checked_loan_evidence(&sequence, Some(evidence.clone()));
            let CheckedLoanCallEvidenceSequenceNode::Append { prefix, .. } = &*sequence.node else {
                panic!("append must create a persistent node");
            };
            assert!(Arc::ptr_eq(prefix, &previous.node));
            if index == 1023 {
                midpoint = Some(sequence.clone());
            }
        }
        let midpoint = midpoint.unwrap();
        let suffix = sequence.suffix_since(&midpoint).unwrap();
        assert_eq!(suffix.len(), 1024);
        assert_eq!(concat_checked_loan_evidence(&midpoint, &suffix), sequence);
        let separately_built_equal_prefix = midpoint
            .to_vec()
            .into_iter()
            .fold(empty_checked_loan_evidence_sequence(), |rebuilt, item| {
                append_checked_loan_evidence(&rebuilt, Some(item))
            });
        assert_eq!(separately_built_equal_prefix, midpoint);
        assert!(
            sequence
                .suffix_since(&separately_built_equal_prefix)
                .is_none()
        );
        assert_eq!(sequence.len(), 2048);
        assert_eq!(sequence, sequence.clone());
        assert_eq!(sequence.to_vec().len(), 2048);

        let alternate_plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(1, 3, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let alternate_recovery = alternate_plan
            .clone()
            .recover_stable_views(&assumptions)
            .unwrap();
        let alternate_evidence = Arc::new(CheckedLoanCallEvidence::new(
            alternate_plan,
            alternate_recovery.ledger,
            alternate_recovery.terminal_ledger,
            alternate_recovery.transitions,
        ));
        let mut separately_built_different = empty_checked_loan_evidence_sequence();
        for _ in 0..2048 {
            separately_built_different = append_checked_loan_evidence(
                &separately_built_different,
                Some(alternate_evidence.clone()),
            );
        }
        assert_ne!(separately_built_different, sequence);
    }

    #[test]
    fn completed_call_history_does_not_slow_outer_ledger_lookup() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 4, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 2, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let recovery = plan.clone().recover_stable_views(&assumptions).unwrap();
        let evidence = Arc::new(CheckedLoanCallEvidence::new(
            plan,
            recovery.ledger,
            recovery.terminal_ledger,
            recovery.transitions,
        ));
        let mut samples = Vec::new();
        for size in [16_usize, 32, 64, 128] {
            let mut sequence = empty_checked_loan_evidence_sequence();
            for _ in 0..size {
                sequence = append_checked_loan_evidence(&sequence, Some(evidence.clone()));
            }
            let ((valid, recovered), work) = crate::persistent::measure_persistent_work(|| {
                (
                    sequence.is_valid(),
                    sequence.recovered_ledger_for(&ledger, caller, false),
                )
            });
            assert!(valid);
            assert_eq!(recovered, Some(ledger.clone()));
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
                "outer ledger lookup grew with completed history: {samples:?}"
            );
        }
    }

    #[test]
    fn checked_evidence_sequence_seals_each_appended_call_locally() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 4, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 2, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let recovery = plan.clone().recover_stable_views(&assumptions).unwrap();
        let mut tampered = CheckedLoanCallEvidence::new(
            plan,
            recovery.ledger,
            recovery.terminal_ledger,
            recovery.transitions,
        );
        tampered.recovery_transitions.reverse();
        let sequence = append_checked_loan_evidence(
            &empty_checked_loan_evidence_sequence(),
            Some(Arc::new(tampered)),
        );
        assert!(!sequence.is_valid());
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
    fn reborrow_rejects_a_borrower_from_another_ledger_arena() {
        let (ledger, owner, _) = participants();
        let (_foreign_ledger, _, foreign_reader) = participants();
        let escrow = memory(0, 4, true);
        let opening = ledger.lend(owner, owner, backing(&escrow), escrow).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let parent = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: opening.description.support(),
            viewed: memory(0, 4, false),
        };
        assert_eq!(
            ledger.reborrow(parent, owner, foreign_reader),
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
        for size in [16_usize, 32, 64, 128] {
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

    #[test]
    fn deep_split_read_join_work_scales_with_explicit_tree_delta() {
        let mut samples = Vec::new();
        for depth in [16_usize, 32, 64, 128] {
            let (base, owner, _reader) = participants();
            let escrow = owned("deep-tree");
            let opening = base.lend(owner, owner, backing(&escrow), escrow).unwrap();
            let mut ledger = base.apply(&opening.transition).unwrap();
            let (((), work), persistent_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut current = opening.root_share;
                    let mut parents = Vec::with_capacity(depth);
                    let mut siblings = Vec::with_capacity(depth);
                    for _ in 0..depth {
                        let (split, left, right) =
                            ledger.split(current, owner, owner, owner).unwrap();
                        ledger = ledger.apply(&split).unwrap();
                        parents.push(current);
                        siblings.push(right);
                        current = left;
                    }
                    assert!(ledger.permits_view(
                        owner,
                        &opening.description,
                        current,
                        &PureFactContext::new()
                    ));
                    for (parent, sibling) in parents.into_iter().zip(siblings).rev() {
                        let join = ledger.join(current, sibling, owner).unwrap();
                        ledger = ledger.apply(&join).unwrap();
                        current = parent;
                    }
                    assert_eq!(current, opening.root_share);
                    assert!(ledger.invariant_holds());
                })
            });
            samples.push((depth, work, persistent_work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3)
                    && pair[1].2 <= pair[0].2.saturating_mul(3),
                "deep split/read/join work exceeded the explicit tree delta: {samples:?}"
            );
        }
    }

    #[test]
    fn dependency_updates_scale_with_changed_scope_entries() {
        let mut samples = Vec::new();
        for size in [16_usize, 32, 64, 128] {
            let (mut ledger, owner, _reader) = participants();
            let parent_fact = owned("dependency-parent");
            let parent = ledger
                .lend(owner, owner, backing(&parent_fact), parent_fact)
                .unwrap();
            ledger = ledger.apply(&parent.transition).unwrap();
            let mut children = Vec::with_capacity(size);
            for index in 0..size {
                let child_fact = owned(&format!("dependency-child-{index}"));
                let child = ledger
                    .lend(owner, owner, backing(&child_fact), child_fact)
                    .unwrap();
                ledger = ledger.apply(&child.transition).unwrap();
                children.push(child);
            }
            let (((), work), persistent_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for child in &children {
                        let transition = ledger
                            .register_dependency(parent.scope, child.scope, owner)
                            .unwrap();
                        ledger = ledger.apply(&transition).unwrap();
                    }
                })
            });
            samples.push((size, work, persistent_work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3)
                    && pair[1].2 <= pair[0].2.saturating_mul(3),
                "dependency updates visited unrelated scope entries: {samples:?}"
            );
        }
    }

    #[test]
    fn disjoint_memory_view_clustering_has_linear_overlap_work() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16_usize, 32, 64, 128] {
            let ledger = LoanLedger::new();
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let caller_resources =
                ResourceContext::new().unchecked_with_fact(memory(0, (size * 2 + 1) as u32, true));
            let requirements = (0..size)
                .map(|index| checked(memory((index * 2) as u32, (index * 2 + 1) as u32, false)))
                .collect::<Vec<_>>();
            let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
                plan_stable_view_transfer(
                    &caller_resources,
                    &requirements,
                    &assumptions,
                    &ledger,
                    caller,
                    callee,
                )
            });
            let plan = plan.expect("disjoint concrete views should form independent loans");
            assert_eq!(plan.stable_views().len(), size);
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "disjoint view clustering compared unrelated candidates: {samples:?}"
            );
        }
    }

    #[test]
    fn overlapping_memory_view_clustering_handles_chains_and_equal_starts() {
        let assumptions = PureFactContext::new();
        let mut chain_samples = Vec::new();
        let mut equal_start_samples = Vec::new();
        for size in [16_usize, 32, 64, 128] {
            let ledger = LoanLedger::new();
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let mut caller_resources = ResourceContext::new();
            let mut chain_requirements = Vec::with_capacity(size * 3);
            let mut equal_requirements = Vec::with_capacity(size * 3);
            for index in 0..size {
                let base = crate::kernel::Pointer {
                    block: crate::kernel::PointerBlock::Concrete(format!("overlap-{index}")),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                };
                let owner = CResourceFact::own_memory(CMemoryRange::new(
                    base.clone(),
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(6),
                ));
                caller_resources = caller_resources.unchecked_with_fact(owner);
                let view = |start, end| {
                    checked(CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(end),
                    )))
                };
                // Three clauses form a transitive overlap chain. Keeping the
                // chain bounded avoids making resource validity itself the
                // measured axis while the number of independent chains grows.
                chain_requirements.extend([view(0, 3), view(2, 5), view(4, 6)]);
                equal_requirements.extend([view(0, 2), view(0, 2), view(0, 2)]);
            }
            let (chain, chain_work) = crate::instrumentation::measure_deterministic_work(|| {
                plan_stable_view_transfer(
                    &caller_resources,
                    &chain_requirements,
                    &assumptions,
                    &ledger,
                    caller,
                    callee,
                )
            });
            let chain = chain.expect("overlapping chains should share backing loans");
            assert_eq!(chain.stable_views().len(), size * 3);
            chain_samples.push((size, chain_work));

            let (equal_start, equal_start_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    plan_stable_view_transfer(
                        &caller_resources,
                        &equal_requirements,
                        &assumptions,
                        &ledger,
                        caller,
                        callee,
                    )
                });
            let equal_start = equal_start.expect("equal-start views should share backing loans");
            assert_eq!(equal_start.stable_views().len(), size * 3);
            equal_start_samples.push((size, equal_start_work));
        }
        for samples in [&chain_samples, &equal_start_samples] {
            for pair in samples.windows(2) {
                assert!(
                    pair[1].1 <= pair[0].1.saturating_mul(3),
                    "overlap clustering work exceeded its explicit view delta: {samples:?}"
                );
            }
        }
    }

    #[test]
    fn loan_certificate_recheck_scales_with_explicit_transition_delta() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16_usize, 32, 64, 128] {
            let ledger = LoanLedger::new();
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let caller_resources =
                ResourceContext::new().unchecked_with_fact(memory(0, (size * 2 + 1) as u32, true));
            let requirements = (0..size)
                .map(|index| checked(memory((index * 2) as u32, (index * 2 + 1) as u32, false)))
                .collect::<Vec<_>>();
            let plan = plan_stable_view_transfer(
                &caller_resources,
                &requirements,
                &assumptions,
                &ledger,
                caller,
                callee,
            )
            .unwrap();
            let planned_ledger = plan.ledger.clone();
            let recovery = plan.clone().recover_stable_views(&assumptions).unwrap();
            let evidence = CheckedLoanCallEvidence::new(
                plan,
                recovery.ledger,
                recovery.terminal_ledger,
                recovery.transitions,
            );
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                evidence
                    .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
                    .unwrap();
            });
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "certificate recheck work exceeded its explicit transition delta: {samples:?}"
            );
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

    fn composite(name: &str, own: bool) -> CResourceFact {
        let resource = CResource::Composite {
            name: name.to_string(),
            arguments: Vec::new().into(),
        };
        if own {
            CResourceFact::own(resource)
        } else {
            CResourceFact::View(resource)
        }
    }

    #[test]
    fn composite_loan_protects_primitive_frontier_and_restores_head_once() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let head = composite("cell", true);
        let piece = memory(0, 4, true);
        let context = ResourceContext::new().unchecked_with_fact(head.clone());
        let support = context.unique_owned_occurrence_for_fact(&head).unwrap().0;
        let opening = ledger
            .lend_composite(
                owner,
                reader,
                support,
                head.clone(),
                CompositeLoanBacking::from_checked_expansion(
                    support,
                    head.clone(),
                    vec![piece.clone()],
                )
                .unwrap(),
            )
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let child = ledger
            .describe_view(
                opening.loan,
                CResourceFact::view_memory(piece.memory_range().unwrap().clone()),
                &assumptions,
            )
            .unwrap();
        assert!(ledger.permits_view(reader, &child, opening.root_share, &assumptions));
        assert_eq!(
            ledger.permits_memory_access(piece.memory_range().unwrap()),
            Err(LoanRefusal::ActiveDependency)
        );
        let end = ledger.end(opening.scope, owner);
        assert_eq!(end, Err(LoanRefusal::ShareStillSplit));
        let transfer = ledger.transfer(opening.root_share, reader, owner).unwrap();
        let ledger = ledger.apply(&transfer).unwrap();
        let end = ledger
            .apply(&ledger.end(opening.scope, owner).unwrap())
            .unwrap();
        assert!(
            end.permits_memory_access(piece.memory_range().unwrap())
                .is_ok()
        );
        let (recover, recovered, recovered_support) = end.recover(opening.loan, owner).unwrap();
        assert_eq!(recovered, head);
        assert_eq!(recovered_support, support);
        let end = end.apply(&recover).unwrap();
        assert_eq!(
            end.recover(opening.loan, owner),
            Err(LoanRefusal::AlreadyRecovered)
        );
    }

    #[test]
    fn composite_planner_rejects_hidden_overlap_and_equal_head_ambiguity() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let head = composite("cell", true);
        let view = composite("cell", false);
        let piece = memory(0, 4, true);
        let overlapping = memory(2, 6, true);
        let context = ResourceContext::new().unchecked_with_facts([head.clone(), overlapping]);
        let support = context.unique_owned_occurrence_for_fact(&head).unwrap().0;
        let backing = CompositeLoanBacking::from_checked_expansion(
            support,
            head.clone(),
            vec![piece.clone()],
        )
        .unwrap();
        let mut backings = BTreeMap::new();
        backings.insert(support, backing);
        let overlap = plan_stable_view_transfer_with_bindings_and_composites(
            &context,
            &[checked(view.clone())],
            &assumptions,
            &ledger,
            owner,
            reader,
            &LoanViewBindings::default(),
            &backings,
        )
        .expect_err("a hidden overlapping resource must be refused");
        assert_eq!(
            overlap
                .loan_diagnostic(LoanRefusalOperation::Plan)
                .expect("planner refusal diagnostic")
                .category(),
            LoanRefusalCategory::ProvenOverlap
        );
        let duplicate = ResourceContext::new().unchecked_with_facts([head.clone(), head]);
        let duplicate_support = duplicate
            .occurrences_for_fact(&composite("cell", true))
            .first()
            .copied()
            .unwrap();
        let mut duplicate_backings = BTreeMap::new();
        duplicate_backings.insert(
            duplicate_support,
            CompositeLoanBacking::from_checked_expansion(
                duplicate_support,
                composite("cell", true),
                vec![piece],
            )
            .unwrap(),
        );
        let duplicate_error = plan_stable_view_transfer_with_bindings_and_composites(
            &duplicate,
            &[checked(view)],
            &assumptions,
            &ledger,
            owner,
            reader,
            &LoanViewBindings::default(),
            &duplicate_backings,
        )
        .expect_err("duplicate support must be refused");
        assert_eq!(
            duplicate_error
                .loan_diagnostic(LoanRefusalOperation::Plan)
                .expect("planner refusal diagnostic")
                .category(),
            LoanRefusalCategory::Unsupported
        );
    }

    #[test]
    fn composite_planner_escrows_one_head_and_recovers_it_once() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let head = composite("cell", true);
        let view = composite("cell", false);
        let piece = memory(0, 4, true);
        let caller = ResourceContext::new().unchecked_with_fact(head.clone());
        let support = caller.unique_owned_occurrence_for_fact(&head).unwrap().0;
        let backing =
            CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece])
                .unwrap();
        let mut backings = BTreeMap::new();
        backings.insert(support, backing);
        let plan = plan_stable_view_transfer_with_bindings_and_composites(
            &caller,
            &[checked(view)],
            &assumptions,
            &ledger,
            owner,
            reader,
            &LoanViewBindings::default(),
            &backings,
        )
        .unwrap();
        assert!(
            !plan
                .caller_resources_after_requirements
                .satisfies_fact(&head, &assumptions)
        );
        assert_eq!(plan.stable_views.len(), 1);
        assert!(
            plan.ledger
                .permits_memory_access(&memory(0, 4, false).memory_range().unwrap().clone())
                .is_err()
        );
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert!(recovery.resources.satisfies_fact(&head, &assumptions));
        assert!(
            recovery
                .ledger
                .permits_memory_access(&memory(0, 4, false).memory_range().unwrap().clone())
                .is_ok()
        );
    }

    #[test]
    fn composite_planner_keeps_other_counted_token_units_usable() {
        let (ledger, owner, reader) = participants();
        let assumptions = PureFactContext::new();
        let token = CResource::Token {
            name: "unit".into(),
            arguments: Vec::new().into(),
        };
        let owned_units = CResourceFact::own_quantity(token.clone(), Bitvector32Term::Constant(3));
        let view = CResourceFact::View(token);
        let caller = ResourceContext::new().unchecked_with_fact(owned_units.clone());
        let plan = plan_stable_view_transfer(
            &caller,
            &[checked(view)],
            &assumptions,
            &ledger,
            owner,
            reader,
        )
        .unwrap();
        assert!(plan.caller_resources_after_requirements.satisfies_fact(
            &CResourceFact::own_quantity(
                CResource::Token {
                    name: "unit".into(),
                    arguments: Vec::new().into(),
                },
                Bitvector32Term::Constant(2),
            ),
            &assumptions,
        ));
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert!(
            recovery
                .resources
                .satisfies_fact(&owned_units, &assumptions)
        );
    }

    #[test]
    fn composite_backing_tamper_and_instance_frontier_are_refused() {
        let (ledger, owner, reader) = participants();
        let head = composite("cell", true);
        let support = backing(&head);
        // A nested composite child is admitted as a permitted description;
        // a viewed piece is not a checked expansion of an owned head.
        let nested = composite("nested", true);
        assert!(
            CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![nested])
                .is_some()
        );
        assert!(
            CompositeLoanBacking::from_checked_expansion(
                support,
                head.clone(),
                vec![composite("nested", false)]
            )
            .is_none()
        );
        let tampered = CompositeLoanBacking {
            support,
            head,
            pieces: vec![CResourceFact::View(CResource::Token {
                name: "tampered".into(),
                arguments: Vec::new().into(),
            })],
        };
        let unsupported = ledger
            .lend_composite(owner, reader, support, tampered.head.clone(), tampered)
            .expect_err("tampered composite backing must be refused");
        assert_eq!(
            unsupported
                .diagnostic(LoanRefusalOperation::Transition)
                .category(),
            LoanRefusalCategory::Unsupported
        );
        let mut opening = ledger
            .lend_composite(
                owner,
                reader,
                support,
                composite("cell", true),
                CompositeLoanBacking::from_checked_expansion(
                    support,
                    composite("cell", true),
                    Vec::new(),
                )
                .unwrap(),
            )
            .unwrap();
        let LoanTransitionEvidence::LendComposite { support_fact, .. } =
            &mut opening.transition.evidence
        else {
            panic!("composite lend evidence")
        };
        *support_fact = CResourceFact::own_token("other".into(), Vec::new());
        let invalid = ledger
            .apply(&opening.transition)
            .expect_err("tampered occurrence evidence must be refused");
        assert_eq!(
            invalid
                .diagnostic(LoanRefusalOperation::Transition)
                .category(),
            LoanRefusalCategory::InvalidEvidence
        );
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
        let rechecked = plan.recheck_entry(&ledger).unwrap();
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
        assert_eq!(recovery.transitions.len(), 3);
        assert_eq!(recovery.ledger, ledger);
        assert_eq!(rechecked, planned_ledger);
        assert!(recovery.recheck_transitions(&planned_ledger).is_ok());
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
    fn joint_planner_rechecks_two_disjoint_entry_loans_by_exact_state_chain() {
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
        assert_eq!(plan.recheck_entry(&ledger).unwrap(), planned_ledger);
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert_eq!(recovery.ledger, ledger);
        assert_eq!(recovery.transitions.len(), 6);
        assert!(recovery.recheck_transitions(&planned_ledger).is_ok());
    }

    #[test]
    fn joint_planner_refuses_an_uncovered_symbolic_view_without_consuming_state() {
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
        // Nothing bounds the symbolic start, so the concrete owner does not
        // entail the requested range and there is no backing to select.
        assert_eq!(
            plan_stable_view_transfer(
                &caller_resources,
                &[checked(symbolic.clone())],
                &assumptions,
                &ledger,
                caller,
                callee,
            ),
            Err(StableViewPlanError::MissingResource(symbolic))
        );
        assert!(ledger.shares_storage_with(&before));
    }

    #[test]
    fn joint_planner_backs_a_covered_symbolic_view_with_its_whole_owner() {
        let assumptions = PureFactContext::new();
        let end = Bitvector32Term::Variable(Variable(71_002));
        let owner = symbolic_memory(Bitvector32Term::Constant(0), end.clone(), true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let view = symbolic_memory(Bitvector32Term::Constant(0), end, false);
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(view.clone())],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .expect("a covering owner backs a symbolic view range");
        assert_eq!(plan.stable_views.len(), 1);
        assert_eq!(plan.stable_views[0].requirement.fact, view);
        // The whole covering owner is escrowed: the algebra cannot split a
        // symbolic range, so no writable remainder may be left behind.
        assert!(
            plan.caller_resources_after_requirements
                .facts()
                .iter()
                .all(|fact| *fact != owner)
        );
        assert!(plan.callee_resources.satisfies_fact(&view, &assumptions));
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert_eq!(recovery.ledger, ledger);
        assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
    }

    #[test]
    fn joint_planner_shares_one_loan_between_two_covered_symbolic_views() {
        let assumptions = PureFactContext::new();
        let end = Bitvector32Term::Variable(Variable(71_003));
        let owner = symbolic_memory(Bitvector32Term::Constant(0), end.clone(), true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let first = symbolic_memory(Bitvector32Term::Constant(0), end.clone(), false);
        let second = symbolic_memory(Bitvector32Term::Constant(0), end, false);
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(first), checked(second)],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .expect("two covered symbolic views share the covering owner");
        // Law 8: unknown aliasing between the two requested ranges may not be
        // resolved into two escrows of the same bytes.
        assert_eq!(plan.entry_transitions.len(), 1);
        assert_eq!(plan.stable_views.len(), 2);
        assert_eq!(plan.stable_views[0].loan, plan.stable_views[1].loan);
    }

    /// Every view the plan composes into the callee context carries its loan
    /// binding on the occurrence itself, not only in the plan's sidecar. The
    /// sidecar alone left the fact indistinguishable from an unbound view, so
    /// normalization was free to merge it with a neighbour and the
    /// per-requirement occurrence lookup then failed with `InvalidResidual`.
    #[test]
    fn joint_planner_binds_every_composed_callee_view_occurrence() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 5, true);
        let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
        let (ledger, caller, callee) = participants();
        let first = memory(0, 1, false);
        let second = memory(3, 4, false);
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(first.clone()), checked(second.clone())],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .expect("two views plan from one owner");
        assert_eq!(plan.stable_views.len(), 2);
        let bound = plan
            .callee_resources
            .live_loan_dependencies()
            .map(|(occurrence, binding)| (occurrence, binding.viewed.clone()))
            .collect::<Vec<_>>();
        assert_eq!(bound.len(), 2);
        assert_ne!(bound[0].0, bound[1].0);
        assert!(bound.iter().any(|(_, viewed)| *viewed == first));
        assert!(bound.iter().any(|(_, viewed)| *viewed == second));
    }

    #[test]
    fn joint_planner_refuses_an_unbound_view_the_caller_does_not_own() {
        let assumptions = PureFactContext::new();
        let caller_resources = ResourceContext::new().unchecked_with_fact(memory(0, 8, false));
        let (ledger, caller, callee) = participants();
        // A view description with no loan binding is not authority, and no
        // owner covers the requirement either.
        assert_eq!(
            plan_stable_view_transfer(
                &caller_resources,
                &[checked(memory(0, 4, false))],
                &assumptions,
                &ledger,
                caller,
                callee,
            ),
            Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))
        );
    }

    #[test]
    fn joint_planner_lends_from_the_owner_beside_an_unbound_view_description() {
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let caller_resources = ResourceContext::new()
            .unchecked_with_fact(owner)
            .unchecked_with_fact(memory(0, 8, false));
        let (ledger, caller, callee) = participants();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 4, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .expect("the owner backs the view that the stale description cannot");
        assert_eq!(plan.stable_views.len(), 1);
        assert_eq!(plan.entry_transitions.len(), 1);
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
        // Whole-context equality is not the right comparison here: each plan
        // binds its composed view occurrences, and an occurrence identity is
        // freshly allocated per plan by construction (law 5). Compare what
        // clause order must not change: the facts, and the viewed fact each
        // live binding carries.
        assert_eq!(
            left.callee_resources.facts(),
            right.callee_resources.facts()
        );
        let bound = |plan: &StableViewTransferPlan| {
            plan.callee_resources
                .live_loan_dependencies()
                .map(|(_, binding)| binding.viewed.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(bound(&left), vec![read.fact.clone()]);
        assert_eq!(bound(&left), bound(&right));
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
            Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))
        );
    }

    #[test]
    fn nested_view_reborrow_pins_parent_and_restores_exact_binding() {
        let assumptions = PureFactContext::new();
        let owned_range = memory(0, 8, true);
        let support = backing(&owned_range);
        let parent_view = memory(0, 8, false);
        let child_view = memory(2, 4, false);
        let (ledger, owner, reader) = participants();
        let opening = ledger
            .lend(owner, owner, support, owned_range.clone())
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let parent_binding = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: parent_view.clone(),
        };
        let parent_resources = ResourceContext::new().unchecked_with_fact(parent_view.clone());
        let (occurrence, _) = parent_resources
            .view_occurrences_for_fact(&parent_view, &assumptions)
            .into_iter()
            .map(|occurrence| (occurrence, ()))
            .next()
            .expect("parent view occurrence");
        let parent_bindings = LoanViewBindings::default().with_inserted(occurrence, parent_binding);
        let plan = plan_stable_view_transfer_with_bindings(
            &parent_resources,
            &[checked(child_view.clone())],
            &assumptions,
            &ledger,
            owner,
            reader,
            &parent_bindings,
        )
        .unwrap();
        assert_eq!(plan.stable_views.len(), 1);
        assert_ne!(plan.stable_views[0].loan, opening.loan);
        assert!(!plan.ledger.permits_view(
            owner,
            &opening.description,
            opening.root_share,
            &assumptions
        ));
        let recovery = plan.recover_stable_views(&assumptions).unwrap();
        assert_eq!(recovery.ledger, ledger);
        assert_eq!(recovery.view_bindings, parent_bindings);
        assert!(
            recovery
                .resources
                .satisfies_fact(&parent_view, &assumptions)
        );
    }

    #[test]
    fn nested_view_reborrow_rejects_wider_child_than_bound_parent() {
        let assumptions = PureFactContext::new();
        let owned_range = memory(0, 8, true);
        let parent_view = memory(2, 4, false);
        let wider_view = memory(0, 8, false);
        let (ledger, owner, reader) = participants();
        let opening = lend_test(&ledger, owner, owner, owned_range);
        let ledger = ledger.apply(&opening.transition).unwrap();
        let parent_resources = ResourceContext::new().unchecked_with_fact(wider_view.clone());
        let occurrence = parent_resources
            .view_occurrences_for_fact(&wider_view, &assumptions)
            .into_iter()
            .next()
            .expect("wider view occurrence");
        let binding = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: opening.description.support(),
            viewed: parent_view,
        };
        let bindings = LoanViewBindings::default().with_inserted(occurrence, binding);
        let invalid = plan_stable_view_transfer_with_bindings(
            &parent_resources,
            &[checked(wider_view)],
            &assumptions,
            &ledger,
            owner,
            reader,
            &bindings,
        )
        .expect_err("a wider range than the bound view must be refused");
        assert_eq!(
            invalid
                .loan_diagnostic(LoanRefusalOperation::Plan)
                .expect("planner refusal diagnostic")
                .category(),
            LoanRefusalCategory::InvalidEvidence
        );
    }

    #[test]
    fn active_memory_index_returns_only_overlapping_live_loans() {
        let owned_range = memory(0, 8, true);
        let (ledger, owner, reader) = participants();
        let opening = ledger
            .lend(owner, reader, backing(&owned_range), owned_range)
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        assert_eq!(
            ledger
                .active_memory_overlaps(memory(2, 4, false).memory_range().unwrap())
                .unwrap(),
            vec![opening.loan]
        );
        assert!(
            ledger
                .active_memory_overlaps(memory(8, 10, false).memory_range().unwrap())
                .unwrap()
                .is_empty()
        );
        assert!(
            ledger
                .permits_memory_access(memory(8, 10, false).memory_range().unwrap())
                .is_ok()
        );
        assert!(
            ledger
                .permits_memory_access(memory(8, 8, false).memory_range().unwrap())
                .is_ok()
        );
        let blocked = ledger
            .permits_memory_access(memory(2, 4, false).memory_range().unwrap())
            .expect_err("a live loan must block overlapping memory access");
        assert_eq!(
            blocked
                .diagnostic(LoanRefusalOperation::MemoryAccess)
                .category(),
            LoanRefusalCategory::ActiveDependency
        );
        let returned = ledger.transfer(opening.root_share, reader, owner).unwrap();
        let ledger = ledger.apply(&returned).unwrap();
        let ended = ledger.end(opening.scope, owner).unwrap();
        let ledger = ledger.apply(&ended).unwrap();
        assert!(
            ledger
                .active_memory_overlaps(memory(2, 4, false).memory_range().unwrap())
                .unwrap()
                .is_empty()
        );
        assert!(
            ledger
                .permits_memory_access(memory(2, 4, false).memory_range().unwrap())
                .is_ok()
        );
        let _ = ledger.recover(opening.loan, owner).unwrap();
    }

    #[test]
    fn active_memory_candidates_ignore_unrelated_live_loans() {
        let mut samples = Vec::new();
        for size in [16_usize, 32, 64, 128] {
            let (mut ledger, owner, reader) = participants();
            for index in 0..size {
                let owned_range = memory((index * 2) as u32, (index * 2 + 1) as u32, true);
                let opening = ledger
                    .lend(owner, reader, backing(&owned_range), owned_range)
                    .unwrap();
                ledger = ledger.apply(&opening.transition).unwrap();
            }
            let query = memory(0, 1, false).memory_range().unwrap().clone();
            let (loans, work) = crate::instrumentation::measure_deterministic_work(|| {
                ledger.active_memory_overlaps(&query).unwrap()
            });
            assert_eq!(loans.len(), 1);
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
                "active interval candidates scanned unrelated live loans: {samples:?}"
            );
        }
    }

    #[test]
    fn ending_nested_memory_loan_keeps_parent_footprint_indexed() {
        let owned_range = memory(0, 8, true);
        let (ledger, owner, reader) = participants();
        let parent = ledger
            .lend(owner, owner, backing(&owned_range), owned_range.clone())
            .unwrap();
        let ledger = ledger.apply(&parent.transition).unwrap();
        let parent_binding = LoanViewBinding {
            loan: parent.loan,
            scope: parent.scope,
            share: parent.root_share,
            support: parent.description.support(),
            viewed: memory(0, 8, false),
        };
        let child = ledger.reborrow(parent_binding, owner, reader).unwrap();
        let ledger = ledger.apply(&child.transition).unwrap();
        let overlapping_fact = memory(1, 2, false);
        let overlapping = overlapping_fact.memory_range().unwrap();
        let active = ledger.active_memory_overlaps(overlapping).unwrap();
        assert!(active.contains(&parent.loan));
        assert!(active.contains(&child.loan));

        let child_return = ledger.transfer(child.root_share, reader, owner).unwrap();
        let ledger = ledger.apply(&child_return).unwrap();
        let child_end = ledger.end(child.scope, owner).unwrap();
        let ledger = ledger.apply(&child_end).unwrap();
        assert_eq!(
            ledger.active_memory_overlaps(overlapping).unwrap(),
            vec![parent.loan]
        );
        let blocked = ledger
            .permits_memory_access(overlapping)
            .expect_err("the parent loan must remain indexed");
        assert_eq!(
            blocked
                .diagnostic(LoanRefusalOperation::MemoryAccess)
                .category(),
            LoanRefusalCategory::ActiveDependency
        );

        let parent_end = ledger.end(parent.scope, owner).unwrap();
        let ledger = ledger.apply(&parent_end).unwrap();
        assert!(
            ledger
                .active_memory_overlaps(overlapping)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn refusal_diagnostics_preserve_overlap_and_boundary_categories() {
        let active = LoanRefusal::ActiveDependency.diagnostic(LoanRefusalOperation::MemoryAccess);
        assert_eq!(active.category(), LoanRefusalCategory::ActiveDependency);
        assert_eq!(active.overlap(), LoanOverlapStatus::ProvenOverlap);

        let unsupported = LoanRefusal::UnsupportedPartition.diagnostic(LoanRefusalOperation::Plan);
        assert_eq!(
            unsupported.category(),
            LoanRefusalCategory::SeparationUnproved
        );
        assert_eq!(unsupported.overlap(), LoanOverlapStatus::SeparationUnproved);

        let wrong_holder = LoanRefusal::WrongHolder.diagnostic(LoanRefusalOperation::Recovery);
        assert_eq!(wrong_holder.category(), LoanRefusalCategory::WrongHolder);
        let wrong_scope = LoanRefusal::WrongScope.diagnostic(LoanRefusalOperation::Transition);
        assert_eq!(wrong_scope.category(), LoanRefusalCategory::WrongScope);
        let stale = LoanRefusal::StalePredecessor.diagnostic(LoanRefusalOperation::Recovery);
        assert_eq!(stale.category(), LoanRefusalCategory::StalePredecessor);
        let recovery = LoanRefusal::AlreadyRecovered.diagnostic(LoanRefusalOperation::Recovery);
        assert_eq!(recovery.category(), LoanRefusalCategory::Recovery);
        let lifetime = LoanRefusal::ScopeEnded.diagnostic(LoanRefusalOperation::Transition);
        assert_eq!(lifetime.category(), LoanRefusalCategory::Lifetime);
        let arena = LoanRefusal::WrongArena.diagnostic(LoanRefusalOperation::Transition);
        assert_eq!(arena.category(), LoanRefusalCategory::WrongArena);
    }

    #[test]
    fn refusal_diagnostic_is_a_small_bounded_payload() {
        assert!(std::mem::size_of::<LoanRefusalDiagnostic>() <= 512);
        let subject = LoanRefusalSubject::resource(memory(0, 4, true));
        let diagnostic = LoanRefusal::ActiveDependency
            .diagnostic_with_subject(LoanRefusalOperation::Plan, subject);
        assert!(diagnostic.subject().resource_fact().is_some());
    }
}
