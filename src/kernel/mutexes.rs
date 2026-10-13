//! Checked ownership exchange for one modeled mutex invariant.
//!
//! A mutex may escrow a folded exclusive resource or protect no Click
//! resource. Acquiring creates a unique guard and, when present, moves that
//! fact into the current C state. The guard is an exclusive resource atom in
//! that same context. Releasing consumes the atom and requires the folded
//! invariant back; ledger heldness alone cannot authorize release.
//!
//! The C binding still has to validate the declaration, pointer, status,
//! and initialization before a pthread call can use these transitions.

mod assumed_protocol;
pub(super) mod helper_contracts;
pub(super) use assumed_protocol::{
    OpaqueMutexAcquisitions, opaque_runtime_transition_with_payload,
};
mod direct_loop_guard;
#[cfg(test)]
mod direct_loop_guard_tests;
mod invariant_interface;
mod loop_protocol;
pub(super) use direct_loop_guard::{
    normalize_direct_loop_guards, prepare_direct_loop_guard, select_direct_loop_guards,
};
pub(super) use loop_protocol::abstract_loop_mutex;

use std::cmp::Ordering as CmpOrdering;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(test)]
use super::loans::MutexUseLoan;
use super::loans::{LoanHoldId, LoanLedger, LoanParticipantId, MutexUseBinding};
use crate::persistent::PersistentMap;

use super::{CResource, CResourceFact, CState, ConditionTerm, Pointer, PureFactContext};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MutexTransitionError {
    NotInitialized,
    MissingGuard(Pointer),
    MissingLive(Pointer),
    MissingUse(Pointer),
    MissingInvariant(CResourceFact),
    /// The selected state is owned but is not the protected type.
    MismatchedInvariant {
        required: CResourceFact,
        supplied: CResourceFact,
    },
    Refusal(&'static str),
    OwnedRefusal(String),
}

impl From<&'static str> for MutexTransitionError {
    fn from(message: &'static str) -> Self {
        Self::Refusal(message)
    }
}

impl MutexTransitionError {
    pub(super) fn into_runtime_error(self, mutex: &Pointer) -> super::CRuntimeError {
        match self {
            Self::NotInitialized => super::CRuntimeError::UninitializedMutex {
                mutex: mutex.clone(),
            },
            Self::MissingLive(mutex) => super::CRuntimeError::MissingMutexLive { mutex },
            Self::MissingUse(mutex) => super::CRuntimeError::MissingMutexUse { mutex },
            Self::MissingGuard(mutex) => super::CRuntimeError::MissingMutexGuard { mutex },
            Self::MissingInvariant(resource) => super::CRuntimeError::MissingMutexInvariant {
                resource: Box::new(resource),
                supplied: None,
            },
            Self::MismatchedInvariant { required, supplied } => {
                super::CRuntimeError::MissingMutexInvariant {
                    resource: Box::new(required),
                    supplied: Some(Box::new(supplied)),
                }
            }
            Self::Refusal(message) => super::CRuntimeError::FunctionContract(message.into()),
            Self::OwnedRefusal(message) => super::CRuntimeError::FunctionContract(message),
        }
    }
}

#[derive(Clone)]
enum MutexEntry {
    /// Heldness supplied by a checked loop resource, never authority itself.
    ConditionalLoop {
        initialization: MutexInitialization,
        epoch: u64,
        held: ConditionTerm,
    },
    Unlocked {
        initialization: MutexInitialization,
        invariant: Option<CResourceFact>,
        interface: Option<Arc<InitializedMutexInterface>>,
    },
    Locked {
        initialization: MutexInitialization,
        invariant: Option<CResourceFact>,
        interface: Option<Arc<InitializedMutexInterface>>,
        epoch: u64,
        lifetime_hold: Option<(LoanHoldId, LoanParticipantId, MutexUseBinding)>,
    },
}

/// A declaration checked at publication, bound to exactly one initialization.
/// Sharing this description conveys no ownership or observed payload value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct InitializedMutexInterface {
    initialization: MutexInitializationId,
    declaration: invariant_interface::MutexInvariantInterface,
}

impl InitializedMutexInterface {
    pub(super) fn description(&self) -> &super::ResourceDescription {
        self.declaration.description()
    }

    pub(super) fn matches_use(&self, fact: &CResourceFact) -> bool {
        matches!(fact.resource(), CResource::MutexUse(identity)
            if identity.initialization == Some(self.initialization.0)
                && identity.mutex == *self.declaration.mutex())
    }
}

/// Identity of one successful initialization, independent of its address and
/// protected assertion. Lock/unlock retain it; destroy/init must replace it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MutexInitialization(MutexInitializationId, u32);

/// Lifetime identities for both runtime initialization and assumed inputs.
/// The private constructor prevents addresses from manufacturing identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct MutexInitializationId(u64);

impl MutexInitializationId {
    pub(super) fn fresh() -> Result<Self, &'static str> {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .map(Self)
        .map_err(|_| "mutex initialization identity space exhausted")
    }
    pub(super) fn description(self, mutex: &Pointer) -> CResourceFact {
        CResourceFact::own(CResource::MutexLive(super::MutexIdentity {
            epoch: Some(self.0),
            mutex: mutex.clone(),
        }))
    }
}

impl MutexInitialization {
    fn resource_fact(self, mutex: &Pointer) -> CResourceFact {
        self.0.description(mutex)
    }

    fn fresh(storage_bytes: u32) -> Result<Self, &'static str> {
        if storage_bytes == 0 {
            return Err("mutex storage extent must be nonzero");
        }
        Ok(Self(MutexInitializationId::fresh()?, storage_bytes))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MutexProtocolMismatch {
    State,
    Initialization,
}

/// A proof-path snapshot. Updates touch only the selected mutex's persistent
/// map path, not unrelated mutexes or resources.
#[derive(Clone)]
pub(super) struct MutexContext {
    state: CState,
    runtime_loan_transition: Option<(
        LoanLedger,
        LoanParticipantId,
        super::loans::CheckedLoanTransition,
    )>,
}

#[derive(Clone)]
pub(super) struct MutexLedger {
    storage: Arc<MutexLedgerStorage>,
}

/// Coarse provenance buckets for retirement queries. A bucket may include
/// conservatively ambiguous pointers, but must never omit a possible alias.
/// Keeping fresh and concrete objects out of the ambiguous buckets avoids
/// scanning unrelated initializations on every allocation retirement.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum StorageProvenance {
    Local,
    Global,
    Fresh,
    External,
    Symbolic,
    Other,
}

impl StorageProvenance {
    fn of(block: &super::PointerBlock) -> Self {
        use super::PointerBlock;
        match block {
            PointerBlock::Concrete(name) if name.starts_with("local:") => Self::Local,
            PointerBlock::Concrete(_) => Self::Global,
            PointerBlock::Heap(_) | PointerBlock::Temporary(_) => Self::Fresh,
            PointerBlock::ExternalArgument | PointerBlock::ExternalObject(_) => Self::External,
            PointerBlock::Symbolic(_)
            | PointerBlock::LoadedPointer(_)
            | PointerBlock::PureFunctionApplication(_) => Self::Symbolic,
            PointerBlock::Function(_)
            | PointerBlock::FunctionSymbolic(_)
            | PointerBlock::StringLiteral { .. } => Self::Other,
        }
    }

    /// Possible aliases *outside* the queried block. Same-block footprints
    /// are visited through `by_block`, including fresh and concrete objects.
    fn cross_block_candidates(self) -> &'static [Self] {
        use StorageProvenance::*;
        match self {
            Fresh => &[Symbolic],
            Local => &[Symbolic, Other],
            Global => &[Symbolic, External, Other],
            External => &[Symbolic, Global, External, Other],
            Symbolic => &[Local, Global, Fresh, External, Symbolic, Other],
            Other => &[Local, Global, External, Symbolic, Other],
        }
    }
}

struct MutexLedgerStorage {
    identity: u64,
    entries: PersistentMap<Pointer, MutexEntry>,
    direct_loop_carriers: PersistentMap<Pointer, Arc<direct_loop_guard::DirectLoopGuard>>,
    direct_loop_selection: Arc<Vec<Pointer>>,
    by_block: PersistentMap<super::PointerBlock, PersistentMap<Pointer, u32>>,
    reserved: MutexStorageIndex,
    by_provenance: PersistentMap<StorageProvenance, PersistentMap<Pointer, u32>>,
    /// Initializations whose symbolic provenance may name any automatic object.
    /// Kept separately so a scope exit never scans unrelated concrete mutexes.
    ambiguous_automatic_storage: PersistentMap<Pointer, ()>,
    /// Initializations that consumed explicit ownership of their storage
    /// bytes. Until destruction returns it nobody owns that storage, so
    /// ownership alone keeps every write and transferred footprint off it.
    consumed_storage: PersistentMap<Pointer, ()>,
    locked_count: usize,
    return_obligation_count: usize,
    /// A loop join need only revisit mutexes changed since its head. Keeping
    /// this path avoids scanning unrelated mutexes on every back edge.
    predecessor: Option<Arc<MutexLedgerStorage>>,
    changed_mutex: Option<Pointer>,
}

/// Dyadic byte intervals select overlapping storage without visiting unrelated
/// mutexes in the same object. Symbolic bounds remain conservative candidates.
#[derive(Clone, Default)]
struct MutexStorageIndex {
    intervals: PersistentMap<super::ResourceMemoryIntervalNode, PersistentMap<Pointer, u32>>,
    subtrees: PersistentMap<super::ResourceMemoryIntervalNode, PersistentMap<Pointer, u32>>,
    symbolic: PersistentMap<super::PointerBlock, PersistentMap<Pointer, u32>>,
}

fn storage_range(mutex: &Pointer, bytes: u32) -> super::CMemoryRange {
    super::CMemoryRange::new_with_element_width(mutex.clone(), 0u32.into(), bytes.into(), 1)
}

impl MutexStorageIndex {
    fn changed(&self, mutex: &Pointer, bytes: u32, insert: bool) -> Self {
        fn update<K: Ord + Clone>(
            map: &mut PersistentMap<K, PersistentMap<Pointer, u32>>,
            key: K,
            mutex: &Pointer,
            bytes: u32,
            insert: bool,
        ) {
            let bucket = map.get(&key).cloned().unwrap_or_default();
            let bucket = if insert {
                bucket.with_inserted(mutex.clone(), bytes)
            } else {
                bucket.without_key(mutex)
            };
            *map = if bucket.is_empty() {
                map.without_key(&key)
            } else {
                map.with_inserted(key, bucket)
            };
        }
        let mut next = self.clone();
        if let Some(nodes) = super::primitives::memory_interval_nodes(&storage_range(mutex, bytes))
        {
            let mut ancestors = std::collections::BTreeSet::new();
            for node in nodes {
                ancestors.extend(super::primitives::memory_interval_ancestors(&node));
                update(&mut next.intervals, node, mutex, bytes, insert);
            }
            for node in ancestors {
                update(&mut next.subtrees, node, mutex, bytes, insert);
            }
        } else {
            update(
                &mut next.symbolic,
                mutex.block.clone(),
                mutex,
                bytes,
                insert,
            );
        }
        next
    }

    fn overlapping(
        &self,
        range: &super::CMemoryRange,
    ) -> Option<std::collections::BTreeMap<Pointer, u32>> {
        let nodes = super::primitives::memory_interval_nodes(range)?;
        let mut candidates = std::collections::BTreeMap::new();
        for node in nodes {
            for ancestor in super::primitives::memory_interval_ancestors(&node) {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(bucket) = self.intervals.get(&ancestor) {
                    candidates.extend(
                        bucket
                            .iter()
                            .map(|(pointer, bytes)| (pointer.clone(), *bytes)),
                    );
                }
            }
            if let Some(bucket) = self.subtrees.get(&node) {
                candidates.extend(
                    bucket
                        .iter()
                        .map(|(pointer, bytes)| (pointer.clone(), *bytes)),
                );
            }
        }
        if let Some(bucket) = self.symbolic.get(&range.base().block) {
            candidates.extend(
                bucket
                    .iter()
                    .map(|(pointer, bytes)| (pointer.clone(), *bytes)),
            );
        }
        Some(candidates)
    }
}

/// Ordinary writes cannot spend a mutex's reserved representation bytes.
/// The ledger retains the reservation when lifecycle ownership is folded.
/// Contract application checks its entire mutable footprint through this same
/// gate, including effects of an abstract preserving helper.
pub(super) fn storage_write_refusal(
    state: &CState,
    write: &super::CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<super::CRuntimeError> {
    // An empty write, whose bounds are one term in either index kind.
    let (write_start, write_end) = write.bound_terms();
    if write_start == write_end {
        return None;
    }
    // A contract input's mutex storage is not checked here. Its initializer
    // consumed explicit ownership of the storage, or reserved it as automatic
    // storage, which no resource can be folded over, and checked every
    // footprint it transferred against it. No memory this body can own
    // reaches it.
    ledger_storage_write_refusal(state.mutex_ledger.as_ref()?, write, assumptions, false)
}

/// Missing ownership that reaches storage a live initialization consumed:
/// the mutex holds those bytes, so diagnostics name it rather than the
/// missing ownership. Free when no initialization consumed storage.
pub(in crate::kernel) fn consumed_storage_refusal(
    state: &CState,
    missing: &super::CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<super::CRuntimeError> {
    let ledger = state.mutex_ledger.as_ref()?;
    if ledger.storage.consumed_storage.is_empty() {
        return None;
    }
    ledger_storage_write_refusal(ledger, missing, assumptions, true)
}

/// A modular use call that may acquire cannot start while the caller owns a
/// possibly matching assumed guard, even when that guard is folded away.
/// The guard projection is computed at independent entry, not at each call.
pub(super) fn abstract_guard_acquisition_refusal(
    state: &CState,
    mutex: &Pointer,
    assumptions: &PureFactContext,
) -> Option<super::CRuntimeError> {
    let inputs = state.mutex_input_reservations.as_ref()?;
    if inputs.guard_unnamed && !mutex.block.starts_with("local:") {
        return Some(super::CRuntimeError::FunctionContract(
            "cannot establish that the mutex is available: an input guard has an unresolved mutex address".into(),
        ));
    }
    let requested = storage_range(
        mutex,
        crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin().mutex_storage_bytes,
    );
    ledger_storage_write_refusal(&inputs.guard_ledger, &requested, assumptions, false).map(|_| {
        super::CRuntimeError::FunctionContract(
            "cannot establish that the mutex is available: an input mutex_guard may hold it".into(),
        )
    })
}

/// Whether `write` may reach storage `ledger` reserves. Storage whose
/// ownership its initialization consumed is skipped unless `include_consumed`:
/// ownership already keeps writes off it, and only a diagnostic for missing
/// ownership asks about it.
fn ledger_storage_write_refusal(
    ledger: &MutexLedger,
    write: &super::CMemoryRange,
    assumptions: &PureFactContext,
    include_consumed: bool,
) -> Option<super::CRuntimeError> {
    if !ledger.has_any_mutex() || write.bound_terms().0 == write.bound_terms().1 {
        return None;
    }
    let block = &write.base().block;
    let direct = ledger
        .storage
        .reserved
        .overlapping(write)
        .unwrap_or_else(|| {
            ledger
                .storage
                .by_block
                .get(block)
                .into_iter()
                .flat_map(|bucket| bucket.iter())
                .map(|(pointer, bytes)| (pointer.clone(), *bytes))
                .collect()
        });
    let possible_aliases = StorageProvenance::of(block)
        .cross_block_candidates()
        .iter()
        .filter_map(|provenance| ledger.storage.by_provenance.get(provenance))
        .flat_map(|bucket| bucket.iter())
        .filter(|(mutex, _)| &mutex.block != block && !mutex.block.proven_distinct(block));
    for (mutex, bytes) in direct.iter().chain(possible_aliases) {
        crate::instrumentation::record_deterministic_work(1);
        if !include_consumed && ledger.storage_consumed(mutex) {
            continue;
        }
        let storage = storage_range(mutex, *bytes);
        // Evaluate ranges in byte units with checked signed arithmetic. This
        // covers interior writes, adjacent fields, and mixed element widths.
        let disjoint = (|| {
            let delta = mutex.exact_element_delta_from_base(write.base(), 1, None)?;
            if !delta.is_constant() {
                return None;
            }
            let start = i64::from(write.constant_start()? as i32)
                .checked_mul(i64::from(write.element_width()))?;
            let end = i64::from(write.constant_end()? as i32)
                .checked_mul(i64::from(write.element_width()))?;
            let storage_end = delta.constant.checked_add(i64::from(*bytes))?;
            Some(start == end || (start < end && (storage_end <= start || end <= delta.constant)))
        })() == Some(true);
        if !disjoint
            && !assumptions.proves_resource_separate(
                &CResource::Memory(write.clone()),
                &CResource::Memory(storage.clone()),
            )
        {
            return Some(super::CRuntimeError::MutexStorageWrite {
                write: Box::new(write.clone()),
                storage: Box::new(storage),
            });
        }
    }
    None
}

/// Immutable storage dependencies of an independently assumed contract input.
/// Also retains descriptions of direct input acquisitions across folding.
/// These descriptions grant no authority; runtime transitions do not consult them.
#[derive(Clone, Debug)]
pub(super) struct MutexInputReservations {
    identity: u64,
    ledger: MutexLedger,
    unnamed: bool,
    guard_ledger: MutexLedger,
    guard_unnamed: bool,
    guards: PersistentMap<Pointer, CResourceFact>,
    lifetimes: PersistentMap<Pointer, CResourceFact>,
    helper_return: Option<Arc<helper_contracts::HelperReturnPermission>>,
}

// Input descriptions are immutable after entry. Compare their identity, not
// every unrelated input, when checking state or loop continuity.
impl PartialEq for MutexInputReservations {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for MutexInputReservations {}
impl PartialOrd for MutexInputReservations {
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}
impl Ord for MutexInputReservations {
    fn cmp(&self, other: &Self) -> CmpOrdering {
        self.identity.cmp(&other.identity)
    }
}
impl Hash for MutexInputReservations {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

impl MutexInputReservations {
    fn empty() -> Self {
        Self {
            identity: MutexLedger::fresh_identity(),
            ledger: MutexLedger::new(),
            unnamed: false,
            guard_ledger: MutexLedger::new(),
            guard_unnamed: false,
            guards: PersistentMap::default(),
            lifetimes: PersistentMap::default(),
            helper_return: None,
        }
    }

    #[cfg(test)]
    pub(super) fn from_ranges(
        ranges: impl IntoIterator<Item = super::CMemoryRange>,
    ) -> Option<Self> {
        Self::from_ranges_and_guards(ranges, std::iter::empty())
    }

    pub(super) fn from_ranges_and_guards(
        ranges: impl IntoIterator<Item = super::CMemoryRange>,
        guards: impl IntoIterator<Item = super::CMemoryRange>,
    ) -> Option<Self> {
        let mut result = Self::empty();
        for range in ranges {
            if range.is_unnamed_footprint() {
                result.unnamed = true;
                continue;
            }
            let Some(bytes) = range.constant_end().filter(|bytes| {
                *bytes > 0 && range.constant_start() == Some(0) && range.element_width() == 1
            }) else {
                result.unnamed = true;
                continue;
            };
            if result.ledger.get(range.base()).is_none() {
                result.ledger = result.ledger.with_inserted(
                    range.base().clone(),
                    MutexEntry::Unlocked {
                        initialization: MutexInitialization::fresh(bytes)
                            .expect("nonempty modeled mutex storage"),
                        invariant: None,
                        interface: None,
                    },
                );
            }
        }
        for range in guards {
            if range.is_unnamed_footprint() {
                result.guard_unnamed = true;
                continue;
            }
            let Some(bytes) = range.constant_end().filter(|bytes| {
                *bytes > 0 && range.constant_start() == Some(0) && range.element_width() == 1
            }) else {
                result.guard_unnamed = true;
                continue;
            };
            if result.guard_ledger.get(range.base()).is_none() {
                result.guard_ledger = result.guard_ledger.with_inserted(
                    range.base().clone(),
                    MutexEntry::Unlocked {
                        initialization: MutexInitialization::fresh(bytes)
                            .expect("nonempty modeled mutex storage"),
                        invariant: None,
                        interface: None,
                    },
                );
            }
        }
        (result.unnamed
            || result.ledger.has_any_mutex()
            || result.guard_unnamed
            || result.guard_ledger.has_any_mutex())
        .then_some(result)
    }
}

/// An acquisition identity. The private fields cannot be synthesized from a
/// mutex address or an integer value copied by C.
pub(super) struct MutexGuard {
    mutex: Pointer,
    initialization: MutexInitialization,
    epoch: u64,
}

fn fresh_acquisition_epoch() -> Result<u64, MutexTransitionError> {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |epoch| {
        epoch.checked_add(1)
    })
    .map_err(|_| MutexTransitionError::Refusal("mutex acquisition identity space exhausted"))
}

/// Bind actual direct guard inputs at independent proof entry. This does not
/// initialize a mutex or make a transition executable. Hidden wrapper inputs
/// remain under the protocol freeze until their occurrences can be bound too.
pub(super) fn bind_assumed_guard_inputs(
    mut state: CState,
    assumptions: &PureFactContext,
) -> Result<CState, super::loans::LoanRefusal> {
    use super::loans::LoanRefusal;
    let inputs = state.resources.facts().iter().filter(|fact|
        matches!(fact.resource(), CResource::MutexGuard(identity) if identity.epoch.is_none()))
        .cloned().collect::<Vec<_>>();
    if !inputs.is_empty() && (!state.preserves_mutex_protocols || state.mutex_ledger.is_some()) {
        return Err(LoanRefusal::InvalidEvidence);
    }
    for fact in inputs {
        state
            .resources
            .unique_owned_occurrence_for_fact(&fact)
            .ok_or(LoanRefusal::MissingBacking)?;
        let CResource::MutexGuard(identity) = fact.resource() else {
            unreachable!()
        };
        // Reject ambiguous or non-unit ownership before allocating an identity.
        if state.resources.mutex_guard_at(&identity.mutex) != Some(&fact) {
            return Err(LoanRefusal::MissingBacking);
        }
        let bound = CResourceFact::own(CResource::MutexGuard(super::MutexIdentity {
            epoch: Some(fresh_acquisition_epoch().map_err(|_| LoanRefusal::InvalidEvidence)?),
            mutex: identity.mutex.clone(),
        }));
        let inputs = state
            .mutex_input_reservations
            .get_or_insert_with(MutexInputReservations::empty);
        if inputs.guards.contains_key(&identity.mutex) {
            return Err(LoanRefusal::InvalidEvidence);
        }
        inputs.identity = MutexLedger::fresh_identity();
        inputs.guards.insert(identity.mutex.clone(), bound.clone());
        state.resources = state
            .resources
            .without_fact_delaying_normalization(&fact, assumptions)
            .ok_or(LoanRefusal::MissingBacking)?
            .try_compose_with_facts_delaying_normalization([bound], assumptions)
            .map_err(|_| LoanRefusal::MissingBacking)?;
    }
    Ok(state)
}

/// Bind direct lifecycle inputs without initializing runtime storage.
pub(super) fn bind_assumed_lifetime_inputs(
    mut state: CState,
    assumptions: &PureFactContext,
) -> Result<CState, super::loans::LoanRefusal> {
    use super::loans::LoanRefusal;
    let inputs = state.resources.facts().iter().filter(|fact|
        matches!(fact.resource(), CResource::MutexLive(identity) if identity.epoch.is_none()))
        .cloned().collect::<Vec<_>>();
    if !inputs.is_empty() && (!state.preserves_mutex_protocols || state.mutex_ledger.is_some()) {
        return Err(LoanRefusal::InvalidEvidence);
    }
    for fact in inputs {
        state
            .resources
            .unique_owned_occurrence_for_fact(&fact)
            .ok_or(LoanRefusal::MissingBacking)?;
        let CResource::MutexLive(identity) = fact.resource() else {
            unreachable!()
        };
        // Reject ambiguous or non-unit ownership before allocating an identity.
        if state.resources.mutex_live_at(&identity.mutex) != Some(&fact) {
            return Err(LoanRefusal::MissingBacking);
        }
        let bound = MutexInitializationId::fresh()
            .map_err(|_| LoanRefusal::IdentitySpaceExhausted)?
            .description(&identity.mutex);
        let inputs = state
            .mutex_input_reservations
            .get_or_insert_with(MutexInputReservations::empty);
        if inputs.lifetimes.contains_key(&identity.mutex) {
            return Err(LoanRefusal::InvalidEvidence);
        }
        inputs.identity = MutexLedger::fresh_identity();
        inputs
            .lifetimes
            .insert(identity.mutex.clone(), bound.clone());
        state.resources = state
            .resources
            .without_fact_delaying_normalization(&fact, assumptions)
            .ok_or(LoanRefusal::MissingBacking)?
            .try_compose_with_facts_delaying_normalization([bound], assumptions)
            .map_err(|_| LoanRefusal::MissingBacking)?;
    }
    Ok(state)
}

impl MutexGuard {
    fn resource_fact(&self) -> CResourceFact {
        CResourceFact::own(CResource::MutexGuard(super::MutexIdentity {
            epoch: Some(self.epoch),
            mutex: self.mutex.clone(),
        }))
    }
}

/// Describe the lifecycle resource for the current initialization. This does
/// not establish ownership; callers must check the ordinary resource context.
pub(super) fn live_resource(
    state: &CState,
    mutex: &Pointer,
    abstract_entry: bool,
) -> Option<CResourceFact> {
    if let Some(ledger) = &state.mutex_ledger {
        ledger.live_resource(mutex)
    } else if let Some(bound) = state
        .mutex_input_reservations
        .as_ref()
        .and_then(|inputs| inputs.lifetimes.get(mutex))
    {
        Some(bound.clone())
    } else if let Some(bound) = state.resources.mutex_live_at(mutex) {
        Some(bound.clone())
    } else if abstract_entry || state.preserves_mutex_protocols {
        Some(CResourceFact::own(CResource::MutexLive(
            super::MutexIdentity {
                epoch: None,
                mutex: mutex.clone(),
            },
        )))
    } else {
        None
    }
}

/// A description is not authority: only a rooted owned occurrence permits use.
pub(super) fn use_resource(state: &CState, mutex: &Pointer) -> CResourceFact {
    state
        .resources
        .mutex_use_candidate_at(mutex)
        .cloned()
        .unwrap_or_else(|| {
            CResourceFact::own(CResource::MutexUse(super::MutexUseIdentity {
                protected: None,
                binding: None,
                initialization: None,
                mutex: mutex.clone(),
            }))
        })
}

/// Describe an acquisition without establishing ownership. Abstract entry
/// assumptions are inputs; execution still requires checked resource transfer.
pub(super) fn guard_resource(
    state: &CState,
    mutex: &Pointer,
    abstract_entry: bool,
) -> Option<CResourceFact> {
    if let Some(guard) = state
        .opaque_mutex_acquisitions
        .as_ref()
        .and_then(|held| held.guard_resource(mutex))
    {
        return Some(guard);
    }
    if let Some(ledger) = &state.mutex_ledger {
        return ledger.guard_resource(mutex);
    }
    if let Some(guard) = state
        .mutex_input_reservations
        .as_ref()
        .and_then(|inputs| inputs.guards.get(mutex))
    {
        return Some(guard.clone());
    }
    if let Some(guard) = state.resources.mutex_guard_at(mutex) {
        return Some(guard.clone());
    }
    (abstract_entry || state.preserves_mutex_protocols).then(|| {
        CResourceFact::own(CResource::MutexGuard(super::MutexIdentity {
            epoch: None,
            mutex: mutex.clone(),
        }))
    })
}

/// Current conservative call discipline: use helpers may acquire, so an
/// entry guard or another outstanding local acquisition must be separate.
pub(super) fn acquisition_availability_refusal(
    state: &CState,
    mutex: &Pointer,
    assumptions: &PureFactContext,
) -> Option<MutexTransitionError> {
    if abstract_guard_acquisition_refusal(state, mutex, assumptions).is_some()
        || state
            .opaque_mutex_acquisitions
            .as_ref()
            .is_some_and(|held| held.acquisition_conflicts(mutex, assumptions))
    {
        return Some(MutexTransitionError::Refusal(
            "Click cannot acquire or lend mutex_use while a possibly aliasing mutex_guard is held",
        ));
    }
    None
}

/// Preconditions for the C initialization operation, before any invariant
/// or lifecycle authority moves. Owning bytes does not require initialized
/// byte values. Automatic objects have implicit storage ownership; all other
/// objects require ordinary explicit memory ownership.
pub(super) fn initialization_storage_refusal(
    state: &CState,
    mutex: &Pointer,
    bytes: u32,
    alignment: u32,
    assumptions: &PureFactContext,
) -> Option<super::CRuntimeError> {
    let resolved = assumptions.equality_graph.storage_address(mutex);
    let range =
        super::CMemoryRange::new_with_element_width(mutex.clone(), 0u32.into(), bytes.into(), 1);
    let automatic = storage_is_automatic(state, mutex, bytes, assumptions);
    if bytes == 0
        || state.memory.is_read_only_block(&resolved.block)
        || state.memory.is_ended_local_address(&resolved)
        || state
            .memory
            .deallocated_heap_allocation_holding(&resolved, assumptions)
            .is_some()
        || (!automatic
            && !state
                .resources
                .owns_storage_access(mutex, bytes, assumptions))
    {
        // A live initialization consumed the ownership; name it.
        if let Some(error) = state
            .mutex_ledger
            .as_ref()
            .and_then(|ledger| ledger_storage_write_refusal(ledger, &range, assumptions, true))
        {
            return Some(error);
        }
        return Some(super::CRuntimeError::MissingResource {
            resource: Box::new(CResourceFact::own_memory(range)),
        });
    }
    if assumptions.decide(&ConditionTerm::pointer_aligned(
        mutex.clone(),
        u64::from(alignment),
    )) != Some(true)
    {
        return Some(super::CRuntimeError::MissingMutexStorageAlignment {
            mutex: mutex.clone(),
            alignment,
        });
    }
    if let Some(error) = storage_write_refusal(state, &range, assumptions) {
        return Some(error);
    }
    state
        .stable_loan_memory_access_refusal(
            &range,
            assumptions,
            super::LoanRefusalOperation::MemoryAccess,
        )
        .map(|refusal| super::CRuntimeError::LoanRefusal(Box::new(refusal)))
}

/// Whether initialization storage is an automatic object, owned implicitly
/// by its scope rather than by an explicit memory resource.
pub(super) fn storage_is_automatic(
    state: &CState,
    mutex: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    let resolved = assumptions.equality_graph.storage_address(mutex);
    resolved.block.starts_with("local:") && state.memory.access_in_bounds(&resolved, bytes)
}

/// A storage release must not leave a live initialization behind. Abstract
/// guard contracts lack checked lifecycle inputs for deciding this dependency;
/// refuse retirement there until the lifetime-loan model can discharge it.
pub(super) fn storage_retirement_refusal(
    state: &CState,
    allocation: &super::CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<super::CRuntimeError> {
    if let Some(inputs) = &state.mutex_input_reservations {
        if inputs.unnamed {
            return Some(super::CRuntimeError::UnsupportedMutexStorageRetirement);
        }
        if let Some(error) = inputs
            .ledger
            .storage_retirement_refusal(allocation, assumptions)
        {
            return Some(error);
        }
    } else if state.preserves_mutex_protocols && state.mutex_ledger.is_none() {
        return Some(super::CRuntimeError::UnsupportedMutexStorageRetirement);
    }
    state
        .mutex_ledger
        .as_ref()?
        .storage_retirement_refusal(allocation, assumptions)
}

/// A concrete automatic object is fresh relative to input object provenance.
/// A symbolic pointer, however, can be constrained to a local address by a
/// later equality. Treat all other non-object provenances conservatively too;
/// initialization storage validity is a separate precondition still to check.
fn may_alias_automatic_storage(block: &super::PointerBlock) -> bool {
    use super::PointerBlock;
    match block {
        PointerBlock::Concrete(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::ExternalObject(_)
        | PointerBlock::Heap(_)
        | PointerBlock::Temporary(_) => false,
        PointerBlock::Symbolic(_)
        | PointerBlock::PureFunctionApplication(_)
        | PointerBlock::LoadedPointer(_)
        | PointerBlock::FunctionSymbolic(_)
        | PointerBlock::Function(_)
        | PointerBlock::StringLiteral { .. } => true,
    }
}

/// Ending the entire automatic object requires every mutex in it to have
/// been destroyed. No address arithmetic can discharge that obligation.
/// This remains true when the owner/guard has been folded or removed from the
/// ordinary resource context. An abstract preserving input predates locals
/// created by its helper and cannot initialize another mutex there.
pub(super) fn automatic_storage_refusal(
    state: &CState,
    local: &str,
    block: &super::PointerBlock,
) -> Option<super::CRuntimeError> {
    let ledger = state.mutex_ledger.as_ref()?;
    let direct = ledger
        .storage
        .by_block
        .get(block)
        .and_then(|entries| entries.iter().next())
        .map(|(mutex, _)| mutex);
    let (mutex, may_alias) = if let Some(mutex) = direct {
        (mutex, false)
    } else {
        (
            ledger.storage.ambiguous_automatic_storage.iter().next()?.0,
            true,
        )
    };
    crate::instrumentation::record_deterministic_work(1);
    Some(super::CRuntimeError::MutexStorageScopeEnd {
        local: local.to_string(),
        mutex: mutex.clone(),
        may_alias,
    })
}

impl MutexContext {
    pub(super) fn new(mut state: CState) -> Self {
        state.mutex_ledger.get_or_insert_with(MutexLedger::new);
        Self {
            state,
            runtime_loan_transition: None,
        }
    }

    #[cfg(test)]
    pub(super) fn state(&self) -> &CState {
        &self.state
    }

    #[cfg(test)]
    pub(super) fn into_state(self) -> CState {
        self.state
    }

    pub(super) fn into_runtime_transition(
        self,
    ) -> (CState, super::loans::CheckedLoanCallEvidenceSequence) {
        use super::loans::{
            CheckedLoanCallEvidence, append_checked_loan_evidence,
            empty_checked_loan_evidence_sequence,
        };
        let mut evidence = empty_checked_loan_evidence_sequence();
        if let Some((before, holder, transition)) = self.runtime_loan_transition {
            let checked = CheckedLoanCallEvidence::runtime_mutex_transition(
                &before,
                holder,
                transition,
                self.state
                    .loan_ledger
                    .as_ref()
                    .expect("mutex loan successor"),
            )
            .expect("checked mutex loan transition");
            evidence = append_checked_loan_evidence(&evidence, Some(Arc::new(checked)));
        }
        (self.state, evidence)
    }

    /// Initialization consumes explicit ownership of the storage bytes, and
    /// destruction returns it. While the mutex is live nobody owns them, so
    /// ownership alone separates every other owned byte from the storage.
    /// Automatic storage is owned by its scope, not by a resource; it keeps
    /// the ledger's write reservation instead.
    pub(super) fn consume_initialized_storage(
        mut self,
        mutex: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        if storage_is_automatic(&self.state, mutex, bytes, assumptions) {
            return Ok(self);
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        if ledger.get(mutex).is_none() {
            return Err("initialized mutex storage is missing from its ledger");
        }
        self.state.resources = self
            .state
            .resources
            .clone()
            .without_owned_storage_access(mutex, bytes, assumptions)
            .ok_or("mutex initialization requires owned storage")?;
        self.state.mutex_ledger = Some(ledger.with_storage_consumed(mutex));
        Ok(self)
    }

    /// Initialize a mutex that transfers no Click resource at lock/unlock.
    pub(super) fn initialize_empty(
        &self,
        mutex: Pointer,
        storage_bytes: u32,
    ) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols");
        }
        let ledger = self
            .state
            .mutex_ledger
            .clone()
            .unwrap_or_else(MutexLedger::new);
        if ledger.get(&mutex).is_some() {
            return Err("mutex is already initialized");
        }
        let initialization = MutexInitialization::fresh(storage_bytes)?;
        let mut state = self.state.clone();
        state.resources = state
            .resources
            .try_compose_with_facts_delaying_normalization(
                [initialization.resource_fact(&mutex)],
                &PureFactContext::new(),
            )
            .map_err(|_| "mutex lifetime authority conflicts with current resources")?;
        state.mutex_ledger = Some(ledger.with_inserted(
            mutex,
            MutexEntry::Unlocked {
                initialization,
                invariant: None,
                interface: None,
            },
        ));
        Ok(Self {
            state,
            runtime_loan_transition: None,
        })
    }

    /// Select the protected assertion through its installed declaration and
    /// actual folded ownership. A declaration alone cannot publish authority.
    pub(super) fn publish_declared(
        &self,
        mutex: &Pointer,
        identity: super::Variable,
        definitions: &std::collections::BTreeMap<String, super::CCompositeResourceDefinition>,
        assumptions: &PureFactContext,
        storage_bytes: u32,
    ) -> Result<Self, &'static str> {
        let instance = self
            .state
            .resources
            .owned_instance(identity)
            .ok_or("selected mutex invariant is not held folded")?;
        let definition = definitions
            .get(instance.name())
            .ok_or("selected mutex resource has no checked declaration")?;
        let interface = invariant_interface::MutexInvariantInterface::check_definition(
            instance, mutex, definition,
        )?;
        self.publish_with_interface(
            interface.mutex().clone(),
            CResourceFact::own(CResource::Instance(instance.clone())),
            assumptions,
            storage_bytes,
            Some(interface),
        )
    }

    // Low-level fixtures exercise escrow without a source declaration.
    #[cfg(test)]
    fn publish(
        &self,
        mutex: Pointer,
        invariant: CResourceFact,
        assumptions: &PureFactContext,
        storage_bytes: u32,
    ) -> Result<Self, &'static str> {
        self.publish_with_interface(mutex, invariant, assumptions, storage_bytes, None)
    }

    fn publish_with_interface(
        &self,
        mutex: Pointer,
        invariant: CResourceFact,
        assumptions: &PureFactContext,
        storage_bytes: u32,
        interface: Option<invariant_interface::MutexInvariantInterface>,
    ) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols");
        }
        let ledger = self
            .state
            .mutex_ledger
            .clone()
            .unwrap_or_else(MutexLedger::new);
        if ledger.get(&mutex).is_some() {
            return Err("mutex is already initialized");
        }
        if !matches!(
            &invariant,
            CResourceFact::Own(CResource::Instance(_), quantity)
                if quantity.as_const() == Some(1)
        ) {
            return Err("mutex invariant must be one folded, exclusive instance");
        }
        // The first transition has no loan evidence. Escrowing a resource
        // beside a possible live borrower would be unsound.
        if self
            .state
            .loan_ledger
            .as_ref()
            .is_some_and(|ledger| ledger.has_active_memory_loans())
            || self.state.loan_view_bindings.iter().next().is_some()
        {
            return Err("mutex publication with a loan ledger is not supported");
        }
        if !self
            .state
            .resources
            .contains_exact_representation(&invariant)
        {
            return Err("mutex invariant is not held as a folded resource");
        }
        let resources = self
            .state
            .resources
            .clone()
            .without_fact_delaying_normalization(&invariant, assumptions)
            .ok_or("mutex invariant cannot be moved to escrow")?;
        let mut state = self.state.clone();
        let initialization = MutexInitialization::fresh(storage_bytes)?;
        state.resources = resources
            .try_compose_with_facts_delaying_normalization(
                [initialization.resource_fact(&mutex)],
                assumptions,
            )
            .map_err(|_| "mutex lifetime authority conflicts with current resources")?;
        state.mutex_ledger = Some(ledger.with_inserted(
            mutex,
            MutexEntry::Unlocked {
                initialization,
                invariant: Some(invariant),
                interface: interface.map(|declaration| {
                    Arc::new(InitializedMutexInterface {
                        initialization: initialization.0,
                        declaration,
                    })
                }),
            },
        ));
        Ok(Self {
            state,
            runtime_loan_transition: None,
        })
    }

    /// Checked adapter staged ahead of surface `mutex_use` call transport.
    /// The owner is removed here, rather than trusting a caller-supplied fact.
    #[cfg(test)]
    pub(super) fn lend_use(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexUseLoan), MutexTransitionError> {
        if self
            .state
            .mutex_ledger
            .as_ref()
            .is_some_and(|ledger| ledger.is_loop_abstract(mutex))
        {
            return Err(
                "conditional loop mutex authority cannot be lent before its heldness is resolved"
                    .into(),
            );
        }
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot lend mutex authority".into());
        }
        let live = self
            .state
            .mutex_ledger
            .as_ref()
            .and_then(|ledger| ledger.live_resource(mutex))
            .ok_or(MutexTransitionError::NotInitialized)?;
        let (support, _) = self
            .state
            .resources
            .unique_owned_occurrence_for_fact(&live)
            .ok_or_else(|| MutexTransitionError::MissingLive(mutex.clone()))?;
        let resources = self
            .state
            .resources
            .clone()
            .without_fact_delaying_normalization(&live, assumptions)
            .ok_or_else(|| MutexTransitionError::MissingLive(mutex.clone()))?;
        let ledger = self
            .state
            .loan_ledger
            .clone()
            .unwrap_or_else(LoanLedger::new);
        let participant = match self.state.loan_participant {
            Some(participant) => participant,
            None => ledger.fresh_participant().map_err(|_| {
                MutexTransitionError::Refusal("cannot establish mutex loan participant")
            })?,
        };
        let (ledger, loan) = ledger
            .lend_mutex_use(participant, participant, support, live)
            .map_err(|_| MutexTransitionError::Refusal("cannot lend mutex lifetime authority"))?;
        let mut state = self.state.clone();
        let usage = ledger
            .mutex_use_resource(loan.usage, participant)
            .map_err(|_| MutexTransitionError::MissingUse(mutex.clone()))?;
        state.resources = resources
            .try_compose_with_facts_delaying_normalization([usage], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal(
                    "mutex use occurrence conflicts with current authority",
                )
            })?;
        state.loan_ledger = Some(ledger);
        state.loan_participant = Some(participant);
        Ok((
            Self {
                state,
                runtime_loan_transition: None,
            },
            loan,
        ))
    }

    fn owned_use_resource(
        &self,
        usage: MutexUseBinding,
    ) -> Result<CResourceFact, MutexTransitionError> {
        let ledger = self
            .state
            .loan_ledger
            .as_ref()
            .ok_or("missing mutex loan ledger")?;
        let participant = self
            .state
            .loan_participant
            .ok_or("missing mutex loan participant")?;
        let fact = ledger
            .mutex_use_resource(usage, participant)
            .map_err(|_| MutexTransitionError::Refusal("mutex use permission is not available"))?;
        if self
            .state
            .resources
            .unique_owned_occurrence_for_fact(&fact)
            .is_none()
        {
            let CResource::MutexUse(identity) = fact.resource() else {
                unreachable!("checked use resource")
            };
            return Err(MutexTransitionError::MissingUse(identity.mutex().clone()));
        }
        Ok(fact)
    }

    /// Staged synchronous helper adapter: reborrow this participant's use
    /// share without regaining the owner or changing the protected state.
    #[cfg(test)]
    pub(super) fn reborrow_use(
        &self,
        usage: MutexUseBinding,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexUseLoan), MutexTransitionError> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot reborrow mutex authority".into());
        }
        let ledger = self
            .state
            .loan_ledger
            .as_ref()
            .ok_or("missing mutex loan ledger")?;
        let participant = self
            .state
            .loan_participant
            .ok_or("missing mutex loan participant")?;
        let parent_fact = self.owned_use_resource(usage)?;
        let (ledger, loan) = ledger
            .reborrow_mutex_use(usage, participant, participant)
            .map_err(|_| {
                MutexTransitionError::Refusal(
                    "mutex use permission is not available for reborrowing",
                )
            })?;
        let child_fact = ledger
            .mutex_use_resource(loan.usage, participant)
            .map_err(|_| MutexTransitionError::Refusal("missing reborrowed mutex use"))?;
        let mut state = self.state.clone();
        state.resources = state
            .resources
            .without_fact_delaying_normalization(&parent_fact, assumptions)
            .ok_or("missing parent mutex use occurrence")?
            .try_compose_with_facts_delaying_normalization([child_fact], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal("mutex use child conflicts with current authority")
            })?;
        state.loan_ledger = Some(ledger);
        Ok((
            Self {
                state,
                runtime_loan_transition: None,
            },
            loan,
        ))
    }
    #[cfg(test)]
    pub(super) fn end_use_reborrow(
        &self,
        loan: &MutexUseLoan,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot end a mutex reborrow".into());
        }
        let ledger = self
            .state
            .loan_ledger
            .as_ref()
            .ok_or("missing mutex loan ledger")?;
        let participant = self
            .state
            .loan_participant
            .ok_or("missing mutex loan participant")?;
        let child_fact = self.owned_use_resource(loan.usage)?;
        let (ledger, parent_fact) = ledger
            .end_mutex_reborrow_with_parent(loan, participant)
            .map_err(|_| {
                MutexTransitionError::Refusal(
                    "mutex use reborrow still has outstanding shares or guards",
                )
            })?;
        let mut state = self.state.clone();
        state.resources = state
            .resources
            .without_fact_delaying_normalization(&child_fact, assumptions)
            .ok_or("missing child mutex use occurrence")?
            .try_compose_with_facts_delaying_normalization([parent_fact], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal("returned mutex use conflicts with current authority")
            })?;
        state.loan_ledger = Some(ledger);
        Ok(Self {
            state,
            runtime_loan_transition: None,
        })
    }

    /// Recovery returns only the escrowed owner, after all shares and holds
    /// are back. No guarded payload or acquisition is manufactured here.
    #[cfg(test)]
    pub(super) fn recover_use(
        &self,
        loan: &MutexUseLoan,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot recover mutex authority".into());
        }
        let ledger = self
            .state
            .loan_ledger
            .as_ref()
            .ok_or("missing mutex loan ledger")?;
        let participant = self
            .state
            .loan_participant
            .ok_or("missing mutex loan participant")?;
        let use_fact = self.owned_use_resource(loan.usage)?;
        let (ledger, owner) = ledger.recover_mutex_use(loan, participant).map_err(|_| {
            MutexTransitionError::Refusal("mutex use loan still has outstanding shares or guards")
        })?;
        let mut state = self.state.clone();
        state.resources = state
            .resources
            .without_fact_delaying_normalization(&use_fact, assumptions)
            .ok_or("missing mutex use occurrence during recovery")?
            .try_compose_with_facts_delaying_normalization([owner], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal(
                    "recovered mutex owner conflicts with current authority",
                )
            })?;
        state.loan_ledger = Some(ledger);
        Ok(Self {
            state,
            runtime_loan_transition: None,
        })
    }

    /// This entry is intentionally not exposed as surface syntax until calls
    /// can transport use occurrences and returned guard dependencies.
    pub(super) fn acquire_using(
        &self,
        mutex: &Pointer,
        usage: MutexUseBinding,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexGuard), MutexTransitionError> {
        self.acquire_with_use(mutex, Some(usage), assumptions)
    }

    pub(super) fn acquire(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexGuard), MutexTransitionError> {
        self.acquire_with_use(mutex, None, assumptions)
    }

    fn acquire_with_use(
        &self,
        mutex: &Pointer,
        usage: Option<MutexUseBinding>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexGuard), MutexTransitionError> {
        if let Some(opened) = self.open_direct_loop_guard(mutex, assumptions)? {
            return opened.acquire_with_use(mutex, usage, assumptions);
        }
        if let Some(concrete) = self.materialize_loop_mutex(mutex, assumptions)? {
            return concrete.acquire_with_use(mutex, usage, assumptions);
        }
        if self.state.preserves_mutex_protocols {
            return Err(MutexTransitionError::Refusal(
                "preserving mutex contracts cannot change mutex protocols",
            ));
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (initialization, invariant, interface) = match ledger.get(mutex) {
            Some(MutexEntry::Unlocked {
                initialization,
                invariant,
                interface,
            }) => (*initialization, invariant.clone(), interface.clone()),
            Some(MutexEntry::Locked { .. } | MutexEntry::ConditionalLoop { .. }) => {
                return Err(MutexTransitionError::Refusal("mutex is already guarded"));
            }
            None => return Err(MutexTransitionError::NotInitialized),
        };
        let mut runtime_loan_transition = None;
        let (loan_ledger, lifetime_hold) = if let Some(usage) = usage {
            self.owned_use_resource(usage)
                .map_err(|_| MutexTransitionError::MissingUse(mutex.clone()))?;
            let participant = self
                .state
                .loan_participant
                .ok_or_else(|| MutexTransitionError::MissingUse(mutex.clone()))?;
            let loans = self
                .state
                .loan_ledger
                .as_ref()
                .ok_or_else(|| MutexTransitionError::MissingUse(mutex.clone()))?;
            let (next, hold, transition) = loans
                .hold_mutex_use_with_transition(
                    usage,
                    &initialization.resource_fact(mutex),
                    participant,
                )
                .map_err(|_| MutexTransitionError::MissingUse(mutex.clone()))?;
            runtime_loan_transition = Some((loans.clone(), participant, transition));
            let loans = next;
            (Some(loans), Some((hold, participant, usage)))
        } else {
            if !self
                .state
                .resources
                .satisfies_fact(&initialization.resource_fact(mutex), assumptions)
            {
                return Err(MutexTransitionError::MissingLive(mutex.clone()));
            }
            (self.state.loan_ledger.clone(), None)
        };
        let resources = self.state.resources.clone();
        let resources = if let Some(invariant) = &invariant {
            resources
                .try_compose_with_facts_delaying_normalization([invariant.clone()], assumptions)
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "mutex invariant conflicts with current authority",
                    )
                })?
        } else {
            resources
        };
        let epoch = fresh_acquisition_epoch()?;
        let mut state = self.state.clone();
        state.loan_ledger = loan_ledger;
        let guard = MutexGuard {
            mutex: mutex.clone(),
            initialization,
            epoch,
        };
        state.resources = resources
            .try_compose_with_facts_delaying_normalization([guard.resource_fact()], assumptions)
            .map_err(|_| {
                MutexTransitionError::Refusal("mutex guard conflicts with current authority")
            })?;
        state.mutex_ledger = Some(ledger.with_inserted(
            mutex.clone(),
            MutexEntry::Locked {
                initialization,
                invariant,
                interface,
                epoch,
                lifetime_hold,
            },
        ));
        Ok((
            Self {
                state,
                runtime_loan_transition,
            },
            MutexGuard {
                mutex: mutex.clone(),
                initialization,
                epoch,
            },
        ))
    }

    pub(super) fn acquire_current(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        // The resource occurrence selects the loan; an address or a loan
        // record alone is not authority. The checked acquisition validates
        // possession and initialization identity before installing its hold.
        // A use description without a binding selects no loan either: the
        // lifecycle authority, when the frame holds it, is the acquisition
        // route, and only its absence reports the missing use.
        let unbound_use = match self.state.resources.mutex_use_candidate_at(mutex) {
            Some(fact) => {
                let CResource::MutexUse(identity) = fact.resource() else {
                    unreachable!()
                };
                match identity.binding {
                    Some(usage) => {
                        return self
                            .acquire_using(mutex, usage, assumptions)
                            .map(|(context, _)| context);
                    }
                    None => true,
                }
            }
            None => false,
        };
        match self.acquire(mutex, assumptions) {
            Err(MutexTransitionError::MissingLive(_)) if unbound_use => {
                Err(MutexTransitionError::MissingUse(mutex.clone()))
            }
            acquired => acquired.map(|(context, _)| context),
        }
    }

    pub(super) fn release_current(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if let Some(opened) = self.open_direct_loop_guard(mutex, assumptions)? {
            return opened.release_current(mutex, assumptions);
        }
        if let Some(concrete) = self.materialize_loop_mutex(mutex, assumptions)? {
            return concrete.release_current(mutex, assumptions);
        }
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols".into());
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (previous, initialization, epoch) = match ledger.get(mutex) {
            Some(MutexEntry::Locked {
                invariant,
                initialization,
                epoch,
                ..
            }) => (invariant, *initialization, *epoch),
            _ => return Err(MutexTransitionError::MissingGuard(mutex.clone())),
        };
        let guard = MutexGuard {
            mutex: mutex.clone(),
            initialization,
            epoch,
        };
        if !self
            .state
            .resources
            .contains_exact_representation(&guard.resource_fact())
        {
            return Err(MutexTransitionError::MissingGuard(mutex.clone()));
        }
        let restored = match previous {
            Some(CResourceFact::Own(CResource::Instance(instance), _)) => {
                let current = self
                    .state
                    .resources
                    .owned_instance(instance.identity())
                    .ok_or_else(|| {
                        MutexTransitionError::MissingInvariant(
                            previous.clone().expect("guarded invariant"),
                        )
                    })?;
                Some(CResourceFact::own(CResource::Instance(current.clone())))
            }
            _ => previous.clone(),
        };
        self.release_with_invariant(guard, restored, assumptions)
    }

    pub(super) fn destroy(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if let Some(opened) = self.open_direct_loop_guard(mutex, assumptions)? {
            return opened.destroy(mutex, assumptions);
        }
        if let Some(concrete) = self.materialize_loop_mutex(mutex, assumptions)? {
            return concrete.destroy(mutex, assumptions);
        }
        if self.state.preserves_mutex_protocols {
            return Err(MutexTransitionError::Refusal(
                "preserving mutex contracts cannot change mutex protocols",
            ));
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let invariant = match ledger.get(mutex) {
            Some(MutexEntry::Unlocked { invariant, .. }) => invariant.clone(),
            Some(MutexEntry::Locked { .. } | MutexEntry::ConditionalLoop { .. }) => {
                return Err(MutexTransitionError::Refusal("cannot destroy a held mutex"));
            }
            None => return Err(MutexTransitionError::NotInitialized),
        };
        let live = ledger.live_resource(mutex).expect("initialized mutex");
        let resources = self
            .state
            .resources
            .clone()
            .without_fact_delaying_normalization(&live, assumptions)
            .ok_or_else(|| MutexTransitionError::MissingLive(mutex.clone()))?;
        let resources = if let Some(invariant) = invariant {
            resources
                .try_compose_with_facts_delaying_normalization([invariant], assumptions)
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "destroyed mutex invariant conflicts with current authority",
                    )
                })?
        } else {
            resources
        };
        let resources = if ledger.storage_consumed(mutex) {
            let bytes = ledger
                .get(mutex)
                .expect("initialized mutex")
                .initialization()
                .1;
            resources
                .try_compose_with_facts_delaying_normalization(
                    [CResourceFact::own_memory(storage_range(mutex, bytes))],
                    assumptions,
                )
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "destroyed mutex storage conflicts with current ownership",
                    )
                })?
        } else {
            resources
        };
        let mut state = self.state.clone();
        state.resources = resources;
        let next = ledger.without(mutex);
        state.mutex_ledger = next.has_any_mutex().then_some(next);
        Ok(Self {
            state,
            runtime_loan_transition: None,
        })
    }

    #[cfg(test)]
    pub(super) fn release(
        &self,
        guard: MutexGuard,
        restored: CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        self.release_with_invariant(guard, Some(restored), assumptions)
    }

    fn release_with_invariant(
        &self,
        guard: MutexGuard,
        restored: Option<CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if let Some(concrete) = self.materialize_loop_mutex(&guard.mutex, assumptions)? {
            return concrete.release_with_invariant(guard, restored, assumptions);
        }
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols".into());
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (previous, lifetime_hold, interface) = match ledger.get(&guard.mutex) {
            Some(MutexEntry::Locked {
                invariant,
                initialization,
                epoch,
                lifetime_hold,
                interface,
            }) if *initialization == guard.initialization && *epoch == guard.epoch => {
                (invariant, *lifetime_hold, interface.clone())
            }
            _ => return Err("mutex guard does not match the current holder".into()),
        };
        let guard_fact = guard.resource_fact();
        if !self
            .state
            .resources
            .contains_exact_representation(&guard_fact)
        {
            return Err(MutexTransitionError::MissingGuard(guard.mutex.clone()));
        }
        let restores_description = if let Some(interface) = &interface {
            matches!(&restored, Some(CResourceFact::Own(CResource::Instance(instance), quantity))
                if quantity.as_const() == Some(1)
                    && interface.declaration.description().matches_instance(instance, assumptions))
        } else {
            // Low-level escrow without a checked declaration supplies no
            // general assertion under which a replacement can be justified.
            same_instance(previous, &restored)
        };
        if !restores_description {
            if interface.is_some() {
                return Err(MutexTransitionError::MissingInvariant(
                    previous
                        .clone()
                        .expect("declared invariant has an escrowed assertion"),
                ));
            }
            return Err("mutex release requires the same resource instance".into());
        }
        if restored.is_some()
            && (self
                .state
                .loan_ledger
                .as_ref()
                .is_some_and(|ledger| ledger.has_active_memory_loans())
                || self.state.loan_view_bindings.iter().next().is_some())
        {
            return Err("mutex release with a loan ledger is not supported".into());
        }
        let resources = if let Some(restored) = &restored {
            if !self.state.resources.contains_exact_representation(restored) {
                return Err(MutexTransitionError::MissingInvariant(restored.clone()));
            }
            self.state
                .resources
                .clone()
                .without_fact_delaying_normalization(restored, assumptions)
                .ok_or("mutex invariant cannot be returned to escrow")?
        } else {
            self.state.resources.clone()
        };
        let mut state = self.state.clone();
        let mut runtime_loan_transition = None;
        if let Some((hold, participant, usage)) = lifetime_hold {
            if state.loan_participant != Some(participant) {
                return Err("mutex guard lifetime hold belongs to another participant".into());
            }
            let loans = state
                .loan_ledger
                .as_ref()
                .ok_or("missing mutex guard lifetime loan")?;
            let (next, transition) = loans
                .release_mutex_use_hold_with_transition(
                    usage,
                    &guard.initialization.resource_fact(&guard.mutex),
                    hold,
                    participant,
                )
                .map_err(|_| MutexTransitionError::Refusal("missing mutex guard lifetime hold"))?;
            runtime_loan_transition = Some((loans.clone(), participant, transition));
            state.loan_ledger = Some(next);
        }
        state.resources = resources
            .without_fact_delaying_normalization(&guard_fact, assumptions)
            .ok_or("mutex guard cannot be consumed")?;
        state.mutex_ledger = Some(ledger.with_inserted(
            guard.mutex,
            MutexEntry::Unlocked {
                initialization: guard.initialization,
                invariant: restored,
                interface,
            },
        ));
        Ok(Self {
            state,
            runtime_loan_transition,
        })
    }
}

impl MutexLedger {
    fn fresh_identity() -> u64 {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_add(1, Ordering::Relaxed)
    }

    fn new() -> Self {
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
                entries: PersistentMap::default(),
                direct_loop_carriers: PersistentMap::default(),
                direct_loop_selection: Arc::new(Vec::new()),
                by_block: PersistentMap::default(),
                reserved: MutexStorageIndex::default(),
                by_provenance: PersistentMap::default(),
                ambiguous_automatic_storage: PersistentMap::default(),
                consumed_storage: PersistentMap::default(),
                locked_count: 0,
                return_obligation_count: 0,
                predecessor: None,
                changed_mutex: None,
            }),
        }
    }

    fn get(&self, mutex: &Pointer) -> Option<&MutexEntry> {
        self.storage.entries.get(mutex)
    }

    /// The type authenticated by this initialization, without exposing an
    /// owned payload or any of its current field observations.
    pub(super) fn protected_type(&self, mutex: &Pointer) -> Option<&super::ResourceDescription> {
        self.get(mutex)?
            .interface()
            .map(|interface| interface.description())
    }

    pub(super) fn check_use_acquisition(
        &self,
        fact: &CResourceFact,
    ) -> Result<(), MutexTransitionError> {
        let CResource::MutexUse(identity) = fact.resource() else {
            return Err("expected mutex_use authority".into());
        };
        match self.get(&identity.mutex) {
            Some(MutexEntry::Unlocked { initialization, .. })
                if identity.initialization == Some(initialization.0.0) =>
            {
                Ok(())
            }
            Some(MutexEntry::Locked { .. }) => Err("mutex is already guarded".into()),
            _ => Err(MutexTransitionError::MissingUse(identity.mutex.clone())),
        }
    }

    /// Read only the selected initialization's description. The call transfer
    /// must separately establish ownership and the participant's live loan.
    pub(super) fn interface_for_use(
        &self,
        fact: &CResourceFact,
    ) -> Result<Option<Arc<InitializedMutexInterface>>, ()> {
        let CResource::MutexUse(identity) = fact.resource() else {
            return Err(());
        };
        let Some(entry) = self.get(&identity.mutex) else {
            return Ok(None);
        };
        if identity.initialization != Some(entry.initialization().0.0) {
            return Err(());
        }
        let binding = entry.interface().cloned();
        if binding
            .as_ref()
            .is_some_and(|binding| !binding.matches_use(fact))
        {
            return Err(());
        }
        Ok(binding)
    }

    /// Forget observations after an opaque helper may have acquired a typed use.
    /// The checked call transfer supplies authority; this only weakens its escrow.
    ///
    /// The previous footprint is derived from current memory, which names it
    /// exactly while no other thread can have run since this thread last
    /// observed it; once it has been forgotten later derivations name only
    /// forgotten memory and forget nothing further. The fresh instance's
    /// footprint is not derived here: unfolding names it in current memory.
    pub(super) fn havoc_protected_for_call(
        state: &CState,
        mutex: &Pointer,
        definition: &super::CCompositeResourceDefinition,
        definitions: &[super::CCompositeResourceDefinition],
        assumptions: &PureFactContext,
        budget: &mut super::ExecutionBudget,
    ) -> Result<(CState, Vec<super::CMemoryRange>), MutexTransitionError> {
        let Some(ledger) = state.mutex_ledger.as_ref() else {
            return Ok((state.clone(), Vec::new()));
        };
        let Some(entry) = ledger.get(mutex) else {
            return Ok((state.clone(), Vec::new()));
        };
        let MutexEntry::Unlocked {
            initialization,
            invariant: Some(invariant),
            interface: Some(interface),
        } = entry
        else {
            return Err("typed mutex call requires an unlocked protected resource".into());
        };
        let CResource::Instance(previous) = invariant.resource() else {
            return Err("typed mutex call requires a folded protected resource".into());
        };
        let ranges = super::functions::checked_owned_memory_ranges(
            invariant,
            definitions,
            state,
            assumptions,
        )
        .ok_or("protected mutex resource has no checked memory footprint")?;
        let memory = if ranges.is_empty() {
            state.memory.clone()
        } else {
            let kept = ranges
                .iter()
                .any(super::CMemoryRange::is_unnamed_footprint)
                .then(|| {
                    super::functions::call_kept_ownership(
                        &state.resources,
                        definitions,
                        state,
                        assumptions,
                    )
                });
            state.memory.clone().with_call_memory_havoc(
                budget
                    .allocate_kernel_variable()
                    .map_err(|_| "protected memory forgetting exceeded its budget")?,
                &ranges,
                assumptions,
                kept.as_ref(),
            )
        };
        let fresh = assumed_protocol::mint_protected_instance(
            interface.description(),
            Some(definition),
            Some(previous.identity()),
            budget,
        )?;
        let mut next = state.clone();
        next.memory = memory;
        next.mutex_ledger = Some(ledger.with_inserted(
            mutex.clone(),
            MutexEntry::Unlocked {
                initialization: *initialization,
                invariant: Some(CResourceFact::own(CResource::Instance(fresh))),
                interface: Some(interface.clone()),
            },
        ));
        Ok((next, ranges))
    }

    /// Visit the queried block and provenance buckets that can alias it.
    /// A different symbolic spelling is not proof of disjoint storage.
    /// Separation facts discharge ambiguous footprints; fresh unrelated
    /// allocations and concrete objects are excluded by the index.
    fn storage_retirement_refusal(
        &self,
        allocation: &super::CMemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<super::CRuntimeError> {
        let block = &allocation.base().block;
        let direct = self
            .storage
            .by_block
            .get(block)
            .into_iter()
            .flat_map(|entries| entries.iter());
        let possible_aliases = StorageProvenance::of(block)
            .cross_block_candidates()
            .iter()
            .filter_map(|provenance| self.storage.by_provenance.get(provenance))
            .flat_map(|entries| entries.iter())
            .filter(|(mutex, _)| &mutex.block != block);
        let allocation_resource = CResource::Memory(allocation.clone());
        for (mutex, bytes) in direct.chain(possible_aliases) {
            crate::instrumentation::record_deterministic_work(1);
            let storage = CResource::Memory(super::CMemoryRange::new_with_element_width(
                mutex.clone(),
                0u32.into(),
                (*bytes).into(),
                1,
            ));
            // Heap byte lengths are unsigned. Do not compare them using
            // signed 32-bit element arithmetic: a large allocation or a
            // footprint crossing INT32_MAX could otherwise appear disjoint.
            let disjoint = (|| {
                if allocation.element_width() != 1 || allocation.constant_start() != Some(0) {
                    return None;
                }
                let extent = i64::from(allocation.constant_end()?);
                let delta = mutex.exact_element_delta_from_base(allocation.base(), 1, None)?;
                if !delta.is_constant() {
                    return None;
                }
                let end = delta.constant.checked_add(i64::from(*bytes))?;
                Some(end <= 0 || delta.constant >= extent)
            })();
            let stated_separation =
                assumptions.proves_exact(&super::Proposition::CResourceSeparate {
                    left: Box::new(allocation_resource.clone()),
                    right: Box::new(storage.clone()),
                }) || (allocation.element_width() == 1
                    && allocation.constant_start() == Some(0)
                    && allocation.constant_end().is_some_and(|extent| {
                        assumptions.proves_stated_byte_separation(
                            allocation.base(),
                            extent,
                            mutex,
                            *bytes,
                        )
                    }));
            if disjoint != Some(true) && !stated_separation {
                return Some(if disjoint == Some(false) {
                    super::CRuntimeError::MutexStorageInUse {
                        mutex: mutex.clone(),
                        allocation: allocation.base().clone(),
                    }
                } else {
                    super::CRuntimeError::MutexStorageSeparationRequired {
                        allocation: Box::new(allocation.clone()),
                        storage: Box::new(super::CMemoryRange::new_with_element_width(
                            mutex.clone(),
                            0u32.into(),
                            (*bytes).into(),
                            1,
                        )),
                    }
                });
            }
        }
        None
    }

    pub(super) fn live_resource(&self, mutex: &Pointer) -> Option<CResourceFact> {
        let (MutexEntry::Unlocked { initialization, .. }
        | MutexEntry::Locked { initialization, .. }
        | MutexEntry::ConditionalLoop { initialization, .. }) = self.get(mutex)?;
        Some(initialization.resource_fact(mutex))
    }

    pub(super) fn guard_resource(&self, mutex: &Pointer) -> Option<CResourceFact> {
        match self.get(mutex) {
            Some(MutexEntry::Locked { epoch, .. } | MutexEntry::ConditionalLoop { epoch, .. }) => {
                Some(CResourceFact::own(CResource::MutexGuard(
                    super::MutexIdentity {
                        epoch: Some(*epoch),
                        mutex: mutex.clone(),
                    },
                )))
            }
            _ => None,
        }
    }

    pub(super) fn held_condition(&self, mutex: &Pointer) -> ConditionTerm {
        match self.get(mutex) {
            Some(MutexEntry::ConditionalLoop { held, .. }) => held.clone(),
            entry => ConditionTerm::Constant(matches!(entry, Some(MutexEntry::Locked { .. }))),
        }
    }

    fn with_inserted(&self, mutex: Pointer, entry: MutexEntry) -> Self {
        let was_locked = matches!(
            self.get(&mutex),
            Some(MutexEntry::Locked { .. } | MutexEntry::ConditionalLoop { .. })
        );
        let now_locked = matches!(
            entry,
            MutexEntry::Locked { .. } | MutexEntry::ConditionalLoop { .. }
        );
        let had_return_obligation = self
            .get(&mutex)
            .is_some_and(MutexEntry::has_return_obligation);
        let has_return_obligation = entry.has_return_obligation();
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
                direct_loop_carriers: self.storage.direct_loop_carriers.clone(),
                direct_loop_selection: self.storage.direct_loop_selection.clone(),
                reserved: if self.get(&mutex).is_none() {
                    self.storage
                        .reserved
                        .changed(&mutex, entry.initialization().1, true)
                } else {
                    self.storage.reserved.clone()
                },
                by_provenance: if self.get(&mutex).is_none() {
                    let provenance = StorageProvenance::of(&mutex.block);
                    let entries = self
                        .storage
                        .by_provenance
                        .get(&provenance)
                        .cloned()
                        .unwrap_or_default()
                        .with_inserted(mutex.clone(), entry.initialization().1);
                    self.storage
                        .by_provenance
                        .with_inserted(provenance, entries)
                } else {
                    self.storage.by_provenance.clone()
                },
                by_block: if self.get(&mutex).is_none() {
                    let entries = self
                        .storage
                        .by_block
                        .get(&mutex.block)
                        .cloned()
                        .unwrap_or_default()
                        .with_inserted(mutex.clone(), entry.initialization().1);
                    self.storage
                        .by_block
                        .with_inserted(mutex.block.clone(), entries)
                } else {
                    self.storage.by_block.clone()
                },
                ambiguous_automatic_storage: if may_alias_automatic_storage(&mutex.block) {
                    self.storage
                        .ambiguous_automatic_storage
                        .with_inserted(mutex.clone(), ())
                } else {
                    self.storage.ambiguous_automatic_storage.clone()
                },
                consumed_storage: self.storage.consumed_storage.clone(),
                entries: self.storage.entries.with_inserted(mutex.clone(), entry),
                locked_count: self.storage.locked_count + usize::from(now_locked)
                    - usize::from(was_locked),
                return_obligation_count: self.storage.return_obligation_count
                    + usize::from(has_return_obligation)
                    - usize::from(had_return_obligation),
                predecessor: Some(self.storage.clone()),
                changed_mutex: Some(mutex.clone()),
            }),
        }
    }

    fn without(&self, mutex: &Pointer) -> Self {
        let was_locked = matches!(
            self.get(mutex),
            Some(MutexEntry::Locked { .. } | MutexEntry::ConditionalLoop { .. })
        );
        let had_return_obligation = self
            .get(mutex)
            .is_some_and(MutexEntry::has_return_obligation);
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
                reserved: self.storage.reserved.changed(
                    mutex,
                    self.get(mutex)
                        .expect("initialized mutex")
                        .initialization()
                        .1,
                    false,
                ),
                entries: self.storage.entries.without_key(mutex),
                direct_loop_carriers: self.storage.direct_loop_carriers.without_key(mutex),
                direct_loop_selection: self.storage.direct_loop_selection.clone(),
                ambiguous_automatic_storage: if may_alias_automatic_storage(&mutex.block) {
                    self.storage.ambiguous_automatic_storage.without_key(mutex)
                } else {
                    self.storage.ambiguous_automatic_storage.clone()
                },
                consumed_storage: self.storage.consumed_storage.without_key(mutex),
                by_provenance: {
                    let provenance = StorageProvenance::of(&mutex.block);
                    let entries = self
                        .storage
                        .by_provenance
                        .get(&provenance)
                        .expect("initialized mutex provenance")
                        .without_key(mutex);
                    if entries.is_empty() {
                        self.storage.by_provenance.without_key(&provenance)
                    } else {
                        self.storage
                            .by_provenance
                            .with_inserted(provenance, entries)
                    }
                },
                by_block: {
                    let entries = self
                        .storage
                        .by_block
                        .get(&mutex.block)
                        .expect("initialized mutex storage")
                        .without_key(mutex);
                    if entries.is_empty() {
                        self.storage.by_block.without_key(&mutex.block)
                    } else {
                        self.storage
                            .by_block
                            .with_inserted(mutex.block.clone(), entries)
                    }
                },
                locked_count: self.storage.locked_count - usize::from(was_locked),
                return_obligation_count: self.storage.return_obligation_count
                    - usize::from(had_return_obligation),
                predecessor: Some(self.storage.clone()),
                changed_mutex: Some(mutex.clone()),
            }),
        }
    }

    fn with_storage_consumed(&self, mutex: &Pointer) -> Self {
        let storage = &self.storage;
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
                entries: storage.entries.clone(),
                direct_loop_carriers: storage.direct_loop_carriers.clone(),
                direct_loop_selection: storage.direct_loop_selection.clone(),
                by_block: storage.by_block.clone(),
                reserved: storage.reserved.clone(),
                by_provenance: storage.by_provenance.clone(),
                ambiguous_automatic_storage: storage.ambiguous_automatic_storage.clone(),
                consumed_storage: storage.consumed_storage.with_inserted(mutex.clone(), ()),
                locked_count: storage.locked_count,
                return_obligation_count: storage.return_obligation_count,
                predecessor: Some(storage.clone()),
                changed_mutex: Some(mutex.clone()),
            }),
        }
    }

    fn storage_consumed(&self, mutex: &Pointer) -> bool {
        self.storage.consumed_storage.contains_key(mutex)
    }

    pub(super) fn has_locked_guard(&self) -> bool {
        self.storage.locked_count != 0
    }

    pub(super) fn has_any_mutex(&self) -> bool {
        !self.storage.entries.is_empty()
    }

    /// An unlocked empty mutex has no payload/guard return obligation yet.
    /// Lifecycle output contracts remain a separate gap.
    pub(super) fn has_return_obligation(&self) -> bool {
        self.storage.return_obligation_count != 0
    }

    /// Compare the protocol state after a loop body with its loop head. A
    /// state from another lineage is rejected.
    pub(super) fn check_protocol_state_since(
        &self,
        next: &Self,
    ) -> Result<(), MutexProtocolMismatch> {
        if self.storage.identity == next.storage.identity {
            return Ok(());
        }
        if self.storage.entries.len() != next.storage.entries.len()
            || self.storage.locked_count != next.storage.locked_count
            || self.storage.return_obligation_count != next.storage.return_obligation_count
        {
            return Err(MutexProtocolMismatch::State);
        }
        let mut changed = std::collections::BTreeSet::new();
        let mut cursor = next.storage.as_ref();
        while cursor.identity != self.storage.identity {
            let (Some(previous), Some(mutex)) = (&cursor.predecessor, &cursor.changed_mutex) else {
                return Err(MutexProtocolMismatch::State);
            };
            changed.insert(mutex);
            cursor = previous.as_ref();
        }
        for mutex in changed {
            match (self.get(mutex), next.get(mutex)) {
                (Some(left), Some(right)) if left.initialization() != right.initialization() => {
                    return Err(MutexProtocolMismatch::Initialization);
                }
                (Some(left), Some(right)) if !left.same_interface(right) => {
                    return Err(MutexProtocolMismatch::State);
                }
                (
                    Some(MutexEntry::Unlocked {
                        invariant: left, ..
                    }),
                    Some(MutexEntry::Unlocked {
                        invariant: right, ..
                    }),
                ) if left == right => {}
                (
                    Some(MutexEntry::Locked {
                        invariant: left,
                        epoch: left_epoch,
                        lifetime_hold: left_hold,
                        ..
                    }),
                    Some(MutexEntry::Locked {
                        invariant: right,
                        epoch: right_epoch,
                        lifetime_hold: right_hold,
                        ..
                    }),
                ) if left == right && left_epoch == right_epoch && left_hold == right_hold => {}
                (
                    Some(MutexEntry::ConditionalLoop {
                        epoch: left_epoch,
                        held: left_held,
                        ..
                    }),
                    Some(MutexEntry::ConditionalLoop {
                        epoch: right_epoch,
                        held: right_held,
                        ..
                    }),
                ) if left_epoch == right_epoch && left_held == right_held => {}
                (None, None) => {}
                _ => return Err(MutexProtocolMismatch::State),
            }
        }
        Ok(())
    }
}

impl MutexEntry {
    fn interface(&self) -> Option<&Arc<InitializedMutexInterface>> {
        match self {
            Self::Unlocked { interface, .. } | Self::Locked { interface, .. } => interface.as_ref(),
            Self::ConditionalLoop { .. } => None,
        }
    }

    fn same_interface(&self, other: &Self) -> bool {
        match (self.interface(), other.interface()) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }

    fn initialization(&self) -> MutexInitialization {
        match self {
            Self::Unlocked { initialization, .. }
            | Self::Locked { initialization, .. }
            | Self::ConditionalLoop { initialization, .. } => *initialization,
        }
    }

    fn has_return_obligation(&self) -> bool {
        !matches!(
            self,
            Self::Unlocked {
                invariant: None,
                ..
            }
        )
    }
}

impl std::fmt::Debug for MutexLedger {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("MutexLedger")
            .field("identity", &self.storage.identity)
            .field("count", &self.storage.entries.len())
            .finish()
    }
}

impl PartialEq for MutexLedger {
    fn eq(&self, other: &Self) -> bool {
        self.storage.identity == other.storage.identity
    }
}

impl Eq for MutexLedger {}

impl Hash for MutexLedger {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.storage.identity.hash(state);
    }
}

impl PartialOrd for MutexLedger {
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}

impl Ord for MutexLedger {
    fn cmp(&self, other: &Self) -> CmpOrdering {
        self.storage.identity.cmp(&other.storage.identity)
    }
}

fn same_instance(previous: &Option<CResourceFact>, restored: &Option<CResourceFact>) -> bool {
    match (previous, restored) {
        (
            Some(CResourceFact::Own(CResource::Instance(previous), previous_quantity)),
            Some(CResourceFact::Own(CResource::Instance(restored), restored_quantity)),
        ) => {
            previous_quantity.as_const() == Some(1)
                && restored_quantity.as_const() == Some(1)
                && previous.identity() == restored.identity()
                && previous.name() == restored.name()
                && previous.arguments() == restored.arguments()
                && previous.schema() == restored.schema()
                && previous.resource_arguments() == restored.resource_arguments()
        }
        (None, None) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn guard_spec(
        mutex: Pointer,
        snapshot: super::super::CResourceSnapshot,
    ) -> super::super::CResourceSpec {
        use super::super::*;
        CResourceSpec::new(
            CResourceTerm::MutexGuard {
                mutex: Box::new(CExpression::Value(CValue::pointer(mutex))),
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            snapshot,
        )
        .unwrap()
    }

    fn evaluate_guard(
        entry: &CState,
        current: &CState,
        mutex: Pointer,
        snapshot: super::super::CResourceSnapshot,
    ) -> CResourceFact {
        super::super::functions::evaluate_function_resource_spec_with_entry(
            entry,
            current,
            &guard_spec(mutex, snapshot),
            &PureFactContext::new(),
            &mut super::super::ExecutionBudget::beside_live_state(),
        )
        .unwrap()
        .unwrap()
    }

    #[test]
    fn assumed_lifetime_inputs_are_generative_and_keep_description_without_authority() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let mut input = CState::new();
        input.preserves_mutex_protocols = true;
        let description = live_resource(&input, &address, true).unwrap();
        input.resources = input.resources.unchecked_with_fact(description.clone());
        let first = bind_assumed_lifetime_inputs(input.clone(), &assumptions).unwrap();
        let second = bind_assumed_lifetime_inputs(input.clone(), &assumptions).unwrap();
        let first_owner = live_resource(&first, &address, false).unwrap();
        let second_owner = live_resource(&second, &address, false).unwrap();
        assert_ne!(first_owner, second_owner);
        assert_ne!(first_owner, description);
        assert!(!second.resources.satisfies_fact(&first_owner, &assumptions));
        let mut hidden = first.clone();
        hidden.resources = ResourceContext::new();
        assert_eq!(
            live_resource(&hidden, &address, false),
            Some(first_owner.clone())
        );
        assert!(!hidden.resources.satisfies_fact(&first_owner, &assumptions));
        assert!(first.mutex_ledger.is_none());
        assert!(
            MutexContext::new(first.clone())
                .destroy(&address, &assumptions)
                .is_err()
        );
        assert_eq!(
            live_resource(
                &bind_assumed_lifetime_inputs(first, &assumptions).unwrap(),
                &address,
                false
            ),
            Some(first_owner)
        );
        let mut duplicate = input.clone();
        duplicate.resources = duplicate.resources.unchecked_with_fact(description.clone());
        assert!(bind_assumed_lifetime_inputs(duplicate, &assumptions).is_err());
        input.resources = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::View(description.resource().clone()));
        assert!(bind_assumed_lifetime_inputs(input, &assumptions).is_err());
    }

    fn assumed_guard_state(address: &Pointer) -> CState {
        let mut state = CState::new();
        state.preserves_mutex_protocols = true;
        let description = guard_resource(&state, address, true).unwrap();
        state.resources = state.resources.unchecked_with_fact(description);
        state
    }

    #[test]
    fn assumed_guard_inputs_are_generative_and_preserve_entry_identity() {
        use super::super::CResourceSnapshot;
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let input = assumed_guard_state(&address);
        let first = bind_assumed_guard_inputs(input.clone(), &assumptions).unwrap();
        let second = bind_assumed_guard_inputs(input.clone(), &assumptions).unwrap();
        let required = evaluate_guard(&first, &second, address.clone(), CResourceSnapshot::Entry);
        let replacement =
            evaluate_guard(&first, &second, address.clone(), CResourceSnapshot::Current);
        assert_ne!(required, replacement);
        assert!(!second.resources.satisfies_fact(&required, &assumptions));
        assert!(!input.resources.satisfies_fact(&required, &assumptions));
        assert!(first.resources.satisfies_fact(&required, &assumptions));
        assert!(first.mutex_ledger.is_none());
        assert!(live_resource(&first, &address, false).is_some());
        assert!(!first.resources.satisfies_fact(
            &live_resource(&first, &address, false).unwrap(),
            &assumptions
        ));
        let unchanged = bind_assumed_guard_inputs(first.clone(), &assumptions).unwrap();
        assert_eq!(guard_resource(&unchanged, &address, false), Some(required));
        let concrete = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap()
            .acquire_current(&address, &assumptions)
            .unwrap();
        assert_ne!(
            guard_resource(concrete.state(), &address, false),
            guard_resource(&first, &address, false)
        );
        assert!(
            MutexContext::new(first)
                .release_current(&address, &assumptions)
                .is_err()
        );
    }

    #[test]
    fn assumed_guard_binding_rejects_invalid_occurrences_and_execution_states() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let input = assumed_guard_state(&address);
        let fact = input.resources.mutex_guard_at(&address).unwrap().clone();
        let mut duplicate = input.clone();
        duplicate.resources = duplicate.resources.unchecked_with_fact(fact.clone());
        assert!(bind_assumed_guard_inputs(duplicate, &assumptions).is_err());
        let mut viewed = input.clone();
        viewed.resources = super::super::ResourceContext::new()
            .unchecked_with_fact(CResourceFact::View(fact.resource().clone()));
        assert!(bind_assumed_guard_inputs(viewed, &assumptions).is_err());
        let mut executing = input.clone();
        executing.preserves_mutex_protocols = false;
        assert!(bind_assumed_guard_inputs(executing, &assumptions).is_err());
        let mut concrete = input;
        concrete.mutex_ledger = Some(MutexLedger::new());
        assert!(bind_assumed_guard_inputs(concrete, &assumptions).is_err());
    }

    #[test]
    fn assumed_guard_lookup_does_not_scan_unrelated_resources() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let mut state =
                bind_assumed_guard_inputs(assumed_guard_state(&address), &assumptions).unwrap();
            let expected = guard_resource(&state, &address, false).unwrap();
            for index in 0..size {
                state.resources =
                    state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("unrelated{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let ((found, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    guard_resource(&state, &address, false)
                })
            });
            assert_eq!(found, Some(expected));
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "guard lookup scans unrelated resources: {samples:?}"
            );
        }
    }

    #[test]
    fn preserved_guard_selects_entry_acquisition_after_reacquisition() {
        use super::super::CResourceSnapshot;
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let entry = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap()
            .acquire_current(&address, &assumptions)
            .unwrap();
        let next = entry
            .release_current(&address, &assumptions)
            .unwrap()
            .acquire_current(&address, &assumptions)
            .unwrap();
        let required = evaluate_guard(
            entry.state(),
            next.state(),
            address.clone(),
            CResourceSnapshot::Entry,
        );
        let replacement = evaluate_guard(
            entry.state(),
            next.state(),
            address,
            CResourceSnapshot::Current,
        );
        assert_ne!(required, replacement);
        assert!(
            entry
                .state()
                .resources
                .satisfies_fact(&required, &assumptions)
        );
        assert!(
            !next
                .state()
                .resources
                .satisfies_fact(&required, &assumptions)
        );
        assert!(
            next.state()
                .resources
                .satisfies_fact(&replacement, &assumptions)
        );
    }

    #[test]
    fn symbolic_guard_description_grants_no_authority_and_is_mutex_specific() {
        use super::super::CResourceSnapshot;
        let assumptions = PureFactContext::new();
        let mut state = CState::new();
        state.preserves_mutex_protocols = true;
        let guard = evaluate_guard(&state, &state, mutex(0), CResourceSnapshot::Current);
        let other = evaluate_guard(&state, &state, mutex(1), CResourceSnapshot::Current);
        assert_ne!(guard, other);
        assert!(!state.resources.satisfies_fact(&guard, &assumptions));
        state.resources = state
            .resources
            .try_compose_with_fact(guard.clone(), &assumptions)
            .unwrap();
        assert!(state.resources.satisfies_fact(&guard, &assumptions));
        assert!(!state.resources.satisfies_fact(&other, &assumptions));
        assert!(
            state
                .resources
                .clone()
                .try_compose_with_fact(guard, &assumptions)
                .is_err()
        );
        let concrete = MutexContext::new(CState::new())
            .initialize_empty(mutex(0), 40)
            .unwrap()
            .acquire_current(&mutex(0), &assumptions)
            .unwrap();
        let concrete_guard = evaluate_guard(
            concrete.state(),
            concrete.state(),
            mutex(0),
            CResourceSnapshot::Current,
        );
        assert!(
            !state
                .resources
                .satisfies_fact(&concrete_guard, &assumptions)
        );
    }

    #[test]
    #[ignore = "nightly: 2s in the parallel gate"]
    fn symbolic_guard_lookup_and_exchange_use_indexed_paths() {
        use super::super::CResourceSnapshot;
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16usize, 64, 256, 1024] {
            let mut state = CState::new();
            state.preserves_mutex_protocols = true;
            for index in 0..size {
                let fact = evaluate_guard(&state, &state, mutex(index), CResourceSnapshot::Current);
                state.resources = state
                    .resources
                    .try_compose_with_fact(fact, &assumptions)
                    .unwrap();
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let fact =
                    evaluate_guard(&state, &state, mutex(size / 2), CResourceSnapshot::Current);
                assert!(state.resources.satisfies_fact(&fact, &assumptions));
                let removed = state
                    .resources
                    .clone()
                    .without_fact_incrementally(&fact, &assumptions)
                    .unwrap();
                assert!(!removed.satisfies_fact(&fact, &assumptions));
                removed.try_compose_with_fact(fact, &assumptions).unwrap()
            });
            samples.push((size, work));
        }
        let baseline = samples[0].1;
        for &(size, work) in &samples {
            assert!(
                work > 0 && work <= baseline + 600 * (size.ilog2() as usize - 4),
                "symbolic guard exchange work: {samples:?}"
            );
        }
    }

    #[test]
    fn preserving_contract_freezes_every_mutex_transition() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (holding, _) = initialized.acquire(&address, &assumptions).unwrap();
        let mut state = holding.into_state();
        state.preserves_mutex_protocols = true;
        let frozen = MutexContext::new(state.clone());
        let message = "preserving mutex contracts cannot change mutex protocols";
        assert_eq!(frozen.initialize_empty(mutex(1), 40).err(), Some(message));
        assert_eq!(
            frozen.acquire(&address, &assumptions).err(),
            Some(MutexTransitionError::Refusal(message))
        );
        assert_eq!(
            frozen.release_current(&address, &assumptions).err(),
            Some(MutexTransitionError::Refusal(message))
        );
        assert_eq!(
            frozen.destroy(&address, &assumptions).err(),
            Some(MutexTransitionError::Refusal(message))
        );
        assert_eq!(frozen.state(), &state);
        let mut unframed = state.clone();
        unframed.preserves_mutex_protocols = false;
        assert_ne!(state, unframed);
    }

    #[test]
    fn guard_ownership_is_independent_of_heldness_and_required_by_unlock() {
        let assumptions = PureFactContext::new();
        let mutex = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(mutex.clone(), 40)
            .unwrap();
        let (holding, guard) = initialized.acquire(&mutex, &assumptions).unwrap();
        let fact = guard.resource_fact();
        let mut missing = holding.clone();
        missing.state.resources = missing
            .state
            .resources
            .clone()
            .without_fact(&fact, &assumptions)
            .unwrap();
        assert_eq!(
            missing
                .state
                .mutex_ledger
                .as_ref()
                .unwrap()
                .held_condition(&mutex),
            ConditionTerm::Constant(true)
        );
        assert_eq!(
            missing.release_current(&mutex, &assumptions).err(),
            Some(MutexTransitionError::MissingGuard(mutex.clone()))
        );
        // An explicit resource exchange can restore the same acquisition's
        // authority. Merely leaving the ledger locked could not do that.
        missing.state.resources = missing
            .state
            .resources
            .try_compose_with_fact(fact.clone(), &assumptions)
            .unwrap();
        let released = missing.release_current(&mutex, &assumptions).unwrap();
        assert!(!released.state.resources.satisfies_fact(&fact, &assumptions));
        let (mut reacquired, current) = released.acquire(&mutex, &assumptions).unwrap();
        assert_ne!(fact, current.resource_fact());
        reacquired.state.resources = reacquired
            .state
            .resources
            .clone()
            .without_fact(&current.resource_fact(), &assumptions)
            .unwrap()
            .try_compose_with_fact(fact, &assumptions)
            .unwrap();
        assert_eq!(
            reacquired.release_current(&mutex, &assumptions).err(),
            Some(MutexTransitionError::MissingGuard(mutex.clone()))
        );
        assert_eq!(
            reacquired
                .release_with_invariant(guard, None, &assumptions)
                .err(),
            Some(MutexTransitionError::Refusal(
                "mutex guard does not match the current holder"
            ))
        );
    }

    #[test]
    fn unlock_reports_guard_then_selected_invariant_without_changing_state() {
        let assumptions = PureFactContext::new();
        let protected = invariant(1, 7);
        let initialized = context(protected.clone())
            .publish(mutex(0), protected.clone(), &assumptions, 40)
            .unwrap();
        let (mut held, guard) = initialized.acquire(&mutex(0), &assumptions).unwrap();
        let guard_fact = guard.resource_fact();
        held.state.resources = held
            .state
            .resources
            .clone()
            .without_fact(&protected, &assumptions)
            .unwrap()
            .without_fact(&guard_fact, &assumptions)
            .unwrap();
        let before = held.state().clone();
        assert_eq!(
            held.release_current(&mutex(0), &assumptions).err(),
            Some(MutexTransitionError::MissingGuard(mutex(0)))
        );
        assert_eq!(held.state(), &before);
        held.state.resources = held
            .state
            .resources
            .clone()
            .try_compose_with_fact(guard_fact, &assumptions)
            .unwrap();
        // Another instance of the same resource is not the protected one.
        held.state.resources = held
            .state
            .resources
            .clone()
            .try_compose_with_fact(invariant(2, 7), &assumptions)
            .unwrap();
        let before = held.state().clone();
        let error = held.release_current(&mutex(0), &assumptions).err().unwrap();
        assert_eq!(
            error,
            MutexTransitionError::MissingInvariant(protected.clone())
        );
        assert_eq!(
            error.into_runtime_error(&mutex(0)),
            super::super::CRuntimeError::MissingMutexInvariant {
                resource: Box::new(protected),
                supplied: None,
            }
        );
        assert_eq!(held.state(), &before);
        // Restoration permits updated fields; the requirement is the selected
        // resource instance, not its model values at initialization.
        held.state.resources = held
            .state
            .resources
            .clone()
            .try_compose_with_fact(invariant(1, 8), &assumptions)
            .unwrap();
        held.release_current(&mutex(0), &assumptions).unwrap();
    }

    #[test]
    fn guard_algebra_is_exclusive_unit_ownership_without_views_or_memory() {
        let assumptions = PureFactContext::new();
        let (holding, guard) = MutexContext::new(CState::new())
            .initialize_empty(mutex(0), 40)
            .unwrap()
            .acquire(&mutex(0), &assumptions)
            .unwrap();
        let fact = guard.resource_fact();
        let resources = &holding.state.resources;
        assert!(fact.core().is_none());
        assert!(fact.core_with_assumptions(&assumptions).is_none());
        assert!(fact.memory_range().is_none());
        assert_eq!(
            super::super::thread_confinement::confined_resource_name(&fact, &[]),
            Some("mutex guard")
        );
        assert!(
            resources
                .clone()
                .try_compose_with_fact(fact.clone(), &assumptions)
                .is_err()
        );
        assert!(
            resources
                .clone()
                .unchecked_with_fact(fact.clone())
                .normalized(&assumptions)
                .validity_error(&assumptions)
                .is_some()
        );
        for invalid in [
            CResourceFact::View(fact.resource().clone()),
            CResourceFact::own_quantity(
                fact.resource().clone(),
                super::super::Bitvector32Term::Constant(0),
            ),
            CResourceFact::own_quantity(
                fact.resource().clone(),
                super::super::Bitvector32Term::Constant(2),
            ),
        ] {
            assert!(!resources.satisfies_fact(&invalid, &assumptions));
            assert!(
                super::super::ResourceContext::new()
                    .try_compose_with_fact(invalid.clone(), &assumptions)
                    .is_err()
            );
            assert!(
                resources
                    .clone()
                    .without_fact(&invalid, &assumptions)
                    .is_none()
            );
        }
        let empty = resources.clone().without_fact(&fact, &assumptions).unwrap();
        assert!(!empty.satisfies_fact(&fact, &assumptions));
        assert!(empty.clone().without_fact(&fact, &assumptions).is_none());
        assert!(
            empty
                .try_compose_with_fact(fact, &assumptions)
                .unwrap()
                .is_valid(&assumptions)
        );
    }

    #[test]
    fn use_resource_algebra_is_exclusive_unit_ownership_without_views_or_memory() {
        let assumptions = PureFactContext::new();
        let (lent, loan) = MutexContext::new(CState::new())
            .initialize_empty(mutex(0), 40)
            .unwrap()
            .lend_use(&mutex(0), &assumptions)
            .unwrap();
        let fact = lent.owned_use_resource(loan.usage).unwrap();
        let resources = &lent.state.resources;
        assert!(fact.core().is_none());
        assert!(fact.core_with_assumptions(&assumptions).is_none());
        assert!(fact.memory_range().is_none());
        assert_eq!(
            super::super::thread_confinement::confined_resource_name(&fact, &[]),
            Some("mutex use")
        );
        assert!(
            resources
                .clone()
                .try_compose_with_fact(fact.clone(), &assumptions)
                .is_err()
        );
        assert!(
            resources
                .clone()
                .unchecked_with_fact(fact.clone())
                .normalized(&assumptions)
                .validity_error(&assumptions)
                .is_some()
        );
        for invalid in [
            CResourceFact::View(fact.resource().clone()),
            CResourceFact::own_quantity(
                fact.resource().clone(),
                super::super::Bitvector32Term::Constant(0),
            ),
            CResourceFact::own_quantity(
                fact.resource().clone(),
                super::super::Bitvector32Term::Constant(2),
            ),
        ] {
            assert!(!resources.satisfies_fact(&invalid, &assumptions));
            assert!(
                super::super::ResourceContext::new()
                    .try_compose_with_fact(invalid.clone(), &assumptions)
                    .is_err()
            );
            assert!(
                resources
                    .clone()
                    .without_fact(&invalid, &assumptions)
                    .is_none()
            );
        }
        let empty = resources.clone().without_fact(&fact, &assumptions).unwrap();
        assert!(!empty.satisfies_fact(&fact, &assumptions));
        assert!(empty.clone().without_fact(&fact, &assumptions).is_none());
        assert!(
            empty
                .try_compose_with_fact(fact, &assumptions)
                .unwrap()
                .is_valid(&assumptions)
        );
    }

    #[test]
    fn guard_transitions_touch_only_logarithmic_index_paths() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16usize, 64, 256, 1024] {
            let mut context = MutexContext::new(CState::new());
            for index in 0..size {
                context = context.initialize_empty(mutex(index), 40).unwrap();
                context = context
                    .acquire_current(&mutex(index), &assumptions)
                    .unwrap();
            }
            let target = mutex(size);
            context = context.initialize_empty(target.clone(), 40).unwrap();
            let ((holding, released), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let holding = context.acquire_current(&target, &assumptions).unwrap();
                    let released = holding.release_current(&target, &assumptions).unwrap();
                    (holding, released)
                });
            assert_eq!(holding.state.resources.facts().len(), 2 * (size + 1));
            assert_eq!(released.state.resources.facts().len(), 2 * size + 1);
            samples.push((size, work));
        }
        let baseline = samples[0].1;
        for &(size, work) in &samples {
            assert!(
                work > 0 && work <= baseline + 600 * (size.ilog2() as usize - 4),
                "guard exchange work: {samples:?}"
            );
        }
    }

    #[test]
    fn lifetime_owner_is_required_independently_of_initialization_metadata() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let live = live_resource(initialized.state(), &address, false).unwrap();
        let mut missing = initialized.clone();
        missing.state.resources = missing
            .state
            .resources
            .clone()
            .without_fact(&live, &assumptions)
            .unwrap();
        let before = missing.state().clone();
        assert_eq!(
            missing.destroy(&address, &assumptions).err(),
            Some(MutexTransitionError::MissingLive(address.clone()))
        );
        assert_eq!(
            missing.acquire_current(&address, &assumptions).err(),
            Some(MutexTransitionError::MissingLive(address.clone()))
        );
        assert_eq!(missing.state(), &before);
        assert_eq!(
            MutexTransitionError::MissingLive(address.clone()).into_runtime_error(&address),
            super::super::CRuntimeError::MissingMutexLive {
                mutex: address.clone()
            }
        );
        // Describing the resource doesn't restore it; checked resource transfer does.
        assert_eq!(
            live_resource(missing.state(), &address, false),
            Some(live.clone())
        );
        missing.state.resources = missing
            .state
            .resources
            .clone()
            .try_compose_with_fact(live.clone(), &assumptions)
            .unwrap();
        let destroyed = missing.destroy(&address, &assumptions).unwrap();
        assert!(destroyed.state.resources.facts().is_empty());
        assert!(live_resource(destroyed.state(), &address, false).is_none());
    }

    #[test]
    fn old_lifetime_owner_cannot_authorize_reinitialized_mutex() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let first = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let old = live_resource(first.state(), &address, false).unwrap();
        let mut next =
            MutexContext::new(first.destroy(&address, &assumptions).unwrap().into_state())
                .initialize_empty(address.clone(), 40)
                .unwrap();
        let fresh = live_resource(next.state(), &address, false).unwrap();
        assert_ne!(old, fresh);
        next.state.resources = next
            .state
            .resources
            .clone()
            .without_fact(&fresh, &assumptions)
            .unwrap()
            .try_compose_with_fact(old, &assumptions)
            .unwrap();
        assert_eq!(
            next.destroy(&address, &assumptions).err(),
            Some(MutexTransitionError::MissingLive(address.clone()))
        );
        assert_eq!(
            next.acquire_current(&address, &assumptions).err(),
            Some(MutexTransitionError::MissingLive(address))
        );
    }

    #[test]
    fn lifetime_and_guard_are_distinct_exclusive_resource_families() {
        let assumptions = PureFactContext::new();
        let identity = super::super::MutexIdentity {
            epoch: Some(17),
            mutex: mutex(0),
        };
        let live = CResourceFact::own(CResource::MutexLive(identity.clone()));
        let guard = CResourceFact::own(CResource::MutexGuard(identity));
        let resources = super::super::ResourceContext::new()
            .try_compose_with_fact(live.clone(), &assumptions)
            .unwrap();
        assert!(!resources.satisfies_fact(&guard, &assumptions));
        assert!(live.core().is_none());
        assert!(live.core_with_assumptions(&assumptions).is_none());
        assert!(live.memory_range().is_none());
        assert!(
            resources
                .clone()
                .try_compose_with_fact(live.clone(), &assumptions)
                .is_err()
        );
        assert!(
            resources
                .clone()
                .unchecked_with_fact(live.clone())
                .normalized(&assumptions)
                .validity_error(&assumptions)
                .is_some()
        );
        // Equal numeric epochs from the two generative namespaces do not collide.
        assert!(
            resources
                .clone()
                .try_compose_with_fact(guard, &assumptions)
                .is_ok()
        );
        for invalid in [
            CResourceFact::View(live.resource().clone()),
            CResourceFact::own_quantity(live.resource().clone(), 0u32.into()),
            CResourceFact::own_quantity(live.resource().clone(), 2u32.into()),
        ] {
            assert!(!resources.satisfies_fact(&invalid, &assumptions));
            assert!(
                resources
                    .clone()
                    .without_fact(&invalid, &assumptions)
                    .is_none()
            );
            assert!(
                super::super::ResourceContext::new()
                    .try_compose_with_fact(invalid.clone(), &assumptions)
                    .is_err()
            );
            assert!(
                super::super::ResourceContext::new()
                    .unchecked_with_fact(invalid)
                    .validity_error(&assumptions)
                    .is_some()
            );
        }
    }

    #[test]
    fn lifetime_transitions_do_not_scan_unrelated_owners() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16usize, 64, 256, 1024] {
            let mut context = MutexContext::new(CState::new());
            for index in 0..size {
                context = context.initialize_empty(mutex(index), 40).unwrap();
            }
            let target = mutex(size);
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .initialize_empty(target.clone(), 40)
                    .unwrap()
                    .destroy(&target, &assumptions)
                    .unwrap()
            });
            assert_eq!(restored.state.resources, context.state.resources);
            samples.push((size, work));
        }
        let baseline = samples[0].1;
        for &(size, work) in &samples {
            assert!(
                work > 0 && work <= baseline + 600 * (size.ilog2() as usize - 4),
                "lifecycle exchange work: {samples:?}"
            );
        }
    }

    #[test]
    fn empty_mutex_supplies_and_consumes_exclusive_guard() {
        let assumptions = PureFactContext::new();
        let mutex = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(mutex.clone(), 40)
            .unwrap();
        assert!(
            !initialized
                .state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .has_return_obligation()
        );
        assert_eq!(initialized.state().resources.facts().len(), 1);
        assert_eq!(
            initialized.initialize_empty(mutex.clone(), 40).err(),
            Some("mutex is already initialized")
        );

        let held = initialized.acquire_current(&mutex, &assumptions).unwrap();
        assert!(
            held.state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .has_return_obligation()
        );
        assert_eq!(held.state().resources.facts().len(), 2);
        assert!(
            held.state()
                .resources
                .facts()
                .iter()
                .any(|fact| matches!(fact.resource(), CResource::MutexGuard(_)))
        );
        assert!(held.acquire_current(&mutex, &assumptions).is_err());
        assert_eq!(
            held.destroy(&mutex, &assumptions).err(),
            Some(MutexTransitionError::Refusal("cannot destroy a held mutex"))
        );

        let unlocked = held.release_current(&mutex, &assumptions).unwrap();
        assert!(
            !unlocked
                .state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .has_return_obligation()
        );
        assert_eq!(unlocked.state().resources.facts().len(), 1);
        let destroyed = unlocked.destroy(&mutex, &assumptions).unwrap();
        assert!(destroyed.state().mutex_ledger.is_none());
    }

    fn automatic_holder() -> (CState, Pointer) {
        let state = CState::new().with_local("holder", super::super::int32(0));
        let slot = state.locals().slot("holder").unwrap().clone();
        let state =
            state.with_memory(super::super::CMemory::new().with_block(slot.block.clone(), 88));
        (state, slot.offset_by_bytes(8))
    }

    #[test]
    fn automatic_storage_requires_destroy_even_without_visible_authority() {
        let assumptions = PureFactContext::new();
        let (state, address) = automatic_holder();
        let initialized = MutexContext::new(state)
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let names = vec!["holder".to_string()];
        let expected = super::super::CRuntimeError::MutexStorageScopeEnd {
            local: "holder".into(),
            mutex: address.clone(),
            may_alias: false,
        };
        for held in [false, true] {
            let mut context = if held {
                initialized.acquire_current(&address, &assumptions).unwrap()
            } else {
                initialized.clone()
            };
            // Folding or otherwise hiding the atoms cannot erase a storage dependency.
            context.state.resources = super::super::ResourceContext::new();
            let before = context.state().clone();
            assert_eq!(
                super::super::eval::end_scope_automatic_lifetimes(context.state(), &names),
                Err(expected.clone())
            );
            assert_eq!(context.state(), &before);
        }
        let destroyed = initialized.destroy(&address, &assumptions).unwrap();
        let expired =
            super::super::eval::end_scope_automatic_lifetimes(destroyed.state(), &names).unwrap();
        assert!(!expired.memory().has_block(&address.block));
        assert!(expired.locals().get("holder").is_none());
    }

    #[test]
    fn every_scope_exit_outcome_checks_initialized_mutexes() {
        use super::super::*;
        let (state, address) = automatic_holder();
        let state = MutexContext::new(state)
            .initialize_empty(address, 40)
            .unwrap()
            .into_state();
        let outcomes = [
            CStatementOutcome::Normal(Box::new(state.clone())),
            CStatementOutcome::Break(Box::new(state.clone())),
            CStatementOutcome::Continue(Box::new(state.clone())),
            CStatementOutcome::Return {
                value: int32(0),
                state: Box::new(state.clone()),
            },
            CStatementOutcome::Throw {
                value: int32(0),
                state: Box::new(state.clone()),
            },
            CStatementOutcome::Jump {
                target: CControlTargetId(1),
                state: Box::new(state.clone()),
            },
        ];
        for outcome in outcomes {
            let paths = eval::paths_after_scope_exit(
                vec![CStatementExecutionPath::new(outcome, vec![].into(), vec![])],
                &["holder".into()],
            );
            assert!(matches!(
                paths[0].outcome,
                CStatementOutcome::RuntimeError(CRuntimeError::MutexStorageScopeEnd { .. })
            ));
        }
        for continue_after in [false, true] {
            let paths = eval::execute_c_statement_paths(
                &state,
                &CStatement::ForStep {
                    step: Box::new(CStatement::Skip),
                    exited_locals: vec!["holder".into()],
                    continue_after,
                },
                &PureFactContext::new(),
                CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert!(matches!(
                paths[0].outcome,
                CStatementOutcome::RuntimeError(CRuntimeError::MutexStorageScopeEnd { .. })
            ));
        }
    }

    #[test]
    fn automatic_storage_index_preserves_other_mutexes_in_the_same_object() {
        let assumptions = PureFactContext::new();
        let (state, first) = automatic_holder();
        let second = first.offset_by_bytes(40);
        let context = MutexContext::new(state)
            .initialize_empty(first.clone(), 40)
            .unwrap()
            .initialize_empty(second.clone(), 40)
            .unwrap()
            .destroy(&first, &assumptions)
            .unwrap();
        assert_eq!(
            automatic_storage_refusal(context.state(), "holder", &first.block),
            Some(super::super::CRuntimeError::MutexStorageScopeEnd {
                local: "holder".into(),
                mutex: second.clone(),
                may_alias: false,
            })
        );
        let context = context.destroy(&second, &assumptions).unwrap();
        assert!(automatic_storage_refusal(context.state(), "holder", &first.block).is_none());
    }

    #[test]
    fn automatic_storage_cannot_ignore_a_symbolic_mutex_alias() {
        let assumptions = PureFactContext::new();
        let (state, address) = automatic_holder();
        let symbolic = Pointer::symbolic(super::super::Variable(72_000));
        assert!(!symbolic.block.proven_distinct(&address.block));
        let context = MutexContext::new(state)
            .initialize_empty(symbolic.clone(), 40)
            .unwrap();
        assert_eq!(
            automatic_storage_refusal(context.state(), "holder", &address.block),
            Some(super::super::CRuntimeError::MutexStorageScopeEnd {
                local: "holder".into(),
                mutex: symbolic.clone(),
                may_alias: true,
            })
        );
        let held = context.acquire_current(&symbolic, &assumptions).unwrap();
        assert!(automatic_storage_refusal(held.state(), "holder", &address.block).is_some());
        let destroyed = held
            .release_current(&symbolic, &assumptions)
            .unwrap()
            .destroy(&symbolic, &assumptions)
            .unwrap();
        assert!(automatic_storage_refusal(destroyed.state(), "holder", &address.block).is_none());
    }

    #[test]
    fn automatic_storage_query_does_not_scan_unrelated_initializations() {
        let mut samples = Vec::new();
        for size in [16usize, 64, 256, 1024] {
            let (state, address) = automatic_holder();
            let mut context = MutexContext::new(state);
            for index in 0..size {
                context = context.initialize_empty(mutex(index), 40).unwrap();
            }
            let (result, unrelated_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    automatic_storage_refusal(context.state(), "holder", &address.block)
                });
            assert!(result.is_none());
            context = context.initialize_empty(address.clone(), 40).unwrap();
            let (result, overlapping_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    automatic_storage_refusal(context.state(), "holder", &address.block)
                });
            assert!(result.is_some());
            samples.push((size, unrelated_work, overlapping_work));
        }
        let (_, absent, present) = samples[0];
        for (size, unrelated, overlapping) in &samples {
            let allowance = 32 * (size.ilog2() as usize - 4);
            assert!(
                *unrelated <= absent + allowance && *overlapping <= present + allowance,
                "scope query work must be logarithmic: {samples:?}"
            );
        }
    }

    #[test]
    fn reserved_storage_survives_unlock_and_hidden_authority_until_destroy() {
        use super::super::*;
        let base = mutex(91_100);
        let address = base.offset_by_bytes(8);
        let assumptions = PureFactContext::new();
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let held = initialized.acquire_current(&address, &assumptions).unwrap();
        let unlocked = held.release_current(&address, &assumptions).unwrap();
        let mut hidden = unlocked.state().clone();
        hidden.resources = ResourceContext::new();
        for state in [initialized.state(), held.state(), unlocked.state(), &hidden] {
            for (offset, bytes) in [(8, 1), (47, 1), (4, 8), (0, 56)] {
                let write = storage_range(&base.offset_by_bytes(offset), bytes);
                assert!(matches!(
                    storage_write_refusal(state, &write, &assumptions),
                    Some(CRuntimeError::MutexStorageWrite { .. })
                ));
            }
            for (offset, bytes) in [(0, 8), (48, 8)] {
                assert!(
                    storage_write_refusal(
                        state,
                        &storage_range(&base.offset_by_bytes(offset), bytes),
                        &assumptions
                    )
                    .is_none()
                );
            }
            // Element indices are not byte offsets: this eight-byte write
            // covers byte 47 even though its index is outside 0..40.
            let mixed =
                CMemoryRange::new_with_element_width(base.clone(), 5u32.into(), 6u32.into(), 8);
            assert!(storage_write_refusal(state, &mixed, &assumptions).is_some());
        }
        let destroyed = unlocked.destroy(&address, &assumptions).unwrap();
        assert!(
            storage_write_refusal(
                destroyed.state(),
                &storage_range(&address, 40),
                &assumptions
            )
            .is_none()
        );
        assert!(
            storage_write_refusal(
                initialized.state(),
                &storage_range(&address, 40),
                &assumptions
            )
            .is_some(),
            "destroy must not mutate the predecessor's reservation"
        );
    }

    #[test]
    fn ordinary_c_store_rejects_live_storage_and_accepts_destroyed_storage() {
        use super::super::*;
        let (state, address) = automatic_holder();
        register_block_alignment(&address.block, 8);
        let context = MutexContext::new(state)
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let statement = c_typed_store(
            CExpression::Value(CValue::pointer(address.clone())),
            c_int32_literal(7),
            CType::Int32,
        );
        let assumptions = PureFactContext::new();
        let outcome = eval::execute_c_statement(context.state(), &statement, &assumptions);
        assert!(
            matches!(
                outcome,
                Some(CStatementOutcome::RuntimeError(
                    CRuntimeError::MutexStorageWrite { .. }
                ))
            ),
            "{outcome:?}"
        );
        let destroyed = context.destroy(&address, &assumptions).unwrap();
        let Some(CStatementOutcome::Normal(after)) =
            eval::execute_c_statement(destroyed.state(), &statement, &assumptions)
        else {
            panic!("destroyed storage should be writable");
        };
        assert_eq!(
            after.memory().load(&address),
            CExpressionOutcome::Value(int32(7))
        );
    }

    #[test]
    fn checked_runtime_transitions_forget_reserved_representation_values() {
        use super::super::*;
        let assumptions = PureFactContext::new();
        for name in [
            "pthread_mutex_lock",
            "pthread_mutex_unlock",
            "pthread_mutex_destroy",
        ] {
            let (state, address) = automatic_holder();
            let mut context = MutexContext::new(state)
                .initialize_empty(address.clone(), 40)
                .unwrap();
            if name == "pthread_mutex_unlock" {
                context = context.acquire_current(&address, &assumptions).unwrap();
            }
            let state = context.state().clone().with_memory(
                context
                    .state()
                    .memory()
                    .clone()
                    .store(address.clone(), int8(17)),
            );
            let environment = CExecutionEnvironment::new().with_modeled_pthread_binding(Some(
                crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
            ));
            let statement = CStatement::Call {
                function_name: name.into(),
                arguments: vec![CExpression::Value(CValue::pointer(address.clone()))],
            };
            let paths = eval::execute_c_statement_paths(
                &state,
                &statement,
                &assumptions,
                CExecutionContext::execute_bodies(&environment),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let CStatementOutcome::Normal(after) = &paths[0].outcome else {
                panic!("{name}: {paths:?}");
            };
            assert_ne!(
                after.memory().load(&address),
                CExpressionOutcome::Value(int8(17)),
                "{name}"
            );
        }
    }

    #[test]
    fn reservation_requires_separation_from_a_symbolic_alias() {
        use super::super::*;
        let address = Pointer::symbolic(Variable(91_101));
        let context = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let write = storage_range(&mutex(91_102), 8);
        let assumptions = PureFactContext::new();
        assert!(storage_write_refusal(context.state(), &write, &assumptions).is_some());
        let separated = assumptions
            .clone()
            .assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(write.clone())),
                right: Box::new(CResource::Memory(storage_range(&address, 40))),
            });
        assert!(storage_write_refusal(context.state(), &write, &separated).is_none());
    }

    #[test]
    fn assumed_guard_projection_distinguishes_guards_from_use_storage() {
        use super::super::*;
        let held = Pointer::symbolic(Variable(91_201));
        let requested = Pointer::symbolic(Variable(91_202));
        let mut state = CState::new();
        state.mutex_input_reservations = MutexInputReservations::from_ranges_and_guards(
            [storage_range(&requested, 40)],
            [storage_range(&held, 40)],
        );
        let assumptions = PureFactContext::new();
        assert!(abstract_guard_acquisition_refusal(&state, &requested, &assumptions).is_some());
        let separated = assumptions
            .clone()
            .assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(storage_range(&requested, 40))),
                right: Box::new(CResource::Memory(storage_range(&held, 40))),
            });
        assert!(abstract_guard_acquisition_refusal(&state, &requested, &separated).is_none());

        state.mutex_input_reservations =
            MutexInputReservations::from_ranges_and_guards([storage_range(&requested, 40)], []);
        assert!(abstract_guard_acquisition_refusal(&state, &requested, &assumptions).is_none());
    }

    #[test]
    fn unresolved_assumed_guard_blocks_external_acquisition_only() {
        let mut state = CState::new();
        state.mutex_input_reservations = MutexInputReservations::from_ranges_and_guards(
            [],
            [super::super::CMemoryRange::unnamed_footprint()],
        );
        let assumptions = PureFactContext::new();
        assert!(
            abstract_guard_acquisition_refusal(
                &state,
                &Pointer::symbolic(super::super::Variable(91_203)),
                &assumptions,
            )
            .is_some()
        );
        assert!(
            abstract_guard_acquisition_refusal(
                &state,
                &Pointer {
                    block: "local:f:fresh_mutex".into(),
                    offset: super::super::PointerOffsetTerm::Constant(0),
                },
                &assumptions,
            )
            .is_none()
        );
    }

    #[test]
    fn initialization_rejects_an_interior_overlap_and_accepts_adjacent_storage() {
        use super::super::*;
        let base = mutex(91_103);
        register_block_alignment(&base.block, 8);
        let state = CState::new().with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own_memory(storage_range(&base, 128))),
        );
        let initialized = MutexContext::new(state)
            .initialize_empty(base.clone(), 40)
            .unwrap();
        let assumptions = PureFactContext::new();
        for offset in [0, 8, 32] {
            assert!(matches!(
                initialization_storage_refusal(
                    initialized.state(),
                    &base.offset_by_bytes(offset),
                    40,
                    8,
                    &assumptions
                ),
                Some(CRuntimeError::MutexStorageWrite { .. })
            ));
        }
        assert!(
            initialization_storage_refusal(
                initialized.state(),
                &base.offset_by_bytes(40),
                40,
                8,
                &assumptions
            )
            .is_none()
        );
    }

    #[test]
    fn abstract_reservation_is_retained_without_granting_runtime_authority() {
        use super::super::*;
        let address = mutex(91_201);
        let mut state = CState::new();
        state.preserves_mutex_protocols = true;
        state.mutex_input_reservations =
            MutexInputReservations::from_ranges([storage_range(&address, 40)]);
        let assumptions = PureFactContext::new();
        let snapshot = state.clone();
        assert!(state.mutex_ledger.is_none());
        assert!(state.resources.facts().is_empty());
        // Ownership, not the reservation, keeps a body's writes off its input
        // mutex storage: no memory the body can own reaches it.
        assert!(storage_write_refusal(&state, &storage_range(&address, 4), &assumptions).is_none());
        assert!(
            storage_retirement_refusal(&state, &storage_range(&address, 64), &assumptions)
                .is_some()
        );
        assert!(
            MutexContext::new(state.clone())
                .destroy(&address, &assumptions)
                .is_err()
        );
        state.resources = ResourceContext::new();
        assert_eq!(state, snapshot);
        let mut forged = state.clone();
        forged.mutex_input_reservations = None;
        assert_ne!(state, forged);
        assert!(!state.shares_non_memory_storage_with(&forged));
    }

    #[test]
    fn unresolved_input_storage_does_not_refuse_writes() {
        use super::super::*;
        let (mut state, local) = automatic_holder();
        state.mutex_input_reservations =
            MutexInputReservations::from_ranges([CMemoryRange::unnamed_footprint()]);
        let assumptions = PureFactContext::new();
        assert!(
            storage_write_refusal(&state, &storage_range(&mutex(91_203), 4), &assumptions)
                .is_none()
        );
        assert!(storage_write_refusal(&state, &storage_range(&local, 4), &assumptions).is_none());
    }

    #[test]
    fn abstract_reservation_queries_do_not_scan_other_mutexes_in_one_object() {
        use super::super::*;
        let base = mutex(91_202);
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut state = CState::new();
            state.mutex_input_reservations = MutexInputReservations::from_ranges(
                (0..size).map(|index| storage_range(&base.offset_by_bytes(index * 64), 40)),
            );
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                for index in [0, size / 2, size - 1] {
                    assert!(
                        storage_retirement_refusal(
                            &state,
                            &storage_range(&base.offset_by_bytes(index * 64 + 39), 1),
                            &assumptions
                        )
                        .is_some()
                    );
                    assert!(
                        storage_retirement_refusal(
                            &state,
                            &storage_range(&base.offset_by_bytes(index * 64 + 40), 8),
                            &assumptions
                        )
                        .is_none()
                    );
                }
            });
            samples.push(work);
        }
        for window in samples.windows(2) {
            assert!(
                window[1] <= window[0] + 2048,
                "abstract reservation query work: {samples:?}"
            );
        }
    }

    #[test]
    fn reservation_index_queries_same_object_in_logarithmic_work() {
        use super::super::*;
        let assumptions = PureFactContext::new();
        let base = mutex(91_104);
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut context = MutexContext::new(CState::new());
            for index in 0..size {
                context = context
                    .initialize_empty(base.offset_by_bytes(index * 64), 40)
                    .unwrap();
            }
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                for index in [0, size / 2, size - 1] {
                    assert!(
                        storage_write_refusal(
                            context.state(),
                            &storage_range(&base.offset_by_bytes(index * 64 + 39), 1),
                            &assumptions
                        )
                        .is_some()
                    );
                    assert!(
                        storage_write_refusal(
                            context.state(),
                            &storage_range(&base.offset_by_bytes(index * 64 + 40), 24),
                            &assumptions
                        )
                        .is_none()
                    );
                }
                let selected = base.offset_by_bytes((size / 2) * 64);
                let next = context.destroy(&selected, &assumptions).unwrap();
                assert!(
                    storage_write_refusal(
                        next.state(),
                        &storage_range(&selected, 40),
                        &assumptions
                    )
                    .is_none()
                );
            });
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] + 4096,
                "reservation queries/updates must grow logarithmically: {samples:?}"
            );
        }
    }

    #[test]
    fn initialization_requires_the_complete_owned_storage_and_alignment() {
        use super::super::*;
        let pointer = Pointer::symbolic(Variable(91_000));
        let aligned = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_aligned(pointer.clone(), 8), true);
        let state_for = |bytes, owned| {
            let range = allocation_range(pointer.clone(), bytes);
            CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
                if owned {
                    CResourceFact::own_memory(range)
                } else {
                    CResourceFact::view_memory(range)
                },
            ))
        };
        for state in [CState::new(), state_for(39, true), state_for(40, false)] {
            assert!(matches!(
                initialization_storage_refusal(&state, &pointer, 40, 8, &aligned),
                Some(CRuntimeError::MissingResource { .. })
            ));
        }
        let state = state_for(40, true);
        assert_eq!(
            initialization_storage_refusal(&state, &pointer, 40, 8, &PureFactContext::new()),
            Some(CRuntimeError::MissingMutexStorageAlignment {
                mutex: pointer.clone(),
                alignment: 8
            })
        );
        assert!(initialization_storage_refusal(&state, &pointer, 40, 8, &aligned).is_none());
        // A larger owned range can supply the full footprint at an interior address.
        let state = state_for(64, true);
        assert!(
            initialization_storage_refusal(&state, &pointer.offset_by_bytes(8), 40, 8, &aligned)
                .is_none()
        );
        assert!(matches!(
            initialization_storage_refusal(&state, &pointer.offset_by_bytes(1), 40, 8, &aligned),
            Some(CRuntimeError::MissingMutexStorageAlignment { .. })
        ));
    }

    #[test]
    fn initialization_rejects_read_only_and_expired_automatic_storage() {
        use super::super::*;
        let (state, pointer) = automatic_holder();
        register_block_alignment(&pointer.block, 8);
        assert!(
            initialization_storage_refusal(&state, &pointer, 40, 8, &PureFactContext::new())
                .is_none()
        );
        let ended = state
            .clone()
            .with_memory(state.memory().clone().without_local_block(&pointer.block));
        assert!(matches!(
            initialization_storage_refusal(&ended, &pointer, 40, 8, &PureFactContext::new()),
            Some(CRuntimeError::MissingResource { .. })
        ));
        let read_only =
            state.with_memory(CMemory::new().with_read_only_block(pointer.block.clone(), 48));
        assert!(matches!(
            initialization_storage_refusal(&read_only, &pointer, 40, 8, &PureFactContext::new()),
            Some(CRuntimeError::MissingResource { .. })
        ));
    }

    #[test]
    fn initialization_forgets_old_representation_and_preserves_adjacent_cells() {
        use super::super::*;
        let (state, pointer) = automatic_holder();
        register_block_alignment(&pointer.block, 8);
        let prefix = state.locals().slot("holder").unwrap().clone();
        let state = state.clone().with_memory(
            state
                .memory()
                .clone()
                .store(pointer.clone(), int8(17))
                .store(prefix.clone(), int32(23)),
        );
        let environment = CExecutionEnvironment::new().with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ));
        let statement = CStatement::Call {
            function_name: "pthread_mutex_init".into(),
            arguments: vec![
                CExpression::Value(CValue::pointer(pointer.clone())),
                c_int32_literal(0),
            ],
        };
        let paths = eval::execute_c_statement_paths(
            &state,
            &statement,
            &PureFactContext::new(),
            CExecutionContext::execute_bodies(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let CStatementOutcome::Normal(after) = &paths[0].outcome else {
            panic!("{paths:?}")
        };
        assert_ne!(
            after.memory().load(&pointer),
            CExpressionOutcome::Value(int8(17))
        );
        assert_eq!(
            after.memory().load(&prefix),
            CExpressionOutcome::Value(int32(23))
        );
        assert!(live_resource(after, &pointer, false).is_some());
    }

    #[test]
    fn initialization_cannot_overwrite_an_active_local_storage_loan() {
        use super::super::*;
        use crate::kernel::loans::{LoanLedger, plan_stable_view_transfer};
        use crate::kernel::prelude::CCheckedResourceFact;
        let (state, pointer) = automatic_holder();
        register_block_alignment(&pointer.block, 8);
        let viewed = CResourceFact::view_memory(allocation_range(pointer.clone(), 40));
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let assumptions = PureFactContext::new();
        let mut plan = plan_stable_view_transfer(
            &ResourceContext::new(),
            &[],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        plan.lend_local_views(
            state.memory(),
            &[CCheckedResourceFact {
                fact: viewed,
                role: CResourceTransferRole::Borrow,
                snapshot: CResourceSnapshot::Entry,
                clause_position: None,
                section_index: None,
                selected_mutex_source: None,
            }],
            &assumptions,
        )
        .unwrap();
        let state = state
            .with_loan_ledger(Some(plan.ledger.clone()))
            .with_loan_participant(Some(caller));
        assert!(matches!(
            initialization_storage_refusal(&state, &pointer, 40, 8, &assumptions),
            Some(CRuntimeError::LoanRefusal(_))
        ));
        for name in [
            "pthread_mutex_lock",
            "pthread_mutex_unlock",
            "pthread_mutex_destroy",
        ] {
            let mut context = MutexContext::new(state.clone())
                .initialize_empty(pointer.clone(), 40)
                .unwrap();
            if name == "pthread_mutex_unlock" {
                context = context.acquire_current(&pointer, &assumptions).unwrap();
            }
            let environment = CExecutionEnvironment::new().with_modeled_pthread_binding(Some(
                crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
            ));
            let paths = eval::execute_c_statement_paths(
                context.state(),
                &CStatement::Call {
                    function_name: name.into(),
                    arguments: vec![CExpression::Value(CValue::pointer(pointer.clone()))],
                },
                &assumptions,
                CExecutionContext::execute_bodies(&environment),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert!(
                matches!(
                    paths[0].outcome,
                    CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
                ),
                "{name}: {paths:?}"
            );
        }
    }

    #[test]
    fn initialization_does_not_reuse_consumed_or_zero_storage_authority() {
        use super::super::*;
        let pointer = Pointer {
            block: PointerBlock::Heap(91_003),
            offset: PointerOffsetTerm::Constant(0),
        };
        let range = allocation_range(pointer.clone(), 40);
        let fact = CResourceFact::own_memory(range.clone());
        let assumptions = PureFactContext::new();
        let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        assert!(resources.owns_storage_access(&pointer, 40, &assumptions));
        let resources = resources.without_fact(&fact, &assumptions).unwrap();
        assert!(!resources.owns_storage_access(&pointer, 40, &assumptions));
        let zero = resources.unchecked_with_fact(CResourceFact::own_quantity(
            CResource::Memory(range),
            0u32.into(),
        ));
        assert!(!zero.owns_storage_access(&pointer, 40, &assumptions));
        let overlapping_zero = zero.unchecked_with_fact(fact);
        assert!(overlapping_zero.owns_storage_access(&pointer, 40, &assumptions));
    }

    #[test]
    fn initialization_storage_lookup_is_indexed_within_one_object() {
        use super::super::*;
        let base = Pointer {
            block: PointerBlock::Heap(91_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut samples = vec![];
        for size in [16usize, 64, 256, 1024] {
            let assumptions = PureFactContext::new();
            let mut resources = ResourceContext::new_with_equalities(&assumptions);
            for index in 0..size {
                // Alternate units, so the index must compare bytes, not element indices.
                let width = if index % 2 == 0 { 1 } else { 8 };
                resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                    CMemoryRange::new_with_element_width(
                        base.clone(),
                        ((index * 64) as u32 / width).into(),
                        ((index * 64 + 40) as u32 / width).into(),
                        width,
                    ),
                ));
            }
            let state = CState::new().with_resource_context(resources);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in [0, size / 2, size - 1] {
                    let pointer = base.offset_by_bytes((index * 64) as u32);
                    assert!(
                        initialization_storage_refusal(
                            &state,
                            &pointer,
                            40,
                            8,
                            &PureFactContext::new()
                        )
                        .is_none()
                    );
                    assert!(
                        initialization_storage_refusal(
                            &state,
                            &pointer.offset_by_bytes(40),
                            40,
                            8,
                            &PureFactContext::new()
                        )
                        .is_some()
                    );
                }
            });
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] + 160,
                "storage query must be logarithmic: {samples:?}"
            );
        }
    }

    fn allocation_range(base: Pointer, bytes: u32) -> super::super::CMemoryRange {
        super::super::CMemoryRange::new_with_element_width(base, 0u32.into(), bytes.into(), 1)
    }

    #[test]
    fn initialized_storage_cannot_be_retired_until_destroyed() {
        let assumptions = PureFactContext::new();
        let base = mutex(0);
        let address = base.offset_by_bytes(8);
        let state = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let whole = allocation_range(base.clone(), 48);
        let expected = Some(super::super::CRuntimeError::MutexStorageInUse {
            mutex: address.clone(),
            allocation: base,
        });
        assert_eq!(
            storage_retirement_refusal(state.state(), &whole, &assumptions),
            expected
        );
        let held = state.acquire_current(&address, &assumptions).unwrap();
        assert_eq!(
            storage_retirement_refusal(held.state(), &whole, &assumptions),
            expected
        );
        let released = held.release_current(&address, &assumptions).unwrap();
        assert_eq!(
            storage_retirement_refusal(released.state(), &whole, &assumptions),
            expected
        );
        let destroyed = released.destroy(&address, &assumptions).unwrap();
        assert_eq!(
            storage_retirement_refusal(destroyed.state(), &whole, &assumptions),
            None
        );
        // The end of a mutex's footprint matters, not only its first byte.
        let tail = allocation_range(address.offset_by_bytes(36), 4);
        assert!(storage_retirement_refusal(state.state(), &tail, &assumptions).is_some());
        let beside = allocation_range(address.offset_by_bytes(40), 4);
        assert_eq!(
            storage_retirement_refusal(state.state(), &beside, &assumptions),
            None
        );
        let elsewhere = allocation_range(mutex(1), 48);
        assert_eq!(
            storage_retirement_refusal(state.state(), &elsewhere, &assumptions),
            None
        );
    }

    #[test]
    fn retirement_candidate_index_covers_every_possible_provenance_alias() {
        use super::super::{PointerBlock, Variable};
        // Include distinct members of every parameterized provenance class.
        let mut blocks = vec![PointerBlock::ExternalArgument];
        for index in 0..2 {
            blocks.extend([
                PointerBlock::Concrete(format!("local:{index}")),
                PointerBlock::Concrete(format!("global:{index}")),
                PointerBlock::Heap(index),
                PointerBlock::Temporary(index),
                PointerBlock::ExternalObject(Variable(index)),
                PointerBlock::Symbolic(Variable(index)),
                PointerBlock::FunctionSymbolic(Variable(index)),
                PointerBlock::Function(format!("function{index}")),
                PointerBlock::StringLiteral {
                    identity: format!("literal{index}"),
                    bytes: vec![0],
                },
            ]);
        }
        for allocation in &blocks {
            for mutex in &blocks {
                if allocation != mutex && !allocation.proven_distinct(mutex) {
                    assert!(
                        StorageProvenance::of(allocation)
                            .cross_block_candidates()
                            .contains(&StorageProvenance::of(mutex)),
                        "missing possible alias: {allocation:?}, {mutex:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn retirement_requires_separation_from_symbolic_initializations() {
        use super::super::*;
        let base = Pointer {
            block: PointerBlock::Heap(90_000),
            offset: PointerOffsetTerm::constant(0),
        };
        let symbolic = Pointer::symbolic(Variable(90_001));
        let context = MutexContext::new(CState::new())
            .initialize_empty(symbolic.clone(), 40)
            .unwrap();
        let allocation = allocation_range(base, 48);
        let storage = allocation_range(symbolic.clone(), 40);
        let expected = Some(CRuntimeError::MutexStorageSeparationRequired {
            allocation: Box::new(allocation.clone()),
            storage: Box::new(storage.clone()),
        });
        let assumptions = PureFactContext::new();
        assert_eq!(
            storage_retirement_refusal(context.state(), &allocation, &assumptions),
            expected
        );
        let mut hidden = context
            .acquire_current(&symbolic, &assumptions)
            .unwrap()
            .into_state();
        hidden.resources = ResourceContext::new();
        assert_eq!(
            storage_retirement_refusal(&hidden, &allocation, &assumptions),
            expected
        );
        let separated = assumptions
            .clone()
            .assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(allocation.clone())),
                right: Box::new(CResource::Memory(storage)),
            });
        assert!(storage_retirement_refusal(context.state(), &allocation, &separated).is_none());
        let destroyed = context.destroy(&symbolic, &assumptions).unwrap();
        assert!(storage_retirement_refusal(destroyed.state(), &allocation, &assumptions).is_none());
    }

    #[test]
    fn declaration_reentry_checks_old_mutex_storage_before_replacing_it() {
        use super::super::*;
        let (state, address) = automatic_holder();
        let context = MutexContext::new(state)
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let layout = CAggregateLayout::new(48, 8, vec![]);
        let declarations = [
            CStatement::Declare {
                name: "holder".into(),
                c_type: CType::Int32,
                array_object_kind: CArrayObjectKind::Scalar,
                array_shape: None,
                volatile: false,
                pointee_volatile: false,
                constant: false,
                pointee_constant: false,
                initializer: None,
                zero_fill: None,
            },
            CStatement::DeclareAggregate {
                name: "holder".into(),
                layout: layout.clone(),
                kind: CAggregateDeclarationKind::Local,
            },
            CStatement::DeclareAggregate {
                name: "holder".into(),
                layout: layout.clone(),
                kind: CAggregateDeclarationKind::Constructor,
            },
            CStatement::DeclareAggregate {
                name: "holder".into(),
                layout,
                kind: CAggregateDeclarationKind::ConstructionDestination,
            },
        ];
        for declaration in declarations {
            for hidden in [false, true] {
                let mut state = context.state().clone();
                if hidden {
                    state.resources = ResourceContext::new();
                }
                let paths = eval::execute_c_statement_paths(
                    &state,
                    &declaration,
                    &PureFactContext::new(),
                    CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                assert!(matches!(&paths[0].outcome,
                    CStatementOutcome::RuntimeError(CRuntimeError::MutexStorageScopeEnd { local, mutex, may_alias: false })
                        if local == "holder" && mutex == &address));
            }
            let destroyed = context.destroy(&address, &PureFactContext::new()).unwrap();
            let paths = eval::execute_c_statement_paths(
                destroyed.state(),
                &declaration,
                &PureFactContext::new(),
                CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let CStatementOutcome::Normal(state) = &paths[0].outcome else {
                panic!("{paths:?}")
            };
            assert_ne!(state.locals().slot("holder").unwrap().block, address.block);
            assert!(!state.memory().has_block(&address.block));
        }
    }

    #[test]
    fn retirement_alias_index_skips_unrelated_objects_at_multiple_sizes() {
        use super::super::*;
        let mut samples = vec![];
        let assumptions = PureFactContext::new();
        for size in [16usize, 64, 256, 1024] {
            let mut context = MutexContext::new(CState::new());
            for index in 0..size {
                for block in [
                    PointerBlock::Heap(index as u64),
                    PointerBlock::Concrete(format!("local:{index}")),
                ] {
                    context = context
                        .initialize_empty(
                            Pointer {
                                block,
                                offset: PointerOffsetTerm::constant(0),
                            },
                            40,
                        )
                        .unwrap();
                }
            }
            let queries = [PointerBlock::Heap(90_000), PointerBlock::ExternalArgument];
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for block in &queries {
                    let range = allocation_range(
                        Pointer {
                            block: block.clone(),
                            offset: PointerOffsetTerm::constant(0),
                        },
                        48,
                    );
                    assert!(
                        storage_retirement_refusal(context.state(), &range, &assumptions).is_none()
                    );
                }
            });
            let symbolic = Pointer::symbolic(Variable(90_001));
            let context = context.initialize_empty(symbolic, 40).unwrap();
            let (_, ambiguous_work) = crate::instrumentation::measure_deterministic_work(|| {
                for block in queries {
                    let range = allocation_range(
                        Pointer {
                            block,
                            offset: PointerOffsetTerm::constant(0),
                        },
                        48,
                    );
                    assert!(matches!(
                        storage_retirement_refusal(context.state(), &range, &assumptions),
                        Some(CRuntimeError::MutexStorageSeparationRequired { .. })
                    ));
                }
            });
            samples.push((size, work, ambiguous_work));
        }
        let (_, absent, present) = samples[0];
        for (size, work, ambiguous) in &samples {
            let allowance = 64 * (size.ilog2() as usize - 4);
            assert!(
                *work <= absent + allowance && *ambiguous <= present + allowance,
                "retirement lookup must be logarithmic: {samples:?}"
            );
        }
    }

    #[test]
    fn storage_retirement_uses_unsigned_heap_extents_and_wide_offsets() {
        let assumptions = PureFactContext::new();
        for (extent, offset) in [(u32::MAX, 8), (i32::MAX as u32, i32::MAX as u32 - 8)] {
            let base = mutex(0);
            let state = MutexContext::new(CState::new())
                .initialize_empty(base.offset_by_bytes(offset), 40)
                .unwrap();
            assert!(
                storage_retirement_refusal(
                    state.state(),
                    &allocation_range(base, extent),
                    &assumptions
                )
                .is_some()
            );
        }
    }

    #[test]
    fn abstract_guard_storage_retirement_requires_lifecycle_support() {
        let state = CState::new().with_resource_context(super::super::ResourceContext::new());
        let mut state = state;
        state.preserves_mutex_protocols = true;
        assert_eq!(
            storage_retirement_refusal(
                &state,
                &allocation_range(mutex(0), 48),
                &PureFactContext::new()
            ),
            Some(super::super::CRuntimeError::UnsupportedMutexStorageRetirement)
        );
    }

    #[test]
    fn storage_retirement_lookup_ignores_unrelated_mutex_blocks() {
        let mut samples = Vec::new();
        let assumptions = PureFactContext::new();
        for size in [16, 64, 256, 1024] {
            let mut state = MutexContext::new(CState::new());
            for index in 0..size {
                state = state.initialize_empty(mutex(index), 40).unwrap();
            }
            let range = allocation_range(mutex(size / 2), 40);
            let (refusal, work) = crate::persistent::measure_persistent_work(|| {
                storage_retirement_refusal(state.state(), &range, &assumptions)
            });
            assert!(refusal.is_some());
            samples.push(work);
            // Destroying one of multiple mutexes in a block retains the other.
            let other = mutex(size / 2).offset_by_bytes(48);
            let state = state.initialize_empty(other.clone(), 40).unwrap();
            let state = state.destroy(range.base(), &assumptions).unwrap();
            assert!(
                storage_retirement_refusal(
                    state.state(),
                    &allocation_range(other, 40),
                    &assumptions
                )
                .is_some()
            );
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] + 16, "{samples:?}");
        }
    }

    #[test]
    fn loop_back_edge_checks_mutex_ownership_and_accepts_a_balanced_exchange() {
        let assumptions = PureFactContext::new();
        let mutex = mutex(0);
        let head = MutexContext::new(CState::new())
            .initialize_empty(mutex.clone(), 40)
            .unwrap();
        let held = head.acquire_current(&mutex, &assumptions).unwrap();
        let mismatch = crate::kernel::c_loop_state_components_match_at_back_edge(
            head.state(),
            held.state(),
            &assumptions,
            &[],
        )
        .unwrap_err();
        assert!(mismatch.contains("mutex ownership"), "{mismatch}");

        let released = held.release_current(&mutex, &assumptions).unwrap();
        crate::kernel::c_loop_state_components_match_at_back_edge(
            head.state(),
            released.state(),
            &assumptions,
            &[],
        )
        .unwrap();
    }

    #[test]
    fn loop_back_edge_rejects_reinitialization_even_with_the_same_invariant() {
        let assumptions = PureFactContext::new();
        for protected in [None, Some(invariant(1, 0))] {
            let initial = match &protected {
                Some(fact) => context(fact.clone()),
                None => MutexContext::new(CState::new()),
            };
            // Keep a second mutex alive: the ledger lineage and aggregate
            // counts alone cannot distinguish replacing the selected mutex.
            let initial = initial.initialize_empty(mutex(1), 40).unwrap();
            let initialize = |state: &MutexContext| match &protected {
                Some(fact) => state
                    .publish(mutex(0), fact.clone(), &assumptions, 40)
                    .unwrap(),
                None => state.initialize_empty(mutex(0), 40).unwrap(),
            };
            let head = initialize(&initial);
            let destroyed = head.destroy(&mutex(0), &assumptions).unwrap();
            let replaced = initialize(&destroyed);
            assert_eq!(
                head.state()
                    .mutex_ledger
                    .as_ref()
                    .unwrap()
                    .check_protocol_state_since(replaced.state().mutex_ledger.as_ref().unwrap()),
                Err(MutexProtocolMismatch::Initialization),
            );
            let error = crate::kernel::c_loop_state_components_match_at_back_edge(
                head.state(),
                replaced.state(),
                &assumptions,
                &[],
            )
            .unwrap_err();
            assert!(
                error.contains("requires the same initialization"),
                "{error}"
            );
            // A balanced exchange still preserves the new initialization.
            let held = replaced.acquire_current(&mutex(0), &assumptions).unwrap();
            let released = held.release_current(&mutex(0), &assumptions).unwrap();
            assert_eq!(
                replaced
                    .state()
                    .mutex_ledger
                    .as_ref()
                    .unwrap()
                    .check_protocol_state_since(released.state().mutex_ledger.as_ref().unwrap()),
                Ok(()),
            );
        }
    }

    #[test]
    fn initialization_is_generative_and_cannot_be_substituted_on_a_guard() {
        let assumptions = PureFactContext::new();
        let initial = MutexContext::new(CState::new());
        let first = initial.initialize_empty(mutex(0), 40).unwrap();
        let second = initial.initialize_empty(mutex(0), 40).unwrap();
        let first_id = first
            .state()
            .mutex_ledger
            .as_ref()
            .unwrap()
            .get(&mutex(0))
            .unwrap()
            .initialization();
        let second_id = second
            .state()
            .mutex_ledger
            .as_ref()
            .unwrap()
            .get(&mutex(0))
            .unwrap()
            .initialization();
        assert_ne!(first_id, second_id);
        let (held, mut guard) = second.acquire(&mutex(0), &assumptions).unwrap();
        // Even a witness with the current acquisition number cannot authorize
        // a transition for a different initialization.
        guard.initialization = first_id;
        assert_eq!(
            held.release_with_invariant(guard, None, &assumptions).err(),
            Some(MutexTransitionError::Refusal(
                "mutex guard does not match the current holder"
            ))
        );
        held.release_current(&mutex(0), &assumptions).unwrap();
    }

    #[test]
    fn loop_may_initialize_and_destroy_a_mutex_absent_at_its_head() {
        let assumptions = PureFactContext::new();
        let head = MutexContext::new(CState::new())
            .initialize_empty(mutex(0), 40)
            .unwrap();
        let local = head.initialize_empty(mutex(1), 40).unwrap();
        let local = local.acquire_current(&mutex(1), &assumptions).unwrap();
        let local = local.release_current(&mutex(1), &assumptions).unwrap();
        let next = local.destroy(&mutex(1), &assumptions).unwrap();
        crate::kernel::c_loop_state_components_match_at_back_edge(
            head.state(),
            next.state(),
            &assumptions,
            &[],
        )
        .unwrap();
    }

    #[test]
    fn loop_mutex_join_work_tracks_changed_keys_not_unrelated_mutexes() {
        let assumptions = PureFactContext::new();
        let mut work = Vec::new();
        let mut replacement_work = Vec::new();
        for size in [32, 128, 512] {
            let mut head = MutexContext::new(CState::new());
            for index in 0..size {
                head = head.initialize_empty(mutex(index), 40).unwrap();
            }
            let selected = mutex(size / 2);
            let held = head.acquire_current(&selected, &assumptions).unwrap();
            let released = held.release_current(&selected, &assumptions).unwrap();
            let (equal, units) = crate::persistent::measure_persistent_work(|| {
                head.state()
                    .mutex_ledger
                    .as_ref()
                    .unwrap()
                    .check_protocol_state_since(released.state().mutex_ledger.as_ref().unwrap())
                    .is_ok()
            });
            assert!(equal);
            work.push(units);
            let replaced = head
                .destroy(&selected, &assumptions)
                .unwrap()
                .initialize_empty(selected, 40)
                .unwrap();
            let (result, units) = crate::persistent::measure_persistent_work(|| {
                head.state()
                    .mutex_ledger
                    .as_ref()
                    .unwrap()
                    .check_protocol_state_since(replaced.state().mutex_ledger.as_ref().unwrap())
            });
            assert_eq!(result, Err(MutexProtocolMismatch::Initialization));
            replacement_work.push(units);
        }
        assert!(work[1] <= work[0] + 8, "{work:?}");
        assert!(work[2] <= work[1] + 8, "{work:?}");
        assert!(
            replacement_work[1] <= replacement_work[0] + 8,
            "{replacement_work:?}"
        );
        assert!(
            replacement_work[2] <= replacement_work[1] + 8,
            "{replacement_work:?}"
        );
    }
    use crate::kernel::{
        CType, PointerOffsetTerm, ResourceContext, ResourceFieldSchema, ResourceFieldType,
        ResourceInstance, Variable, int32,
    };

    fn mutex(index: usize) -> Pointer {
        Pointer {
            block: format!("mutex-{index}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn invariant(identity: u64, revision: u32) -> CResourceFact {
        let schema = ResourceFieldSchema::new(vec![(
            "revision".into(),
            ResourceFieldType::C(CType::Int32),
        )])
        .unwrap();
        CResourceFact::own(CResource::Instance(
            ResourceInstance::new(
                Variable(identity),
                "counter_state".into(),
                Vec::new().into(),
                schema,
                vec![int32(revision).into()].into(),
            )
            .unwrap(),
        ))
    }

    fn context(fact: CResourceFact) -> MutexContext {
        MutexContext::new(
            CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(fact)),
        )
    }

    #[test]
    fn shared_acquisitions_forget_each_previous_payload_observation() {
        use crate::kernel::{
            CCompositeResourceDefinition, CParameter, CValue, ExecutionBudget, ResourceDescription,
        };
        use std::collections::BTreeMap;

        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let schema = ResourceFieldSchema::new(vec![(
            "revision".into(),
            ResourceFieldType::C(CType::Int32),
        )])
        .unwrap();
        let instance = ResourceInstance::new(
            Variable(902),
            "counter_state".into(),
            vec![CValue::pointer(address.clone()).into()].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap();
        let expected_type = ResourceDescription::from_instance(&instance);
        let definition = CCompositeResourceDefinition::new(
            "counter_state",
            vec![CParameter::new("p", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )
        .with_instance_schema(Some(schema));
        let definitions = BTreeMap::from([("counter_state".into(), definition.clone())]);
        let initialized = context(CResourceFact::own(CResource::Instance(instance.clone())))
            .publish_declared(
                &address,
                instance.identity(),
                &definitions,
                &assumptions,
                40,
            )
            .unwrap();
        assert_eq!(
            initialized
                .state
                .mutex_ledger
                .as_ref()
                .unwrap()
                .protected_type(&address),
            Some(&expected_type)
        );
        let mut state = initialized.into_state();
        let mut previous = instance;
        let mut budget = ExecutionBudget::new();
        for _ in 0..3 {
            let (fresh, _) = MutexLedger::havoc_protected_for_call(
                &state,
                &address,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                &mut budget,
            )
            .unwrap();
            let held = MutexContext::new(fresh)
                .acquire_current(&address, &assumptions)
                .unwrap();
            let current = held
                .state
                .resources
                .owned_instance(previous.identity())
                .unwrap();
            assert_ne!(
                current, &previous,
                "another worker may have changed the payload"
            );
            assert_eq!(ResourceDescription::from_instance(current), expected_type);
            previous = current.clone();
            assert!(held.state.mutex_ledger.as_ref().unwrap().has_locked_guard());
            state = held
                .release_current(&address, &assumptions)
                .unwrap()
                .into_state();
            assert!(!state.mutex_ledger.as_ref().unwrap().has_locked_guard());
        }
        // A parent may write under the lock and join its last worker without
        // acquiring again. Release must forget that write immediately.
        let mut held = MutexContext::new(state)
            .acquire_current(&address, &assumptions)
            .unwrap();
        let old = CResourceFact::own(CResource::Instance(previous.clone()));
        let mut written = previous.clone();
        written.fields = vec![int32(99).into()].into();
        held.state.resources = held
            .state
            .resources
            .clone()
            .without_fact(&old, &assumptions)
            .unwrap()
            .try_compose_with_fact(
                CResourceFact::own(CResource::Instance(written.clone())),
                &assumptions,
            )
            .unwrap();
        let released = held.release_current(&address, &assumptions).unwrap();
        let (fresh, _) = MutexLedger::havoc_protected_for_call(
            released.state(),
            &address,
            &definition,
            std::slice::from_ref(&definition),
            &assumptions,
            &mut budget,
        )
        .unwrap();
        let destroyed = MutexContext::new(fresh)
            .destroy(&address, &assumptions)
            .unwrap();
        let returned = destroyed
            .state
            .resources
            .owned_instance(previous.identity())
            .unwrap();
        assert_ne!(returned.fields(), written.fields());
        assert_eq!(ResourceDescription::from_instance(returned), expected_type);
        let empty = MutexContext::new(CState::new())
            .initialize_empty(mutex(1), 40)
            .unwrap();
        assert!(
            empty
                .state
                .mutex_ledger
                .as_ref()
                .unwrap()
                .protected_type(&mutex(1))
                .is_none()
        );
    }

    fn runtime_mutex_call(
        state: &CState,
        address: &Pointer,
        name: &str,
    ) -> Result<CState, super::super::CRuntimeError> {
        use super::super::*;
        let environment = CExecutionEnvironment::new().with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ));
        let statement = CStatement::Call {
            function_name: name.into(),
            arguments: vec![CExpression::Value(CValue::pointer(address.clone()))],
        };
        let paths = eval::execute_c_statement_paths(
            state,
            &statement,
            &PureFactContext::new(),
            CExecutionContext::execute_bodies(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        let path = paths.into_iter().next().unwrap();
        if let CStatementOutcome::Normal(after) = &path.outcome {
            if state.loan_ledger != after.loan_ledger {
                let before = state.loan_ledger.as_ref().unwrap();
                let holder = state.loan_participant.unwrap();
                assert_eq!(path.loan_evidence.len(), 1);
                assert!(path.loan_evidence.is_valid());
                assert_eq!(
                    path.loan_evidence
                        .recovered_ledger_for(before, holder, false),
                    after.loan_ledger
                );
            } else {
                assert!(path.loan_evidence.is_empty());
            }
        }
        match path.outcome {
            CStatementOutcome::Normal(state) => Ok(*state),
            CStatementOutcome::RuntimeError(error) => Err(error),
            other => panic!("unexpected mutex call outcome: {other:?}"),
        }
    }

    #[test]
    fn runtime_acquisition_uses_owned_loan_and_pins_it_until_unlock() {
        let assumptions = PureFactContext::new();
        let (state, address) = automatic_holder();
        let payload = invariant(1, 0);
        let state = state
            .with_resource_context(ResourceContext::new().unchecked_with_fact(payload.clone()));
        let initialized = MutexContext::new(state)
            .publish(address.clone(), payload.clone(), &assumptions, 40)
            .unwrap();
        let owner = live_resource(initialized.state(), &address, false).unwrap();
        let (lent, root) = initialized.lend_use(&address, &assumptions).unwrap();
        let (child, loan) = lent.reborrow_use(root.usage, &assumptions).unwrap();
        let use_fact = child.owned_use_resource(loan.usage).unwrap();
        let locked = MutexContext::new(
            runtime_mutex_call(child.state(), &address, "pthread_mutex_lock").unwrap(),
        );
        assert!(
            locked
                .state
                .resources
                .satisfies_fact(&payload, &assumptions)
        );
        assert!(
            locked
                .state
                .resources
                .satisfies_fact(&use_fact, &assumptions)
        );
        assert!(!locked.state.resources.satisfies_fact(&owner, &assumptions));
        assert!(locked.end_use_reborrow(&loan, &assumptions).is_err());
        assert!(locked.recover_use(&root, &assumptions).is_err());
        assert!(runtime_mutex_call(locked.state(), &address, "pthread_mutex_destroy").is_err());
        let unlocked = MutexContext::new(
            runtime_mutex_call(locked.state(), &address, "pthread_mutex_unlock").unwrap(),
        );
        assert!(
            !unlocked
                .state
                .resources
                .satisfies_fact(&payload, &assumptions)
        );
        let parent = unlocked.end_use_reborrow(&loan, &assumptions).unwrap();
        let recovered = parent.recover_use(&root, &assumptions).unwrap();
        assert!(
            recovered
                .state
                .resources
                .satisfies_fact(&owner, &assumptions)
        );
        let destroyed =
            runtime_mutex_call(recovered.state(), &address, "pthread_mutex_destroy").unwrap();
        assert!(destroyed.resources.satisfies_fact(&payload, &assumptions));
    }

    #[test]
    fn runtime_use_acquisition_rejects_descriptions_and_stale_initializations() {
        let assumptions = PureFactContext::new();
        let (state, address) = automatic_holder();
        let initialized = MutexContext::new(state.clone())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (lent, loan) = initialized.lend_use(&address, &assumptions).unwrap();
        let fact = lent.owned_use_resource(loan.usage).unwrap();
        let mut missing = lent.state().clone();
        missing.resources = missing.resources.without_fact(&fact, &assumptions).unwrap();
        assert!(runtime_mutex_call(&missing, &address, "pthread_mutex_lock").is_err());
        missing.resources =
            missing
                .resources
                .unchecked_with_fact(CResourceFact::own(CResource::MutexUse(
                    super::super::MutexUseIdentity {
                        protected: None,
                        binding: None,
                        initialization: None,
                        mutex: address.clone(),
                    },
                )));
        assert!(matches!(
            runtime_mutex_call(&missing, &address, "pthread_mutex_lock"),
            Err(super::super::CRuntimeError::MissingMutexUse { .. })
        ));
        let replacement = MutexContext::new(state)
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let mut stale = lent.state().clone();
        stale.mutex_ledger = replacement.state.mutex_ledger;
        assert!(matches!(
            runtime_mutex_call(&stale, &address, "pthread_mutex_lock"),
            Err(super::super::CRuntimeError::MissingMutexUse { .. })
        ));
        let mut frozen = lent.state().clone();
        frozen.preserves_mutex_protocols = true;
        let held = runtime_mutex_call(&frozen, &address, "pthread_mutex_lock").unwrap();
        assert!(held.opaque_mutex_acquisitions.is_some());
        assert_eq!(
            held.resources.facts().len(),
            frozen.resources.facts().len() + 1
        );
        assert!(held.resources.satisfies_fact(&fact, &assumptions));
        let returned = runtime_mutex_call(&held, &address, "pthread_mutex_unlock").unwrap();
        assert!(returned.opaque_mutex_acquisitions.is_none());
        assert_eq!(returned.resources.facts(), frozen.resources.facts());
    }

    #[test]
    fn automatic_use_acquisition_does_not_scan_the_resource_frame() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let mut context = MutexContext::new(CState::new())
                .initialize_empty(mutex(0), 40)
                .unwrap();
            let (lent, _) = context.lend_use(&mutex(0), &assumptions).unwrap();
            context = lent;
            for index in 0..size {
                context.state.resources =
                    context
                        .state
                        .resources
                        .unchecked_with_fact(CResourceFact::own(CResource::Token {
                            name: format!("frame{index}"),
                            arguments: vec![].into(),
                        }));
            }
            let ((result, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .acquire_current(&mutex(0), &assumptions)
                        .map(MutexContext::into_runtime_transition)
                })
            });
            assert!(result.is_ok());
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "use acquisition scans the frame: {samples:?}"
            );
        }
    }

    #[test]
    fn acquire_current_uses_the_lifecycle_authority_beside_an_unbound_use_description() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let live = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let live_fact = live
            .state
            .mutex_ledger
            .as_ref()
            .unwrap()
            .live_resource(&address)
            .unwrap();
        // A use description without a loan binding is not authority. Beside
        // the owned lifecycle it must not shadow the ordinary acquisition.
        let unbound = CResourceFact::own(CResource::MutexUse(super::super::MutexUseIdentity {
            protected: None,
            binding: None,
            initialization: None,
            mutex: address.clone(),
        }));
        let mut shadowed = live.clone();
        shadowed.state.resources = shadowed.state.resources.unchecked_with_fact(unbound);
        assert!(
            shadowed
                .state
                .resources
                .mutex_use_candidate_at(&address)
                .is_some()
        );
        let acquired = shadowed.acquire_current(&address, &assumptions).unwrap();
        assert!(acquired.state.resources.mutex_guard_at(&address).is_some());
        let released = acquired.release_current(&address, &assumptions).unwrap();
        assert!(released.state.resources.mutex_live_at(&address).is_some());
        assert!(released.state.resources.mutex_guard_at(&address).is_none());
        // Without the lifecycle authority the description still reports the
        // missing use, not a missing initialization.
        let mut without_live = shadowed.clone();
        without_live.state.resources = without_live
            .state
            .resources
            .without_fact(&live_fact, &assumptions)
            .unwrap();
        assert_eq!(
            without_live.acquire_current(&address, &assumptions).err(),
            Some(MutexTransitionError::MissingUse(address.clone()))
        );
        // Destroying a mutex whose frame holds only the lifecycle authority
        // leaves no mutex fact behind.
        let destroyed = live.destroy(&address, &assumptions).unwrap();
        assert!(destroyed.state.resources.mutex_live_at(&address).is_none());
        assert!(
            destroyed
                .state
                .resources
                .mutex_use_candidate_at(&address)
                .is_none()
        );
        assert!(destroyed.state.resources.mutex_guard_at(&address).is_none());
        assert!(destroyed.state.mutex_ledger.is_none());
    }

    #[test]
    fn use_resource_requires_owned_occurrence_in_addition_to_live_loan() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (lent, loan) = initialized.lend_use(&address, &assumptions).unwrap();
        let use_fact = lent.owned_use_resource(loan.usage).unwrap();
        let mut missing = lent.clone();
        missing.state.resources = missing
            .state
            .resources
            .without_fact(&use_fact, &assumptions)
            .unwrap();
        assert!(
            missing
                .state
                .loan_ledger
                .as_ref()
                .unwrap()
                .mutex_use_resource(loan.usage, missing.state.loan_participant.unwrap())
                .is_ok()
        );
        assert_eq!(
            missing
                .acquire_using(&address, loan.usage, &assumptions)
                .err(),
            Some(MutexTransitionError::MissingUse(address.clone()))
        );
        assert_eq!(
            missing.reborrow_use(loan.usage, &assumptions).err(),
            Some(MutexTransitionError::MissingUse(address.clone()))
        );
        assert_eq!(
            missing.recover_use(&loan, &assumptions).err(),
            Some(MutexTransitionError::MissingUse(address.clone()))
        );
        // An ordinary resource move restores the ability to act. The loan
        // description alone, even with the correct pointer, did not do so.
        missing.state.resources = missing
            .state
            .resources
            .try_compose_with_fact(use_fact, &assumptions)
            .unwrap();
        assert!(
            missing
                .acquire_using(&address, loan.usage, &assumptions)
                .is_ok()
        );
        let recovered = missing.recover_use(&loan, &assumptions).unwrap();
        assert!(
            recovered
                .state
                .resources
                .facts()
                .iter()
                .all(|fact| !matches!(fact.resource(), CResource::MutexUse(_)))
        );
    }

    #[test]
    fn use_resource_exchange_restores_exact_parent_and_refuses_missing_child() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (lent, root) = initialized.lend_use(&address, &assumptions).unwrap();
        let parent_fact = lent.owned_use_resource(root.usage).unwrap();
        let (child_state, child) = lent.reborrow_use(root.usage, &assumptions).unwrap();
        let child_fact = child_state.owned_use_resource(child.usage).unwrap();
        assert_ne!(parent_fact, child_fact);
        assert!(
            !child_state
                .state
                .resources
                .satisfies_fact(&parent_fact, &assumptions)
        );
        assert!(
            child_state
                .state
                .resources
                .satisfies_fact(&child_fact, &assumptions)
        );
        let mut missing_child = child_state.clone();
        missing_child.state.resources = missing_child
            .state
            .resources
            .without_fact(&child_fact, &assumptions)
            .unwrap();
        assert!(
            missing_child
                .end_use_reborrow(&child, &assumptions)
                .is_err()
        );
        // Putting a pinned parent atom into the resource context cannot
        // bypass the loan's independent possession check.
        missing_child.state.resources = missing_child
            .state
            .resources
            .try_compose_with_fact(parent_fact.clone(), &assumptions)
            .unwrap();
        assert!(
            missing_child
                .acquire_using(&address, root.usage, &assumptions)
                .is_err()
        );
        let restored = child_state.end_use_reborrow(&child, &assumptions).unwrap();
        assert_eq!(
            restored.owned_use_resource(root.usage).unwrap(),
            parent_fact
        );
        assert!(
            !restored
                .state
                .resources
                .satisfies_fact(&child_fact, &assumptions)
        );
        assert!(
            restored
                .acquire_using(&address, child.usage, &assumptions)
                .is_err()
        );
        // A stale child atom also grants nothing after its scope has ended.
        let mut forged = restored.clone();
        forged.state.resources = forged
            .state
            .resources
            .try_compose_with_fact(child_fact, &assumptions)
            .unwrap();
        assert!(
            forged
                .acquire_using(&address, child.usage, &assumptions)
                .is_err()
        );
        assert!(restored.recover_use(&root, &assumptions).is_ok());
    }

    #[test]
    fn nested_use_reborrow_keeps_owner_escrowed_until_every_guard_and_scope_returns() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let payload = invariant(1, 0);
        let initialized = context(payload.clone())
            .publish(address.clone(), payload.clone(), &assumptions, 40)
            .unwrap();
        let owner = live_resource(initialized.state(), &address, false).unwrap();
        let (lent, root) = initialized.lend_use(&address, &assumptions).unwrap();
        let (child_state, child) = lent.reborrow_use(root.usage, &assumptions).unwrap();
        let (grandchild_state, grandchild) =
            child_state.reborrow_use(child.usage, &assumptions).unwrap();
        assert!(
            grandchild_state
                .acquire_using(&address, child.usage, &assumptions)
                .is_err()
        );
        assert!(
            grandchild_state
                .acquire_using(&address, root.usage, &assumptions)
                .is_err()
        );
        let (held, _) = grandchild_state
            .acquire_using(&address, grandchild.usage, &assumptions)
            .unwrap();
        assert!(held.state.resources.satisfies_fact(&payload, &assumptions));
        assert!(!held.state.resources.satisfies_fact(&owner, &assumptions));
        assert!(held.end_use_reborrow(&grandchild, &assumptions).is_err());
        assert!(held.end_use_reborrow(&child, &assumptions).is_err());
        assert!(held.recover_use(&root, &assumptions).is_err());
        let released = held.release_current(&address, &assumptions).unwrap();
        assert!(released.recover_use(&grandchild, &assumptions).is_err());
        let child_restored = released
            .end_use_reborrow(&grandchild, &assumptions)
            .unwrap();
        assert!(
            child_restored
                .acquire_using(&address, grandchild.usage, &assumptions)
                .is_err()
        );
        let root_restored = child_restored
            .end_use_reborrow(&child, &assumptions)
            .unwrap();
        assert!(
            !root_restored
                .state
                .resources
                .satisfies_fact(&owner, &assumptions)
        );
        let (held, _) = root_restored
            .acquire_using(&address, root.usage, &assumptions)
            .unwrap();
        let recovered = held
            .release_current(&address, &assumptions)
            .unwrap()
            .recover_use(&root, &assumptions)
            .unwrap();
        assert!(recovered.destroy(&address, &assumptions).is_ok());
    }

    #[test]
    fn use_reborrow_respects_protocol_freeze_and_rejects_replaced_child() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (lent, root) = initialized.lend_use(&address, &assumptions).unwrap();
        let (child_state, child) = lent.reborrow_use(root.usage, &assumptions).unwrap();
        let mut frozen = child_state.clone();
        frozen.state.preserves_mutex_protocols = true;
        assert!(frozen.reborrow_use(child.usage, &assumptions).is_err());
        assert!(frozen.end_use_reborrow(&child, &assumptions).is_err());
        let root_state = child_state.end_use_reborrow(&child, &assumptions).unwrap();
        let (replacement_state, replacement) =
            root_state.reborrow_use(root.usage, &assumptions).unwrap();
        assert!(
            replacement_state
                .acquire_using(&address, child.usage, &assumptions)
                .is_err()
        );
        assert!(
            replacement_state
                .end_use_reborrow(&child, &assumptions)
                .is_err()
        );
        assert!(
            replacement_state
                .acquire_using(&address, replacement.usage, &assumptions)
                .is_ok()
        );
    }

    #[test]
    fn use_loan_escrows_owner_and_guard_blocks_recovery_until_release() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let payload = invariant(1, 0);
        let updated = invariant(1, 1);
        let initialized = context(payload.clone())
            .publish(address.clone(), payload.clone(), &assumptions, 40)
            .unwrap();
        let owner = live_resource(initialized.state(), &address, false).unwrap();
        let (lent, loan) = initialized.lend_use(&address, &assumptions).unwrap();
        assert!(!lent.state.resources.satisfies_fact(&owner, &assumptions));
        assert!(!lent.state.resources.satisfies_fact(&payload, &assumptions));
        assert!(lent.lend_use(&address, &assumptions).is_err());
        assert!(lent.acquire(&address, &assumptions).is_err());
        assert!(lent.destroy(&address, &assumptions).is_err());
        let (mut held, guard) = lent
            .acquire_using(&address, loan.usage, &assumptions)
            .unwrap();
        assert!(held.state.resources.satisfies_fact(&payload, &assumptions));
        assert!(held.recover_use(&loan, &assumptions).is_err());
        assert!(held.destroy(&address, &assumptions).is_err());
        assert!(
            held.acquire_using(&address, loan.usage, &assumptions)
                .is_err()
        );
        // Keep the program's actual protected-state update: lending does not
        // freeze the payload or require its historical field value on release.
        held.state.resources = held
            .state
            .resources
            .clone()
            .without_fact(&payload, &assumptions)
            .unwrap()
            .try_compose_with_fact(updated.clone(), &assumptions)
            .unwrap();
        assert!(
            held.release(
                MutexGuard {
                    mutex: guard.mutex.clone(),
                    initialization: guard.initialization,
                    epoch: guard.epoch
                },
                payload.clone(),
                &assumptions
            )
            .is_err()
        );
        assert!(held.recover_use(&loan, &assumptions).is_err());
        let released = held.release(guard, updated.clone(), &assumptions).unwrap();
        assert!(
            !released
                .state
                .resources
                .satisfies_fact(&updated, &assumptions)
        );
        assert!(
            !released
                .state
                .resources
                .satisfies_fact(&owner, &assumptions)
        );
        let (held_again, _) = released
            .acquire_using(&address, loan.usage, &assumptions)
            .unwrap();
        assert!(
            held_again
                .state
                .resources
                .satisfies_fact(&updated, &assumptions)
        );
        let released = held_again.release_current(&address, &assumptions).unwrap();
        let recovered = released.recover_use(&loan, &assumptions).unwrap();
        assert!(
            recovered
                .state
                .resources
                .satisfies_fact(&owner, &assumptions)
        );
        assert!(recovered.recover_use(&loan, &assumptions).is_err());
        assert!(
            recovered
                .acquire_using(&address, loan.usage, &assumptions)
                .is_err()
        );
        let destroyed = recovered.destroy(&address, &assumptions).unwrap();
        assert!(
            destroyed
                .state
                .resources
                .satisfies_fact(&updated, &assumptions)
        );
    }

    #[test]
    fn use_loan_rejects_other_mutex_initialization_participant_and_stale_guard() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let other = mutex(1);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap()
            .initialize_empty(other.clone(), 40)
            .unwrap();
        let (lent, loan) = initialized.lend_use(&address, &assumptions).unwrap();
        assert_eq!(
            lent.acquire_using(&other, loan.usage, &assumptions).err(),
            Some(MutexTransitionError::MissingUse(other))
        );
        let mut foreign = lent.clone();
        foreign.state.loan_participant = Some(
            foreign
                .state
                .loan_ledger
                .as_ref()
                .unwrap()
                .fresh_participant()
                .unwrap(),
        );
        assert_eq!(
            foreign
                .acquire_using(&address, loan.usage, &assumptions)
                .err(),
            Some(MutexTransitionError::MissingUse(address.clone()))
        );
        assert!(foreign.recover_use(&loan, &assumptions).is_err());
        let (held, old_guard) = lent
            .acquire_using(&address, loan.usage, &assumptions)
            .unwrap();
        let released = held.release_current(&address, &assumptions).unwrap();
        let (held, _) = released
            .acquire_using(&address, loan.usage, &assumptions)
            .unwrap();
        assert!(
            held.release_with_invariant(old_guard, None, &assumptions)
                .is_err()
        );
        assert!(held.recover_use(&loan, &assumptions).is_err());
        let recovered = held
            .release_current(&address, &assumptions)
            .unwrap()
            .recover_use(&loan, &assumptions)
            .unwrap();
        let reinitialized = MutexContext::new(
            recovered
                .destroy(&address, &assumptions)
                .unwrap()
                .into_state(),
        )
        .initialize_empty(address.clone(), 40)
        .unwrap();
        assert_eq!(
            reinitialized
                .acquire_using(&address, loan.usage, &assumptions)
                .err(),
            Some(MutexTransitionError::MissingUse(address.clone()))
        );
        // An active old loan is also insufficient for a new initialization,
        // even if a hostile state substitutes its mutex registry.
        let mut substituted = lent;
        substituted.state.mutex_ledger = reinitialized.state.mutex_ledger;
        assert_eq!(
            substituted
                .acquire_using(&address, loan.usage, &assumptions)
                .err(),
            Some(MutexTransitionError::MissingUse(address))
        );
    }

    #[test]
    fn use_guard_cannot_release_without_its_loan_state_or_holder() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (lent, loan) = initialized.lend_use(&address, &assumptions).unwrap();
        let (held, _) = lent
            .acquire_using(&address, loan.usage, &assumptions)
            .unwrap();
        let mut no_hold = held.clone();
        no_hold.state.loan_ledger = lent.state.loan_ledger.clone();
        assert!(no_hold.release_current(&address, &assumptions).is_err());
        let mut no_ledger = held.clone();
        no_ledger.state.loan_ledger = None;
        assert!(no_ledger.release_current(&address, &assumptions).is_err());
        let mut wrong_holder = held.clone();
        wrong_holder.state.loan_participant = Some(
            held.state
                .loan_ledger
                .as_ref()
                .unwrap()
                .fresh_participant()
                .unwrap(),
        );
        assert!(
            wrong_holder
                .release_current(&address, &assumptions)
                .is_err()
        );
        let mut frozen = lent.clone();
        frozen.state.preserves_mutex_protocols = true;
        assert!(
            frozen
                .acquire_using(&address, loan.usage, &assumptions)
                .is_err()
        );
        assert!(frozen.recover_use(&loan, &assumptions).is_err());
        assert!(frozen.lend_use(&address, &assumptions).is_err());
        assert!(
            held.release_current(&address, &assumptions)
                .unwrap()
                .recover_use(&loan, &assumptions)
                .is_ok()
        );
    }

    #[test]
    fn preserving_protocol_cannot_forget_a_guards_lifetime_hold() {
        let assumptions = PureFactContext::new();
        let address = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let (lent, loan) = initialized.lend_use(&address, &assumptions).unwrap();
        let (held, _) = lent
            .acquire_using(&address, loan.usage, &assumptions)
            .unwrap();
        let ledger = held.state.mutex_ledger.as_ref().unwrap();
        let mut entry = ledger.get(&address).unwrap().clone();
        let MutexEntry::Locked { lifetime_hold, .. } = &mut entry else {
            panic!("locked")
        };
        assert!(lifetime_hold.take().is_some());
        let without_hold = ledger.with_inserted(address, entry);
        assert_eq!(
            ledger.check_protocol_state_since(&without_hold),
            Err(MutexProtocolMismatch::State)
        );
    }

    #[test]
    fn use_loan_round_trip_does_not_scan_unrelated_mutexes() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let assumptions = PureFactContext::new();
            let mut initialized = MutexContext::new(CState::new());
            for index in 0..size {
                initialized = initialized.initialize_empty(mutex(index), 40).unwrap();
            }
            let ((recovered, work), persistent_work) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        let (lent, loan) = initialized.lend_use(&mutex(0), &assumptions).unwrap();
                        let (held, _) = lent
                            .acquire_using(&mutex(0), loan.usage, &assumptions)
                            .unwrap();
                        held.release_current(&mutex(0), &assumptions)
                            .unwrap()
                            .recover_use(&loan, &assumptions)
                            .unwrap()
                    })
                });
            assert!(recovered.destroy(&mutex(0), &assumptions).is_ok());
            samples.push((size, work, persistent_work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
                "one mutex loan scans unrelated initializations: {samples:?}"
            );
        }
    }

    #[test]
    fn lock_moves_only_the_published_folded_instance_and_unlock_returns_its_new_state() {
        let assumptions = PureFactContext::new();
        let old = invariant(1, 0);
        let updated = invariant(1, 1);
        let mutex = mutex(0);
        let published = context(old.clone())
            .publish(mutex.clone(), old.clone(), &assumptions, 40)
            .unwrap();
        assert!(
            !published
                .state()
                .resources
                .satisfies_fact(&old, &assumptions)
        );
        assert!(published.acquire(&self::mutex(1), &assumptions).is_err());

        let (mut holding, guard) = published.acquire(&mutex, &assumptions).unwrap();
        assert!(holding.state().resources.satisfies_fact(&old, &assumptions));
        assert!(holding.acquire(&mutex, &assumptions).is_err());

        // This is the resource-context exchange a checked unfold, C write,
        // and fold would perform. The instance identity remains the same.
        holding.state.resources = holding
            .state
            .resources
            .clone()
            .without_fact(&old, &assumptions)
            .unwrap()
            .try_compose_with_fact(updated.clone(), &assumptions)
            .unwrap();
        let unlocked = holding
            .release(guard, updated.clone(), &assumptions)
            .unwrap();
        assert!(
            !unlocked
                .state()
                .resources
                .satisfies_fact(&updated, &assumptions)
        );
        let (reacquired, _) = unlocked.acquire(&mutex, &assumptions).unwrap();
        assert!(
            reacquired
                .state()
                .resources
                .satisfies_fact(&updated, &assumptions)
        );
    }

    #[test]
    fn unlock_refuses_unfolded_wrong_and_stale_resources() {
        let assumptions = PureFactContext::new();
        let old = invariant(1, 0);
        let mutex = mutex(0);
        let published = context(old.clone())
            .publish(mutex.clone(), old.clone(), &assumptions, 40)
            .unwrap();
        let (holding, guard) = published.acquire(&mutex, &assumptions).unwrap();
        let mut unfolded = holding.clone();
        unfolded.state.resources = unfolded
            .state
            .resources
            .clone()
            .without_fact(&old, &assumptions)
            .unwrap();
        assert_eq!(
            unfolded.release(guard, old.clone(), &assumptions).err(),
            Some(MutexTransitionError::MissingInvariant(old.clone()))
        );

        let wrong = invariant(2, 0);
        let (holding, guard) = published.acquire(&mutex, &assumptions).unwrap();
        assert_eq!(
            holding.release(guard, wrong, &assumptions).err(),
            Some(MutexTransitionError::Refusal(
                "mutex release requires the same resource instance"
            ))
        );
        let stale = MutexGuard {
            mutex: mutex.clone(),
            initialization: MutexInitialization(MutexInitializationId(0), 40),
            epoch: 0,
        };
        assert_eq!(
            holding.release(stale, old, &assumptions).err(),
            Some(MutexTransitionError::Refusal(
                "mutex guard does not match the current holder"
            ))
        );
    }

    #[test]
    fn publication_requires_exclusive_folded_authority() {
        let assumptions = PureFactContext::new();
        let fact = invariant(1, 0);
        let mutex = mutex(0);
        let initial = context(fact.clone());
        assert_eq!(
            initial
                .publish(mutex.clone(), invariant(2, 0), &assumptions, 40)
                .err(),
            Some("mutex invariant is not held as a folded resource")
        );
        let published = initial
            .publish(mutex.clone(), fact.clone(), &assumptions, 40)
            .unwrap();
        assert_eq!(
            published.publish(mutex, fact, &assumptions, 40).err(),
            Some("mutex is already initialized")
        );
    }

    #[test]
    fn c_path_lock_unlock_destroy_returns_the_folded_resource() {
        let assumptions = PureFactContext::new();
        let fact = invariant(1, 0);
        let mutex = mutex(0);
        let initialized = context(fact.clone())
            .publish(mutex.clone(), fact.clone(), &assumptions, 40)
            .unwrap();
        assert_eq!(
            initialized.release_current(&mutex, &assumptions).err(),
            Some(MutexTransitionError::MissingGuard(mutex.clone()))
        );
        let holding = initialized.acquire_current(&mutex, &assumptions).unwrap();
        assert_eq!(
            holding.destroy(&mutex, &assumptions).err(),
            Some(MutexTransitionError::Refusal("cannot destroy a held mutex"))
        );
        let released = holding.release_current(&mutex, &assumptions).unwrap();
        let destroyed = released.destroy(&mutex, &assumptions).unwrap();
        assert!(
            destroyed
                .state()
                .resources
                .satisfies_fact(&fact, &assumptions)
        );
        assert!(destroyed.state().mutex_ledger.is_none());
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    use crate::kernel::*;
    // A real reserved mutex makes the emptiness reader inspect a native write.
    #[test]
    fn wide_writes_to_reserved_mutex_storage_are_refused_without_panicking() {
        let base = Pointer::symbolic(Variable(985_000));
        let ledger = MutexLedger::new().with_inserted(
            base.clone(),
            MutexEntry::Unlocked {
                initialization: MutexInitialization::fresh(40).unwrap(),
                invariant: None,
                interface: None,
            },
        );
        let wide = CMemoryRange::new_wide(
            base,
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            1,
        );
        assert!(
            ledger_storage_write_refusal(&ledger, &wide, &PureFactContext::new(), false).is_some()
        );
    }
}
