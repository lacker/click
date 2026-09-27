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

use std::cmp::Ordering as CmpOrdering;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::persistent::PersistentMap;

use super::{CResource, CResourceFact, CState, ConditionTerm, Pointer, PureFactContext};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MutexTransitionError {
    NotInitialized,
    MissingGuard(Pointer),
    MissingLive(Pointer),
    MissingInvariant(CResourceFact),
    Refusal(&'static str),
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
            Self::MissingGuard(mutex) => super::CRuntimeError::MissingMutexGuard { mutex },
            Self::MissingInvariant(resource) => {
                super::CRuntimeError::MissingMutexInvariant { resource }
            }
            Self::Refusal(message) => super::CRuntimeError::FunctionContract(message.into()),
        }
    }
}

#[derive(Clone)]
enum MutexEntry {
    Unlocked {
        initialization: MutexInitialization,
        invariant: Option<CResourceFact>,
    },
    Locked {
        initialization: MutexInitialization,
        invariant: Option<CResourceFact>,
        epoch: u64,
    },
}

/// Identity of one successful initialization, independent of its address and
/// protected assertion. Lock/unlock retain it; destroy/init must replace it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MutexInitialization(u64, u32);

impl MutexInitialization {
    fn resource_fact(self, mutex: &Pointer) -> CResourceFact {
        CResourceFact::own(CResource::MutexLive(super::MutexIdentity {
            epoch: Some(self.0),
            mutex: mutex.clone(),
        }))
    }

    fn fresh(storage_bytes: u32) -> Result<Self, &'static str> {
        if storage_bytes == 0 {
            return Err("mutex storage extent must be nonzero");
        }
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .map(|identity| Self(identity, storage_bytes))
        .map_err(|_| "mutex initialization identity space exhausted")
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
            PointerBlock::Symbolic(_) => Self::Symbolic,
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
    by_block: PersistentMap<super::PointerBlock, PersistentMap<Pointer, u32>>,
    reserved: MutexStorageIndex,
    by_provenance: PersistentMap<StorageProvenance, PersistentMap<Pointer, u32>>,
    /// Initializations whose symbolic provenance may name any automatic object.
    /// Kept separately so a scope exit never scans unrelated concrete mutexes.
    ambiguous_automatic_storage: PersistentMap<Pointer, ()>,
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
    let ledger = state.mutex_ledger.as_ref()?;
    if !ledger.has_any_mutex() || write.start() == write.end() {
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
        let storage = storage_range(mutex, *bytes);
        // Evaluate ranges in byte units with checked signed arithmetic. This
        // covers interior writes, adjacent fields, and mixed element widths.
        let disjoint = (|| {
            let delta = mutex.exact_element_delta_from_base(write.base(), 1, None)?;
            if !delta.is_constant() {
                return None;
            }
            let start = i64::from(write.start().as_const()? as i32)
                .checked_mul(i64::from(write.element_width()))?;
            let end = i64::from(write.end().as_const()? as i32)
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
                write: write.clone(),
                storage,
            });
        }
    }
    None
}

/// An acquisition identity. The private fields cannot be synthesized from a
/// mutex address or an integer value copied by C.
pub(super) struct MutexGuard {
    mutex: Pointer,
    initialization: MutexInitialization,
    epoch: u64,
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

/// Describe an acquisition without establishing ownership. Abstract entry
/// assumptions are inputs; execution still requires checked resource transfer.
pub(super) fn guard_resource(
    state: &CState,
    mutex: &Pointer,
    abstract_entry: bool,
) -> Option<CResourceFact> {
    if let Some(ledger) = &state.mutex_ledger {
        return ledger.guard_resource(mutex);
    }
    (abstract_entry || state.preserves_mutex_protocols).then(|| {
        CResourceFact::own(CResource::MutexGuard(super::MutexIdentity {
            epoch: None,
            mutex: mutex.clone(),
        }))
    })
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
    let resolved = super::primitives::storage_pointer_spellings(mutex, assumptions)
        .pop()
        .expect("storage spelling");
    let range =
        super::CMemoryRange::new_with_element_width(mutex.clone(), 0u32.into(), bytes.into(), 1);
    let automatic =
        resolved.block.starts_with("local:") && state.memory.access_in_bounds(&resolved, bytes);
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
        return Some(super::CRuntimeError::MissingResource {
            resource: CResourceFact::own_memory(range),
        });
    }
    if assumptions.decide(&ConditionTerm::pointer_aligned(
        mutex.clone(),
        u64::from(alignment),
    )) != Some(true)
        && assumptions.decide(&ConditionTerm::pointer_aligned(
            resolved.clone(),
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
        .map(super::CRuntimeError::LoanRefusal)
}

/// A storage release must not leave a live initialization behind. Abstract
/// guard contracts lack checked lifecycle inputs for deciding this dependency;
/// refuse retirement there until the lifetime-loan model can discharge it.
pub(super) fn storage_retirement_refusal(
    state: &CState,
    allocation: &super::CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<super::CRuntimeError> {
    if state.preserves_mutex_protocols && state.mutex_ledger.is_none() {
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
        Self { state }
    }

    pub(super) fn state(&self) -> &CState {
        &self.state
    }

    pub(super) fn into_state(self) -> CState {
        self.state
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
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
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
            },
        ));
        Ok(Self { state })
    }

    /// Deposit one folded, exclusive instance into an initialized mutex.
    /// The C binder will check that `mutex` is the field declared by this
    /// resource's `guarded_by` clause.
    pub(super) fn publish(
        &self,
        mutex: Pointer,
        invariant: CResourceFact,
        assumptions: &PureFactContext,
        storage_bytes: u32,
    ) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols");
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
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
            },
        ));
        Ok(Self { state })
    }

    pub(super) fn acquire(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexGuard), MutexTransitionError> {
        if self.state.preserves_mutex_protocols {
            return Err(MutexTransitionError::Refusal(
                "preserving mutex contracts cannot change mutex protocols",
            ));
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (initialization, invariant) = match ledger.get(mutex) {
            Some(MutexEntry::Unlocked {
                initialization,
                invariant,
            }) => (*initialization, invariant.clone()),
            Some(MutexEntry::Locked { .. }) => {
                return Err(MutexTransitionError::Refusal("mutex is already guarded"));
            }
            None => return Err(MutexTransitionError::NotInitialized),
        };
        if !self
            .state
            .resources
            .satisfies_fact(&initialization.resource_fact(mutex), assumptions)
        {
            return Err(MutexTransitionError::MissingLive(mutex.clone()));
        }
        let resources = if let Some(invariant) = &invariant {
            self.state
                .resources
                .clone()
                .try_compose_with_facts_delaying_normalization([invariant.clone()], assumptions)
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "mutex invariant conflicts with current authority",
                    )
                })?
        } else {
            self.state.resources.clone()
        };
        static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);
        let epoch = NEXT_EPOCH
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |epoch| {
                epoch.checked_add(1)
            })
            .map_err(|_| {
                MutexTransitionError::Refusal("mutex acquisition identity space exhausted")
            })?;
        let mut state = self.state.clone();
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
                epoch,
            },
        ));
        Ok((
            Self { state },
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
        self.acquire(mutex, assumptions).map(|(context, _)| context)
    }

    pub(super) fn release_current(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols".into());
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (previous, initialization, epoch) = match ledger.get(mutex) {
            Some(MutexEntry::Locked {
                invariant,
                initialization,
                epoch,
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
        if self.state.preserves_mutex_protocols {
            return Err(MutexTransitionError::Refusal(
                "preserving mutex contracts cannot change mutex protocols",
            ));
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let invariant = match ledger.get(mutex) {
            Some(MutexEntry::Unlocked { invariant, .. }) => invariant.clone(),
            Some(MutexEntry::Locked { .. }) => {
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
        let mut state = self.state.clone();
        state.resources = resources;
        let next = ledger.without(mutex);
        state.mutex_ledger = next.has_any_mutex().then_some(next);
        Ok(Self { state })
    }

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
        if self.state.preserves_mutex_protocols {
            return Err("preserving mutex contracts cannot change mutex protocols".into());
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let previous = match ledger.get(&guard.mutex) {
            Some(MutexEntry::Locked {
                invariant,
                initialization,
                epoch,
            }) if *initialization == guard.initialization && *epoch == guard.epoch => invariant,
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
        if !same_instance(previous, &restored) {
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
        state.resources = resources
            .without_fact_delaying_normalization(&guard_fact, assumptions)
            .ok_or("mutex guard cannot be consumed")?;
        state.mutex_ledger = Some(ledger.with_inserted(
            guard.mutex,
            MutexEntry::Unlocked {
                initialization: guard.initialization,
                invariant: restored,
            },
        ));
        Ok(Self { state })
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
                by_block: PersistentMap::default(),
                reserved: MutexStorageIndex::default(),
                by_provenance: PersistentMap::default(),
                ambiguous_automatic_storage: PersistentMap::default(),
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
                if allocation.element_width() != 1 || allocation.start().as_const() != Some(0) {
                    return None;
                }
                let extent = i64::from(allocation.end().as_const()?);
                let delta = mutex.exact_element_delta_from_base(allocation.base(), 1, None)?;
                if !delta.is_constant() {
                    return None;
                }
                let end = delta.constant.checked_add(i64::from(*bytes))?;
                Some(end <= 0 || delta.constant >= extent)
            })() == Some(true);
            if !disjoint
                && !assumptions.proves_exact(&super::Proposition::CResourceSeparate {
                    left: allocation_resource.clone(),
                    right: storage,
                })
            {
                return Some(if &mutex.block == block {
                    super::CRuntimeError::MutexStorageInUse {
                        mutex: mutex.clone(),
                        allocation: allocation.base().clone(),
                    }
                } else {
                    super::CRuntimeError::MutexStorageSeparationRequired {
                        allocation: allocation.clone(),
                        storage: super::CMemoryRange::new_with_element_width(
                            mutex.clone(),
                            0u32.into(),
                            (*bytes).into(),
                            1,
                        ),
                    }
                });
            }
        }
        None
    }

    pub(super) fn live_resource(&self, mutex: &Pointer) -> Option<CResourceFact> {
        let (MutexEntry::Unlocked { initialization, .. }
        | MutexEntry::Locked { initialization, .. }) = self.get(mutex)?;
        Some(initialization.resource_fact(mutex))
    }

    pub(super) fn guard_resource(&self, mutex: &Pointer) -> Option<CResourceFact> {
        match self.get(mutex) {
            Some(MutexEntry::Locked { epoch, .. }) => Some(CResourceFact::own(
                CResource::MutexGuard(super::MutexIdentity {
                    epoch: Some(*epoch),
                    mutex: mutex.clone(),
                }),
            )),
            _ => None,
        }
    }

    pub(super) fn held_condition(&self, mutex: &Pointer) -> ConditionTerm {
        ConditionTerm::Constant(matches!(self.get(mutex), Some(MutexEntry::Locked { .. })))
    }

    fn with_inserted(&self, mutex: Pointer, entry: MutexEntry) -> Self {
        let was_locked = matches!(self.get(&mutex), Some(MutexEntry::Locked { .. }));
        let now_locked = matches!(entry, MutexEntry::Locked { .. });
        let had_return_obligation = self
            .get(&mutex)
            .is_some_and(MutexEntry::has_return_obligation);
        let has_return_obligation = entry.has_return_obligation();
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
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
        let was_locked = matches!(self.get(mutex), Some(MutexEntry::Locked { .. }));
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
                ambiguous_automatic_storage: if may_alias_automatic_storage(&mutex.block) {
                    self.storage.ambiguous_automatic_storage.without_key(mutex)
                } else {
                    self.storage.ambiguous_automatic_storage.clone()
                },
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
                        ..
                    }),
                    Some(MutexEntry::Locked {
                        invariant: right,
                        epoch: right_epoch,
                        ..
                    }),
                ) if left == right && left_epoch == right_epoch => {}
                (None, None) => {}
                _ => return Err(MutexProtocolMismatch::State),
            }
        }
        Ok(())
    }
}

impl MutexEntry {
    fn initialization(&self) -> MutexInitialization {
        match self {
            Self::Unlocked { initialization, .. } | Self::Locked { initialization, .. } => {
                *initialization
            }
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
                resource: protected
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
            CStatementOutcome::Normal(state.clone()),
            CStatementOutcome::Break(state.clone()),
            CStatementOutcome::Continue(state.clone()),
            CStatementOutcome::Return {
                value: int32(0),
                state: state.clone(),
            },
            CStatementOutcome::Throw {
                value: int32(0),
                state: state.clone(),
            },
            CStatementOutcome::Jump {
                target: CControlTargetId(1),
                state: state.clone(),
            },
        ];
        for outcome in outcomes {
            let paths = eval::paths_after_scope_exit(
                vec![CStatementExecutionPath {
                    outcome,
                    facts: vec![],
                    obligations: vec![],
                    loop_invariant_correspondence: Default::default(),
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }],
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
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
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
                &environment,
                CExecutionSemantics::EXECUTE_BODIES,
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
        let separated = assumptions.assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(write.clone()),
            right: CResource::Memory(storage_range(&address, 40)),
        });
        assert!(storage_write_refusal(context.state(), &write, &separated).is_none());
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
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
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
                &environment,
                CExecutionSemantics::EXECUTE_BODIES,
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
            let mut resources = ResourceContext::new();
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
            allocation: allocation.clone(),
            storage: storage.clone(),
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
                left: CResource::Memory(allocation.clone()),
                right: CResource::Memory(storage),
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
                volatile: false,
                pointee_volatile: false,
                constant: false,
                pointee_constant: false,
            },
            CStatement::DeclareAggregate {
                name: "holder".into(),
                layout: layout.clone(),
                construction: false,
            },
            CStatement::DeclareAggregate {
                name: "holder".into(),
                layout,
                construction: true,
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
                    &CExecutionEnvironment::new(),
                    CExecutionSemantics::EXECUTE_BODIES,
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
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
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
            initialization: MutexInitialization(0, 40),
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
