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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MutexTransitionError {
    NotInitialized,
    Refusal(&'static str),
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
struct MutexInitialization(u64);

impl MutexInitialization {
    fn fresh() -> Result<Self, &'static str> {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .map(Self)
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

struct MutexLedgerStorage {
    identity: u64,
    entries: PersistentMap<Pointer, MutexEntry>,
    locked_count: usize,
    return_obligation_count: usize,
    /// A loop join need only revisit mutexes changed since its head. Keeping
    /// this path avoids scanning unrelated mutexes on every back edge.
    predecessor: Option<Arc<MutexLedgerStorage>>,
    changed_mutex: Option<Pointer>,
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
        CResourceFact::own(CResource::MutexGuard(super::MutexGuardIdentity {
            epoch: Some(self.epoch),
            mutex: self.mutex.clone(),
        }))
    }
}

/// Describe the acquisition selected by a resource clause. This does not insert
/// ownership. Abstract entry construction may assume this atom just as it assumes
/// other declared input resources; execution must consume checked ownership.
pub(super) fn guard_resource(
    state: &CState,
    mutex: &Pointer,
    abstract_entry: bool,
) -> Option<CResourceFact> {
    if let Some(ledger) = &state.mutex_ledger {
        return ledger.guard_resource(mutex);
    }
    (abstract_entry || state.preserves_mutex_protocols).then(|| {
        CResourceFact::own(CResource::MutexGuard(super::MutexGuardIdentity {
            epoch: None,
            mutex: mutex.clone(),
        }))
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
    pub(super) fn initialize_empty(&self, mutex: Pointer) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving guard contracts cannot change mutex protocols");
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        if ledger.get(&mutex).is_some() {
            return Err("mutex is already initialized");
        }
        let mut state = self.state.clone();
        state.mutex_ledger = Some(ledger.with_inserted(
            mutex,
            MutexEntry::Unlocked {
                initialization: MutexInitialization::fresh()?,
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
    ) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving guard contracts cannot change mutex protocols");
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
            .without_fact(&invariant, assumptions)
            .ok_or("mutex invariant cannot be moved to escrow")?;
        let mut state = self.state.clone();
        state.resources = resources;
        state.mutex_ledger = Some(ledger.with_inserted(
            mutex,
            MutexEntry::Unlocked {
                initialization: MutexInitialization::fresh()?,
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
                "preserving guard contracts cannot change mutex protocols",
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
        let resources = if let Some(invariant) = &invariant {
            self.state
                .resources
                .clone()
                .try_compose_with_fact(invariant.clone(), assumptions)
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
            .try_compose_with_fact(guard.resource_fact(), assumptions)
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
    ) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving guard contracts cannot change mutex protocols");
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (previous, initialization, epoch) = match ledger.get(mutex) {
            Some(MutexEntry::Locked {
                invariant,
                initialization,
                epoch,
            }) => (invariant, *initialization, *epoch),
            _ => return Err("mutex is not held by this C path"),
        };
        let restored = match previous {
            Some(CResourceFact::Own(CResource::Instance(instance), _)) => {
                let current = self
                    .state
                    .resources
                    .owned_instance(instance.identity())
                    .ok_or("mutex invariant must be folded before unlock")?;
                Some(CResourceFact::own(CResource::Instance(current.clone())))
            }
            _ => previous.clone(),
        };
        self.release_with_invariant(
            MutexGuard {
                mutex: mutex.clone(),
                initialization,
                epoch,
            },
            restored,
            assumptions,
        )
    }

    pub(super) fn destroy(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexTransitionError> {
        if self.state.preserves_mutex_protocols {
            return Err(MutexTransitionError::Refusal(
                "preserving guard contracts cannot change mutex protocols",
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
        let resources = if let Some(invariant) = invariant {
            self.state
                .resources
                .clone()
                .try_compose_with_fact(invariant, assumptions)
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "destroyed mutex invariant conflicts with current authority",
                    )
                })?
        } else {
            self.state.resources.clone()
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
    ) -> Result<Self, &'static str> {
        self.release_with_invariant(guard, Some(restored), assumptions)
    }

    fn release_with_invariant(
        &self,
        guard: MutexGuard,
        restored: Option<CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        if self.state.preserves_mutex_protocols {
            return Err("preserving guard contracts cannot change mutex protocols");
        }
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let previous = match ledger.get(&guard.mutex) {
            Some(MutexEntry::Locked {
                invariant,
                initialization,
                epoch,
            }) if *initialization == guard.initialization && *epoch == guard.epoch => invariant,
            _ => return Err("mutex guard does not match the current holder"),
        };
        let guard_fact = guard.resource_fact();
        if !self
            .state
            .resources
            .contains_exact_representation(&guard_fact)
        {
            return Err("mutex unlock requires ownership of the current guard");
        }
        if !same_instance(previous, &restored) {
            return Err("mutex release requires the same resource instance");
        }
        if restored.is_some()
            && (self
                .state
                .loan_ledger
                .as_ref()
                .is_some_and(|ledger| ledger.has_active_memory_loans())
                || self.state.loan_view_bindings.iter().next().is_some())
        {
            return Err("mutex release with a loan ledger is not supported");
        }
        let resources = if let Some(restored) = &restored {
            if !self.state.resources.contains_exact_representation(restored) {
                return Err("mutex invariant must be folded before unlock");
            }
            self.state
                .resources
                .clone()
                .without_fact(restored, assumptions)
                .ok_or("mutex invariant cannot be returned to escrow")?
        } else {
            self.state.resources.clone()
        };
        let mut state = self.state.clone();
        state.resources = resources
            .without_fact(&guard_fact, assumptions)
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

    pub(super) fn guard_resource(&self, mutex: &Pointer) -> Option<CResourceFact> {
        match self.get(mutex) {
            Some(MutexEntry::Locked { epoch, .. }) => Some(CResourceFact::own(
                CResource::MutexGuard(super::MutexGuardIdentity {
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
                entries: self.storage.entries.without_key(mutex),
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

    /// An unlocked empty mutex has no resource or guard to discharge at return.
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
            .initialize_empty(address.clone())
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
            .initialize_empty(mutex(0))
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
            .initialize_empty(address.clone())
            .unwrap();
        let (holding, _) = initialized.acquire(&address, &assumptions).unwrap();
        let mut state = holding.into_state();
        state.preserves_mutex_protocols = true;
        let frozen = MutexContext::new(state.clone());
        let message = "preserving guard contracts cannot change mutex protocols";
        assert_eq!(frozen.initialize_empty(mutex(1)).err(), Some(message));
        assert_eq!(
            frozen.acquire(&address, &assumptions).err(),
            Some(MutexTransitionError::Refusal(message))
        );
        assert_eq!(
            frozen.release_current(&address, &assumptions).err(),
            Some(message)
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
            .initialize_empty(mutex.clone())
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
            Some("mutex unlock requires ownership of the current guard")
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
            Some("mutex unlock requires ownership of the current guard")
        );
        assert_eq!(
            reacquired
                .release_with_invariant(guard, None, &assumptions)
                .err(),
            Some("mutex guard does not match the current holder")
        );
    }

    #[test]
    fn guard_algebra_is_exclusive_unit_ownership_without_views_or_memory() {
        let assumptions = PureFactContext::new();
        let (holding, guard) = MutexContext::new(CState::new())
            .initialize_empty(mutex(0))
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
                context = context.initialize_empty(mutex(index)).unwrap();
                context = context
                    .acquire_current(&mutex(index), &assumptions)
                    .unwrap();
            }
            let target = mutex(size);
            context = context.initialize_empty(target.clone()).unwrap();
            let ((holding, released), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let holding = context.acquire_current(&target, &assumptions).unwrap();
                    let released = holding.release_current(&target, &assumptions).unwrap();
                    (holding, released)
                });
            assert_eq!(holding.state.resources.facts().len(), size + 1);
            assert_eq!(released.state.resources.facts().len(), size);
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
    fn empty_mutex_supplies_and_consumes_exclusive_guard() {
        let assumptions = PureFactContext::new();
        let mutex = mutex(0);
        let initialized = MutexContext::new(CState::new())
            .initialize_empty(mutex.clone())
            .unwrap();
        assert!(
            !initialized
                .state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .has_return_obligation()
        );
        assert!(initialized.state().resources.facts().is_empty());
        assert_eq!(
            initialized.initialize_empty(mutex.clone()).err(),
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
        assert_eq!(held.state().resources.facts().len(), 1);
        assert!(matches!(
            held.state().resources.facts()[0].resource(),
            CResource::MutexGuard(_)
        ));
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
        assert!(unlocked.state().resources.facts().is_empty());
        let destroyed = unlocked.destroy(&mutex, &assumptions).unwrap();
        assert!(destroyed.state().mutex_ledger.is_none());
    }

    #[test]
    fn loop_back_edge_checks_mutex_ownership_and_accepts_a_balanced_exchange() {
        let assumptions = PureFactContext::new();
        let mutex = mutex(0);
        let head = MutexContext::new(CState::new())
            .initialize_empty(mutex.clone())
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
            let initial = initial.initialize_empty(mutex(1)).unwrap();
            let initialize = |state: &MutexContext| match &protected {
                Some(fact) => state.publish(mutex(0), fact.clone(), &assumptions).unwrap(),
                None => state.initialize_empty(mutex(0)).unwrap(),
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
        let first = initial.initialize_empty(mutex(0)).unwrap();
        let second = initial.initialize_empty(mutex(0)).unwrap();
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
            Some("mutex guard does not match the current holder")
        );
        held.release_current(&mutex(0), &assumptions).unwrap();
    }

    #[test]
    fn loop_may_initialize_and_destroy_a_mutex_absent_at_its_head() {
        let assumptions = PureFactContext::new();
        let head = MutexContext::new(CState::new())
            .initialize_empty(mutex(0))
            .unwrap();
        let local = head.initialize_empty(mutex(1)).unwrap();
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
                head = head.initialize_empty(mutex(index)).unwrap();
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
                .initialize_empty(selected)
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
            .publish(mutex.clone(), old.clone(), &assumptions)
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
            .publish(mutex.clone(), old.clone(), &assumptions)
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
            Some("mutex invariant must be folded before unlock")
        );

        let wrong = invariant(2, 0);
        let (holding, guard) = published.acquire(&mutex, &assumptions).unwrap();
        assert_eq!(
            holding.release(guard, wrong, &assumptions).err(),
            Some("mutex release requires the same resource instance")
        );
        let stale = MutexGuard {
            mutex: mutex.clone(),
            initialization: MutexInitialization(0),
            epoch: 0,
        };
        assert_eq!(
            holding.release(stale, old, &assumptions).err(),
            Some("mutex guard does not match the current holder")
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
                .publish(mutex.clone(), invariant(2, 0), &assumptions)
                .err(),
            Some("mutex invariant is not held as a folded resource")
        );
        let published = initial
            .publish(mutex.clone(), fact.clone(), &assumptions)
            .unwrap();
        assert_eq!(
            published.publish(mutex, fact, &assumptions).err(),
            Some("mutex is already initialized")
        );
    }

    #[test]
    fn c_path_lock_unlock_destroy_returns_the_folded_resource() {
        let assumptions = PureFactContext::new();
        let fact = invariant(1, 0);
        let mutex = mutex(0);
        let initialized = context(fact.clone())
            .publish(mutex.clone(), fact.clone(), &assumptions)
            .unwrap();
        assert_eq!(
            initialized.release_current(&mutex, &assumptions).err(),
            Some("mutex is not held by this C path")
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
