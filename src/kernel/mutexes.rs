//! Checked ownership exchange for one modeled mutex invariant.
//!
//! An unlocked mutex escrows a folded exclusive resource. Acquiring moves
//! that exact fact into the current C state and creates a unique guard.
//! Releasing requires the folded fact back, so an unfolded or damaged body
//! cannot be published to the next holder.
//!
//! The C binding still has to validate the declaration, pointer, status,
//! and initialization before a pthread call can use these transitions.

use std::cmp::Ordering as CmpOrdering;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::persistent::PersistentMap;

use super::{CResource, CResourceFact, CState, Pointer, PureFactContext};

#[derive(Debug)]
pub(super) enum MutexAcquireError {
    MissingPublishedInvariant,
    Refusal(&'static str),
}

#[derive(Clone)]
enum MutexEntry {
    Unlocked(CResourceFact),
    Locked {
        invariant: CResourceFact,
        epoch: u64,
    },
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
}

/// An acquisition identity. The private fields cannot be synthesized from a
/// mutex address or an integer value copied by C.
pub(super) struct MutexGuard {
    mutex: Pointer,
    epoch: u64,
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

    /// Deposit one folded, exclusive instance into an initialized mutex.
    /// The C binder will check that `mutex` is the field declared by this
    /// resource's `guarded_by` clause.
    pub(super) fn publish(
        &self,
        mutex: Pointer,
        invariant: CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        if ledger.get(&mutex).is_some() {
            return Err("mutex already has an invariant");
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
        state.mutex_ledger = Some(ledger.with_inserted(mutex, MutexEntry::Unlocked(invariant)));
        Ok(Self { state })
    }

    pub(super) fn acquire(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexGuard), MutexAcquireError> {
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let invariant = match ledger.get(mutex) {
            Some(MutexEntry::Unlocked(invariant)) => invariant.clone(),
            Some(MutexEntry::Locked { .. }) => {
                return Err(MutexAcquireError::Refusal("mutex is already guarded"));
            }
            None => return Err(MutexAcquireError::MissingPublishedInvariant),
        };
        let resources = self
            .state
            .resources
            .clone()
            .try_compose_with_fact(invariant.clone(), assumptions)
            .map_err(|_| {
                MutexAcquireError::Refusal("mutex invariant conflicts with current authority")
            })?;
        static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);
        let epoch = NEXT_EPOCH.fetch_add(1, Ordering::Relaxed);
        let mut state = self.state.clone();
        state.resources = resources;
        state.mutex_ledger =
            Some(ledger.with_inserted(mutex.clone(), MutexEntry::Locked { invariant, epoch }));
        Ok((
            Self { state },
            MutexGuard {
                mutex: mutex.clone(),
                epoch,
            },
        ))
    }

    pub(super) fn acquire_current(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexAcquireError> {
        self.acquire(mutex, assumptions).map(|(context, _)| context)
    }

    pub(super) fn release_current(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let (previous, epoch) = match ledger.get(mutex) {
            Some(MutexEntry::Locked { invariant, epoch }) => (invariant, *epoch),
            _ => return Err("mutex is not held by this C path"),
        };
        let restored = match previous {
            CResourceFact::Own(CResource::Instance(instance), _) => {
                let current = self
                    .state
                    .resources
                    .owned_instance(instance.identity())
                    .ok_or("mutex invariant must be folded before unlock")?;
                CResourceFact::own(CResource::Instance(current.clone()))
            }
            _ => previous.clone(),
        };
        self.release(
            MutexGuard {
                mutex: mutex.clone(),
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
    ) -> Result<Self, &'static str> {
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let invariant = match ledger.get(mutex) {
            Some(MutexEntry::Unlocked(invariant)) => invariant.clone(),
            Some(MutexEntry::Locked { .. }) => return Err("cannot destroy a held mutex"),
            None => return Err("mutex has no published invariant"),
        };
        let resources = self
            .state
            .resources
            .clone()
            .try_compose_with_fact(invariant, assumptions)
            .map_err(|_| "destroyed mutex invariant conflicts with current authority")?;
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
        let ledger = self.state.mutex_ledger.as_ref().expect("mutex ledger");
        let previous = match ledger.get(&guard.mutex) {
            Some(MutexEntry::Locked { invariant, epoch }) if *epoch == guard.epoch => invariant,
            _ => return Err("mutex guard does not match the current holder"),
        };
        if !same_instance(previous, &restored) {
            return Err("mutex release requires the same resource instance");
        }
        if self
            .state
            .loan_ledger
            .as_ref()
            .is_some_and(|ledger| ledger.has_active_memory_loans())
            || self.state.loan_view_bindings.iter().next().is_some()
        {
            return Err("mutex release with a loan ledger is not supported");
        }
        if !self
            .state
            .resources
            .contains_exact_representation(&restored)
        {
            return Err("mutex invariant must be folded before unlock");
        }
        let resources = self
            .state
            .resources
            .clone()
            .without_fact(&restored, assumptions)
            .ok_or("mutex invariant cannot be returned to escrow")?;
        let mut state = self.state.clone();
        state.resources = resources;
        state.mutex_ledger =
            Some(ledger.with_inserted(guard.mutex, MutexEntry::Unlocked(restored)));
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
            }),
        }
    }

    fn get(&self, mutex: &Pointer) -> Option<&MutexEntry> {
        self.storage.entries.get(mutex)
    }

    fn with_inserted(&self, mutex: Pointer, entry: MutexEntry) -> Self {
        let was_locked = matches!(self.get(&mutex), Some(MutexEntry::Locked { .. }));
        let now_locked = matches!(entry, MutexEntry::Locked { .. });
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
                entries: self.storage.entries.with_inserted(mutex, entry),
                locked_count: self.storage.locked_count + usize::from(now_locked)
                    - usize::from(was_locked),
            }),
        }
    }

    fn without(&self, mutex: &Pointer) -> Self {
        let was_locked = matches!(self.get(mutex), Some(MutexEntry::Locked { .. }));
        Self {
            storage: Arc::new(MutexLedgerStorage {
                identity: Self::fresh_identity(),
                entries: self.storage.entries.without_key(mutex),
                locked_count: self.storage.locked_count - usize::from(was_locked),
            }),
        }
    }

    pub(super) fn has_locked_guard(&self) -> bool {
        self.storage.locked_count != 0
    }

    pub(super) fn has_any_mutex(&self) -> bool {
        !self.storage.entries.is_empty()
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

fn same_instance(previous: &CResourceFact, restored: &CResourceFact) -> bool {
    match (previous, restored) {
        (
            CResourceFact::Own(CResource::Instance(previous), previous_quantity),
            CResourceFact::Own(CResource::Instance(restored), restored_quantity),
        ) => {
            previous_quantity.as_const() == Some(1)
                && restored_quantity.as_const() == Some(1)
                && previous.identity() == restored.identity()
                && previous.name() == restored.name()
                && previous.arguments() == restored.arguments()
                && previous.schema() == restored.schema()
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        unfolded.state.resources = ResourceContext::new();
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
            Some("mutex already has an invariant")
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
            Some("cannot destroy a held mutex")
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
