//! Checked ownership exchange for one modeled mutex invariant.
//!
//! An unlocked mutex escrows a folded exclusive resource. Acquiring moves
//! that exact fact into the current C state and creates a unique guard.
//! Releasing requires the folded fact back, so an unfolded or damaged body
//! cannot be published to the next holder.
//!
//! The C binding still has to validate the declaration, pointer, status,
//! and initialization before a pthread call can use these transitions.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::persistent::PersistentMap;

use super::{CResource, CResourceFact, CState, Pointer, PureFactContext};

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
#[derive(Clone, Default)]
pub(super) struct MutexContext {
    state: CState,
    mutexes: PersistentMap<Pointer, MutexEntry>,
}

/// An acquisition identity. The private fields cannot be synthesized from a
/// mutex address or an integer value copied by C.
pub(super) struct MutexGuard {
    mutex: Pointer,
    epoch: u64,
}

impl MutexContext {
    pub(super) fn new(state: CState) -> Self {
        Self {
            state,
            mutexes: PersistentMap::default(),
        }
    }

    pub(super) fn state(&self) -> &CState {
        &self.state
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
        if self.mutexes.get(&mutex).is_some() {
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
        Ok(Self {
            state,
            mutexes: self
                .mutexes
                .with_inserted(mutex, MutexEntry::Unlocked(invariant)),
        })
    }

    pub(super) fn acquire(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<(Self, MutexGuard), &'static str> {
        let invariant = match self.mutexes.get(mutex) {
            Some(MutexEntry::Unlocked(invariant)) => invariant.clone(),
            Some(MutexEntry::Locked { .. }) => return Err("mutex is already guarded"),
            None => return Err("mutex has no published invariant"),
        };
        let resources = self
            .state
            .resources
            .clone()
            .try_compose_with_fact(invariant.clone(), assumptions)
            .map_err(|_| "mutex invariant conflicts with current authority")?;
        static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);
        let epoch = NEXT_EPOCH.fetch_add(1, Ordering::Relaxed);
        let mut state = self.state.clone();
        state.resources = resources;
        Ok((
            Self {
                state,
                mutexes: self
                    .mutexes
                    .with_inserted(mutex.clone(), MutexEntry::Locked { invariant, epoch }),
            },
            MutexGuard {
                mutex: mutex.clone(),
                epoch,
            },
        ))
    }

    pub(super) fn release(
        &self,
        guard: MutexGuard,
        restored: CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, &'static str> {
        let previous = match self.mutexes.get(&guard.mutex) {
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
        Ok(Self {
            state,
            mutexes: self
                .mutexes
                .with_inserted(guard.mutex, MutexEntry::Unlocked(restored)),
        })
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
}
