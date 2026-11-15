//! Loop-local abstraction of a guard carried by an ordinary resource.
//!
//! The loop rule checks resource custody at entry and every backedge. This
//! module changes only protocol metadata; neither abstraction nor resolving
//! its heldness creates an owned guard. Payloads and loan-backed guards are
//! deliberately excluded until the loop rule can account for their custody.
use super::*;

pub(in crate::kernel) fn abstract_loop_mutex(
    state: &ExecutionState,
    mutex: &Pointer,
    held: ConditionTerm,
) -> Result<ExecutionState, String> {
    if state.preserves_mutex_protocols {
        return Err("loop mutex abstraction requires a concrete initialization".into());
    }
    let ledger = state
        .mutex_ledger
        .as_ref()
        .ok_or("Requires an initialized loop mutex")?;
    let entry = ledger
        .get(mutex)
        .ok_or("Requires an initialized loop mutex")?;
    let initialization = empty_concrete_initialization(entry)
        .ok_or("loop mutex abstraction currently requires an empty mutex without a use hold")?;
    let live = initialization.resource_fact(mutex);
    if state
        .resources
        .unique_owned_occurrence_for_fact(&live)
        .is_none()
    {
        return Err("Requires owns mutex_live for loop mutex abstraction".into());
    }
    let epoch =
        fresh_acquisition_epoch().map_err(|_| "cannot allocate loop acquisition identity")?;
    let mut result = state.clone();
    result.mutex_ledger = Some(ledger.with_inserted(
        mutex.clone(),
        MutexEntry::ConditionalLoop {
            initialization,
            epoch,
            held,
        },
    ));
    Ok(result)
}

fn empty_concrete_initialization(entry: &MutexEntry) -> Option<MutexInitialization> {
    match entry {
        MutexEntry::Unlocked {
            initialization,
            invariant: None,
            interface: None,
        }
        | MutexEntry::Locked {
            initialization,
            invariant: None,
            interface: None,
            lifetime_hold: None,
            ..
        } => Some(*initialization),
        _ => None,
    }
}

impl MutexContext {
    /// Resolve one conditional receipt under checked path premises, without
    /// altering resources. Unlock still requires the exact owned guard atom.
    pub(super) fn materialize_loop_mutex(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Option<Self>, MutexTransitionError> {
        let Some(ledger) = &self.state.mutex_ledger else {
            return Ok(None);
        };
        let Some(MutexEntry::ConditionalLoop {
            initialization,
            epoch,
            held,
        }) = ledger.get(mutex)
        else {
            return Ok(None);
        };
        let held = crate::kernel::loops::condition_is_decided(assumptions, held).ok_or(
            MutexTransitionError::Refusal(
                "Requires the loop resource to determine whether the mutex is held",
            ),
        )?;
        let entry = if held {
            MutexEntry::Locked {
                initialization: *initialization,
                invariant: None,
                interface: None,
                epoch: *epoch,
                lifetime_hold: None,
            }
        } else {
            MutexEntry::Unlocked {
                initialization: *initialization,
                invariant: None,
                interface: None,
            }
        };
        let mut state = self.state.clone();
        state.mutex_ledger = Some(ledger.with_inserted(mutex.clone(), entry));
        Ok(Some(Self {
            state,
            runtime_loan_transition: None,
        }))
    }
}

impl MutexLedger {
    pub(in crate::kernel) fn is_loop_abstract(&self, mutex: &Pointer) -> bool {
        matches!(self.get(mutex), Some(MutexEntry::ConditionalLoop { .. }))
    }

    /// The caller has independently checked that each listed mutex's returned
    /// loop resource accounts for its actual heldness. All other entries keep
    /// the strict protocol comparison, including acquisition and loan identity.
    pub(in crate::kernel) fn check_loop_protocol_state_since(
        &self,
        next: &Self,
        checked_mutexes: &[Pointer],
    ) -> Result<(), MutexProtocolMismatch> {
        let mut compared = next.clone();
        let mut seen = std::collections::BTreeSet::new();
        for mutex in checked_mutexes {
            crate::instrumentation::record_deterministic_work(1);
            if !seen.insert(mutex) {
                return Err(MutexProtocolMismatch::State);
            }
            let Some(top @ MutexEntry::ConditionalLoop { initialization, .. }) = self.get(mutex)
            else {
                return Err(MutexProtocolMismatch::State);
            };
            let actual = next.get(mutex).ok_or(MutexProtocolMismatch::State)?;
            if actual.initialization() != *initialization {
                return Err(MutexProtocolMismatch::Initialization);
            }
            if empty_concrete_initialization(actual).is_none() {
                return Err(MutexProtocolMismatch::State);
            }
            compared = compared.with_inserted(mutex.clone(), top.clone());
        }
        self.check_protocol_state_since(&compared)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MachineTerm, PointerOffsetTerm, Variable};

    fn mutex(index: usize) -> Pointer {
        Pointer {
            block: format!("loop-mutex-{index}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }
    fn initialized(address: &Pointer) -> MutexContext {
        MutexContext::new(ExecutionState::new())
            .initialize_empty(address.clone(), 40)
            .unwrap()
    }
    fn abstracted(context: &MutexContext, address: &Pointer, held: bool) -> MutexContext {
        MutexContext::new(
            abstract_loop_mutex(context.state(), address, ConditionTerm::Constant(held)).unwrap(),
        )
    }
    fn reveal_guard(context: &MutexContext, address: &Pointer) -> MutexContext {
        let mut state = context.state().clone();
        let guard = state
            .mutex_ledger
            .as_ref()
            .unwrap()
            .guard_resource(address)
            .unwrap();
        state.resources = state.resources.clone().unchecked_with_fact(guard);
        MutexContext::new(state)
    }

    #[test]
    fn conditional_description_never_grants_guard_ownership() {
        let address = mutex(0);
        let concrete = initialized(&address);
        let head = abstracted(&concrete, &address, true);
        assert_eq!(head.state().resources, concrete.state().resources);
        assert!(
            head.state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .has_locked_guard()
        );
        assert!(
            head.state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .has_return_obligation()
        );
        assert!(matches!(
            head.release_current(&address, &PureFactContext::new()),
            Err(MutexTransitionError::MissingGuard(_))
        ));
        assert!(head.destroy(&address, &PureFactContext::new()).is_err());
        assert!(
            head.acquire_current(&address, &PureFactContext::new())
                .is_err()
        );
        let released = reveal_guard(&head, &address)
            .release_current(&address, &PureFactContext::new())
            .unwrap();
        assert!(
            released
                .release_current(&address, &PureFactContext::new())
                .is_err()
        );
        assert!(released.destroy(&address, &PureFactContext::new()).is_ok());
    }

    #[test]
    fn unresolved_heldness_and_stale_receipts_are_rejected() {
        let address = mutex(0);
        let concrete = initialized(&address);
        let condition =
            ConditionTerm::signed_less_than(MachineTerm::Variable(Variable(999)), 0u32.into());
        let head =
            MutexContext::new(abstract_loop_mutex(concrete.state(), &address, condition).unwrap());
        let assumptions = PureFactContext::new();
        assert!(head.acquire_current(&address, &assumptions).is_err());
        assert!(head.release_current(&address, &assumptions).is_err());
        assert!(head.destroy(&address, &assumptions).is_err());
        assert!(head.lend_use(&address, &assumptions).is_err());
        let old = abstracted(&concrete, &address, true);
        let fresh = abstracted(&concrete, &address, true);
        let stale_guard = old
            .state()
            .mutex_ledger
            .as_ref()
            .unwrap()
            .guard_resource(&address)
            .unwrap();
        let mut state = fresh.into_state();
        state.resources = state.resources.clone().unchecked_with_fact(stale_guard);
        assert!(matches!(
            MutexContext::new(state).release_current(&address, &assumptions),
            Err(MutexTransitionError::MissingGuard(_))
        ));
    }

    #[test]
    fn loop_protocol_relaxes_only_selected_acquisitions_in_same_initialization() {
        let address = mutex(0);
        let other = mutex(1);
        let context = initialized(&address)
            .initialize_empty(other.clone(), 40)
            .unwrap();
        let head = abstracted(&context, &address, false);
        let next = head
            .acquire_current(&address, &PureFactContext::new())
            .unwrap();
        let top = head.state().mutex_ledger.as_ref().unwrap();
        assert!(
            top.check_protocol_state_since(next.state().mutex_ledger.as_ref().unwrap())
                .is_err()
        );
        assert!(
            top.check_loop_protocol_state_since(
                next.state().mutex_ledger.as_ref().unwrap(),
                std::slice::from_ref(&address)
            )
            .is_ok()
        );
        assert!(
            top.check_loop_protocol_state_since(
                next.state().mutex_ledger.as_ref().unwrap(),
                &[address.clone(), address.clone()]
            )
            .is_err()
        );
        let changed_frame = next
            .acquire_current(&other, &PureFactContext::new())
            .unwrap();
        assert!(
            top.check_loop_protocol_state_since(
                changed_frame.state().mutex_ledger.as_ref().unwrap(),
                std::slice::from_ref(&address)
            )
            .is_err()
        );
        let reset = head
            .destroy(&address, &PureFactContext::new())
            .unwrap()
            .initialize_empty(address.clone(), 40)
            .unwrap();
        assert_eq!(
            top.check_loop_protocol_state_since(
                reset.state().mutex_ledger.as_ref().unwrap(),
                std::slice::from_ref(&address)
            ),
            Err(MutexProtocolMismatch::Initialization)
        );
        let unrelated = initialized(&address);
        assert!(
            top.check_loop_protocol_state_since(
                unrelated.state().mutex_ledger.as_ref().unwrap(),
                std::slice::from_ref(&address)
            )
            .is_err()
        );
    }

    #[test]
    fn loop_abstraction_requires_owned_lifetime_and_no_loan_hold() {
        let address = mutex(0);
        let context = initialized(&address);
        let (loaned, usage) = context.lend_use(&address, &PureFactContext::new()).unwrap();
        assert!(
            abstract_loop_mutex(loaned.state(), &address, ConditionTerm::Constant(false)).is_err()
        );
        let (held, _) = loaned
            .acquire_using(&address, usage.usage, &PureFactContext::new())
            .unwrap();
        assert!(
            abstract_loop_mutex(held.state(), &address, ConditionTerm::Constant(true)).is_err()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/mutexes/loop_protocol/tests.rs");
    }
}

#[cfg(test)]
mod loop_rule_tests {
    use super::*;
    use crate::kernel::functions::{loop_instance_guard, rewrite_resource_instance};
    use crate::kernel::loops::{loop_binder_state_components_match_at_back_edge, loop_binders};
    use crate::kernel::{
        ComparisonOperator, CompositeResourceDefinition, PointerOffsetTerm, ProgramExpression,
        ProgramType, ProgramValue, ResourceAccessMode, ResourceFamily, ResourceFieldSchema,
        ResourceFieldType, ResourceInstance, ResourceQuantity, ResourceSpec, ResourceStateSource,
        ResourceTerm, ResourceTransferRole, SpecExpression, SpecProposition, Variable, int32,
    };

    fn address() -> Pointer {
        Pointer {
            block: "loop-rule-mutex".into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }
    fn schema() -> ResourceFieldSchema {
        ResourceFieldSchema::new(vec![(
            "parity".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap()
    }
    fn definition() -> CompositeResourceDefinition {
        let guard = ResourceSpec::new(
            ResourceTerm::MutexGuard {
                mutex: Box::new(ProgramExpression::Value(ProgramValue::pointer(address()))),
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .unwrap();
        let mut definition = CompositeResourceDefinition::new(
            "loop_guard",
            vec![],
            Some(SpecProposition::Comparison {
                left: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("parity"),
                ),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(int32(1)),
            }),
            false,
            vec![guard],
            vec![],
        )
        .with_instance_schema(Some(schema()));
        definition.contains_mutex_authority = true;
        definition
    }
    fn instance(parity: u32) -> ResourceInstance {
        ResourceInstance::new(
            Variable(707),
            "loop_guard".into(),
            vec![].into(),
            schema(),
            vec![int32(parity).into()].into(),
        )
        .unwrap()
    }
    fn binder() -> ResourceSpec {
        ResourceSpec::instance(
            Variable(707),
            "guard".into(),
            schema(),
            ResourceSpec::declared(
                ResourceFamily::Composite,
                ResourceAccessMode::Own,
                "loop_guard".into(),
                vec![],
                vec![],
                ResourceTransferRole::Borrow,
                ResourceStateSource::Current,
            )
            .unwrap(),
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap()
    }
    fn top_and_next() -> (ExecutionState, ExecutionState, CompositeResourceDefinition) {
        let definition = definition();
        let assumptions = PureFactContext::new();
        let initialized = MutexContext::new(ExecutionState::new())
            .initialize_empty(address(), 40)
            .unwrap();
        let (folded, _) = rewrite_resource_instance(
            initialized.state(),
            &instance(0),
            &definition,
            &assumptions,
            false,
        )
        .unwrap();
        let top = abstract_loop_mutex(&folded, &address(), ConditionTerm::Constant(false)).unwrap();
        let (opened, _) =
            rewrite_resource_instance(&top, &instance(0), &definition, &assumptions, true).unwrap();
        let acquired = MutexContext::new(opened)
            .acquire_current(&address(), &assumptions)
            .unwrap();
        let (next, _) = rewrite_resource_instance(
            acquired.state(),
            &instance(1),
            &definition,
            &assumptions,
            false,
        )
        .unwrap();
        (top, next, definition)
    }

    #[test]
    fn checked_loop_guard_join_accepts_ordinary_folded_acquisition() {
        let (top, next, definition) = top_and_next();
        let binders = loop_binders(&[binder()]);
        assert!(
            loop_binder_state_components_match_at_back_edge(
                &top,
                &next,
                &binders,
                &PureFactContext::new(),
                &[definition]
            )
            .is_ok()
        );
    }

    #[test]
    fn checked_loop_guard_join_rejects_missing_or_inconsistent_custody() {
        let (top, next, definition) = top_and_next();
        let assumptions = PureFactContext::new();
        let binders = loop_binders(&[binder()]);
        let (opened, _) =
            rewrite_resource_instance(&next, &instance(1), &definition, &assumptions, true)
                .unwrap();
        assert!(
            loop_binder_state_components_match_at_back_edge(
                &top,
                &opened,
                &binders,
                &assumptions,
                std::slice::from_ref(&definition)
            )
            .unwrap_err()
            .contains("Requires owns")
        );
        // Idle is an ordinary empty resource, so it can be folded while the
        // actual acquisition remains outstanding beside it. The join must
        // reject that mismatch before erasing the returned model value.
        let (idle, _) =
            rewrite_resource_instance(&opened, &instance(0), &definition, &assumptions, false)
                .unwrap();
        assert!(
            loop_binder_state_components_match_at_back_edge(
                &top,
                &idle,
                &binders,
                &assumptions,
                std::slice::from_ref(&definition)
            )
            .unwrap_err()
            .contains("does not match")
        );
        let duplicate = vec![binders[0].clone(), binders[0].clone()];
        assert!(
            loop_binder_state_components_match_at_back_edge(
                &top,
                &next,
                &duplicate,
                &assumptions,
                &[definition]
            )
            .is_err()
        );
    }

    #[test]
    fn checked_loop_guard_join_does_not_discard_exposed_guard() {
        let (top, next, definition) = top_and_next();
        let mut forged = next.clone();
        let guard = forged
            .mutex_ledger
            .as_ref()
            .unwrap()
            .guard_resource(&address())
            .unwrap();
        forged.resources = forged.resources.clone().unchecked_with_fact(guard);
        assert!(
            loop_binder_state_components_match_at_back_edge(
                &top,
                &forged,
                &loop_binders(&[binder()]),
                &PureFactContext::new(),
                &[definition]
            )
            .is_err()
        );
    }

    #[test]
    fn loop_guard_projection_rejects_unsupported_body_metadata() {
        let (state, _, definition) = top_and_next();
        let mut invalid = Vec::new();
        let mut candidate = definition.clone();
        candidate.parameters.push(crate::kernel::program_parameter(
            "extra",
            ProgramType::Int32,
        ));
        invalid.push(candidate);
        let mut candidate = definition.clone();
        candidate.recursive = true;
        invalid.push(candidate);
        let mut candidate = definition.clone();
        candidate.facts.push(SpecProposition::Comparison {
            left: SpecExpression::Value(int32(0)),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        });
        invalid.push(candidate);
        for (role, retained_state, term_state) in [
            (
                ResourceTransferRole::Borrow,
                ResourceStateSource::Current,
                ResourceStateSource::Current,
            ),
            (
                ResourceTransferRole::Consume,
                ResourceStateSource::Entry,
                ResourceStateSource::Current,
            ),
            (
                ResourceTransferRole::Consume,
                ResourceStateSource::Current,
                ResourceStateSource::Entry,
            ),
        ] {
            let mut candidate = definition.clone();
            candidate.contains = vec![
                ResourceSpec::new(
                    ResourceTerm::MutexGuard {
                        mutex: Box::new(ProgramExpression::Value(ProgramValue::pointer(address()))),
                        state_source: term_state,
                    },
                    ResourceAccessMode::Own,
                    ResourceQuantity::One,
                    role,
                    retained_state,
                )
                .unwrap(),
            ];
            invalid.push(candidate);
        }
        for candidate in invalid {
            assert!(
                loop_instance_guard(&state, &instance(0), &[candidate], &PureFactContext::new())
                    .is_err()
            );
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/mutexes/loop_protocol/loop_rule_tests.rs");
    }
}
