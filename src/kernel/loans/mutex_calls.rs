//! Checked resource partition and restoration for one synchronous mutex-use
//! requirement. The contract planner selects the source occurrence. This
//! component never assumes missing authority and does not certify a C body.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MutexUseCallError {
    MissingResource(ResourceFact),
    Unavailable(&'static str),
    Loan(LoanRefusal),
    InvalidResources(crate::kernel::ResourceContextValidityError),
}

impl From<LoanRefusal> for MutexUseCallError {
    fn from(error: LoanRefusal) -> Self {
        Self::Loan(error)
    }
}

/// Retains the source, participants, and checked entry evidence, so return
/// cannot choose a different owner or parent with the same printed address.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexUseCallTransfer {
    pub(crate) caller_resources: ResourceContext,
    pub(crate) callee_resources: ResourceContext,
    pub(crate) ledger: LoanLedger,
    pub(crate) entry_transition: CheckedLoanTransition,
    pub(crate) entry_transitions: Vec<CheckedLoanTransition>,
    suspended_parent: Option<MutexUseBinding>,
    retained_resource: Option<ResourceFact>,
    pub(crate) usage: MutexUseBinding,
    source: ResourceFact,
    selected_alias: Option<Variable>,
    interface: Option<Arc<crate::kernel::mutexes::InitializedMutexInterface>>,
    required_type: Option<ResourceDescription>,
    loan: MutexUseLoan,
    caller: LoanParticipantId,
    callee: LoanParticipantId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexUseCallReturn {
    pub(crate) ledger: LoanLedger,
    pub(crate) caller_resources: ResourceContext,
    /// The other returned clauses remain for the surrounding contract planner
    /// to check and transfer; this component neither grants nor discards them.
    pub(crate) remaining_resources: ResourceContext,
    pub(crate) exit_transitions: Vec<CheckedLoanTransition>,
    pub(crate) authority_updates: Vec<MutexAuthorityUpdate>,
}

/// An alias transport generated only while checking an actual authority exchange.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutexAuthorityUpdate {
    pub(crate) source_occurrence: ResourceOccurrenceId,
    pub(crate) source: ResourceFact,
    pub(crate) derived: ResourceFact,
}

impl MutexUseCallTransfer {
    pub(crate) fn prepare(
        ledger: &LoanLedger,
        caller: LoanParticipantId,
        callee: LoanParticipantId,
        resources: &ResourceContext,
        source: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexUseCallError> {
        let (support, _) = resources
            .unique_owned_occurrence_for_fact(source)
            .ok_or_else(|| MutexUseCallError::MissingResource(source.clone()))?;
        let (ledger, loan, entry_transition) = match source.resource() {
            Resource::MutexLive(_) => {
                ledger.lend_mutex_use_with_transition(caller, callee, support, source.clone())?
            }
            Resource::MutexUse(identity) => {
                ledger.check_mutex_use_available(
                    identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                    caller,
                    resources,
                )?;
                if ledger.mutex_use_resource(
                    identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                    caller,
                )? != *source
                {
                    return Err(LoanRefusal::MissingLoanBinding.into());
                }
                ledger.reborrow_mutex_use_with_transition(
                    identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                    caller,
                    callee,
                )?
            }
            _ => return Err(LoanRefusal::UnsupportedResource.into()),
        };
        let caller_resources = resources
            .clone()
            .without_fact_delaying_normalization(source, assumptions)
            .ok_or_else(|| MutexUseCallError::MissingResource(source.clone()))?;
        let use_fact = ledger.mutex_use_resource(loan.usage, callee)?;
        let callee_resources = ResourceContext::new()
            .try_compose_with_facts_delaying_normalization([use_fact], assumptions)
            .map_err(MutexUseCallError::InvalidResources)?;
        Ok(Self {
            caller_resources,
            callee_resources,
            ledger,
            usage: loan.usage,
            source: source.clone(),
            selected_alias: None,
            interface: None,
            required_type: None,
            loan,
            entry_transitions: vec![entry_transition.clone()],
            entry_transition,
            suspended_parent: None,
            retained_resource: None,
            caller,
            callee,
        })
    }

    /// Keep a caller share available while the worker holds its own child scope.
    pub(crate) fn prepare_suspended(
        ledger: &LoanLedger,
        caller: LoanParticipantId,
        callee: LoanParticipantId,
        resources: &ResourceContext,
        source: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, MutexUseCallError> {
        let (support, _) = resources
            .unique_owned_occurrence_for_fact(source)
            .ok_or_else(|| MutexUseCallError::MissingResource(source.clone()))?;
        let mut ledger = ledger.clone();
        let mut transitions = Vec::new();
        let parent = match source.resource() {
            Resource::MutexLive(_) => {
                let (next, root, transition) = ledger.lend_mutex_use_with_transition(
                    caller,
                    caller,
                    support,
                    source.clone(),
                )?;
                ledger = next;
                transitions.push(transition);
                root.usage
            }
            Resource::MutexUse(identity) => {
                let usage = identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?;
                ledger.check_mutex_use_available(usage, caller, resources)?;
                if ledger.mutex_use_resource(usage, caller)? != *source {
                    return Err(LoanRefusal::MissingLoanBinding.into());
                }
                usage
            }
            _ => return Err(LoanRefusal::UnsupportedResource.into()),
        };
        let (split, retained, worker) = ledger.split(parent.0.share, caller, caller, caller)?;
        ledger = ledger.apply(&split)?;
        transitions.push(split);
        let retained = MutexUseBinding(LoanAuthorityBinding {
            share: retained,
            ..parent.0
        });
        let worker = MutexUseBinding(LoanAuthorityBinding {
            share: worker,
            ..parent.0
        });
        let (ledger, loan, entry_transition) =
            ledger.reborrow_mutex_use_with_transition(worker, caller, callee)?;
        transitions.push(entry_transition.clone());
        let caller_resources = resources
            .clone()
            .without_fact_delaying_normalization(source, assumptions)
            .ok_or_else(|| MutexUseCallError::MissingResource(source.clone()))?
            .try_compose_with_facts_delaying_normalization(
                [ledger.mutex_use_resource(retained, caller)?],
                assumptions,
            )
            .map_err(MutexUseCallError::InvalidResources)?;
        let callee_resources = ResourceContext::new()
            .try_compose_with_facts_delaying_normalization(
                [ledger.mutex_use_resource(loan.usage, callee)?],
                assumptions,
            )
            .map_err(MutexUseCallError::InvalidResources)?;
        let retained_resource = Some(ledger.mutex_use_resource(retained, caller)?);
        Ok(Self {
            caller_resources,
            callee_resources,
            ledger,
            entry_transition,
            entry_transitions: transitions,
            retained_resource,
            suspended_parent: Some(worker),
            usage: loan.usage,
            source: source.clone(),
            selected_alias: None,
            interface: None,
            required_type: None,
            loan,
            caller,
            callee,
        })
    }

    pub(crate) fn retained_authority_update(
        &self,
        resources: &ResourceContext,
    ) -> Option<MutexAuthorityUpdate> {
        // A lifecycle source keeps its proof name on the use share the parent
        // retains; recovery at join moves the name back to the lifecycle.
        if !matches!(
            self.source.resource(),
            Resource::MutexUse(_) | Resource::MutexLive(_)
        ) {
            return None;
        }
        Some(MutexAuthorityUpdate {
            source_occurrence: resources.unique_owned_occurrence_for_fact(&self.source)?.0,
            source: self.source.clone(),
            derived: self.retained_resource.clone()?,
        })
    }

    pub(crate) fn is_suspended(&self) -> bool {
        self.suspended_parent.is_some()
    }

    /// Resume only this worker against current ownership, never its entry state.
    pub(super) fn finish_suspended_checked_ledger(
        &self,
        mut ledger: LoanLedger,
        mut caller_resources: ResourceContext,
        returned_resources: &ResourceContext,
        assumptions: &PureFactContext,
    ) -> Result<MutexUseCallReturn, MutexUseCallError> {
        let parent = self.suspended_parent.ok_or(LoanRefusal::InvalidEvidence)?;
        let expected = ledger.mutex_use_resource(self.usage, self.callee)?;
        if self
            .interface
            .as_ref()
            .is_some_and(|interface| !interface.matches_use(&expected))
        {
            return Err(MutexUseCallError::MissingResource(expected));
        }
        if returned_resources
            .unique_owned_occurrence_for_fact(&expected)
            .is_none()
        {
            return Err(MutexUseCallError::MissingResource(expected));
        }
        let remaining_resources = returned_resources
            .clone()
            .without_fact_delaying_normalization(&expected, assumptions)
            .ok_or_else(|| MutexUseCallError::MissingResource(expected.clone()))?;
        let transfer = ledger.transfer(self.usage.0.share, self.callee, self.caller)?;
        ledger = ledger.apply(&transfer)?;
        let end = ledger.end(self.loan.scope, self.caller)?;
        ledger = ledger.apply(&end)?;
        let mut exit_transitions = vec![transfer, end];
        let mut current = parent.0.share;
        let mut consumed_authorities = Vec::new();
        loop {
            let record = ledger
                .storage
                .data
                .shares
                .get(&current)
                .ok_or(LoanRefusal::MissingShare)?;
            let Some(ancestor) = record.parent else {
                break;
            };
            let (left, right) = ledger
                .storage
                .data
                .shares
                .get(&ancestor)
                .and_then(|record| record.children)
                .ok_or(LoanRefusal::NotSiblings)?;
            let sibling = if left == current {
                right
            } else if right == current {
                left
            } else {
                return Err(LoanRefusal::NotSiblings.into());
            };
            if !ledger
                .storage
                .data
                .shares
                .get(&sibling)
                .is_some_and(|record| {
                    record.holder == Some(self.caller) && record.pinned_by.is_none()
                })
            {
                break;
            }
            let sibling_use = MutexUseBinding(LoanAuthorityBinding {
                share: sibling,
                ..parent.0
            });
            let sibling_fact = ledger.mutex_use_resource(sibling_use, self.caller)?;
            let occurrence = caller_resources
                .unique_owned_occurrence_for_fact(&sibling_fact)
                .ok_or_else(|| MutexUseCallError::MissingResource(sibling_fact.clone()))?
                .0;
            consumed_authorities.push((occurrence, sibling_fact.clone()));
            caller_resources = caller_resources
                .without_fact_delaying_normalization(&sibling_fact, assumptions)
                .ok_or_else(|| MutexUseCallError::MissingResource(sibling_fact.clone()))?;
            let join = ledger.join(left, right, self.caller)?;
            ledger = ledger.apply(&join)?;
            exit_transitions.push(join);
            current = ancestor;
        }
        let restored_use = MutexUseBinding(LoanAuthorityBinding {
            share: current,
            ..parent.0
        });
        let restored = if ledger.loan_is_recoverable_by(parent.0.loan, self.caller)
            && ledger.scope_can_end(parent.0.scope, self.caller)
        {
            let end = ledger.end(parent.0.scope, self.caller)?;
            ledger = ledger.apply(&end)?;
            exit_transitions.push(end);
            let (recover, owner, support) = ledger.recover(parent.0.loan, self.caller)?;
            consumed_authorities.push((support, owner.clone()));
            ledger = ledger.apply(&recover)?;
            exit_transitions.push(recover);
            owner
        } else {
            ledger.mutex_use_resource(restored_use, self.caller)?
        };
        let authority_updates = consumed_authorities
            .into_iter()
            .map(|(source_occurrence, source)| MutexAuthorityUpdate {
                source_occurrence,
                source,
                derived: restored.clone(),
            })
            .collect();
        caller_resources = caller_resources
            .try_compose_with_facts_delaying_normalization([restored], assumptions)
            .map_err(MutexUseCallError::InvalidResources)?;
        Ok(MutexUseCallReturn {
            ledger,
            caller_resources,
            remaining_resources,
            exit_transitions,
            authority_updates,
        })
    }

    /// Attach only metadata authenticated by the selected concrete
    /// initialization. Preparing the transfer has already checked ownership
    /// and the callee's loan; a source declaration cannot supply this binding.
    pub(in crate::kernel) fn bind_interface(
        &mut self,
        protocols: &crate::kernel::mutexes::MutexLedger,
    ) -> Result<(), MutexUseCallError> {
        let fact = self.ledger.mutex_use_resource(self.usage, self.callee)?;
        protocols
            .check_use_acquisition(&fact)
            .map_err(|error| match error {
                crate::kernel::mutexes::MutexTransitionError::Refusal(message) => {
                    MutexUseCallError::Unavailable(message)
                }
                _ => MutexUseCallError::MissingResource(self.source.clone()),
            })?;
        let interface = protocols
            .interface_for_use(&fact)
            .map_err(|_| MutexUseCallError::MissingResource(self.source.clone()))?;
        // A repeated check must not erase or replace an established binding.
        if let Some(previous) = &self.interface
            && !interface
                .as_ref()
                .is_some_and(|next| Arc::ptr_eq(previous, next))
        {
            return Err(MutexUseCallError::MissingResource(self.source.clone()));
        }
        self.interface = interface;
        Ok(())
    }

    pub(crate) fn with_required_type(mut self, protected: Option<ResourceDescription>) -> Self {
        self.required_type = protected;
        self
    }

    /// Validate the requested assertion against authenticated initialization or
    /// entry evidence. Writing a stronger contract never supplies this evidence.
    pub(in crate::kernel) fn check_protected_type(
        &self,
        assumptions: &PureFactContext,
    ) -> Result<(), MutexUseCallError> {
        let Some(required) = &self.required_type else {
            return Ok(());
        };
        let actual = self
            .interface
            .as_ref()
            .map(|interface| interface.description())
            .or(self
                .ledger
                .mutex_use_protected_type(self.usage, self.callee)?);
        let matches = actual.is_some_and(|actual| {
            actual.family() == required.family()
                && actual.schema() == required.schema()
                && actual.resource_arguments() == required.resource_arguments()
                && actual.arguments().len() == required.arguments().len()
                && actual
                    .arguments()
                    .iter()
                    .zip(required.arguments())
                    .all(|(left, right)| {
                        left == right
                            || crate::kernel::resource_arguments_proven_equal(
                                left,
                                right,
                                assumptions,
                            )
                    })
        });
        if !matches {
            return Err(MutexUseCallError::MissingResource(self.source.clone()));
        }
        Ok(())
    }

    pub(crate) fn required_resource(&self) -> ResourceFact {
        let mut fact = self.callee_resource().expect("checked mutex use transfer");
        if let ResourceFact::Own(Resource::MutexUse(identity), _) = &mut fact {
            identity.protected = self.required_type.clone();
        }
        fact
    }

    pub(crate) fn source_resource(&self) -> &ResourceFact {
        &self.source
    }

    pub(crate) fn with_selected_alias(mut self, alias: Variable) -> Self {
        self.selected_alias = Some(alias);
        self
    }

    pub(crate) fn selected_alias(&self) -> Option<Variable> {
        self.selected_alias
    }

    pub(crate) fn callee_resource(&self) -> Result<ResourceFact, LoanRefusal> {
        self.ledger.mutex_use_resource(self.usage, self.callee)
    }

    #[cfg(test)]
    pub(crate) fn recheck_entry(&self, predecessor: &LoanLedger) -> Result<(), LoanRefusal> {
        let mut checked = predecessor.clone();
        for transition in &self.entry_transitions {
            checked = checked.apply(transition)?;
        }
        if checked != self.ledger {
            return Err(LoanRefusal::InvalidEvidence);
        }
        Ok(())
    }

    /// The body must already be certified. Its explicit loan deltas connect
    /// this exact entry to the returned ledger; a sibling ledger is insufficient.
    /// Assumed roots belong only to modular entry, never an executing call.
    #[cfg(test)]
    pub(crate) fn finish(
        &self,
        returned_ledger: &LoanLedger,
        returned_participant: LoanParticipantId,
        returned_resources: &ResourceContext,
        body_transitions: &[CheckedLoanTransition],
        assumptions: &PureFactContext,
    ) -> Result<MutexUseCallReturn, MutexUseCallError> {
        if returned_participant != self.callee {
            return Err(LoanRefusal::WrongHolder.into());
        }
        let mut ledger = self.ledger.clone();
        for transition in body_transitions {
            if matches!(
                transition.evidence,
                LoanTransitionEvidence::BorrowedMutexUseRoot { .. }
                    | LoanTransitionEvidence::BorrowedRoot { local: None, .. }
            ) {
                return Err(LoanRefusal::InvalidEvidence.into());
            }
            crate::instrumentation::record_deterministic_work(1);
            ledger = ledger.apply(transition)?;
        }
        if ledger != *returned_ledger {
            return Err(LoanRefusal::InvalidEvidence.into());
        }
        self.finish_checked_ledger(ledger, returned_resources, assumptions)
    }

    /// Used only inside the common planner's checked entry/recovery chain.
    pub(super) fn finish_checked_ledger(
        &self,
        mut ledger: LoanLedger,
        returned_resources: &ResourceContext,
        assumptions: &PureFactContext,
    ) -> Result<MutexUseCallReturn, MutexUseCallError> {
        let expected = ledger.mutex_use_resource(self.usage, self.callee)?;
        if self
            .interface
            .as_ref()
            .is_some_and(|binding| !binding.matches_use(&expected))
        {
            return Err(MutexUseCallError::MissingResource(expected));
        }
        if returned_resources
            .unique_owned_occurrence_for_fact(&expected)
            .is_none()
        {
            return Err(MutexUseCallError::MissingResource(expected));
        }
        let remaining_resources = returned_resources
            .clone()
            .without_fact_delaying_normalization(&expected, assumptions)
            .ok_or_else(|| MutexUseCallError::MissingResource(expected.clone()))?;
        let mut exit_transitions = Vec::new();
        let transfer = ledger.transfer(self.usage.0.share, self.callee, self.caller)?;
        ledger = ledger.apply(&transfer)?;
        exit_transitions.push(transfer);
        let end = ledger.end(self.loan.scope, self.caller)?;
        ledger = ledger.apply(&end)?;
        exit_transitions.push(end);
        let restored = match self.source.resource() {
            Resource::MutexLive(_) => {
                let (recovery, owner, _) = ledger.recover(self.loan.loan, self.caller)?;
                ledger = ledger.apply(&recovery)?;
                exit_transitions.push(recovery);
                owner
            }
            Resource::MutexUse(identity) => ledger.mutex_use_resource(
                identity.binding.ok_or(LoanRefusal::MissingLoanBinding)?,
                self.caller,
            )?,
            _ => return Err(LoanRefusal::UnsupportedResource.into()),
        };
        if restored != self.source {
            return Err(LoanRefusal::MissingLoanBinding.into());
        }
        let caller_resources = self
            .caller_resources
            .clone()
            .try_compose_with_facts_delaying_normalization([restored], assumptions)
            .map_err(MutexUseCallError::InvalidResources)?;
        Ok(MutexUseCallReturn {
            ledger,
            caller_resources,
            remaining_resources,
            exit_transitions,
            authority_updates: Vec::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MutexIdentity, Pointer, Variable};

    fn owner() -> ResourceFact {
        ResourceFact::own(Resource::MutexLive(MutexIdentity {
            epoch: Some(91),
            mutex: Pointer::symbolic(Variable(100)),
        }))
    }

    fn protected_type(argument: u32) -> ResourceDescription {
        let instance = crate::kernel::ResourceInstance::new(
            Variable(800),
            "counter_state".into(),
            vec![crate::kernel::int32(argument).into()].into(),
            crate::kernel::ResourceFieldSchema::new(vec![(
                "value".into(),
                crate::kernel::ResourceFieldType::Program(crate::kernel::ProgramType::Int32),
            )])
            .unwrap(),
            vec![crate::kernel::int32(0).into()].into(),
        )
        .unwrap();
        ResourceDescription::from_instance(&instance)
    }

    #[test]
    fn suspended_siblings_recover_current_shares_in_either_order() {
        for reverse in [false, true] {
            for borrowed in [false, true] {
                let ledger = LoanLedger::new();
                let caller = ledger.fresh_participant().unwrap();
                let worker1 = ledger.fresh_participant().unwrap();
                let worker2 = ledger.fresh_participant().unwrap();
                let resources = ResourceContext::new().unchecked_with_fact(owner());
                let assumptions = PureFactContext::new();
                let (ledger, source) = if borrowed {
                    let (support, _) = resources
                        .unique_owned_occurrence_for_fact(&owner())
                        .unwrap();
                    let (ledger, input) = ledger
                        .borrowed_mutex_use_input_with_protected(
                            caller,
                            support,
                            Pointer::symbolic(Variable(100)),
                            Some(protected_type(1)),
                        )
                        .unwrap();
                    let fact = ledger.mutex_use_resource(input.usage, caller).unwrap();
                    (ledger, fact)
                } else {
                    (ledger, owner())
                };
                let resources = ResourceContext::new().unchecked_with_fact(source.clone());
                let mut named_state =
                    crate::kernel::ExecutionState::new().with_resource_context(resources.clone());
                let mut names = crate::kernel::named_authority::NamedMutexAuthorities::new()
                    .bind(Variable(7000), &source, &named_state)
                    .unwrap();
                let first = MutexUseCallTransfer::prepare_suspended(
                    &ledger,
                    caller,
                    worker1,
                    &resources,
                    &source,
                    &assumptions,
                )
                .unwrap();
                first.recheck_entry(&ledger).unwrap();
                named_state.resources = first.caller_resources.clone();
                let updates: Vec<_> = first
                    .retained_authority_update(&resources)
                    .into_iter()
                    .collect();
                names = names
                    .apply_checked_mutex_updates(&updates, &named_state)
                    .unwrap();
                // A lifecycle source's name follows its retained use share too.
                assert!(names.resolve(Variable(7000), &named_state).is_some());
                let retained = first
                    .caller_resources
                    .mutex_use_at(&Pointer::symbolic(Variable(100)))
                    .unwrap()
                    .clone();
                if borrowed {
                    first
                        .clone()
                        .with_required_type(Some(protected_type(1)))
                        .check_protected_type(&assumptions)
                        .unwrap();
                }
                let second = MutexUseCallTransfer::prepare_suspended(
                    &first.ledger,
                    caller,
                    worker2,
                    &first.caller_resources,
                    &retained,
                    &assumptions,
                )
                .unwrap();
                second.recheck_entry(&first.ledger).unwrap();
                named_state.resources = second.caller_resources.clone();
                let updates: Vec<_> = second
                    .retained_authority_update(&first.caller_resources)
                    .into_iter()
                    .collect();
                names = names
                    .apply_checked_mutex_updates(&updates, &named_state)
                    .unwrap();
                assert!(
                    MutexUseCallTransfer::prepare_suspended(
                        &second.ledger,
                        caller,
                        worker2,
                        &second.caller_resources,
                        &retained,
                        &assumptions
                    )
                    .is_err()
                );
                let parent = first.suspended_parent.unwrap();
                assert!(!second.ledger.scope_can_end(parent.0.scope, caller));
                let (early, last) = if reverse {
                    (&second, &first)
                } else {
                    (&first, &second)
                };
                let joined = early
                    .finish_suspended_checked_ledger(
                        second.ledger.clone(),
                        second.caller_resources.clone(),
                        &early.callee_resources,
                        &assumptions,
                    )
                    .unwrap();
                assert!(
                    joined
                        .caller_resources
                        .mutex_live_at(&Pointer::symbolic(Variable(100)))
                        .is_none()
                );
                named_state.resources = joined.caller_resources.clone();
                names = names
                    .apply_checked_mutex_updates(&joined.authority_updates, &named_state)
                    .unwrap();
                // A lifecycle source's name follows its retained use share too.
                assert!(names.resolve(Variable(7000), &named_state).is_some());
                assert!(!joined.ledger.scope_can_end(parent.0.scope, caller));
                assert!(
                    early
                        .finish_suspended_checked_ledger(
                            joined.ledger.clone(),
                            joined.caller_resources.clone(),
                            &early.callee_resources,
                            &assumptions
                        )
                        .is_err()
                );
                let done = last
                    .finish_suspended_checked_ledger(
                        joined.ledger,
                        joined.caller_resources,
                        &last.callee_resources,
                        &assumptions,
                    )
                    .unwrap();
                assert!(
                    done.caller_resources
                        .unique_owned_occurrence_for_fact(&source)
                        .is_some()
                );
                named_state.resources = done.caller_resources.clone();
                names = names
                    .apply_checked_mutex_updates(&done.authority_updates, &named_state)
                    .unwrap();
                assert_eq!(names.resolve(Variable(7000), &named_state), Some(&source));
                if borrowed {
                    assert!(
                        done.caller_resources
                            .mutex_live_at(&Pointer::symbolic(Variable(100)))
                            .is_none()
                    );
                }
            }
        }
    }

    #[test]
    fn bound_typed_requirement_keeps_occurrence_identity_without_assuming_its_type() {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let worker = ledger.fresh_participant().unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(owner());
        let assumptions = PureFactContext::new();
        let first = MutexUseCallTransfer::prepare_suspended(
            &ledger,
            caller,
            worker,
            &resources,
            &owner(),
            &assumptions,
        )
        .unwrap();
        let mut required = first.retained_resource.clone().unwrap();
        let ResourceFact::Own(Resource::MutexUse(identity), _) = &mut required else {
            panic!("use");
        };
        identity.protected = Some(protected_type(1));
        let checked = CheckedResourceFact {
            fact: required,
            role: ResourceTransferRole::Borrow,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: Some(0),
            selected_mutex_source: None,
        };
        let second = plan_stable_view_transfer_with_bindings_and_composites_for_worker(
            &first.caller_resources,
            std::slice::from_ref(&checked),
            &assumptions,
            &first.ledger,
            caller,
            worker,
            &LoanViewBindings::default(),
            &BTreeMap::new(),
            true,
        )
        .unwrap();
        second.recheck_entry(&first.ledger).unwrap();
        // Selection is successful, but the requested type still needs concrete
        // initialization evidence. The written requirement cannot grant it.
        assert!(
            second.mutex_uses[0]
                .check_protected_type(&assumptions)
                .is_err()
        );
        let mut wrong = checked;
        let ResourceFact::Own(Resource::MutexUse(identity), _) = &mut wrong.fact else {
            panic!("use");
        };
        identity.binding = Some(first.usage);
        assert!(
            plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                &first.caller_resources,
                &[wrong],
                &assumptions,
                &first.ledger,
                caller,
                worker,
                &LoanViewBindings::default(),
                &BTreeMap::new(),
                true
            )
            .is_err()
        );
    }

    #[test]
    fn returned_sibling_candidate_can_acquire_and_spawn_before_last_join() {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let worker = ledger.fresh_participant().unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(owner());
        let assumptions = PureFactContext::new();
        let first = MutexUseCallTransfer::prepare_suspended(
            &ledger,
            caller,
            worker,
            &resources,
            &owner(),
            &assumptions,
        )
        .unwrap();
        let retained = first.retained_resource.as_ref().unwrap();
        let second = MutexUseCallTransfer::prepare_suspended(
            &first.ledger,
            caller,
            worker,
            &first.caller_resources,
            retained,
            &assumptions,
        )
        .unwrap();
        let joined = first
            .finish_suspended_checked_ledger(
                second.ledger.clone(),
                second.caller_resources.clone(),
                &first.callee_resources,
                &assumptions,
            )
            .unwrap();
        let pointer = Pointer::symbolic(Variable(100));
        assert!(joined.caller_resources.mutex_use_at(&pointer).is_none());
        let candidate = joined
            .caller_resources
            .mutex_use_candidate_at(&pointer)
            .unwrap();
        let Resource::MutexUse(identity) = candidate.resource() else {
            panic!("use candidate");
        };
        let usage = identity.binding.unwrap();
        joined
            .ledger
            .check_mutex_use_available(usage, caller, &joined.caller_resources)
            .unwrap();
        let (held, hold) = joined
            .ledger
            .hold_mutex_use(usage, &owner(), caller)
            .unwrap();
        let released = held.release(hold, caller).unwrap();
        let third = MutexUseCallTransfer::prepare_suspended(
            &released,
            caller,
            worker,
            &joined.caller_resources,
            candidate,
            &assumptions,
        )
        .unwrap();
        let joined = third
            .finish_suspended_checked_ledger(
                third.ledger.clone(),
                third.caller_resources.clone(),
                &third.callee_resources,
                &assumptions,
            )
            .unwrap();
        let done = second
            .finish_suspended_checked_ledger(
                joined.ledger,
                joined.caller_resources,
                &second.callee_resources,
                &assumptions,
            )
            .unwrap();
        assert!(
            done.caller_resources
                .unique_owned_occurrence_for_fact(&owner())
                .is_some()
        );
    }

    #[test]
    fn suspended_sibling_availability_does_not_unpin_the_worker_parent() {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let worker = ledger.fresh_participant().unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(owner());
        let assumptions = PureFactContext::new();
        let plan = MutexUseCallTransfer::prepare_suspended(
            &ledger,
            caller,
            worker,
            &resources,
            &owner(),
            &assumptions,
        )
        .unwrap();
        let parent = plan.suspended_parent.unwrap();
        let mut invented = plan.callee_resource().unwrap();
        let ResourceFact::Own(Resource::MutexUse(identity), _) = &mut invented else {
            panic!("use");
        };
        identity.binding = Some(parent);
        let forged_resources = ResourceContext::new().unchecked_with_fact(invented);
        assert_eq!(
            plan.ledger
                .check_mutex_use_available(parent, caller, &forged_resources),
            Err(LoanRefusal::MissingLoanBinding)
        );
        let Resource::MutexUse(retained) = plan.retained_resource.as_ref().unwrap().resource()
        else {
            panic!("retained use");
        };
        plan.ledger
            .check_mutex_use_available(retained.binding.unwrap(), caller, &plan.caller_resources)
            .unwrap();
    }

    #[test]
    fn suspended_return_requires_ownership_and_released_guard() {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let worker = ledger.fresh_participant().unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(owner());
        let assumptions = PureFactContext::new();
        let plan = MutexUseCallTransfer::prepare_suspended(
            &ledger,
            caller,
            worker,
            &resources,
            &owner(),
            &assumptions,
        )
        .unwrap();
        assert!(
            plan.finish_suspended_checked_ledger(
                plan.ledger.clone(),
                plan.caller_resources.clone(),
                &ResourceContext::new(),
                &assumptions
            )
            .is_err()
        );
        let (held, _) = plan
            .ledger
            .hold_mutex_use(plan.usage, &owner(), worker)
            .unwrap();
        assert!(
            plan.finish_suspended_checked_ledger(
                held,
                plan.caller_resources.clone(),
                &plan.callee_resources,
                &assumptions
            )
            .is_err()
        );
        // The failed attempts are persistent: the original valid return still works.
        let done = plan
            .finish_suspended_checked_ledger(
                plan.ledger.clone(),
                plan.caller_resources.clone(),
                &plan.callee_resources,
                &assumptions,
            )
            .unwrap();
        assert!(
            done.caller_resources
                .unique_owned_occurrence_for_fact(&owner())
                .is_some()
        );
    }

    #[test]
    fn typed_modular_use_reborrows_and_returns_the_same_protected_assertion() {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(owner());
        let (support, _) = resources
            .unique_owned_occurrence_for_fact(&owner())
            .unwrap();
        let protected = protected_type(1);
        let (ledger, input) = ledger
            .borrowed_mutex_use_input_with_protected(
                caller,
                support,
                Pointer::symbolic(Variable(100)),
                Some(protected.clone()),
            )
            .unwrap();
        let source = ledger.mutex_use_resource(input.usage, caller).unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(source.clone());
        let assumptions = PureFactContext::new();
        let plan = MutexUseCallTransfer::prepare(
            &ledger,
            caller,
            callee,
            &resources,
            &source,
            &assumptions,
        )
        .unwrap()
        .with_required_type(Some(protected));
        plan.check_protected_type(&assumptions).unwrap();
        let wrong = plan.clone().with_required_type(Some(protected_type(2)));
        assert!(wrong.check_protected_type(&assumptions).is_err());
        let restored = plan
            .finish(
                &plan.ledger,
                callee,
                &plan.callee_resources,
                &[],
                &assumptions,
            )
            .unwrap();
        assert!(
            restored
                .caller_resources
                .unique_owned_occurrence_for_fact(&source)
                .is_some()
        );
    }

    #[test]
    fn bare_lifetime_authority_cannot_establish_a_protected_type() {
        let (_, plan) = plan();
        assert!(
            plan.with_required_type(Some(protected_type(1)))
                .check_protected_type(&PureFactContext::new())
                .is_err()
        );
    }

    fn token(name: &str) -> ResourceFact {
        ResourceFact::own(Resource::Token {
            name: name.into(),
            arguments: Vec::new().into(),
        })
    }

    fn plan() -> (LoanLedger, MutexUseCallTransfer) {
        let before = LoanLedger::new();
        let caller = before.fresh_participant().unwrap();
        let callee = before.fresh_participant().unwrap();
        let resources = ResourceContext::new()
            .unchecked_with_fact(owner())
            .unchecked_with_fact(token("caller frame"));
        let plan = MutexUseCallTransfer::prepare(
            &before,
            caller,
            callee,
            &resources,
            &owner(),
            &PureFactContext::new(),
        )
        .unwrap();
        (before, plan)
    }

    #[test]
    fn named_use_plan_selects_exact_sibling_share_and_rejects_stale_generation() {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let live = owner();
        let support = ResourceContext::new()
            .unchecked_with_fact(live.clone())
            .unique_owned_occurrence_for_fact(&live)
            .unwrap()
            .0;
        let (ledger, root) = ledger
            .lend_mutex_use(caller, caller, support, live)
            .unwrap();
        let (split, first_share, second_share) = ledger
            .split(root.usage.0.share, caller, caller, caller)
            .unwrap();
        let ledger = ledger.apply(&split).unwrap();
        let first = MutexUseBinding(LoanAuthorityBinding {
            share: first_share,
            ..root.usage.0
        });
        let second = MutexUseBinding(LoanAuthorityBinding {
            share: second_share,
            ..root.usage.0
        });
        let first_fact = ledger.mutex_use_resource(first, caller).unwrap();
        let second_fact = ledger.mutex_use_resource(second, caller).unwrap();
        assert_ne!(first_fact, second_fact);
        let resources = ResourceContext::new()
            .unchecked_with_fact(first_fact.clone())
            .unchecked_with_fact(second_fact.clone());
        let ResourceFact::Own(Resource::MutexUse(first_identity), _) = &first_fact else {
            unreachable!()
        };
        let evaluated_requirement = first_identity.clone();
        let mut required = CheckedResourceFact {
            fact: ResourceFact::own(Resource::MutexUse(evaluated_requirement)),
            role: ResourceTransferRole::Borrow,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: Some(0),
            selected_mutex_source: Some(Arc::new((Variable(500), second_fact.clone()))),
        };
        // A generic lookup is ambiguous here. The selected proof name picks
        // the second share even when the evaluated clause picked its sibling.
        let plan = plan_stable_view_transfer_with_bindings_and_composites_for_worker(
            &resources,
            std::slice::from_ref(&required),
            &PureFactContext::new(),
            &ledger,
            caller,
            callee,
            &LoanViewBindings::default(),
            &BTreeMap::new(),
            false,
        )
        .unwrap();
        assert_eq!(plan.mutex_uses[0].source_resource(), &second_fact);
        assert_eq!(plan.mutex_uses[0].selected_alias(), Some(Variable(500)));
        let mut stale = first_identity.clone();
        stale.initialization = Some(u64::MAX);
        required.fact = ResourceFact::own(Resource::MutexUse(stale));
        assert!(matches!(
            plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                &resources,
                std::slice::from_ref(&required),
                &PureFactContext::new(),
                &ledger,
                caller,
                callee,
                &LoanViewBindings::default(),
                &BTreeMap::new(),
                false,
            ),
            Err(StableViewPlanError::MissingResource(_))
        ));
    }

    #[test]
    fn use_call_lends_one_occurrence_and_restores_exact_owner_and_frame() {
        let (before, plan) = plan();
        let assumptions = PureFactContext::new();
        plan.recheck_entry(&before).unwrap();
        assert!(!plan.caller_resources.satisfies_fact(&owner(), &assumptions));
        assert!(
            plan.caller_resources
                .satisfies_fact(&token("caller frame"), &assumptions)
        );
        assert_eq!(plan.callee_resources.facts().len(), 1);
        assert!(!plan.callee_resources.satisfies_fact(&owner(), &assumptions));
        assert!(
            !plan
                .callee_resources
                .satisfies_fact(&token("caller frame"), &assumptions)
        );
        assert!(
            plan.ledger
                .mutex_use_resource(plan.usage, plan.caller)
                .is_err()
        );
        let returned = plan
            .callee_resources
            .clone()
            .unchecked_with_fact(token("other returned clause"));
        let result = plan
            .finish(&plan.ledger, plan.callee, &returned, &[], &assumptions)
            .unwrap();
        assert!(
            result
                .caller_resources
                .satisfies_fact(&owner(), &assumptions)
        );
        assert!(
            result
                .caller_resources
                .satisfies_fact(&token("caller frame"), &assumptions)
        );
        assert_eq!(
            result.remaining_resources.facts(),
            &[token("other returned clause")]
        );
        let mut recheck = plan.ledger.clone();
        for transition in &result.exit_transitions {
            recheck = recheck.apply(transition).unwrap();
        }
        assert_eq!(recheck, result.ledger);
        assert!(result.ledger.invariant_holds());
        assert!(
            result
                .ledger
                .mutex_use_resource(plan.usage, plan.callee)
                .is_err()
        );
        assert!(
            plan.finish(&result.ledger, plan.callee, &returned, &[], &assumptions)
                .is_err()
        );
    }

    #[test]
    fn use_call_reborrows_an_assumed_input_through_nested_helpers() {
        let before = LoanLedger::new();
        let caller = before.fresh_participant().unwrap();
        let callee = before.fresh_participant().unwrap();
        let helper = before.fresh_participant().unwrap();
        let support = ResourceContext::new()
            .unchecked_with_fact(token("clause"))
            .unique_owned_occurrence_for_fact(&token("clause"))
            .unwrap()
            .0;
        let (before, input) = before
            .borrowed_mutex_use_input(caller, support, Pointer::symbolic(Variable(100)))
            .unwrap();
        let source = before.mutex_use_resource(input.usage, caller).unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(source.clone());
        let assumptions = PureFactContext::new();
        let outer = MutexUseCallTransfer::prepare(
            &before,
            caller,
            callee,
            &resources,
            &source,
            &assumptions,
        )
        .unwrap();
        let supplied = outer
            .ledger
            .mutex_use_resource(outer.usage, callee)
            .unwrap();
        let inner = MutexUseCallTransfer::prepare(
            &outer.ledger,
            callee,
            helper,
            &outer.callee_resources,
            &supplied,
            &assumptions,
        )
        .unwrap();
        assert!(
            inner
                .ledger
                .mutex_use_resource(outer.usage, callee)
                .is_err()
        );
        let inner_return = inner
            .finish(
                &inner.ledger,
                helper,
                &inner.callee_resources,
                &[],
                &assumptions,
            )
            .unwrap();
        let body: Vec<_> = std::iter::once(inner.entry_transition.clone())
            .chain(inner_return.exit_transitions)
            .collect();
        let result = outer
            .finish(
                &inner_return.ledger,
                callee,
                &inner_return.caller_resources,
                &body,
                &assumptions,
            )
            .unwrap();
        result
            .ledger
            .check_mutex_use_input_return(&input, caller, &result.caller_resources)
            .unwrap();
        assert_eq!(result.caller_resources.facts(), &[source]);
        assert!(result.remaining_resources.facts().is_empty());
        assert!(result.ledger.recover(input.usage.0.loan, caller).is_err());
        assert!(result.ledger.invariant_holds());
    }

    #[test]
    fn use_call_refuses_missing_duplicate_or_invalid_source_ownership() {
        let (before, plan) = plan();
        let assumptions = PureFactContext::new();
        let missing = MutexUseCallTransfer::prepare(
            &before,
            plan.caller,
            plan.callee,
            &ResourceContext::new(),
            &owner(),
            &assumptions,
        )
        .unwrap_err();
        assert_eq!(missing, MutexUseCallError::MissingResource(owner()));
        let duplicate = ResourceContext::new()
            .unchecked_with_fact(owner())
            .unchecked_with_fact(owner());
        assert!(
            MutexUseCallTransfer::prepare(
                &before,
                plan.caller,
                plan.callee,
                &duplicate,
                &owner(),
                &assumptions
            )
            .is_err()
        );
        for source in [
            ResourceFact::View(owner().resource().clone()),
            ResourceFact::Own(
                owner().resource().clone(),
                Box::new(MachineTerm::constant(2)),
            ),
            token("unrelated"),
        ] {
            assert!(
                MutexUseCallTransfer::prepare(
                    &before,
                    plan.caller,
                    plan.callee,
                    &ResourceContext::new().unchecked_with_fact(source.clone()),
                    &source,
                    &assumptions
                )
                .is_err()
            );
        }
        let fact = plan
            .ledger
            .mutex_use_resource(plan.usage, plan.callee)
            .unwrap();
        assert!(
            MutexUseCallTransfer::prepare(
                &plan.ledger,
                plan.caller,
                plan.callee,
                &ResourceContext::new().unchecked_with_fact(fact.clone()),
                &fact,
                &assumptions
            )
            .is_err()
        );
        let helper = plan.ledger.fresh_participant().unwrap();
        let inner = MutexUseCallTransfer::prepare(
            &plan.ledger,
            plan.callee,
            helper,
            &plan.callee_resources,
            &fact,
            &assumptions,
        )
        .unwrap();
        assert!(
            MutexUseCallTransfer::prepare(
                &inner.ledger,
                plan.callee,
                helper,
                &plan.callee_resources,
                &fact,
                &assumptions
            )
            .is_err()
        );
    }

    #[test]
    fn use_call_return_requires_exact_resource_participant_and_checked_history() {
        let (before, plan) = plan();
        let assumptions = PureFactContext::new();
        let missing = plan
            .finish(
                &plan.ledger,
                plan.callee,
                &ResourceContext::new(),
                &[],
                &assumptions,
            )
            .unwrap_err();
        assert_eq!(
            missing,
            MutexUseCallError::MissingResource(plan.callee_resources.facts()[0].clone())
        );
        assert!(
            plan.finish(
                &plan.ledger,
                plan.caller,
                &plan.callee_resources,
                &[],
                &assumptions
            )
            .is_err()
        );
        let duplicate = plan
            .callee_resources
            .clone()
            .unchecked_with_fact(plan.callee_resources.facts()[0].clone());
        assert!(
            plan.finish(&plan.ledger, plan.callee, &duplicate, &[], &assumptions)
                .is_err()
        );
        let alternate = MutexUseCallTransfer::prepare(
            &before,
            plan.caller,
            plan.callee,
            &ResourceContext::new().unchecked_with_fact(owner()),
            &owner(),
            &assumptions,
        )
        .unwrap();
        assert!(
            plan.finish(
                &alternate.ledger,
                plan.callee,
                &alternate.callee_resources,
                &[],
                &assumptions
            )
            .is_err()
        );
        assert!(plan.recheck_entry(&plan.ledger).is_err());
        let (held, hold, hold_step) = plan
            .ledger
            .hold_authority_with_transition(plan.usage.0, plan.callee)
            .unwrap();
        assert!(
            plan.finish(
                &held,
                plan.callee,
                &plan.callee_resources,
                &[],
                &assumptions
            )
            .is_err()
        );
        assert_eq!(
            plan.finish(
                &held,
                plan.callee,
                &plan.callee_resources,
                std::slice::from_ref(&hold_step),
                &assumptions
            ),
            Err(MutexUseCallError::Loan(LoanRefusal::ActiveDependency))
        );
        let (released, release_step) = held.release_with_transition(hold, plan.callee).unwrap();
        let result = plan
            .finish(
                &released,
                plan.callee,
                &plan.callee_resources,
                &[hold_step, release_step],
                &assumptions,
            )
            .unwrap();
        assert!(
            result
                .caller_resources
                .satisfies_fact(&owner(), &assumptions)
        );
        assert!(
            plan.ledger
                .mutex_use_resource(plan.usage, plan.callee)
                .is_ok(),
            "failed returns never mutate entry"
        );
    }

    #[test]
    fn use_call_rejects_proof_entry_assumptions_in_body_evidence() {
        let (_, plan) = plan();
        let data = &plan.ledger.storage.data;
        let arena = data.arena;
        let support = plan.loan.usage.0.support;
        let transition = plan
            .ledger
            .issue(LoanTransitionEvidence::BorrowedMutexUseRoot {
                holder: plan.callee,
                support,
                mutex: Pointer::symbolic(Variable(200)),
                protected: None,
                initialization: crate::kernel::mutexes::MutexInitializationId::fresh().unwrap(),
                scope: LoanScopeId {
                    arena,
                    ordinal: data.next_scope,
                },
                loan: LoanId {
                    arena,
                    ordinal: data.next_loan,
                },
                root: LoanShareId {
                    arena,
                    ordinal: data.next_share,
                },
            })
            .unwrap();
        let illicit = plan.ledger.apply(&transition).unwrap();
        assert_eq!(
            plan.finish(
                &illicit,
                plan.callee,
                &plan.callee_resources,
                &[transition],
                &PureFactContext::new()
            ),
            Err(MutexUseCallError::Loan(LoanRefusal::InvalidEvidence))
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/loans/mutex_calls/tests.rs");
    }
}
