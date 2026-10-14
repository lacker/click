//! Same-thread acquisition transfer through ordinary resource contracts.
//!
//! The interface selects a net protocol effect. Independent body checking
//! establishes that effect; a call applies the same checked runtime exchange
//! in the caller's scope, so an escaping guard never loses its lifetime hold.

use super::assumed_protocol::{AssumedMutexGuard, AssumedMutexProtocol};
use super::*;
use crate::kernel::{
    CFunctionContractInterface, CResourceSpec, CResourceTerm, CResourceTransferRole,
    ResourceFamily, Variable,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum HelperEffect {
    Acquire,
    Release,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct HelperContract {
    pub(in crate::kernel) effect: HelperEffect,
    pub(in crate::kernel) access: CResourceSpec,
    pub(in crate::kernel) guard: CResourceSpec,
    pub(in crate::kernel) payload: Option<CResourceSpec>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct HelperCall {
    pub(in crate::kernel) contract: HelperContract,
    pub(in crate::kernel) source: CResourceFact,
    pub(in crate::kernel) required: CResourceFact,
    pub(in crate::kernel) guard: Option<CResourceFact>,
}

/// Only direct, unconditional named interfaces are supported here. Preserving
/// contracts retain their existing path and its more general resource rules.
pub(in crate::kernel) fn classify(
    interface: &CFunctionContractInterface,
) -> Result<Option<HelperContract>, &'static str> {
    let effects = interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
        .filter(|spec| {
            spec.family() == ResourceFamily::MutexGuard
                && spec.role() != CResourceTransferRole::Borrow
        })
        .collect::<Vec<_>>();
    if effects.is_empty() {
        return Ok(None);
    }
    let unsupported = "unsupported mutex helper contract: requires one named preserved mutex_use and one produced or consumed guard";
    if effects.len() != 1 {
        return Err(unsupported);
    }
    let guard = effects[0];
    let effect = match guard.role() {
        CResourceTransferRole::Produce => HelperEffect::Acquire,
        CResourceTransferRole::Consume => HelperEffect::Release,
        _ => return Err(unsupported),
    };
    if interface
        .resource_requires()
        .iter()
        .any(|spec| spec.role() == CResourceTransferRole::Produce)
        || interface
            .resource_ensures()
            .iter()
            .any(|spec| spec.role() == CResourceTransferRole::Consume)
    {
        return Err("mutex helper resource transfer is in the wrong contract section");
    }
    let uses = interface
        .resource_requires()
        .iter()
        .filter(|spec| spec.family() == ResourceFamily::MutexUse)
        .collect::<Vec<_>>();
    let [access] = uses.as_slice() else {
        return Err(unsupported);
    };
    if access.role() != CResourceTransferRole::Borrow
        || access.mutex_authority_binding().is_none()
        || guard.mutex_authority_binding().is_none()
        || access.is_view()
        || guard.is_view()
        || access.guard().is_some()
        || guard.guard().is_some()
        || !interface
            .resource_ensures()
            .iter()
            .any(|spec| same_preserved_access(spec, access))
    {
        return Err(unsupported);
    }
    let CResourceTerm::MutexUse { protected, .. } = access.term() else {
        unreachable!()
    };
    let payload = if let Some(protected) = protected {
        let candidates = match effect {
            HelperEffect::Acquire => interface.resource_ensures(),
            HelperEffect::Release => interface.resource_requires(),
        }
        .iter()
        .filter(|spec| {
            spec.role() == guard.role()
                && spec.instance_schema() == Some(&protected.schema)
                && spec.instance_resource_spec().is_some_and(|inner| {
                    inner.contained_definition_name()
                        == protected.resource.contained_definition_name()
                })
        })
        .collect::<Vec<_>>();
        let [payload] = candidates.as_slice() else {
            return Err(
                "unsupported typed mutex helper: requires one matching named protected state transfer",
            );
        };
        Some((*payload).clone())
    } else {
        None
    };
    for spec in interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
    {
        if spec.is_view() || spec.guard().is_some() {
            return Err(
                "unsupported mutex helper contract: viewed and conditional resource clauses are not supported",
            );
        }
        if matches!(spec.family(), ResourceFamily::MutexLive)
            || (matches!(spec.family(), ResourceFamily::MutexGuard) && spec != guard)
            || (matches!(spec.family(), ResourceFamily::MutexUse)
                && !same_preserved_access(spec, access))
            || spec.contained_definition_name().is_some_and(|name| {
                interface
                    .composite_resource_definition(name)
                    .is_some_and(|definition| definition.contains_mutex_authority)
            })
        {
            return Err(unsupported);
        }
    }
    Ok(Some(HelperContract {
        effect,
        access: (*access).clone(),
        guard: guard.clone(),
        payload,
    }))
}

fn same_preserved_access(left: &CResourceSpec, right: &CResourceSpec) -> bool {
    left.term() == right.term()
        && left.mutex_authority_binding() == right.mutex_authority_binding()
        && left.role() == right.role()
        && left.access() == right.access()
        && left.snapshot() == right.snapshot()
        && left.quantity() == right.quantity()
}

/// This is installed only while rooting an independent acquisition helper's
/// actual input. An equal-looking address from another proof cannot use it.
#[derive(Clone, Debug)]
pub(super) struct HelperReturnPermission {
    protocol: AssumedMutexProtocol,
}

pub(in crate::kernel) fn install_entry(
    mut state: CState,
    contract: &HelperContract,
    access: &CResourceFact,
    guard: Option<&CResourceFact>,
    payload: Option<crate::kernel::ResourceInstance>,
) -> Result<CState, MutexTransitionError> {
    let CResource::MutexUse(identity) = access.resource() else {
        return Err("mutex helper entry requires rooted use authority".into());
    };
    let usage = identity
        .binding
        .ok_or("mutex helper entry requires rooted use authority")?;
    let protocol = AssumedMutexProtocol::bind(&state, usage)?;
    if protocol.use_fact != *access {
        return Err("mutex helper entry use does not match its selected occurrence".into());
    }
    let inputs = state
        .mutex_input_reservations
        .get_or_insert_with(MutexInputReservations::empty);
    if inputs.helper_return.is_some() {
        return Err("mutex helper entry was already authorized".into());
    }
    inputs.identity = MutexLedger::fresh_identity();
    match contract.effect {
        HelperEffect::Acquire => {
            inputs.helper_return = Some(Arc::new(HelperReturnPermission { protocol }));
        }
        HelperEffect::Release => {
            let guard = guard.ok_or("releasing helper requires an owned input guard")?;
            if inputs.guards.get(&identity.mutex) != Some(guard)
                || state
                    .resources
                    .unique_owned_occurrence_for_fact(guard)
                    .is_none()
            {
                return Err(MutexTransitionError::MissingGuard(identity.mutex.clone()));
            }
            if payload.as_ref().is_some_and(|instance| {
                !identity.protected.as_ref().is_some_and(|description| {
                    description.matches_instance(instance, &PureFactContext::new())
                })
            }) || identity.protected.is_some() != payload.is_some()
            {
                return Err("releasing helper state does not match its typed use".into());
            }
            inputs.guards = inputs.guards.without_key(&identity.mutex);
            inputs.guard_ledger = inputs.guard_ledger.without(&identity.mutex);
            let loans = protocol.loans(&state)?;
            let (next, hold, _) = loans
                .hold_mutex_use_with_transition(usage, &protocol.lifetime, protocol.holder)
                .map_err(|_| {
                    MutexTransitionError::Refusal("cannot root consumed guard lifetime")
                })?;
            state.loan_ledger = Some(next);
            let holder = protocol.holder;
            let initialization = identity.initialization.expect("rooted use initialization");
            let receipt = AssumedMutexGuard {
                protocol,
                fact: guard.clone(),
                hold,
                payload,
            };
            state.opaque_mutex_acquisitions = Some(OpaqueMutexAcquisitions {
                identity: MutexLedger::fresh_identity(),
                receipts: PersistentMap::default()
                    .with_inserted(identity.mutex.clone(), Arc::new(receipt)),
                holders: PersistentMap::default().with_inserted(holder, 1),
                storage: MutexLedger::new().with_inserted(
                    identity.mutex.clone(),
                    MutexEntry::Unlocked {
                        initialization: MutexInitialization(
                            MutexInitializationId(initialization),
                            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin()
                                .mutex_storage_bytes,
                        ),
                        invariant: None,
                        interface: None,
                    },
                ),
            });
        }
    }
    Ok(state)
}

/// Raw returns may export precisely one live receipt rooted in this helper's
/// input. The full interface output checks still run at the function boundary.
pub(in crate::kernel) fn permits_return(state: &CState) -> bool {
    let Some(permission) = state
        .mutex_input_reservations
        .as_ref()
        .and_then(|inputs| inputs.helper_return.as_ref())
    else {
        return false;
    };
    let Some(held) = &state.opaque_mutex_acquisitions else {
        return false;
    };
    let protocol = &permission.protocol;
    let Some(guard) = held.receipts.get(protocol.mutex()) else {
        return false;
    };
    if guard.protocol != *protocol
        || held.holders.get(&protocol.holder) != Some(&1)
        || state
            .resources
            .unique_owned_occurrence_for_fact(&guard.fact)
            .is_none()
    {
        return false;
    }
    let Ok(loans) = protocol.loans(state) else {
        return false;
    };
    loans
        .release_mutex_use_hold_with_transition(
            protocol.usage,
            &protocol.lifetime,
            guard.hold,
            protocol.holder,
        )
        .is_ok_and(|(released, _)| {
            released
                .check_assumed_mutex_use_return(protocol.usage, protocol.holder, &state.resources)
                .is_ok()
        })
}

pub(in crate::kernel) fn exported_guard(state: &CState) -> Option<CResourceFact> {
    if !permits_return(state) {
        return None;
    }
    let permission = state
        .mutex_input_reservations
        .as_ref()?
        .helper_return
        .as_ref()?;
    state
        .opaque_mutex_acquisitions
        .as_ref()?
        .guard_resource(permission.protocol.mutex())
}

pub(in crate::kernel) fn same_export_permission(entry: &CState, returned: &CState) -> bool {
    match (
        entry
            .mutex_input_reservations
            .as_ref()
            .and_then(|inputs| inputs.helper_return.as_ref()),
        returned
            .mutex_input_reservations
            .as_ref()
            .and_then(|inputs| inputs.helper_return.as_ref()),
    ) {
        (Some(left), Some(right)) => left.protocol == right.protocol,
        _ => false,
    }
}

/// Authenticate a call's selected occurrence before the ordinary partition
/// reserves it. A declaration's stronger type is never evidence of that type.
pub(in crate::kernel) fn check_call_access(
    state: &CState,
    source: &CResourceFact,
    required: &CResourceFact,
    effect: HelperEffect,
    assumptions: &PureFactContext,
) -> Result<(), MutexTransitionError> {
    let CResource::MutexUse(required) = required.resource() else {
        return Err("mutex helper requires use authority".into());
    };
    if state
        .resources
        .unique_owned_occurrence_for_fact(source)
        .is_none()
    {
        return Err(MutexTransitionError::MissingUse(required.mutex.clone()));
    }
    let (mutex, initialization, declared_type) = match source.resource() {
        CResource::MutexLive(live) => (&live.mutex, live.epoch, None),
        CResource::MutexUse(usage) => {
            let holder = state
                .loan_participant
                .ok_or("missing mutex use participant")?;
            let loans = state.loan_ledger.as_ref().ok_or("missing mutex use loan")?;
            let binding = usage.binding.ok_or("missing rooted mutex use authority")?;
            if loans.mutex_use_resource(binding, holder).ok().as_ref() != Some(source) {
                return Err(MutexTransitionError::MissingUse(required.mutex.clone()));
            }
            if effect == HelperEffect::Acquire {
                loans
                    .check_mutex_use_available(binding, holder, &state.resources)
                    .map_err(|_| {
                        MutexTransitionError::Refusal(
                            "mutex_use has an outstanding mutex_guard or reborrow",
                        )
                    })?;
            }
            (&usage.mutex, usage.initialization, usage.protected.as_ref())
        }
        _ => return Err(MutexTransitionError::MissingUse(required.mutex.clone())),
    };
    if mutex != &required.mutex
        || initialization.is_none()
        || required
            .initialization
            .is_some_and(|epoch| Some(epoch) != initialization)
    {
        return Err(MutexTransitionError::MissingUse(required.mutex.clone()));
    }
    let actual = state
        .mutex_ledger
        .as_ref()
        .and_then(|ledger| ledger.protected_type(mutex))
        .or(declared_type);
    match (&required.protected, actual) {
        (None, None) => {
            if state
                .mutex_ledger
                .as_ref()
                .and_then(|ledger| ledger.get(mutex))
                .is_some_and(|entry| match entry {
                    MutexEntry::Unlocked { invariant, .. }
                    | MutexEntry::Locked { invariant, .. } => invariant.is_some(),
                    _ => true,
                })
            {
                return Err("unary mutex transfer helpers require a payload-free protocol".into());
            }
        }
        (Some(required), Some(actual))
            if required.family() == actual.family()
                && required.schema() == actual.schema()
                && required.resource_arguments() == actual.resource_arguments()
                && required.arguments().len() == actual.arguments().len()
                && required
                    .arguments()
                    .iter()
                    .zip(actual.arguments())
                    .all(|(left, right)| {
                        crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                    }) => {}
        (None, Some(_)) => {
            return Err("unary mutex transfer helpers require a payload-free protocol".into());
        }
        _ => return Err(MutexTransitionError::MissingUse(mutex.clone())),
    }
    if let Some(ledger) = &state.mutex_ledger {
        let current = ledger
            .live_resource(mutex)
            .ok_or(MutexTransitionError::NotInitialized)?;
        if !matches!(current.resource(), CResource::MutexLive(live) if live.epoch == initialization)
        {
            return Err(MutexTransitionError::MissingUse(mutex.clone()));
        }
    }
    if effect == HelperEffect::Acquire {
        if let Some(error) = super::acquisition_availability_refusal(state, mutex, assumptions) {
            return Err(error);
        }
        if state
            .mutex_ledger
            .as_ref()
            .is_some_and(|ledger| !matches!(ledger.get(mutex), Some(MutexEntry::Unlocked { .. })))
        {
            return Err("mutex is already guarded".into());
        }
    }
    Ok(())
}

/// Apply a certified helper's net exchange in the caller scope. Ordinary
/// ownership partition and effect checks are performed by the call engine.
pub(in crate::kernel) fn apply_call_effect(
    state: &CState,
    source: &CResourceFact,
    required: &CResourceFact,
    effect: HelperEffect,
    guard: Option<&CResourceFact>,
    payload: Option<Variable>,
    definition: Option<&crate::kernel::CCompositeResourceDefinition>,
    definitions: &[crate::kernel::CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut crate::kernel::ExecutionBudget,
) -> Result<
    (
        CState,
        crate::kernel::loans::CheckedLoanCallEvidenceSequence,
        Vec<crate::kernel::CMemoryRange>,
    ),
    MutexTransitionError,
> {
    check_call_access(state, source, required, effect, assumptions)?;
    let CResource::MutexUse(usage) = required.resource() else {
        unreachable!()
    };
    let mutex = &usage.mutex;
    if effect == HelperEffect::Release {
        let actual = super::guard_resource(state, mutex, false)
            .ok_or_else(|| MutexTransitionError::MissingGuard(mutex.clone()))?;
        if guard != Some(&actual)
            || state
                .resources
                .unique_owned_occurrence_for_fact(&actual)
                .is_none()
        {
            return Err(MutexTransitionError::MissingGuard(mutex.clone()));
        }
        if let CResource::MutexUse(selected) = source.resource()
            && let Some(MutexEntry::Locked {
                lifetime_hold: Some((_, _, binding)),
                ..
            }) = state
                .mutex_ledger
                .as_ref()
                .and_then(|ledger| ledger.get(mutex))
            && selected.binding != Some(*binding)
        {
            return Err("guard lifetime belongs to a different selected mutex_use".into());
        }
    }
    if state.preserves_mutex_protocols && effect == HelperEffect::Acquire {
        let (next, evidence) =
            super::assumed_protocol::opaque_runtime_transition_with_selected_use(
                state,
                mutex,
                true,
                assumptions,
                definition,
                definitions,
                payload,
                budget,
                Some(source),
            )?;
        if payload.is_some_and(|identity| next.owned_resource_instance(identity).is_none()) {
            return Err("acquiring helper did not produce its state".into());
        }
        // Acquisition changes no memory: every release already forgot its
        // protected footprint.
        return Ok((next, evidence, Vec::new()));
    }
    let mut next = state.clone();
    let mut ranges = Vec::new();
    // Both acquisition and release helpers can write their owned protected
    // state. Refresh its model and memory before applying the net exchange.
    let fresh = if let Some(description) = &usage.protected {
        let identity = payload.ok_or("typed mutex helper requires named state transport")?;
        if effect == HelperEffect::Release {
            let old = next
                .owned_resource_instance(identity)
                .ok_or("releasing helper requires its owned protected state")?;
            if !description.matches_instance(old, assumptions) {
                return Err("releasing helper state has a different protected type".into());
            }
            let old = CResourceFact::own(CResource::Instance(old.clone()));
            next.resources = next
                .resources
                .without_fact_delaying_normalization(&old, assumptions)
                .ok_or("releasing helper lost its protected state")?;
        }
        let (memory, fresh) = super::assumed_protocol::fresh_protected_payload(
            &next,
            assumptions,
            description,
            definition,
            Some(identity),
            budget,
        )?;
        let fresh = fresh.expect("typed protected payload");
        ranges = crate::kernel::functions::checked_owned_memory_ranges(
            &CResourceFact::own(CResource::Instance(fresh.clone())),
            std::slice::from_ref(definition.expect("checked protected definition")),
            &next,
            assumptions,
        )
        .ok_or("protected helper state has no checked memory footprint")?;
        next.memory = memory;
        Some(fresh)
    } else {
        None
    };
    if next.preserves_mutex_protocols {
        if effect == HelperEffect::Release
            && let Some(fresh) = fresh
        {
            next.resources = next
                .resources
                .try_compose_with_facts_delaying_normalization(
                    [CResourceFact::own(CResource::Instance(fresh))],
                    assumptions,
                )
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "protected helper state conflicts with caller ownership",
                    )
                })?;
        }
        // Opaque acquisition itself creates the same named fresh instance.
        let (next, evidence) =
            super::assumed_protocol::opaque_runtime_transition_with_selected_use(
                &next,
                mutex,
                effect == HelperEffect::Acquire,
                assumptions,
                definition,
                definitions,
                payload,
                budget,
                Some(source),
            )?;
        return Ok((next, evidence, ranges));
    }
    if effect == HelperEffect::Acquire {
        if let Some(fresh) = fresh {
            let ledger = next
                .mutex_ledger
                .as_ref()
                .ok_or(MutexTransitionError::NotInitialized)?;
            let Some(MutexEntry::Unlocked {
                initialization,
                interface,
                ..
            }) = ledger.get(mutex)
            else {
                return Err("mutex is already guarded".into());
            };
            next.mutex_ledger = Some(ledger.with_inserted(
                mutex.clone(),
                MutexEntry::Unlocked {
                    initialization: *initialization,
                    interface: interface.clone(),
                    invariant: Some(CResourceFact::own(CResource::Instance(fresh))),
                },
            ));
        }
        let context = MutexContext::new(next);
        let acquired = if let CResource::MutexUse(usage) = source.resource() {
            context
                .acquire_using(
                    mutex,
                    usage.binding.ok_or("missing selected use binding")?,
                    assumptions,
                )?
                .0
        } else {
            context.acquire(mutex, assumptions)?.0
        };
        let (next, evidence) = acquired.into_runtime_transition();
        Ok((next, evidence, ranges))
    } else {
        if let Some(fresh) = &fresh {
            next.resources = next
                .resources
                .try_compose_with_facts_delaying_normalization(
                    [CResourceFact::own(CResource::Instance(fresh.clone()))],
                    assumptions,
                )
                .map_err(|_| {
                    MutexTransitionError::Refusal(
                        "protected helper state conflicts with caller ownership",
                    )
                })?;
        }
        let ledger = next
            .mutex_ledger
            .as_ref()
            .ok_or(MutexTransitionError::NotInitialized)?;
        let Some(MutexEntry::Locked {
            initialization,
            epoch,
            ..
        }) = ledger.get(mutex)
        else {
            return Err(MutexTransitionError::MissingGuard(mutex.clone()));
        };
        let guard = MutexGuard {
            mutex: mutex.clone(),
            initialization: *initialization,
            epoch: *epoch,
        };
        let context = MutexContext::new(next).release_with_invariant(
            guard,
            fresh.map(|instance| CResourceFact::own(CResource::Instance(instance))),
            assumptions,
        )?;
        let (next, evidence) = context.into_runtime_transition();
        Ok((next, evidence, ranges))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        CExpression, CFunction, CFunctionOutcome, CResourceAccessMode, CResourceQuantity,
        CResourceSnapshot, CType, CValue, ExecutionBudget, ResourceContext, c_function, c_skip,
    };

    fn mutex() -> Pointer {
        Pointer::symbolic(Variable(851))
    }

    fn spec(guard: bool, role: CResourceTransferRole) -> CResourceSpec {
        let snapshot = if role == CResourceTransferRole::Produce {
            CResourceSnapshot::Post
        } else {
            CResourceSnapshot::Entry
        };
        let address = CExpression::Value(CValue::pointer(mutex()));
        CResourceSpec::new(
            if guard {
                CResourceTerm::MutexGuard {
                    mutex: Box::new(address),
                    snapshot,
                }
            } else {
                CResourceTerm::MutexUse {
                    mutex: Box::new(address),
                    snapshot,
                    protected: None,
                }
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            role,
            snapshot,
        )
        .unwrap()
        .with_mutex_authority_binding(
            Variable(if guard { 854 } else { 853 }),
            if guard { "guard" } else { "access" }.into(),
        )
        .unwrap()
    }

    fn function(name: &str, effect: HelperEffect) -> CFunction {
        let access = spec(false, CResourceTransferRole::Borrow);
        let guard = spec(
            true,
            if effect == HelperEffect::Acquire {
                CResourceTransferRole::Produce
            } else {
                CResourceTransferRole::Consume
            },
        );
        let (requires, ensures) = match effect {
            HelperEffect::Acquire => (vec![access.clone()], vec![access, guard]),
            HelperEffect::Release => (vec![access.clone(), guard], vec![access]),
        };
        c_function(CType::Void, name, vec![], c_skip()).with_resource_summary(requires, ensures)
    }

    fn input(function: &CFunction, release: bool) -> CState {
        let mut state = CState::new();
        state.resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
            CResource::MutexUse(crate::kernel::MutexUseIdentity {
                protected: None,
                binding: None,
                initialization: None,
                mutex: mutex(),
            }),
        ));
        if release {
            state.resources =
                state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::MutexGuard(
                        crate::kernel::MutexIdentity {
                            epoch: None,
                            mutex: mutex(),
                        },
                    )));
        }
        crate::kernel::api::c_state_with_borrowed_contract_inputs(
            state,
            function,
            &[],
            &PureFactContext::new(),
        )
        .unwrap()
    }

    fn certifies(entry: &CState, function: &CFunction, returned: &CState) -> bool {
        crate::kernel::functions::function_return_resources_definitionally_established(
            entry,
            function,
            &[],
            &CFunctionOutcome::Return {
                value: CValue::Void,
                state: Box::new(returned.clone()),
            },
            &PureFactContext::new(),
        )
    }

    #[test]
    fn helper_export_requires_exact_rooted_input_and_live_owned_receipt() {
        let assumptions = PureFactContext::new();
        let function = function("helper_export_root_a", HelperEffect::Acquire);
        let entry = input(&function, false);
        assert!(!certifies(&entry, &function, &entry));
        let (held, _) = super::super::assumed_protocol::opaque_runtime_transition_with_payload(
            &entry,
            &mutex(),
            true,
            &assumptions,
            None,
            &[],
            None,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert!(permits_return(&held));
        assert!(crate::kernel::eval::return_authority_refusal(&held).is_none());
        assert!(certifies(&entry, &function, &held));
        let other_function = self::function("helper_export_root_b", HelperEffect::Acquire);
        let other = input(&other_function, false);
        let mut grafted = held.clone();
        grafted.mutex_input_reservations = other.mutex_input_reservations.clone();
        assert!(!permits_return(&grafted));
        assert!(crate::kernel::eval::return_authority_refusal(&grafted).is_some());
        assert!(!certifies(&entry, &function, &grafted));
        let guard = exported_guard(&held).unwrap();
        let mut hidden = held.clone();
        hidden.resources = hidden
            .resources
            .without_fact_delaying_normalization(&guard, &assumptions)
            .unwrap();
        assert!(!permits_return(&hidden));
        assert!(!certifies(&entry, &function, &hidden));
        let receipt = held
            .opaque_mutex_acquisitions
            .as_ref()
            .unwrap()
            .receipts
            .get(&mutex())
            .unwrap();
        let mut hidden_hold = held.clone();
        hidden_hold.loan_ledger = Some(
            held.loan_ledger
                .as_ref()
                .unwrap()
                .hold_mutex_use_with_transition(
                    receipt.protocol.usage,
                    &receipt.protocol.lifetime,
                    receipt.protocol.holder,
                )
                .unwrap()
                .0,
        );
        assert!(!permits_return(&hidden_hold));
        assert!(!certifies(&entry, &function, &hidden_hold));
    }

    #[test]
    fn consumed_helper_guard_must_discharge_its_receipt_not_only_its_atom() {
        let assumptions = PureFactContext::new();
        let function = function("helper_consume_input", HelperEffect::Release);
        let entry = input(&function, true);
        assert!(crate::kernel::eval::return_authority_refusal(&entry).is_some());
        assert!(!certifies(&entry, &function, &entry));
        let guard = super::super::guard_resource(&entry, &mutex(), false).unwrap();
        let mut hidden = entry.clone();
        hidden.resources = hidden
            .resources
            .without_fact_delaying_normalization(&guard, &assumptions)
            .unwrap();
        assert!(crate::kernel::eval::return_authority_refusal(&hidden).is_some());
        assert!(!certifies(&entry, &function, &hidden));
        let (released, _) = super::super::assumed_protocol::opaque_runtime_transition_with_payload(
            &entry,
            &mutex(),
            false,
            &assumptions,
            None,
            &[],
            None,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert!(crate::kernel::eval::return_authority_refusal(&released).is_none());
        assert!(certifies(&entry, &function, &released));
    }

    #[test]
    fn preserving_guard_contract_rejects_a_replacement_acquisition() {
        let assumptions = PureFactContext::new();
        let input = MutexContext::new(CState::new())
            .initialize_empty(mutex(), 40)
            .unwrap()
            .acquire_current(&mutex(), &assumptions)
            .unwrap();
        let replaced = input
            .release_current(&mutex(), &assumptions)
            .unwrap()
            .acquire_current(&mutex(), &assumptions)
            .unwrap();
        let guard = spec(true, CResourceTransferRole::Borrow);
        let function = c_function(CType::Void, "preserve_exact_guard", vec![], c_skip())
            .with_resource_summary(vec![guard.clone()], vec![guard]);
        assert!(certifies(input.state(), &function, input.state()));
        assert!(!certifies(input.state(), &function, replaced.state()));
    }

    #[test]
    fn helper_effect_roles_cannot_be_moved_to_the_opposite_section() {
        let access = spec(false, CResourceTransferRole::Borrow);
        let guard = spec(true, CResourceTransferRole::Consume);
        let wrong = c_function(CType::Void, "wrong_guard_section", vec![], c_skip())
            .with_resource_summary(vec![access.clone()], vec![access, guard]);
        assert!(classify(wrong.contract_interface()).is_err());
    }

    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn helper_transfers_ignore_unrelated_resources_protocols_and_history() {
        let assumptions = PureFactContext::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let function = function(&format!("helper_scaling_{size}"), HelperEffect::Acquire);
            let mut state = input(&function, false);
            let source = state
                .resources
                .mutex_use_candidate_at(&mutex())
                .unwrap()
                .clone();
            let holder = state.loan_participant.unwrap();
            for index in 0..size {
                let marker = CResourceFact::own(CResource::Token {
                    name: format!("unrelated_helper_frame_{index}"),
                    arguments: vec![].into(),
                });
                state.resources = state.resources.unchecked_with_fact(marker.clone());
                let support = state
                    .resources
                    .unique_owned_occurrence_for_fact(&marker)
                    .unwrap()
                    .0;
                let (ledger, other) = state
                    .loan_ledger
                    .as_ref()
                    .unwrap()
                    .borrowed_mutex_use_input(
                        holder,
                        support,
                        Pointer::symbolic(Variable(900 + index)),
                    )
                    .unwrap();
                state.resources = state
                    .resources
                    .unchecked_with_fact(ledger.mutex_use_resource(other.usage, holder).unwrap());
                state.loan_ledger = Some(ledger);
                let (held, _, _) = apply_call_effect(
                    &state,
                    &source,
                    &source,
                    HelperEffect::Acquire,
                    None,
                    None,
                    None,
                    &[],
                    &assumptions,
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                let guard = exported_guard(&held).unwrap();
                state = apply_call_effect(
                    &held,
                    &source,
                    &source,
                    HelperEffect::Release,
                    Some(&guard),
                    None,
                    None,
                    &[],
                    &assumptions,
                    &mut ExecutionBudget::new(),
                )
                .unwrap()
                .0;
            }
            let ((released, work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (held, _, _) = apply_call_effect(
                        &state,
                        &source,
                        &source,
                        HelperEffect::Acquire,
                        None,
                        None,
                        None,
                        &[],
                        &assumptions,
                        &mut ExecutionBudget::new(),
                    )
                    .unwrap();
                    assert!(permits_return(&held));
                    let guard = exported_guard(&held).unwrap();
                    let (released, _, _) = apply_call_effect(
                        &held,
                        &source,
                        &source,
                        HelperEffect::Release,
                        Some(&guard),
                        None,
                        None,
                        &[],
                        &assumptions,
                        &mut ExecutionBudget::new(),
                    )
                    .unwrap();
                    released
                })
            });
            assert_eq!(
                released.resources.facts().len(),
                state.resources.facts().len()
            );
            samples.push((work, persistent));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
                "mutex helper transition scans unrelated frame or history: {samples:?}"
            );
        }
    }
}
