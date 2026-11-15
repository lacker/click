use super::*;
use crate::kernel::int32;

#[test]
fn automatic_lifetime_event_rejects_active_local_loan_and_forged_retirement() {
    use crate::kernel::loans::{LoanLedger, plan_stable_view_transfer};
    use crate::kernel::prelude::CheckedResourceFact;
    use crate::kernel::{ResourceStateSource, ResourceTransferRole};
    let state = ExecutionState::new()
        .with_local("selected", int32(5))
        .with_memory(Memory::new().with_block("local:selected", 4));
    let pointer = state.locals().slot("selected").unwrap().clone();
    let viewed = ResourceFact::view_memory(MemoryRange::new(pointer.clone(), 0.into(), 1.into()));
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
        &[CheckedResourceFact {
            fact: viewed,
            role: ResourceTransferRole::Borrow,
            state_source: ResourceStateSource::Entry,
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
    let names = vec!["selected".to_string()];
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    assert!(core.record_automatic_lifetime_end(&state, &names).is_err());
    let forged = CheckedAutomaticLifetimeEnd {
        before_state: state.clone(),
        names,
        after_state: state
            .clone()
            .with_memory(state.memory().clone().without_local_block(&pointer.block)),
    };
    assert!(forged.advance_checked(&state).is_none());
}

#[test]
fn automatic_lifetime_event_rejects_forged_mutex_storage_retirement() {
    let state = ExecutionState::new()
        .with_local("holder", int32(0))
        .with_memory(Memory::new().with_block("local:holder", 48));
    let address = state.locals().slot("holder").unwrap().offset_by_bytes(8);
    let context = crate::kernel::mutexes::MutexContext::new(state)
        .initialize_empty(address.clone(), 40)
        .unwrap();
    let state = context.state();
    let names = vec!["holder".to_string()];
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    assert!(matches!(
        core.record_automatic_lifetime_end(state, &names),
        Err(RuntimeError::MutexStorageScopeEnd { .. })
    ));
    let forged = CheckedAutomaticLifetimeEnd {
        before_state: state.clone(),
        names: names.clone(),
        after_state: state
            .clone()
            .with_memory(state.memory().clone().without_local_block(&address.block)),
    };
    assert!(forged.advance_checked(state).is_none());
    assert_eq!(core.reached_state(), state);
    let destroyed = context
        .destroy(&address, &PureFactContext::new())
        .unwrap()
        .into_state();
    let mut core = ExecutionProofCore::at_entry(destroyed.clone(), ExecutionFrontier::default());
    let after = core
        .record_automatic_lifetime_end(&destroyed, &names)
        .unwrap();
    let events = core.execution_evidence[0].to_vec();
    let CheckedExecutionEvent::AutomaticLifetimeEnd(event) = &events[0] else {
        panic!("missing scope event")
    };
    assert_eq!(event.advance_checked(&destroyed), Some(after));
}

#[test]
fn automatic_lifetime_end_records_the_retired_storage_footprint() {
    let state = ExecutionState::new()
        .with_local("selected", int32(5))
        .with_memory(Memory::new().with_block("local:selected", 4));
    let slot = state.locals().slot("selected").unwrap().clone();
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    let after = core
        .record_automatic_lifetime_end(&state, &["selected".into()])
        .unwrap();
    let footprint = core
        .last_footprint
        .as_ref()
        .expect("scope cleanup has a footprint");
    assert_eq!(footprint.before, *state.memory());
    assert_eq!(footprint.after, *after.memory());
    let retired = Resource::Memory(MemoryRange::new_with_element_width(
        slot,
        0u32.into(),
        4u32.into(),
        1,
    ));
    assert!(footprint.complete);
    assert!(footprint.members.contains(&retired));
    let statement = crate::kernel::RegionFootprint::transition(
        "region(0).footprint".into(),
        &state,
        &state,
        &ExecutionFacts::new(),
    );
    let whole_statement = crate::kernel::RegionFootprint::with_scope_cleanup(&statement, footprint);
    let outside = Resource::Memory(MemoryRange::new_with_element_width(
        Memory::frame_local_pointer(0, "outside"),
        0u32.into(),
        4u32.into(),
        1,
    ));
    assert!(crate::kernel::region_footprint::separate_using(
        &Resource::Footprint(whole_statement),
        &outside,
        &PureFactContext::new(),
    ));
    assert!(!crate::kernel::region_footprint::separate_using(
        &Resource::Footprint(footprint.clone()),
        &retired,
        &PureFactContext::new(),
    ));
    core.record_automatic_lifetime_end(&after, &[]).unwrap();
    assert!(
        core.last_footprint.is_none(),
        "no-op cleanup must not repeat the previous effect"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/automatic_lifetime_tests.rs");
}
