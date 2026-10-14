use super::direct_loop_guard::{
    normalize_direct_loop_guards, prepare_direct_loop_guard, select_direct_loop_guards,
};
use super::*;
use crate::kernel::*;

fn address(index: usize) -> Pointer {
    Pointer {
        block: format!("direct-loop-{index}").into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn spec() -> CResourceSpec {
    CResourceSpec::new(
        CResourceTerm::MutexGuard {
            mutex: Box::new(c_variable("mutex")),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Current,
    )
    .unwrap()
    .with_guard(SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("flag")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    })
}
fn entry() -> CState {
    MutexContext::new(
        CState::new()
            .with_local("mutex", CValue::pointer(address(0)))
            .with_local("flag", int32(0)),
    )
    .initialize_empty(address(0), 40)
    .unwrap()
    .state
}
fn head(entry: &CState, identity: u64) -> CState {
    let (state, _) = prepare_direct_loop_guard(
        entry,
        entry,
        &spec(),
        Variable(identity),
        &PureFactContext::new(),
    )
    .unwrap();
    select_direct_loop_guards(&state, vec![address(0)])
}
#[test]
fn direct_loop_guard_requires_real_entry_custody() {
    let state = entry().with_local("flag", int32(1));
    assert!(
        prepare_direct_loop_guard(
            &state,
            &state,
            &spec(),
            Variable(700),
            &PureFactContext::new()
        )
        .unwrap_err()
        .contains("mutex_guard")
    );
}
#[test]
fn direct_loop_guard_rechecks_changed_discriminator_without_mutex_operations() {
    let top = head(&entry(), 701);
    let next = top.clone().with_local("flag", int32(1));
    assert!(
        normalize_direct_loop_guards(&top, &next, &PureFactContext::new())
            .unwrap_err()
            .contains("mutex_guard")
    );
}
#[test]
fn direct_loop_guard_metadata_does_not_replace_owned_carrier() {
    let locked = MutexContext::new(entry())
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let top = head(&locked.state().clone().with_local("flag", int32(1)), 702);
    let mut missing = top.clone();
    let instance = missing
        .resources
        .owned_instance(Variable(702))
        .unwrap()
        .clone();
    missing.resources = missing
        .resources
        .without_fact_incrementally(
            &CResourceFact::own(CResource::Instance(instance)),
            &PureFactContext::new(),
        )
        .unwrap();
    let locked = MutexContext::new(missing.clone().with_local("flag", int32(1)));
    assert!(
        locked
            .release_current(&address(0), &PureFactContext::new())
            .is_err()
    );
}
#[test]
fn direct_loop_guard_checked_open_allows_a_subsequent_loop() {
    let first = head(&entry(), 703);
    let locked = MutexContext::new(first)
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let unlocked = locked
        .release_current(&address(0), &PureFactContext::new())
        .unwrap();
    let second = head(unlocked.state(), 704);
    assert!(second.resources.owned_instance(Variable(704)).is_some());
    assert!(second.resources.owned_instance(Variable(703)).is_none());
}
#[test]
fn direct_loop_guard_rejects_changed_mutex_address() {
    let entry = entry();
    let changed = entry
        .clone()
        .with_local("mutex", CValue::pointer(address(1)));
    assert!(
        prepare_direct_loop_guard(
            &entry,
            &changed,
            &spec(),
            Variable(705),
            &PureFactContext::new()
        )
        .is_err()
    );
}
#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn direct_loop_guard_lookup_ignores_unrelated_mutexes() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut context = MutexContext::new(entry());
        for index in 1..size {
            context = context.initialize_empty(address(index), 40).unwrap();
        }
        let top = head(context.state(), 706);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            MutexContext::new(top).acquire_current(&address(0), &PureFactContext::new())
        });
        assert!(result.is_ok());
        measurements.push(work);
    }
    assert!(
        measurements[3] <= measurements[0] * 2 + 64,
        "indexed lookup work grew with unrelated mutexes: {measurements:?}"
    );
}

#[test]
fn direct_loop_guard_empty_carrier_allows_a_subsequent_loop() {
    let first = head(&entry(), 707);
    let second = head(&first, 708);
    assert!(second.resources.owned_instance(Variable(708)).is_some());
    assert!(second.resources.owned_instance(Variable(707)).is_none());
}
