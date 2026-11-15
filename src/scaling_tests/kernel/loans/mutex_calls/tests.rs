// Scaling tests of `src/kernel/loans/mutex_calls.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn suspended_mutex_share_recovery_scales_with_worker_count() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let worker = ledger.fresh_participant().unwrap();
        let resources = ResourceContext::new().unchecked_with_fact(owner());
        let assumptions = PureFactContext::new();
        let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut ledger = ledger;
                let mut resources = resources;
                let mut source = owner();
                let mut workers = Vec::new();
                for _ in 0..size {
                    let plan = MutexUseCallTransfer::prepare_suspended(
                        &ledger,
                        caller,
                        worker,
                        &resources,
                        &source,
                        &assumptions,
                    )
                    .unwrap();
                    ledger = plan.ledger.clone();
                    resources = plan.caller_resources.clone();
                    source = resources
                        .mutex_use_at(&Pointer::symbolic(Variable(100)))
                        .unwrap()
                        .clone();
                    workers.push(plan);
                }
                // Oldest first exercises the final climb across all returned siblings.
                for plan in workers {
                    let returned = plan
                        .finish_suspended_checked_ledger(
                            ledger,
                            resources,
                            &plan.callee_resources,
                            &assumptions,
                        )
                        .unwrap();
                    ledger = returned.ledger;
                    resources = returned.caller_resources;
                }
                assert!(
                    resources
                        .unique_owned_occurrence_for_fact(&owner())
                        .is_some()
                );
            })
        });
        samples.push((size, work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 6 && pair[1].2 <= pair[0].2 * 6,
            "mutex worker share recovery must scale near-linearly: {samples:?}"
        );
    }
}

#[test]
fn use_call_partition_and_return_ignore_unrelated_resources() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let mut resources = ResourceContext::new().unchecked_with_fact(owner());
        for index in 0..size {
            resources = resources.unchecked_with_fact(token(&format!("frame {index}")));
        }
        let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let plan = MutexUseCallTransfer::prepare(
                    &ledger,
                    caller,
                    callee,
                    &resources,
                    &owner(),
                    &PureFactContext::new(),
                )
                .unwrap();
                plan.recheck_entry(&ledger).unwrap();
                plan.finish(
                    &plan.ledger,
                    callee,
                    &plan.callee_resources,
                    &[],
                    &PureFactContext::new(),
                )
                .unwrap()
            })
        });
        assert_eq!(returned.caller_resources.facts().len(), size + 1);
        samples.push((size, work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
            "call boundary scans unrelated frame: {samples:?}"
        );
    }
}

#[test]
fn use_call_return_recheck_scales_with_explicit_certificate_delta() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (_, plan) = plan();
        let mut ledger = plan.ledger.clone();
        let mut steps = Vec::new();
        for _ in 0..size {
            let (held, hold, step) = ledger
                .hold_authority_with_transition(plan.usage.0, plan.callee)
                .unwrap();
            steps.push(step);
            let (released, step) = held.release_with_transition(hold, plan.callee).unwrap();
            steps.push(step);
            ledger = released;
        }
        let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                plan.finish(
                    &ledger,
                    plan.callee,
                    &plan.callee_resources,
                    &steps,
                    &PureFactContext::new(),
                )
                .unwrap()
            })
        });
        assert!(returned.ledger.invariant_holds());
        samples.push((size, work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3 && pair[1].2 <= pair[0].2 * 3,
            "return recheck exceeds explicit delta growth: {samples:?}"
        );
    }
}

#[test]
fn integrated_use_planner_reserves_and_recovers_without_scanning_the_frame() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let mut resources = ResourceContext::new().unchecked_with_fact(owner());
        for index in 0..size {
            resources = resources.unchecked_with_fact(token(&format!("frame {index}")));
        }
        let required = CheckedResourceFact {
            fact: ResourceFact::own(Resource::MutexUse(crate::kernel::MutexUseIdentity {
                binding: None,
                protected: None,
                initialization: None,
                mutex: Pointer::symbolic(Variable(100)),
            })),
            role: ResourceTransferRole::Borrow,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: Some(0),
            selected_mutex_source: None,
        };
        let assumptions = PureFactContext::new();
        let ((recovered, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let plan = plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                    &resources,
                    std::slice::from_ref(&required),
                    &assumptions,
                    &ledger,
                    caller,
                    callee,
                    &LoanViewBindings::default(),
                    &BTreeMap::new(),
                    false,
                )
                .unwrap();
                plan.recheck_entry(&ledger).unwrap();
                let entry = plan.ledger.clone();
                let recovered = plan
                    .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
                    .unwrap();
                assert_eq!(
                    recovered.recheck_transitions(&entry, caller).unwrap(),
                    recovered.terminal_ledger
                );
                recovered
            })
        });
        assert_eq!(recovered.ledger, ledger);
        assert!(recovered.resources.satisfies_fact(&owner(), &assumptions));
        assert_eq!(recovered.resources.facts().len(), size + 1);
        assert!(
            plan_stable_view_transfer_with_bindings_and_composites_for_worker(
                &resources,
                &[required.clone(), required.clone()],
                &assumptions,
                &ledger,
                caller,
                callee,
                &LoanViewBindings::default(),
                &BTreeMap::new(),
                false
            )
            .is_err()
        );
        let suspended = plan_stable_view_transfer_with_bindings_and_composites_for_worker(
            &resources,
            &[required],
            &assumptions,
            &ledger,
            caller,
            callee,
            &LoanViewBindings::default(),
            &BTreeMap::new(),
            true,
        )
        .unwrap();
        suspended.recheck_entry(&ledger).unwrap();
        let entry = suspended.ledger.clone();
        let retained = suspended.caller_resources_after_requirements.clone();
        let recovered = suspended
            .recover_suspended_views(
                entry.clone(),
                retained,
                LoanViewBindings::default(),
                BTreeMap::new(),
                &assumptions,
            )
            .unwrap();
        assert_eq!(
            recovered.recheck_transitions(&entry, caller).unwrap(),
            recovered.ledger
        );
        assert!(recovered.resources.satisfies_fact(&owner(), &assumptions));
        assert_ne!(recovered.ledger, ledger);
        samples.push((size, work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
            "integrated use planner scans unrelated frame: {samples:?}"
        );
    }
}
