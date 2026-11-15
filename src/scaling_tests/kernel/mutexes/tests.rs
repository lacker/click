// Scaling tests of `src/kernel/mutexes.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn assumed_guard_lookup_does_not_scan_unrelated_resources() {
    let assumptions = PureFactContext::new();
    let address = mutex(0);
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let mut state =
            bind_assumed_guard_inputs(assumed_guard_state(&address), &assumptions).unwrap();
        let expected = guard_resource(&state, &address, false).unwrap();
        for index in 0..size {
            state.resources =
                state
                    .resources
                    .unchecked_with_fact(ResourceFact::own(Resource::Token {
                        name: format!("unrelated{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let ((found, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                guard_resource(&state, &address, false)
            })
        });
        assert_eq!(found, Some(expected));
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "guard lookup scans unrelated resources: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn symbolic_guard_lookup_and_exchange_use_indexed_paths() {
    use super::super::super::ResourceStateSource;
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut state = ExecutionState::new();
        state.preserves_mutex_protocols = true;
        // Every input is a distinct opaque guard over the same empty memory.
        // Assemble and validate that frame once; the measured exchange below
        // still consumes and reinstalls its selected guard through checked APIs.
        let guards = (0..size)
            .map(|index| evaluate_guard(&state, &state, mutex(index), ResourceStateSource::Current))
            .collect::<Vec<_>>();
        state.resources = ResourceContext::new()
            .try_compose_with_facts(guards, &assumptions)
            .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let fact = evaluate_guard(
                &state,
                &state,
                mutex(size / 2),
                ResourceStateSource::Current,
            );
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
#[ignore = "nightly: 0.8s in the parallel gate"]
fn guard_transitions_touch_only_logarithmic_index_paths() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut context = MutexContext::new(ExecutionState::new());
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
#[ignore = "nightly: 0.7s in the parallel gate"]
fn lifetime_transitions_do_not_scan_unrelated_owners() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut context = MutexContext::new(ExecutionState::new());
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
#[ignore = "nightly: 0.7s in the parallel gate"]
fn automatic_storage_query_does_not_scan_unrelated_initializations() {
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let (state, address) = automatic_holder();
        let mut context = MutexContext::new(state);
        for index in 0..size {
            context = context.initialize_empty(mutex(index), 40).unwrap();
        }
        let (result, unrelated_work) = crate::instrumentation::measure_deterministic_work(|| {
            automatic_storage_refusal(context.state(), "holder", &address.block)
        });
        assert!(result.is_none());
        context = context.initialize_empty(address.clone(), 40).unwrap();
        let (result, overlapping_work) = crate::instrumentation::measure_deterministic_work(|| {
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
#[ignore = "nightly: 0.6s in the parallel gate"]
fn abstract_reservation_queries_do_not_scan_other_mutexes_in_one_object() {
    use super::super::super::*;
    let base = mutex(91_202);
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut state = ExecutionState::new();
        state.mutex_input_reservations = MutexInputReservations::from_ranges(
            (0..size).map(|index| storage_range(&base.offset_by_bytes(index * 64), 40)),
        );
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            for index in [0, size / 2, size - 1] {
                assert!(
                    storage_retirement_refusal(
                        &state,
                        &storage_range(&base.offset_by_bytes(index * 64 + 39), 1),
                        &assumptions
                    )
                    .is_some()
                );
                assert!(
                    storage_retirement_refusal(
                        &state,
                        &storage_range(&base.offset_by_bytes(index * 64 + 40), 8),
                        &assumptions
                    )
                    .is_none()
                );
            }
        });
        samples.push(work);
    }
    for window in samples.windows(2) {
        assert!(
            window[1] <= window[0] + 2048,
            "abstract reservation query work: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn reservation_index_queries_same_object_in_logarithmic_work() {
    use super::super::super::*;
    let assumptions = PureFactContext::new();
    let base = mutex(91_104);
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut context = MutexContext::new(ExecutionState::new());
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
                storage_write_refusal(next.state(), &storage_range(&selected, 40), &assumptions)
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
#[ignore = "nightly: 0.8s in the parallel gate"]
fn initialization_storage_lookup_is_indexed_within_one_object() {
    use super::super::super::*;
    let base = Pointer {
        block: PointerBlock::Heap(91_001),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = vec![];
    for size in [16usize, 64, 256, 1024] {
        let assumptions = PureFactContext::new();
        let mut resources = ResourceContext::new_with_equalities(&assumptions);
        for index in 0..size {
            // Alternate units, so the index must compare bytes, not element indices.
            let width = if index % 2 == 0 { 1 } else { 8 };
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    base.clone(),
                    ((index * 64) as u32 / width).into(),
                    ((index * 64 + 40) as u32 / width).into(),
                    width,
                ),
            ));
        }
        let state = ExecutionState::new().with_resource_context(resources);
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

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn retirement_alias_index_skips_unrelated_objects_at_multiple_sizes() {
    use super::super::super::*;
    let mut samples = vec![];
    let assumptions = PureFactContext::new();
    for size in [16usize, 64, 256, 1024] {
        let mut context = MutexContext::new(ExecutionState::new());
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
                    Some(RuntimeError::MutexStorageSeparationRequired { .. })
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
#[ignore = "nightly: 0.6s in the parallel gate"]
fn storage_retirement_lookup_ignores_unrelated_mutex_blocks() {
    let mut samples = Vec::new();
    let assumptions = PureFactContext::new();
    for size in [16, 64, 256, 1024] {
        let mut state = MutexContext::new(ExecutionState::new());
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
            storage_retirement_refusal(state.state(), &allocation_range(other, 40), &assumptions)
                .is_some()
        );
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 16, "{samples:?}");
    }
}

#[test]
fn loop_mutex_join_work_tracks_changed_keys_not_unrelated_mutexes() {
    let assumptions = PureFactContext::new();
    let mut work = Vec::new();
    let mut replacement_work = Vec::new();
    for size in [32, 128, 512] {
        let mut head = MutexContext::new(ExecutionState::new());
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

#[test]
fn automatic_use_acquisition_does_not_scan_the_resource_frame() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let mut context = MutexContext::new(ExecutionState::new())
            .initialize_empty(mutex(0), 40)
            .unwrap();
        let (lent, _) = context.lend_use(&mutex(0), &assumptions).unwrap();
        context = lent;
        for index in 0..size {
            context.state.resources =
                context
                    .state
                    .resources
                    .unchecked_with_fact(ResourceFact::own(Resource::Token {
                        name: format!("frame{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let ((result, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                context
                    .acquire_current(&mutex(0), &assumptions)
                    .map(MutexContext::into_runtime_transition)
            })
        });
        assert!(result.is_ok());
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "use acquisition scans the frame: {samples:?}"
        );
    }
}

#[test]
fn use_loan_round_trip_does_not_scan_unrelated_mutexes() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let assumptions = PureFactContext::new();
        let mut initialized = MutexContext::new(ExecutionState::new());
        for index in 0..size {
            initialized = initialized.initialize_empty(mutex(index), 40).unwrap();
        }
        let ((recovered, work), persistent_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (lent, loan) = initialized.lend_use(&mutex(0), &assumptions).unwrap();
                    let (held, _) = lent
                        .acquire_using(&mutex(0), loan.usage, &assumptions)
                        .unwrap();
                    held.release_current(&mutex(0), &assumptions)
                        .unwrap()
                        .recover_use(&loan, &assumptions)
                        .unwrap()
                })
            });
        assert!(recovered.destroy(&mutex(0), &assumptions).is_ok());
        samples.push((size, work, persistent_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
            "one mutex loan scans unrelated initializations: {samples:?}"
        );
    }
}
