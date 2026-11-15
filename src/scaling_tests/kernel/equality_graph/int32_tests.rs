// Scaling tests of `src/kernel/equality_graph/int32_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;

#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn unsigned_congruence_registration_and_late_merges_scale_with_touched_uses() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                for i in 0..size {
                    let (a, b) = (var(i), var(i + size));
                    let (left, right) = (
                        unsigned_composition(a.clone()),
                        unsigned_composition(b.clone()),
                    );
                    assert!(!graph.are_int32_equal(&left, &right));
                    graph.add_int32_equality(&a, &b);
                    assert!(graph.are_int32_equal(&left, &right));
                }
            })
        });
        assert!(work < 1000 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 10_000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn fact_transport_graph_queries_scale_without_building_the_legacy_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let source = ConditionTerm::signed_less_than(sum(var(0)), var(size + 2));
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let target = ConditionTerm::signed_less_than(sum(var(index)), var(size + 2));
                assert!(context.condition_matches(&source, &target));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn resolved_four_byte_load_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "resolved-int32-scale".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let memory = intern_memory(
            Memory::new()
                .with_block("resolved-int32-scale", 4)
                .store(pointer.clone(), ProgramValue::Int32(sum(var(0)))),
        );
        let load = MachineTerm::Variable(load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        ));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(context.memory_loads_proven_equal(&load, &sum(var(index))));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn two_resolved_four_byte_load_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let pointer = |offset| Pointer {
            block: "two-resolved-int32-scale".into(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let memory = intern_memory(
            Memory::new()
                .with_block("two-resolved-int32-scale", 8)
                .store(pointer(0), ProgramValue::Int32(sum(var(0))))
                .store(pointer(4), ProgramValue::Int32(sum(var(size)))),
        );
        let load = |offset| {
            MachineTerm::Variable(load_variable_for_cell_with_origin(
                &memory,
                &pointer(offset),
                crate::kernel::LoadKind::Int32,
                4,
                &memory,
            ))
        };
        let (left, right) = (load(0), load(4));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert!(context.memory_loads_proven_equal(&left, &right));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn direct_composite_int32_argument_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let resource = |value| Resource::Composite {
            name: "indexed-value-scale".into(),
            arguments: vec![ProgramValue::Int32(sum(value)).into()].into(),
        };
        let left = resource(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(crate::kernel::memory_provenance::resources_directly_match(
                    &left,
                    &resource(var(index)),
                    &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn resource_instance_int32_argument_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let schema = ResourceFieldSchema::new(vec![(
            "stamp".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap();
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let instance = |value| {
            Resource::Instance(
                ResourceInstance::new(
                    Variable(6200),
                    "instance-value-scale".into(),
                    vec![ProgramValue::Int32(sum(value)).into()].into(),
                    schema.clone(),
                    vec![ProgramValue::Int32(MachineTerm::constant(3)).into()].into(),
                )
                .unwrap(),
            )
        };
        let left = instance(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(crate::kernel::memory_provenance::resources_directly_match(
                    &left,
                    &instance(var(index)),
                    &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn typed_int32_value_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let left = ProgramValue::Int32(sum(var(0)));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right = ProgramValue::Int32(sum(var(index)));
                assert!(crate::kernel::reasoning::memory_resolution::program_values_proven_equal_for_memory_resolution(
                    &left, &right, &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn certified_int32_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let left = sum(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let goal = Proposition::ConditionIs(eq(&left, &sum(var(index))), true);
                assert!(crate::kernel::PureFactContext::settles_exactly(
                    &context, &goal,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn graph_equal_addend_matching_scales_without_the_legacy_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let fixed = var(size + 2);
        let last = var(size + 3);
        let left = MachineTerm::add(MachineTerm::add(var(0), fixed.clone()), last.clone());
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right =
                    MachineTerm::add(var(index), MachineTerm::add(fixed.clone(), last.clone()));
                assert!(context.bitvector_add_terms_proven_equal(&left, &right));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn int32_context_insertion_and_forks_scale_with_indexed_work() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let ((context, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut context = PureFactContext::new();
                for i in 0..size {
                    context = context.assume_condition(eq(&var(i), &var(i + 1)), true);
                    assert!(context.equality_graph.are_int32_equal(&var(0), &var(i + 1)));
                }
                context
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 300 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1200 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let branch = context
                    .clone()
                    .assume_condition(eq(&var(size), &var(size + 1)), true);
                assert!(
                    branch
                        .equality_graph
                        .are_int32_equal(&var(0), &var(size + 1))
                );
                assert!(
                    !context
                        .equality_graph
                        .are_int32_equal(&var(0), &var(size + 1))
                );
            })
        });
        assert!(work < 300, "size={size}, fork work={work}");
        assert!(
            map_work < 1200 * logarithm,
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
fn scalar_support_tracking_does_not_compare_unrelated_state_contents_across_arenas() {
    fn sample(size: usize) -> (PureFactContext, usize) {
        std::thread::spawn(move || {
            let _session = VerificationSession::enter();
            let address = Pointer {
                block: "selected".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let mut memory = Memory::new().with_block("selected", 4);
            for i in 0..size {
                memory = memory.with_block(format!("unrelated-{i}"), 4);
            }
            let memory = intern_memory(memory.store(
                address.clone(),
                ProgramValue::Int32(MachineTerm::constant(7)),
            ));
            let load =
                MachineTerm::MemoryLoad(memory, Box::new(address), crate::kernel::LoadKind::Int32);
            crate::instrumentation::measure_deterministic_work(|| {
                PureFactContext::new().assume_condition(eq(&load, &MachineTerm::constant(7)), true)
            })
        })
        .join()
        .expect("independent verification arena")
    }
    for size in [16, 64, 256, 1024] {
        // Retain the first context while admitting the same raw load shape in
        // another arena. Global raw-term interning used to compare the two
        // complete, independently allocated states during the second insert.
        let (held, _) = sample(size);
        let (_, work) = sample(size);
        assert!(work < 100, "size={size}, second-arena work={work}");
        drop(held);
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn offset_premise_shallow_decision_and_forks_scale() {
    let add = |v| binary_node!(Int32, Add, Box::new(v), Box::new(MachineTerm::constant(1)));
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let mut parent = PureFactContext::new();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    parent = parent.clone().assume_condition(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(var(i), 4),
                            PointerOffsetTerm::scale_int32(var(i + 1), 4),
                        ),
                        true,
                    );
                }
                for i in 1..=size {
                    assert_eq!(
                        parent.decide_bitvector_equality_shallow(&add(var(0)), &add(var(i))),
                        Some(true)
                    );
                    assert_eq!(parent.decide(&eq(&var(0), &var(i))), Some(true));
                }
                let branch = parent
                    .clone()
                    .assume_condition(eq(&var(size), &var(size + 1)), true);
                assert_eq!(
                    branch.decide_bitvector_equality_shallow(&add(var(0)), &add(var(size + 1))),
                    Some(true)
                );
                assert_ne!(
                    parent.decide_bitvector_equality_shallow(&add(var(0)), &add(var(size + 1))),
                    Some(true)
                );
            })
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 150 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn shared_constant_discovery_scales_with_the_admitted_chain() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                context = context
                    .clone()
                    .assume_condition(eq(&var(i), &var(i + 1)), true);
            }
            context = context
                .clone()
                .assume_condition(eq(&var(size), &MachineTerm::constant(37)), true);
            assert_eq!(
                context.known_signed_constant_after_normalization(&var(0)),
                Some(37)
            );
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn exact_alias_enumeration_ignores_unrelated_sources() {
    let mut previous = None;
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let a = Pointer::symbolic(Variable(960_000));
        let b = Pointer::symbolic(Variable(960_001));
        let mut context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(970_000 + 2 * i)),
                    Pointer::symbolic(Variable(970_001 + 2 * i)),
                ),
                true,
            );
        }
        let (aliases, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .exact_pointer_aliases(&a)
                .cloned()
                .collect::<Vec<_>>()
        });
        assert_eq!(aliases, vec![b]);
        if let Some(previous) = previous {
            assert_eq!(work, previous);
        }
        previous = Some(work);
    }
}

#[test]
fn unrelated_wide_inputs_do_not_disable_selected_atomic_matching() {
    let mut baseline = None;
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new()
            .assume_condition(eq(&var(980_000), &var(980_001)), true)
            .assume_condition(
                ConditionTerm::signed_less_than(var(980_001), var(980_002)),
                true,
            );
        for i in 0..size {
            context = context
                .assume_condition(ConditionTerm::uint64_equal(var(i), var(i + 10_000)), true);
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.has_matching_condition_fact_for_memory_resolution(
                &ConditionTerm::signed_less_than(var(980_000), var(980_002)),
                true,
            )
        });
        assert!(found);
        if let Some(baseline) = baseline {
            assert_eq!(work, baseline, "size={size}");
        }
        baseline = Some(work);
    }
}

#[test]
fn unrelated_offset_inputs_preserve_the_selected_parameter_partition() {
    use crate::kernel::{MemoryRange, ResourceContext, ResourceFact};
    let mut baseline = None;
    for size in [4u64, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let parameter = |i| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(var(i), 4),
        };
        let write = parameter(990_000);
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new(write.clone(), 0u32.into(), 1u32.into()),
        ));
        let mut context =
            PureFactContext::new().assume_proposition(Proposition::ResourceComposition(resources));
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(var(i), 4),
                    PointerOffsetTerm::scale_int32(var(i + 10_000), 4),
                ),
                true,
            );
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.parameter_store_partition(&write, 4).is_some()
        });
        assert!(found);
        if let Some(baseline) = baseline {
            assert_eq!(work, baseline, "size={size}");
        }
        baseline = Some(work);
        let relevant = context.assume_condition(eq(&var(990_000), &var(990_001)), true);
        assert!(relevant.parameter_store_partition(&write, 4).is_none());
    }
}

#[test]
fn complete_pointer_scalar_evidence_ignores_unrelated_inputs() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index * 2), &var(index * 2 + 1)), true);
        }
        let pointer = |id| {
            PointerValue::new(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(var(id), 4),
                },
                ProgramType::Int32Pointer,
            )
        };
        for (a, b) in [(941_010, 941_011), (941_011, 941_012)] {
            context = context.assume_condition(
                ConditionTerm::pointer_value_equal(pointer(a), pointer(b)),
                true,
            );
        }
        let (class, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.recorded_equality_class(&var(941_010))
        });
        assert_eq!(class, BTreeSet::from([var(941_011), var(941_012)]));
        assert!(work <= 32, "size={size}, work={work}");
    }
}

/// Unknown-class reads must not be paired with settled reads at other
/// states. With N reads in each group, one refused query used to allocate
/// N squared pairs and cost 95*N*N + 1 units (97,281 at N=32).
#[test]
fn constant_queries_ignore_other_state_candidates() {
    for same_address in [true, false] {
        let mut samples = Vec::new();
        for size in [4u64, 8, 16, 32] {
            let _session = VerificationSession::enter();
            let pointer = Pointer {
                block: "constant-bridge-scale".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let query = var(880_000);
            let mut context = PureFactContext::new();
            let mut memory =
                Memory::new().with_block("constant-bridge-scale", 4 * (size as u32 + 1));
            let mut unknown_reads = Vec::new();
            // Every state is separated by a call that may write the cell.
            // The postconditions can consistently equate the first N reads to
            // an unknown value and the later reads to different constants.
            for index in 0..2 * size {
                let mut address = pointer.clone();
                if !same_address && index >= size {
                    address.offset = PointerOffsetTerm::Constant(4 * (index - size + 1) as i64);
                }
                memory = memory.with_call_memory_havoc(
                    Variable(881_000 + index),
                    &[MemoryRange::new_with_element_width(
                        address.clone(),
                        0u32.into(),
                        1u32.into(),
                        4,
                    )],
                    &PureFactContext::new(),
                    None,
                );
                let load = MachineTerm::MemoryLoad(
                    intern_memory(memory.clone()),
                    Box::new(address),
                    LoadKind::Int32,
                );
                if index < size {
                    context = context.assume_condition(eq(&load, &query), true);
                    unknown_reads.push(load);
                } else {
                    context = context.assume_condition(
                        eq(&load, &MachineTerm::constant((index - size + 1) as u32)),
                        true,
                    );
                }
            }
            let (answer, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                context.known_signed_constant_after_normalization(&query)
            });
            assert_eq!(answer, None, "havocs separate the states");
            // Distinct queries, not repeated hits in one query's memo.
            let ((), repeated_work) = crate::instrumentation::measure_deterministic_work(|| {
                for load in &unknown_reads {
                    assert_eq!(
                        context.known_signed_constant_after_normalization(load),
                        None
                    );
                }
            });
            let explicit = context.assume_condition(eq(&query, &37u32.into()), true);
            let (answer, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                explicit.known_signed_constant_after_normalization(&query)
            });
            assert_eq!(
                answer,
                Some(37),
                "an explicit equality supplies the constant"
            );
            samples.push((size, miss_work, repeated_work, hit_work));
            assert!(miss_work <= 8 && hit_work <= 8, "{samples:?}");
            assert!(repeated_work <= 8 * size as usize, "{samples:?}");
        }
        eprintln!(
            "constant queries (same_address={same_address}; size, miss, repeated, hit): {samples:?}"
        );
    }
}
