// Scaling tests of `src/kernel/tests/resource_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn normalized_resource_spec_evaluation_preserves_indexed_lookup_scaling() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let names = (0..size)
                .map(|index| format!("token{index}"))
                .collect::<Vec<_>>();
            let context = ResourceContext::new().unchecked_with_facts(
                names
                    .iter()
                    .cloned()
                    .map(|name| ResourceFact::own_token(name, Vec::new())),
            );
            let spec = ResourceSpec::declared(
                ResourceFamily::Token,
                ResourceAccessMode::Own,
                names[size / 2].clone(),
                Vec::new(),
                Vec::new(),
                ResourceTransferRole::Consume,
                ResourceStateSource::Current,
            )
            .unwrap();
            let state = ExecutionState::new().with_resource_context(context);
            let assumptions = PureFactContext::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut budget = ExecutionBudget::default();
                let fact = crate::kernel::functions::evaluate_function_resource_spec(
                    &state,
                    &spec,
                    &assumptions,
                    &mut budget,
                )
                .unwrap()
                .unwrap();
                assert!(state.resources().satisfies_fact(&fact, &assumptions));
                let remaining = state
                    .resources()
                    .clone()
                    .without_fact_delaying_normalization(&fact, &assumptions)
                    .expect("indexed lookup finds the normalized token");
                assert_eq!(remaining.facts().len(), size - 1);
            });
            assert!(work > 0);
            (size, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3) + 64),
        "normalized resource evaluation is superlinear: {samples:?}"
    );
}

#[test]
fn aliased_memory_consumption_does_not_walk_the_pointer_class() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let pointer = |i| Pointer::symbolic(Variable(800_000 + i));
        let cell =
            |base| MemoryRange::new(base, MachineTerm::constant(0), MachineTerm::constant(1));
        let mut assumptions = PureFactContext::new();
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(cell(pointer(size))));
        for i in 1..=size {
            assumptions = assumptions
                .assume_condition(ConditionTerm::pointer_equal(pointer(0), pointer(i)), true);
        }
        // Establish the paired state once. Subsequent queries and forks
        // must share its persistent index, rather than enumerate aliases.
        resources = resources
            .without_fact_incrementally(&ResourceFact::view_memory(cell(pointer(0))), &assumptions)
            .unwrap();
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.without_fact_incrementally(
                &ResourceFact::own_memory(cell(pointer(0))),
                &assumptions,
            )
        });
        assert!(remaining.unwrap().facts().is_empty());
        samples.push((size, work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 3 + 64,
        "fixed consumption walked the growing alias class: {samples:?}"
    );
}

#[test]
fn paired_memory_index_updates_move_the_smaller_resource_payload() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let root = Pointer::symbolic(Variable(820_000));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                Pointer {
                    block: root.block.clone(),
                    offset: PointerOffsetTerm::Constant(i as i64 * 4),
                },
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )));
        }
        let mut assumptions = PureFactContext::new();
        resources.synchronize_memory_equalities(&assumptions);
        let (assumptions, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 1..=size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::pointer_equal(
                        root.clone(),
                        Pointer::symbolic(Variable(820_000 + i)),
                    ),
                    true,
                );
                resources.synchronize_memory_equalities(&assumptions);
            }
            assumptions
        });
        let required = ResourceFact::own_memory(MemoryRange::new(
            Pointer::symbolic(Variable(820_000 + size)),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ));
        let (remaining, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.without_fact_incrementally(&required, &assumptions)
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work, query_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 6 + 128,
            "class updates repeatedly moved a large payload: {samples:?}"
        );
        assert!(
            pair[1].2 <= pair[0].2 * 2 + 64,
            "lookup scanned unrelated addresses: {samples:?}"
        );
    }
}

#[test]
fn paired_memory_consumption_indexes_disjoint_spans_at_one_base() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let owner = Pointer::symbolic(Variable(840_000));
        let alias = Pointer::symbolic(Variable(840_001));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                owner.clone(),
                MachineTerm::constant(i as u32 * 2),
                MachineTerm::constant(i as u32 * 2 + 1),
            )));
        }
        let assumptions = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
        resources.synchronize_memory_equalities(&assumptions);
        let required = ResourceFact::own_memory(MemoryRange::new(
            alias,
            MachineTerm::constant(size as u32),
            MachineTerm::constant(size as u32 + 1),
        ));
        let ((remaining, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources.without_fact_incrementally(&required, &assumptions)
            })
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work, map_work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 2 + 64,
        "consumption scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[2].2 <= samples[0].2 * 3 + 128,
        "index work scanned unrelated ranges: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn indexed_memory_lookup_ignores_unrelated_pointer_parameters() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(870_000 + id)),
        };
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                at(i),
                0u32.into(),
                1u32.into(),
            )));
        }
        let limit = MachineTerm::Variable(Variable(871_100));
        let index = MachineTerm::Variable(Variable(869_000));
        let symbolic = resources
            .clone()
            .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                at(size),
                0u32.into(),
                limit.clone(),
            )));
        let concrete = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            at(size),
            0u32.into(),
            4u32.into(),
        )));
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_than(index.clone(), limit), true);
        symbolic.synchronize_memory_equalities(&facts);
        let query = at(size).offset_by_elements(index, 4);
        let required =
            |base| ResourceFact::view_memory(MemoryRange::new(base, 1u32.into(), 2u32.into()));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(symbolic.permits_memory_read(&query, 4, &facts));
                assert!(!symbolic.permits_memory_read(&at(size + 1), 4, &facts));
                assert!(concrete.satisfies_memory_fact_structurally(&required(at(size))));
                assert!(!concrete.satisfies_memory_fact_structurally(&required(at(size + 1))));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "structural lookup scanned unrelated parameters: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "structural index scanned unrelated parameters: {samples:?}"
    );
}

#[test]
fn write_candidates_do_not_scan_unrelated_memory_ranges() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let owner = Pointer::symbolic(Variable(860_000));
        let alias = Pointer::symbolic(Variable(860_001));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    owner.clone(),
                    (i as u32 * 8).into(),
                    (i as u32 * 8 + 4).into(),
                    1,
                ),
            ));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let facts = empty
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
        resources.synchronize_memory_equalities(&facts);
        let at = |offset| Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let query = |offset| {
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    resources
                        .memory_write_range(&at(offset), 4, &facts)
                        .is_some()
                })
            })
        };
        let ((hit, work), map_work) = query(size as i64 * 4);
        let ((miss, miss_work), miss_map_work) = query(size as i64 * 4 + 4);
        assert!(hit);
        assert!(!miss);
        assert!(
            resources
                .memory_write_range(&at(size as i64 * 4), 4, &empty)
                .is_none()
        );
        samples.push((size, work, map_work, miss_work, miss_map_work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 2 + 32 && samples[2].3 <= samples[0].3 * 2 + 32,
        "write checks scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[2].2 <= samples[0].2 * 3 + 128 && samples[2].4 <= samples[0].4 * 3 + 128,
        "write index work scanned unrelated ranges: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn owned_fragment_reservation_scales_with_fragments_not_ambient_memory() {
    for base in [
        Pointer::symbolic(Variable(862_010)),
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(862_011)), 4),
        },
    ] {
        let fact = |start: u32, end: u32| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                base.clone(),
                start.into(),
                end.into(),
                1,
            ))
        };
        let measure = |fragments: u32, ambient: u32| {
            let mut resources = ResourceContext::new();
            for i in 0..fragments {
                resources = resources.unchecked_with_fact(fact(i * 4, i * 4 + 4));
            }
            for i in 0..ambient {
                resources = resources.unchecked_with_fact(fact(8192 + i * 8, 8196 + i * 8));
            }
            let facts = PureFactContext::new();
            resources.synchronize_memory_equalities(&facts);
            let required = fact(0, fragments * 4);
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    assert!(
                        resources
                            .directly_supporting_owned_entry(&required, &facts)
                            .is_none()
                    );
                    let (_, supports) = resources
                        .reserve_owned_memory_fragments(&required, &facts)
                        .unwrap();
                    assert_eq!(supports.len(), fragments as usize);
                })
            });
            (work, map_work)
        };
        let ambient = [16, 64, 256, 1024].map(|n| measure(4, n));
        assert!(
            ambient[3].0 <= ambient[0].0 * 2 + 32,
            "reservation scanned unrelated memory: {ambient:?}"
        );
        assert!(
            ambient[3].1 <= ambient[0].1 * 4 + 256,
            "reservation index scanned unrelated memory: {ambient:?}"
        );
        let fragments = [8, 32, 128].map(|n| measure(n, 0));
        assert!(
            fragments[2].0 <= fragments[0].0 * 20 + 128,
            "reservation is superlinear: {fragments:?}"
        );
        assert!(
            fragments[2].1 <= fragments[0].1 * 40 + 1024,
            "reservation index is superlinear: {fragments:?}"
        );
        eprintln!("fragment reservation at {base:?}: ambient {ambient:?}; fragments {fragments:?}");
    }
}

#[test]
fn specification_read_candidates_do_not_scan_unrelated_memory_ranges() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let owner = Pointer::symbolic(Variable(850_000));
        let alias = Pointer::symbolic(Variable(850_001));
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                owner.clone(),
                MachineTerm::constant(i as u32 * 2),
                MachineTerm::constant(i as u32 * 2 + 1),
            )));
        }
        let facts = PureFactContext::new();
        resources.synchronize_memory_equalities(&facts);
        let facts =
            facts.assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
        resources.synchronize_memory_equalities(&facts);
        let at = |index| Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(index * 4),
        };
        let ((allowed, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources.permits_memory_read(&at(size as i64), 4, &facts)
            })
        });
        assert!(allowed);
        let ((denied, miss_work), miss_map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    resources.permits_memory_read(&at(size as i64 + 1), 4, &facts)
                })
            });
        assert!(!denied, "a gap between ranges is not readable");
        samples.push((size, work, map_work, miss_work, miss_map_work));
    }
    assert!(
        samples[2].1 <= samples[0].1 * 2 + 32 && samples[2].3 <= samples[0].3 * 2 + 32,
        "read checks scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[2].2 <= samples[0].2 * 3 + 128 && samples[2].4 <= samples[0].4 * 3 + 128,
        "read index work scanned unrelated ranges: {samples:?}"
    );
}

#[test]
fn stored_child_arguments_require_owned_memory() {
    let (instance, mut definition, state) = recursive_child_fixture();
    let arm = &mut definition.matched.as_mut().unwrap().arms[1];
    let Some(segment) = arm.contains[0].memory_segment_mut() else {
        unreachable!()
    };
    segment.end = crate::kernel::program_expression::int32_literal(2); // one LP64 pointer
    arm.children[0].arguments = vec![SpecExpression::ProgramExpression(
        ProgramExpression::TypedLoad {
            pointer: Box::new(crate::kernel::program_expression::variable("p")),
            value_type: ProgramType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
    )];
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let assumptions = PureFactContext::new();
    let rewrite = |state: &ExecutionState,
                   definition: &CompositeResourceDefinition,
                   assumptions: &PureFactContext,
                   unfold| {
        crate::kernel::rewrite_resource_instance_selecting_children(
            state,
            &instance,
            definition,
            std::slice::from_ref(definition),
            assumptions,
            unfold,
            Some(&children),
        )
    };
    let open = rewrite(&state, &definition, &assumptions, true)
        .unwrap()
        .state;
    rewrite(&open, &definition, &assumptions, false).unwrap();
    let mut unreadable = definition.clone();
    unreadable.matched.as_mut().unwrap().arms[1]
        .contains
        .clear();
    // Even a caller using permissive specification lowering cannot grant
    // child construction an unchecked read outside the owned body.
    assert!(
        rewrite(
            &state,
            &unreadable,
            &assumptions.clone().allow_symbolic_contract_loads(),
            true
        )
        .is_err()
    );
    let mut missing = open.clone();
    missing.resources = ResourceContext::new().unchecked_with_facts(
        open.resources()
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_none())
            .cloned(),
    );
    assert!(rewrite(&missing, &definition, &assumptions, false).is_err());
    assert!(rewrite(&open, &unreadable, &assumptions, false).is_err());
    let concrete = Pointer {
        block: "unowned-link".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let concrete_state = state.clone().with_memory(
        Memory::new()
            .with_block("unowned-link", 8)
            .store(concrete.clone(), ProgramValue::pointer(Pointer::null())),
    );
    let mut concrete_definition = definition.clone();
    concrete_definition.matched.as_mut().unwrap().arms[1].children[0].arguments =
        vec![SpecExpression::ProgramExpression(
            ProgramExpression::TypedLoad {
                pointer: Box::new(crate::kernel::program_expression::pointer_value(
                    concrete.clone(),
                )),
                value_type: ProgramType::Int32Pointer,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            },
        )];
    // A materialized C block is not authority to read a link outside the
    // resource body, even though ordinary C execution can access that block.
    assert!(rewrite(&concrete_state, &concrete_definition, &assumptions, true).is_err());
    concrete_definition.matched.as_mut().unwrap().arms[1]
        .contains
        .push(ResourceSpec::owned_memory(MemorySegment {
            uninitialized: false,
            value_runs: Default::default(),
            base: crate::kernel::program_expression::pointer_value(concrete),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(2),
            element_width: 4,
            guard: None,
        }));
    rewrite(&concrete_state, &concrete_definition, &assumptions, true).unwrap();
    // This unchecked fixture assumes contradictory ownership. Unfold exposes
    // the held body; it does not search the frame to rediscover the conflict.
    let mut overlap = state.clone();
    overlap.resources = overlap.resources.unchecked_with_facts(
        open.resources()
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_some())
            .cloned(),
    );
    assert!(rewrite(&overlap, &definition, &assumptions, true).is_ok());
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut framed = open.clone();
        for i in 0..size {
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    MachineTerm::Variable(Variable(1000 + i)),
                    4,
                ),
            };
            framed.resources = framed
                .resources
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    other,
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                )));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite(&framed, &definition, &assumptions, false)
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn instance_fold_preserves_memory_pieces_without_scanning_unrelated_resources() {
    let (instance, mut definition, _) = instance_memory_fixture();
    definition.contains = (0..3)
        .map(|i| {
            ResourceSpec::owned_memory(MemorySegment {
                uninitialized: false,
                value_runs: Default::default(),
                base: crate::kernel::program_expression::variable("p"),
                start: crate::kernel::program_expression::int32_literal(i),
                end: crate::kernel::program_expression::int32_literal(i + 1),
                element_width: 4,
                guard: None,
            })
        })
        .collect();
    let ProgramValue::Pointer(value) = instance.arguments()[0].as_program_value().unwrap() else {
        unreachable!()
    };
    let pointer = value.pointer().clone();
    let pieces = (0..3)
        .map(|i| {
            ResourceFact::own_memory(MemoryRange::new(
                pointer.clone(),
                MachineTerm::constant(i),
                MachineTerm::constant(i + 1),
            ))
        })
        .collect::<Vec<_>>();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut resources = ResourceContext::new().unchecked_with_facts(pieces.iter().cloned());
        for i in 0..size {
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    MachineTerm::Variable(Variable(1000 + i)),
                    4,
                ),
            };
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                other,
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )));
        }
        let state = ExecutionState::new().with_resource_context(resources);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                false,
                Some(&[]),
            )
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn independent_children_kernel_work_ignores_unrelated_instances() {
    let (instance, definition, initial) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = initial.clone();
        for identity in 10_000..10_000 + size {
            state
                .resources
                .record_instance_consumption(Variable(identity), Some(InstanceConsumption::Unfold));
        }
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let open = crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                true,
                Some(&children),
            )
            .unwrap()
            .state;
            assert!(open.instance_field_scope.is_empty());
            crate::kernel::rewrite_resource_instance_selecting_children(
                &open,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                false,
                Some(&children),
            )
            .unwrap()
        });
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn resource_match_constructor_index_tracks_evidence_and_scales_locally() {
    let ty = resource_index_type("Mark", vec![]);
    let model = resource_index_variable(&ty, 7);
    let constructor = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![],
        },
    };
    let equality = Proposition::Equal(
        Term::Algebraic(model.clone()),
        Term::Algebraic(constructor.clone()),
    );
    let reversed = Proposition::Equal(
        Term::Algebraic(constructor.clone()),
        Term::Algebraic(model.clone()),
    );
    for fact in [equality.clone(), reversed] {
        let assumptions = PureFactContext::new().assume_proposition(fact);
        assert_eq!(
            assumptions.known_algebraic_constructor(&model),
            Some(constructor.clone())
        );
        let restricted = assumptions.restricted_to_facts(&[], &[]);
        assert!(restricted.known_algebraic_constructor(&model).is_none());
    }
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_proposition(equality.clone());
        for index in 100..100 + size {
            assumptions.insert_proposition_fact(Proposition::Equal(
                Term::Algebraic(resource_index_variable(&ty, index)),
                Term::Algebraic(constructor.clone()),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                assumptions.known_algebraic_constructor(&model),
                Some(constructor.clone())
            );
        });
        assert!(work > 0, "constructor lookup must count candidate visits");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}

#[test]
fn instance_memory_fold_work_is_local_to_the_selected_instance() {
    let (instance, definition, initial) = instance_memory_fixture();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = initial.clone();
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (open, _) =
                rewrite_resource_instance(&state, &instance, &definition, &assumptions, true)
                    .unwrap();
            assert!(open.resource_instance_fields(instance.identity()).is_none());
            rewrite_resource_instance(&open, &instance, &definition, &assumptions, false).unwrap()
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] + 128,
            "unrelated handle scaling: {samples:?}"
        );
    }
}

#[test]
fn resource_instance_lookup_and_transfer_scale_by_identity() {
    let ty = resource_index_type("Mark", vec![]);
    let m = resource_index_variable(&ty, 1);
    let n = resource_index_variable(&ty, 2);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(m.clone()),
        Term::Algebraic(n.clone()),
    ));
    let selected = ResourceFact::own(Resource::Instance(field_instance(1, n, 0)));
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (context, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = ResourceContext::new();
            for identity in 1..=size {
                context = context
                    .try_compose_into_valid_context_delaying_normalization(
                        [ResourceFact::own(Resource::Instance(field_instance(
                            identity,
                            m.clone(),
                            0,
                        )))],
                        &assumptions,
                    )
                    .unwrap();
            }
            context
        });
        assert!(context.shares_storage_with(&context.clone()));
        let bindings = std::sync::Arc::new(
            (1..=size)
                .map(|id| (Variable(size + id), Variable(id)))
                .collect(),
        );
        let mut state = ExecutionState::new().with_resource_context(context.clone());
        state.resource_bindings = Some(bindings);
        let retained_state = state.clone();
        assert!(std::sync::Arc::ptr_eq(
            state.resource_bindings.as_ref().unwrap(),
            retained_state.resource_bindings.as_ref().unwrap()
        ));
        let (remaining, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                state
                    .owned_resource_instance(Variable(size + 1))
                    .unwrap()
                    .identity(),
                Variable(1)
            );
            // A formal absent from the map must not fall back to a caller ID.
            assert!(state.owned_resource_instance(Variable(1)).is_none());
            let mut missing = retained_state.clone();
            missing.resources = ResourceContext::new();
            assert!(
                missing
                    .owned_resource_instance(Variable(size + 1))
                    .is_none()
            );
            assert!(context.owned_instance(Variable(1)).is_some());
            assert!(context.owned_instance(Variable(size + 1)).is_none());
            assert!(context.satisfies_fact(&selected, &assumptions));
            context
                .without_fact_delaying_normalization(&selected, &assumptions)
                .unwrap()
        });
        assert_eq!(remaining.facts().len(), size as usize - 1);
        samples.push((build_work, query_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 3 + 16,
            "instance build scaling: {samples:?}"
        );
        assert!(
            pair[1].1 <= pair[0].1 + 64,
            "fixed identity query scaling: {samples:?}"
        );
    }
}

#[test]
fn symbolic_resource_indices_share_states_and_scale_with_indexed_context() {
    let ty = resource_index_type("Mark", vec![]);
    let selected = ResourceFact::own(indexed_resource(
        resource_index_variable(&ty, 991_000),
        false,
    ));
    let renamed = ResourceFact::own(indexed_resource(
        resource_index_variable(&ty, 991_001),
        false,
    ));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(resource_index_variable(&ty, 991_000)),
        Term::Algebraic(resource_index_variable(&ty, 991_001)),
    ));
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (_, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = ResourceContext::new();
            for i in 0..size {
                let fact = ResourceFact::own(Resource::Token {
                    name: format!("indexed_{i}"),
                    arguments: vec![AlgebraicValue::Algebraic(resource_index_variable(
                        &ty,
                        992_000 + i,
                    ))]
                    .into(),
                });
                let cloned = fact.clone();
                let (Resource::Token { arguments: a, .. }, Resource::Token { arguments: b, .. }) =
                    (fact.resource(), cloned.resource())
                else {
                    unreachable!()
                };
                assert!(std::sync::Arc::ptr_eq(a, b));
                context = context.unchecked_with_fact(fact);
            }
            context
        });
        let context = unrelated_token_context(size as usize).unchecked_with_fact(selected.clone());
        let (remaining, transfer_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.without_fact_delaying_normalization(&renamed, &assumptions)
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize);
        samples.push((size, build_work, transfer_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3).saturating_add(16),
            "building ADT-indexed resources: {samples:?}"
        );
        assert!(
            pair[1].2 <= pair[0].2.saturating_mul(2).saturating_add(16),
            "fixed indexed transfer: {samples:?}"
        );
    }
}

#[test]
fn symbolic_resource_indices_exact_transfer_scales_with_same_family_indices() {
    let ty = resource_index_type("Mark", vec![]);
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let selected = ResourceFact::own(indexed_resource(resource_index_variable(&ty, 1), false));
        let context = ResourceContext::new().unchecked_with_facts((1..=size).map(|id| {
            ResourceFact::own(indexed_resource(resource_index_variable(&ty, id), false))
        }));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.without_fact_delaying_normalization(&selected, &PureFactContext::new())
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(16),
            "exact ADT index lookup: {samples:?}"
        );
    }
}

#[test]
fn zero_resource_identity_ignores_unrelated_resources() {
    let quantity = MachineTerm::Variable(Variable(911_000));
    let intermediate = MachineTerm::Variable(Variable(911_001));
    let assumptions = PureFactContext::new()
        .assume_proposition(equality(quantity.clone(), intermediate.clone()))
        .assume_proposition(equality(intermediate, MachineTerm::constant(0)));
    let required = ResourceFact::own_quantity(
        Resource::Token {
            name: "empty".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        quantity,
    );
    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size);
            let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .clone()
                    .without_fact_delaying_normalization(&required, &assumptions)
            });
            assert_eq!(remaining.expect("zero consumption should succeed"), context);
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "zero-resource identity work changed with unrelated resources: {samples:?}"
    );
}

#[test]
fn owned_support_lookup_scales_with_unrelated_supported_facts() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let projected = ResourceFact::view_composite("nested".to_string(), vec![int32(7)]);
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let context = unrelated_token_context(size)
            .unchecked_with_fact(authority.clone())
            .unchecked_with_supported_facts(&authority, [projected.clone()]);
        let (support, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .directly_supporting_owned_entry(&projected, &PureFactContext::new())
                .map(|(_, support)| support)
        });
        assert_eq!(support, Some(&authority));
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(16),
            "indexed support lookup scanned unrelated facts: {samples:?}"
        );
    }
}

#[test]
fn cached_support_updates_ignore_unrelated_cached_supports() {
    let target = ResourceFact::own_composite("target_cache".to_string(), Vec::new());
    let mut samples = Vec::new();
    for size in [4_usize, 8, 16, 32] {
        let mut context = ResourceContext::new();
        for index in 0..size {
            let support = ResourceFact::own_composite(format!("cached_{index}"), Vec::new());
            context = context.unchecked_with_fact(support.clone());
            let occurrence = context.owned_occurrences_for_fact(&support)[0];
            context = context.with_cached_supported_expansion_for_occurrence(
                occurrence,
                &support,
                vec![ResourceFact::own_token(format!("body_{index}"), Vec::new())],
            );
        }
        context = context.unchecked_with_fact(target.clone());
        let target_occurrence = context.owned_occurrences_for_fact(&target)[0];
        let before_cache_allocations = crate::persistent::persistent_node_allocations();
        let (context, cache_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.with_cached_supported_expansion_for_occurrence(
                target_occurrence,
                &target,
                vec![ResourceFact::own_token(
                    "target_body".to_string(),
                    Vec::new(),
                )],
            )
        });
        let cache_allocations =
            crate::persistent::persistent_node_allocations() - before_cache_allocations;
        let before_remove_allocations = crate::persistent::persistent_node_allocations();
        let (remaining, remove_work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .without_exact_representation_for_occurrence(target_occurrence)
                .expect("the target support should be removable")
        });
        let remove_allocations =
            crate::persistent::persistent_node_allocations() - before_remove_allocations;
        assert_eq!(remaining.cached_supported_expansions(&target).len(), 0);
        samples.push((
            size,
            cache_work,
            remove_work,
            cache_allocations,
            remove_allocations,
        ));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8)
                && pair[1].2 <= pair[0].2.saturating_mul(2).saturating_add(8),
            "support cache updates scanned unrelated cached authorities: {samples:?}"
        );
    }
    let base_height = usize::BITS as usize - samples[0].0.leading_zeros() as usize;
    for (size, _, _, cache_allocations, remove_allocations) in samples {
        let height = usize::BITS as usize - size.leading_zeros() as usize;
        // A global canonical-map rebuild grows with every unrelated cache;
        // this logarithmic bound rejects that shape while allowing the
        // persistent paths for the affected support bucket.
        let bound = 32 * (height - base_height + 1);
        assert!(
            cache_allocations <= bound && remove_allocations <= bound,
            "support cache updates scaled with unrelated cache count at size {size}: cache={cache_allocations}, remove={remove_allocations}, bound={bound}"
        );
    }
}

#[test]
fn support_removal_visits_only_the_supported_projections() {
    const PROJECTION_COUNT: usize = 8;
    for size in [16_usize, 64, 256, 1024] {
        let authority =
            ResourceFact::own_composite("authority".to_string(), vec![int32(size as u32)]);
        let projections = (0..PROJECTION_COUNT)
            .map(|index| {
                ResourceFact::view_token(format!("projection_{index}"), vec![int32(size as u32)])
            })
            .collect::<Vec<_>>();
        let context = unrelated_token_context(size)
            .unchecked_with_fact(authority.clone())
            .unchecked_with_supported_facts(&authority, projections.clone());
        let ancestor = context.clone();

        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .without_exact_representation(&authority)
                .expect("the authority should be removable")
        });
        assert_eq!(
            work, PROJECTION_COUNT,
            "retiring support in a size-{size} context must visit only its projections"
        );
        assert_eq!(remaining.facts().len(), size);
        assert_eq!(ancestor.facts().len(), size + PROJECTION_COUNT + 1);
        for projection in projections {
            assert!(!remaining.satisfies_fact(&projection, &PureFactContext::new()));
        }
    }
}

#[test]
fn exact_resource_lookup_is_indexed_after_context_construction() {
    let required = ResourceFact::own_token("target".to_string(), vec![int32(0)]);
    for size in [16, 32, 64, 128] {
        let context = unrelated_token_context(size).unchecked_with_fact(required.clone());
        assert!(context.satisfies_fact(&required, &PureFactContext::new()));
        let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.satisfies_fact(&required, &PureFactContext::new())
        });
        assert!(satisfied);
        assert_eq!(
            work, 0,
            "indexed exact lookup scanned a size-{size} context"
        );
    }
}

#[test]
fn exact_owned_resource_satisfies_view_without_entailment_scan() {
    let range = memory_range(
        Pointer {
            block: "owned-view-target".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        8,
    );
    let owned = ResourceFact::own_memory(range.clone());
    let required = ResourceFact::view_memory(range);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size).unchecked_with_fact(owned.clone());
            assert!(context.satisfies_fact(&required, &PureFactContext::new()));
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &PureFactContext::new())
            });
            assert!(satisfied);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "exact ownership-to-view lookup should ignore unrelated resources: {samples:?}"
    );
}

/// A composite held under another spelling of its pointer is found among
/// the held composites whose pointer is related to the required one, not by
/// checking entailment against every held composite of the shape: a fold of
/// one heap object beside many costs the same at every size.
#[test]
fn nonexact_composite_entailment_ignores_unrelated_instances_of_the_shape() {
    let object = |index: u64| Pointer::symbolic(Variable(783_000 + index));
    let boxed = |pointer: Pointer| {
        ResourceFact::own_composite("boxed".into(), vec![ProgramValue::pointer(pointer)])
    };
    let alias = Pointer::symbolic(Variable(782_999));
    let work = [16u64, 64, 256].map(|size| {
        let context = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| boxed(object(index))));
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(
                PointerValue::new(alias.clone(), ProgramType::Int32Pointer),
                PointerValue::new(object(size - 1), ProgramType::Int32Pointer),
            ),
            true,
        );
        let (held, used) = crate::instrumentation::measure_deterministic_work(|| {
            context.satisfies_fact(&boxed(alias.clone()), &assumptions)
        });
        assert!(held, "size={size}");
        used
    });
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] + 2),
        "composite entailment grows with unrelated instances of its shape: {work:?}"
    );
}

#[test]
fn nonexact_memory_entailment_ignores_unrelated_blocks() {
    let target_base = Pointer {
        block: "target-block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let required = ResourceFact::view_memory(memory_range(target_base.clone(), 2, 6));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    ResourceFact::view_memory(memory_range(
                        Pointer {
                            block: format!("unrelated-{index}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        8,
                    ))
                }))
                .unchecked_with_fact(ResourceFact::own_memory(memory_range(
                    target_base.clone(),
                    0,
                    8,
                )));
            assert_eq!(context.direct_match_candidates(&required).count(), 1);
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &PureFactContext::new())
            });
            assert!(satisfied);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed memory entailment should not inspect unrelated blocks: {samples:?}"
    );
}

#[test]
fn unrelated_resource_normalization_has_linear_deterministic_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size);
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.normalized(&PureFactContext::new())
            });
            assert_eq!(normalized.facts().len(), size);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "resource normalization is superlinear: {samples:?}"
        );
    }
}

#[test]
fn adjacent_memory_normalization_has_linearithmic_deterministic_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: "p".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_memory(memory_range(base.clone(), index as u32, index as u32 + 1))
            }));
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.normalized(&PureFactContext::new())
            });
            assert_eq!(normalized.facts().len(), 1);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "adjacent resource normalization is superlinear: {samples:?}"
        );
    }
}

#[test]
fn disjoint_concrete_range_validity_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: "p".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_memory(memory_range(
                    base.clone(),
                    (index * 2) as u32,
                    (index * 2 + 1) as u32,
                ))
            }));
            let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.validity_error(&PureFactContext::new())
            });
            assert!(error.is_none());
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "concrete range validation is superlinear: {samples:?}"
        );
    }
}

#[test]
fn observable_structural_separation_does_not_materialize_owned_pairs() {
    for same_base in [false, true] {
        let samples = [16, 32, 64, 128]
            .into_iter()
            .map(|size| {
                let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                    ResourceFact::own_memory(memory_range(
                        Pointer {
                            block: if same_base {
                                "shared_block".into()
                            } else {
                                format!("block_{index}").into()
                            },
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        if same_base { (index * 2) as u32 } else { 0 },
                        if same_base { (index * 2 + 1) as u32 } else { 1 },
                    ))
                }));
                let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .observable_facts(&PureFactContext::new())
                        .expect("structurally disjoint memory ranges should compose")
                });
                assert_eq!(facts.len(), 1, "size-{size} projection materialized pairs");
                assert!(matches!(facts[0], Proposition::ResourceComposition(_)));
                assert!(crate::kernel::search::ProofSearch::proves(
                    &(PureFactContext::new()),
                    &Proposition::ResourceSeparate {
                        left: Box::new(context.facts()[0].resource().clone()),
                        right: Box::new(context.facts()[size - 1].resource().clone()),
                    }
                ));
                (size, work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "observable resource projection is superlinear: {samples:?}"
            );
        }
    }
}

#[test]
fn inserting_a_disjoint_concrete_range_uses_interval_neighbors() {
    for size in [16, 32, 64, 128] {
        let base = Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            ResourceFact::own_memory(memory_range(
                base.clone(),
                (index * 2) as u32,
                (index * 2 + 1) as u32,
            ))
        }));
        let next =
            ResourceFact::own_memory(memory_range(base, (size * 2) as u32, (size * 2 + 1) as u32));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.try_compose_into_valid_context_delaying_normalization(
                std::iter::once(next),
                &PureFactContext::new(),
            )
        });
        assert!(result.is_ok());
        assert!(
            work <= size + 4,
            "indexed insertion did too much work for {size} existing ranges: {work}"
        );
    }
}

#[test]
fn native_large_coordinate_insertion_uses_interval_neighbors() {
    for (origin, width) in [(1u64 << 63, 1), (1u64 << 62, 4)] {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(995_100));
            let owned = |start, end| {
                ResourceFact::own_memory(MemoryRange::new_wide(
                    base.clone(),
                    MachineTerm::uint64_constant(start),
                    MachineTerm::uint64_constant(end),
                    width,
                ))
            };
            let assumptions = PureFactContext::new();
            let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts(
                (0..size).map(|i| owned(origin + 4 + 2 * i as u64, origin + 5 + 2 * i as u64)),
            );
            context.synchronize_memory_equalities(&assumptions);
            let mut work = Vec::new();
            // A fixed disjoint insertion, then collisions with the first and last owners.
            for (next, accepted) in [
                (owned(origin, origin + 1), true),
                (owned(origin + 4, origin + 5), false),
                (
                    owned(
                        origin + 4 + 2 * (size - 1) as u64,
                        origin + 5 + 2 * (size - 1) as u64,
                    ),
                    false,
                ),
            ] {
                for _ in 0..3 {
                    let (result, units) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            context
                                .clone()
                                .try_compose_into_valid_context_delaying_normalization(
                                    [next.clone()],
                                    &assumptions,
                                )
                        });
                    assert_eq!(result.is_ok(), accepted);
                    assert_eq!(context.facts().len(), size);
                    work.push(units);
                }
            }
            samples.push((size, work));
        }
        eprintln!("native insertion origin={origin}, width={width}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 48)),
            "large native coordinates scan ambient owners: {samples:?}"
        );
    }
}

#[test]
fn translated_owner_insertion_uses_interval_neighbors() {
    for symbolic in [false, true] {
        for native in [false, true] {
            let mut samples = Vec::new();
            for size in [4usize, 16, 64] {
                let _session = crate::kernel::VerificationSession::enter();
                let assumptions = PureFactContext::new();
                let owned = |byte_offset: i64| {
                    let base = Pointer {
                        block: PointerBlock::Symbolic(Variable(995_300)),
                        offset: if symbolic {
                            PointerOffsetTerm::add(
                                PointerOffsetTerm::Variable(Variable(995_301)),
                                PointerOffsetTerm::Constant(byte_offset),
                            )
                        } else {
                            PointerOffsetTerm::Constant(byte_offset)
                        },
                    };
                    ResourceFact::own_memory(if native {
                        MemoryRange::new_wide(
                            base,
                            MachineTerm::uint64_constant(0),
                            MachineTerm::uint64_constant(1),
                            4,
                        )
                    } else {
                        MemoryRange::new_with_element_width(base, 0u32.into(), 1u32.into(), 4)
                    })
                };
                let context = ResourceContext::new_with_equalities(&assumptions)
                    .unchecked_with_facts((0..size).map(|i| owned(8 * i as i64)));
                context.synchronize_memory_equalities(&assumptions);
                let mut work = Vec::new();
                for (next, accepted) in [
                    (owned(-8), true),
                    (owned(0), false),
                    (owned(8 * (size - 1) as i64), false),
                ] {
                    for _ in 0..3 {
                        let (result, units) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                context
                                    .clone()
                                    .try_compose_into_valid_context_delaying_normalization(
                                        [next.clone()],
                                        &assumptions,
                                    )
                            });
                        assert_eq!(result.is_ok(), accepted);
                        assert_eq!(context.facts().len(), size);
                        work.push(units);
                    }
                }
                samples.push((size, work));
            }
            eprintln!("translated owners symbolic={symbolic}, native={native}: {samples:?}");
            assert!(
                samples.windows(2).all(|pair| pair[0]
                    .1
                    .iter()
                    .zip(&pair[1].1)
                    .all(|(small, large)| *large <= *small + 48)),
                "constant base translations scan ambient owners: {samples:?}"
            );
        }
    }
}

#[test]
fn constant_neighbor_overlap_checks_do_not_walk_pointer_alias_pairs() {
    for native in [false, true] {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let p = Pointer::symbolic(Variable(995_850));
            let mut assumptions = PureFactContext::new();
            for i in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::pointer_equal(
                        p.clone(),
                        Pointer::symbolic(Variable(995_851 + i as u64)),
                    ),
                    true,
                );
            }
            let owned = |start: u32| {
                ResourceFact::own_memory(if native {
                    MemoryRange::new_wide(
                        p.clone(),
                        MachineTerm::uint64_constant(u64::from(start)),
                        MachineTerm::uint64_constant(u64::from(start + 1)),
                        4,
                    )
                } else {
                    MemoryRange::new_with_element_width(
                        p.clone(),
                        start.into(),
                        (start + 1).into(),
                        4,
                    )
                })
            };
            let context =
                ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(owned(0));
            context.synchronize_memory_equalities(&assumptions);
            let mut work = Vec::new();
            for (start, accepted) in [(1, true), (0, false)] {
                for _ in 0..3 {
                    let (result, units) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            context
                                .clone()
                                .try_compose_into_valid_context_delaying_normalization(
                                    [owned(start)],
                                    &assumptions,
                                )
                        });
                    assert_eq!(result.is_ok(), accepted);
                    assert_eq!(context.facts().len(), 1);
                    work.push(units);
                }
            }
            samples.push((size, work));
        }
        eprintln!("constant neighbor overlap, native={native}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 24)),
            "constant neighbor comparison walks alias pairs: {samples:?}"
        );
    }
}

#[test]
fn owner_insertion_does_not_walk_aliases_into_unowned_blocks() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let p = Pointer::symbolic(Variable(995_730));
        let mut assumptions = PureFactContext::new();
        for i in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::pointer_equal(
                    p.clone(),
                    Pointer::symbolic(Variable(995_731 + i as u64)),
                ),
                true,
            );
        }
        let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::new_with_element_width(
                p.clone(),
                0u32.into(),
                1u32.into(),
                4,
            )),
        );
        context.synchronize_memory_equalities(&assumptions);
        let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            p,
            0u32.into(),
            1u32.into(),
            4,
        ));
        let mut work = Vec::new();
        for _ in 0..3 {
            let (result, units) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .clone()
                    .try_compose_into_valid_context_delaying_normalization(
                        [required.clone()],
                        &assumptions,
                    )
            });
            assert!(result.is_ok());
            assert_eq!(context.facts().len(), 1);
            work.push(units);
        }
        samples.push((size, work));
    }
    eprintln!("owner insertion beside unowned aliases: {samples:?}");
    assert!(
        samples.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 24)),
        "owner insertion walks aliases into unowned blocks: {samples:?}"
    );
}

#[test]
fn ownership_alias_checks_do_not_filter_read_only_views() {
    for has_owner in [false, true] {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let p = Pointer::symbolic(Variable(995_700));
            let q = Pointer::symbolic(Variable(995_701));
            let index = MachineTerm::var(Variable(995_702));
            let end = MachineTerm::add(index.clone(), 1u32.into());
            let assumptions = PureFactContext::new()
                .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true)
                .assume_condition(
                    ConditionTerm::signed_less_than(4u32.into(), end.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(index.clone(), 5u32.into()),
                    true,
                );
            let range = |base, start, end| MemoryRange::new_with_element_width(base, start, end, 4);
            let mut context = ResourceContext::new_with_equalities(&assumptions)
                .unchecked_with_facts((0..size).map(|i| {
                    ResourceFact::view_memory(range(
                        q.clone(),
                        (16 + 4 * i as u32).into(),
                        (17 + 4 * i as u32).into(),
                    ))
                }));
            if has_owner {
                context = context.unchecked_with_fact(ResourceFact::own_memory(range(
                    q.clone(),
                    4u32.into(),
                    5u32.into(),
                )));
            }
            context.synchronize_memory_equalities(&assumptions);
            let required = ResourceFact::own_memory(range(p, index, end));
            let mut work = Vec::new();
            for _ in 0..3 {
                let (result, units) = crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .clone()
                        .try_compose_into_valid_context_delaying_normalization(
                            [required.clone()],
                            &assumptions,
                        )
                });
                assert_eq!(result.is_ok(), !has_owner);
                assert_eq!(context.facts().len(), size + usize::from(has_owner));
                work.push(units);
            }
            samples.push((size, work));
        }
        eprintln!("ownership checks beside views, has_owner={has_owner}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 24)),
            "ownership checks filter read-only views: {samples:?}"
        );
    }
}

#[test]
fn exact_pointer_alias_ownership_checks_select_interval_neighbors() {
    for native in [false, true] {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let p = Pointer::symbolic(Variable(995_600));
            let q = Pointer::symbolic(Variable(995_601));
            let assumptions = PureFactContext::new()
                .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
            let owned = |base: Pointer, start: u32| {
                ResourceFact::own_memory(if native {
                    MemoryRange::new_wide(
                        base,
                        MachineTerm::uint64_constant(u64::from(start)),
                        MachineTerm::uint64_constant(u64::from(start + 1)),
                        4,
                    )
                } else {
                    MemoryRange::new_with_element_width(base, start.into(), (start + 1).into(), 4)
                })
            };
            let context = ResourceContext::new_with_equalities(&assumptions)
                .unchecked_with_facts((0..size).map(|i| owned(q.clone(), 4 + 4 * i as u32)));
            context.synchronize_memory_equalities(&assumptions);
            let mut work = Vec::new();
            for (start, accepted) in [(0, true), (4, false), (4 * size as u32, false)] {
                for _ in 0..3 {
                    let (result, units) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            context
                                .clone()
                                .try_compose_into_valid_context_delaying_normalization(
                                    [owned(p.clone(), start)],
                                    &assumptions,
                                )
                        });
                    assert_eq!(result.is_ok(), accepted);
                    assert_eq!(context.facts().len(), size);
                    work.push(units);
                }
            }
            samples.push((size, work));
        }
        eprintln!("exact alias owner checks, native={native}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 48)),
            "exact pointer aliases scan owned fragments: {samples:?}"
        );
    }
}

#[test]
fn unrelated_origin_does_not_disable_owned_interval_neighbors() {
    for native in [false, true] {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let assumptions = PureFactContext::new();
            let owned = |variable, displacement| {
                let base = Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::add(
                        PointerOffsetTerm::scale_int32(MachineTerm::var(Variable(variable)), 1),
                        PointerOffsetTerm::Constant(displacement),
                    ),
                };
                ResourceFact::own_memory(if native {
                    MemoryRange::new_wide(
                        base,
                        MachineTerm::uint64_constant(0),
                        MachineTerm::uint64_constant(1),
                        4,
                    )
                } else {
                    MemoryRange::new_with_element_width(base, 0u32.into(), 1u32.into(), 4)
                })
            };
            let context = ResourceContext::new_with_equalities(&assumptions)
                .unchecked_with_facts((0..size).map(|i| owned(995_500, 8 * i as i64)))
                .unchecked_with_fact(owned(995_501, 0));
            context.synchronize_memory_equalities(&assumptions);
            let mut work = Vec::new();
            for (required, accepted) in [
                (owned(995_500, -8), true),
                (owned(995_500, 0), false),
                (owned(995_500, 8 * (size - 1) as i64), false),
            ] {
                for _ in 0..3 {
                    let (result, units) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            context
                                .clone()
                                .try_compose_into_valid_context_delaying_normalization(
                                    [required.clone()],
                                    &assumptions,
                                )
                        });
                    assert_eq!(result.is_ok(), accepted);
                    assert_eq!(context.facts().len(), size + 1);
                    work.push(units);
                }
            }
            samples.push((size, work));
        }
        eprintln!("owner insertion with an unrelated origin, native={native}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 48)),
            "an unrelated origin disables indexed owner checks: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn installing_a_certified_resource_group_does_not_recheck_internal_pairs() {
    let base = Pointer {
        block: "certified_group".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let facts = (0..size)
            .map(|index| {
                ResourceFact::own_memory(memory_range(
                    base.clone(),
                    (index * 2) as u32,
                    (index * 2 + 1) as u32,
                ))
            })
            .collect::<Vec<_>>();
        ResourceContext::new()
            .try_compose_with_facts(facts.clone(), &PureFactContext::new())
            .expect("the resource group must be valid before it is certified");
        let (installed, work) = crate::instrumentation::measure_deterministic_work(|| {
            ResourceContext::new()
                .try_compose_certified_group_into_valid_context_delaying_normalization(
                    facts,
                    &PureFactContext::new(),
                )
        });
        assert!(installed.is_ok());
        // Installation now also closes each explicit span into the address
        // graph, including the complete-address shift for displaced starts.
        // Bound that fixed per-input work and its growth; internal pair
        // comparisons would grow quadratically across these sizes.
        assert!(
            work <= 96 * size,
            "installing a certified size-{size} group rechecked its internal pairs: {work}"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
        "certified installation grew superlinearly: {samples:?}"
    );
    let rescanned = samples
        .iter()
        .zip([4, 16, 64, 256])
        .map(|(work, size)| {
            let size = usize::try_from(size).unwrap();
            work + size * size
        })
        .collect::<Vec<_>>();
    assert!(
        rescanned.windows(2).any(|pair| pair[1] > pair[0] * 5),
        "the smaller fixture must detect internal pair checks: {samples:?}"
    );
}

#[test]
fn resource_consumption_ignores_unrelated_exact_shapes() {
    let required = ResourceFact::view_token("target".to_string(), vec![int32(7)]);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    ResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
                }))
                .unchecked_with_fact(ResourceFact::own_token(
                    "target".to_string(),
                    vec![int32(7)],
                ));
            assert_eq!(context.direct_match_candidates(&required).count(), 1);
            let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.without_fact_delaying_normalization(&required, &PureFactContext::new())
            });
            assert!(remaining.is_some());
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed token consumption should not inspect unrelated resource shapes: {samples:?}"
    );
}

#[test]
fn incremental_quantity_consumption_normalizes_only_the_exact_resource_bucket() {
    let mut samples = Vec::new();
    for size in [4_u32, 16, 64, 256, 1024] {
        let target_resource = Resource::Token {
            name: "shared_name".to_string(),
            arguments: vec![int32(size + 1).into()].into(),
        };
        let unit = ResourceFact::Own(target_resource.clone(), Box::new(MachineTerm::constant(1)));
        let required =
            ResourceFact::own_quantity(target_resource.clone(), MachineTerm::constant(2));
        let context = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_token("shared_name".to_string(), vec![int32(index)])
            }))
            .unchecked_with_fact(unit.clone())
            .unchecked_with_fact(unit.clone());
        let ancestor = context.clone();
        assert!(context.storage.materialized.get().is_none());

        let before = crate::persistent::persistent_node_allocations();
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .clone()
                .without_fact_incrementally(&required, &PureFactContext::new())
        });
        let remaining = remaining.expect("two retained units should satisfy quantity two");
        samples.push((
            size,
            usize::BITS as usize - (size as usize).leading_zeros() as usize,
            crate::persistent::persistent_node_allocations() - before,
            work,
        ));
        assert!(!remaining.satisfies_fact(&unit, &PureFactContext::new()));
        assert!(
            remaining.contains_exact_representation(&ResourceFact::own_token(
                "shared_name".to_string(),
                vec![int32(size / 2)],
            ))
        );
        assert!(remaining.storage.materialized.get().is_none());
        assert_eq!(
            ancestor
                .storage
                .index
                .exact
                .get(&unit)
                .map_or(0, |entries| entries.len()),
            2,
            "incremental consumption must leave its ancestor unchanged"
        );
        assert!(ancestor.shares_storage_with(&context));
    }

    let (_, base_height, base_allocations, base_work) = samples[0];
    for (size, height, allocations, work) in samples {
        let allocation_bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= allocation_bound,
            "size {size} incremental quantity consumption allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(
            work <= base_work + 2,
            "size {size} incremental quantity consumption used {work} deterministic units (base {base_work})"
        );
    }

    let unit = ResourceFact::own_token("target".to_string(), Vec::new());
    let context = ResourceContext::new()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit);
    let unavailable = ResourceFact::own_quantity(
        Resource::Token {
            name: "target".to_string(),
            arguments: Vec::new().into(),
        },
        MachineTerm::constant(3),
    );
    assert!(
        context
            .clone()
            .without_fact_incrementally(&unavailable, &PureFactContext::new())
            .is_none(),
        "failed incremental consumption must not manufacture a larger quantity"
    );
    assert_eq!(context.facts().len(), 2);
}

#[test]
fn cross_block_alias_owner_lookup_ignores_unrelated_bases() {
    let target = Pointer {
        block: PointerBlock::Symbolic(Variable(41_100)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let argument = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(target.clone(), argument.clone()),
        true,
    );
    let query = ResourceFact::own_memory(memory_range(argument, 0, 1));
    let samples = [8usize, 16, 32, 64].map(|size| {
        let mut facts = vec![ResourceFact::own_memory(memory_range(target.clone(), 0, 1))];
        facts.extend((1..size).map(|index| {
            ResourceFact::own_memory(memory_range(
                Pointer {
                    block: target.block.clone(),
                    offset: PointerOffsetTerm::Constant((index * 8) as i64),
                },
                0,
                1,
            ))
        }));
        let existing = ResourceContext::new().unchecked_with_facts(facts);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            existing.try_compose_into_valid_context_delaying_normalization(
                [query.clone()],
                &assumptions,
            )
        });
        assert!(
            result.is_err(),
            "the exact alias must be checked at size {size}"
        );
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 2),
        "unrelated bases increased exact-alias lookup work: {samples:?}"
    );
}

#[test]
fn symbolic_same_block_ranges_emit_no_pairs_with_near_linear_work() {
    // The lazy-separation acceptance curve: N symbolic same-block owned
    // ranges expose one compact composition authority and zero pairwise
    // ResourceSeparate propositions, in work near-linear in N.
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            };
            let endpoints = (0..=size)
                .map(|index| MachineTerm::Variable(Variable(94_000 + index as u64)))
                .collect::<Vec<_>>();
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_memory(MemoryRange::new(
                    base.clone(),
                    endpoints[index].clone(),
                    endpoints[index + 1].clone(),
                ))
            }));
            let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.observable_facts_assuming_valid(&PureFactContext::new())
            });
            let pair_count = facts
                .iter()
                .filter(|fact| matches!(fact, Proposition::ResourceSeparate { .. }))
                .count();
            assert_eq!(
                pair_count, 0,
                "symbolic same-block ranges must not materialize pairwise separations"
            );
            assert!(
                facts
                    .iter()
                    .any(|fact| matches!(fact, Proposition::ResourceComposition(_))),
                "multi-owner contexts should expose one compact authority"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "observable fact projection is superlinear: {samples:?}"
        );
    }
}

/// Exposing a cell that an unfolded composite holds is a structural lookup
/// at each unfolding, not a proof: with a chain of order facts relating the
/// composites' pointers, reasoning about every candidate at every unfolding
/// grows superlinearly, while the structural answer stays near linear in the
/// number of composites. Regression for the binary-tree slowdown, where
/// certification exposed each derived load through the resource algebra's
/// reasoning and took minutes.
#[test]
fn composite_exposure_finds_held_cells_by_structure_near_linearly() {
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("item", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment {
            uninitialized: false,
            value_runs: Default::default(),
            base: crate::kernel::program_expression::variable("item"),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    let pointer = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(900_000 + index)), 4),
    };
    let samples = [4_u64, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                ResourceFact::own_composite(
                    "cell".to_string(),
                    vec![ProgramValue::pointer(pointer(index))],
                )
            }));
            let mut assumptions = PureFactContext::new();
            for index in 0..size - 1 {
                assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(900_000 + index)),
                        MachineTerm::Variable(Variable(900_000 + index + 1)),
                    ),
                    true,
                ));
            }
            let target = ResourceFact::view_memory(memory_range(pointer(size - 1), 0, 1));
            let (exposed, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::expose_composite_resource_fact(
                    &context,
                    &target,
                    std::slice::from_ref(&definition),
                    &Memory::new(),
                    &assumptions,
                )
            });
            assert!(
                exposed.is_some(),
                "size {size}: the unfolded cell should be exposed"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    eprintln!("composite exposure samples: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "composite exposure is superlinear: {samples:?}"
        );
    }
}

/// Package 3 regression. The quantity relations behind populations and
/// the resource algebra are decided by exact lookup and the retained atomic
/// condition checker, so an ambient context of unrelated bounded variables must
/// not change their work. The general prover this replaced scanned every
/// condition fact for an inconsistency and every proposition fact for a
/// singleton substitution, so its work grew with `size`.
#[test]
fn quantity_relations_ignore_unrelated_facts() {
    let count = MachineTerm::Variable(Variable(960_001));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size).assume_condition(
                ConditionTerm::equal(count.clone(), MachineTerm::constant(3)),
                true,
            );
            let (decided, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    // `resource_quantity_is_positive`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::signed_greater_than(count.clone(), MachineTerm::constant(0)),
                    ),
                    // `resource_quantity_at_least`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::signed_greater_equal(
                            count.clone(),
                            MachineTerm::constant(2),
                        ),
                    ),
                    // An exact quantity equality
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::equal(count.clone(), MachineTerm::constant(3)),
                    ),
                    // A relation that does not follow: the miss must also be
                    // flat, and must not be repaired by a broader search.
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::equal(count.clone(), MachineTerm::constant(4)),
                    ),
                ]
            });
            assert_eq!(
                decided,
                [true, true, true, false],
                "size {size}: exact quantity routes decided the wrong relations"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "quantity relations scanned unrelated facts: {samples:?}"
    );
}

/// The same curve through the resource-algebra entry points that consume those
/// relations: symbolic-quantity entailment (`resource_quantity_at_least` and
/// the residual test in `consume_exact_resource_fact`) and access-mode coring
/// (`resource_quantity_is_positive`).
#[test]
fn symbolic_quantity_consumption_ignores_unrelated_facts() {
    let available_quantity = MachineTerm::Variable(Variable(960_011));
    let required_quantity = MachineTerm::Variable(Variable(960_012));
    let resource = Resource::Token {
        name: "counted".to_string(),
        arguments: vec![int32(7).into()].into(),
    };
    let available = ResourceFact::own_quantity(resource.clone(), available_quantity.clone());
    let required = ResourceFact::own_quantity(resource.clone(), required_quantity.clone());
    let empty_quantity = MachineTerm::Variable(Variable(960_014));
    let empty_core = ResourceFact::own_quantity(resource, empty_quantity.clone());
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size)
                .assume_condition(
                    ConditionTerm::signed_greater_equal(
                        available_quantity.clone(),
                        required_quantity.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_than(
                        available_quantity.clone(),
                        MachineTerm::constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::equal(empty_quantity.clone(), MachineTerm::constant(0)),
                    true,
                );
            let context = ResourceContext::new().unchecked_with_fact(available.clone());
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    context.satisfies_fact(&required, &assumptions),
                    available.core_with_assumptions(&assumptions).is_some(),
                    // The miss matters too: an exactly-zero quantity has no
                    // access-mode core, and the general prover answered that
                    // only after scanning every ambient condition fact for an
                    // inconsistency and every proposition fact for a singleton
                    // substitution.
                    empty_core.core_with_assumptions(&assumptions).is_some(),
                )
            });
            assert_eq!(
                outcome,
                (true, true, false),
                "size {size}: symbolic quantity entailment lost its exact premise"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "symbolic quantity consumption scanned unrelated facts: {samples:?}"
    );
}

/// Allocation separation now asks the retained atomic resource checker rather
/// than the general prover, so the same flat curve applies to it.
#[test]
fn allocation_separation_ignores_unrelated_facts() {
    let allocation_base = Pointer {
        block: "package-3-allocation".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = own_memory_fact(
        Pointer {
            block: "package-3-held".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        8,
    );
    let overlapping = own_memory_fact(allocation_base.clone(), 0, 8);
    let bytes = MachineTerm::constant(16);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size);
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    held.is_proven_separate_from_allocation_with_element_width(
                        &allocation_base,
                        &HeapExtent::int32(bytes.clone()),
                        4,
                        &assumptions,
                    ),
                    overlapping.is_proven_separate_from_allocation_with_element_width(
                        &allocation_base,
                        &HeapExtent::int32(bytes.clone()),
                        4,
                        &assumptions,
                    ),
                )
            });
            assert_eq!(
                outcome,
                (true, false),
                "size {size}: allocation separation decided the wrong blocks"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "allocation separation scanned unrelated facts: {samples:?}"
    );
}

/// Package 10(a) regression for `ResourceContext::satisfies_fact`'s miss
/// path.
///
/// A resource query that misses must be paid for by the fact it names and by
/// the resources the context indexes under that fact's block — never by the
/// ambient condition facts that happen to be in scope. Two axes are measured,
/// each with one fixed query.
///
/// The resource axis is flat. On the ambient-condition axis the residual
/// slope is the exact order-path walk in `condition_reasoning/order_paths.rs`,
/// a whole-context loop inside the frozen condition checker that
/// the kernel authority boundary in `docs/internals/proof-objects.md` treats as a separate indexing debt. This test
/// pins the slope that remains after the two `condition_facts` scans in
/// `exact_less_equal_for_memory_resolution` became indexed lookups at the two
/// endpoints the query names. Before that change the same query grew at twice
/// this rate (93, 157, 285, 541 over these sizes), so the assertion fails on
/// the old representation.
#[test]
fn satisfies_fact_miss_ignores_unrelated_facts() {
    let base = Pointer {
        block: "package-10a-held".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = own_memory_fact(base.clone(), 0, 8);
    let adjacent = own_memory_fact(base.clone(), 8, 16);
    let symbolic_end = MachineTerm::Variable(Variable(970_001));
    // A miss whose end is symbolic: the shape that reaches the proof-aware
    // containment layers instead of being refused by constant bounds.
    let missing = own_memory_fact(base.clone(), 0, symbolic_end);
    let context = ResourceContext::new()
        .unchecked_with_fact(held.clone())
        .unchecked_with_fact(adjacent.clone());

    let sizes = [16, 32, 64, 128];
    let ambient = sizes
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size);
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&missing, &assumptions)
            });
            assert!(
                !satisfied,
                "size {size}: the missing resource was satisfied"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let base_work = ambient[0].1;
    assert!(
        ambient
            .iter()
            .all(|(size, work)| *work <= base_work + 2 * (size - sizes[0])),
        "satisfies_fact's miss path still scans ambient condition facts: {ambient:?}"
    );

    // The other axis: unrelated resources in the same context, with the
    // ambient fact context held empty. The block index must keep this flat.
    let resources = sizes
        .into_iter()
        .map(|size| {
            let mut wide = ResourceContext::new()
                .unchecked_with_fact(held.clone())
                .unchecked_with_fact(adjacent.clone());
            for index in 0..size {
                wide = wide.unchecked_with_fact(own_memory_fact(
                    Pointer {
                        block: format!("package-10a-unrelated-{index}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    0,
                    4,
                ));
            }
            let assumptions = PureFactContext::new();
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                wide.satisfies_fact(&missing, &assumptions)
            });
            assert!(
                !satisfied,
                "size {size}: the missing resource was satisfied"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let base_work = resources[0].1;
    assert!(
        resources
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "satisfies_fact's miss path scanned unrelated resources: {resources:?}"
    );
}

#[test]
fn resource_model_arm_selection_ignores_unrelated_premises() {
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 11);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let exclusion = |value: &AlgebraicTerm| {
        Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(value.clone()),
            Term::Algebraic(empty.clone()),
        )))
    };
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_proposition(exclusion(&model));
        for index in 100..100 + size {
            assumptions.insert_proposition_fact(exclusion(&resource_index_variable(&ty, index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                select_resource_model_arm(&model, &assumptions),
                Some(ResourceModelArmSelection::Variant("Filled".to_string()))
            );
        });
        assert!(work > 0, "arm selection must count the premises it visits");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}

/// An adversarially ordered dependency chain is retried through an indexed
/// event worklist.  Its deterministic work should grow with the explicit
/// dependency nodes and edges, not with repeated whole-section scans.
#[test]
fn dependent_resource_clause_work_scales_with_dependency_nodes() {
    let pointer = |index: usize| Pointer {
        // Keep each node in its own block so the curve measures the clause
        // dependency walk rather than the unrelated same-block range
        // normalization cost of the resource algebra.
        block: PointerBlock::Concrete(format!("dependency-{index}")),
        offset: PointerOffsetTerm::Constant((index as i64) * 4),
    };
    let load = |pointer: Pointer| ProgramExpression::TypedLoad {
        pointer: Box::new(crate::kernel::program_expression::pointer_value(pointer)),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let samples = [4_usize, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let pointers = (0..=size).map(pointer).collect::<Vec<_>>();
            let memory = pointers.windows(2).fold(Memory::new(), |memory, pair| {
                memory.store(pair[0].clone(), ProgramValue::pointer(pair[1].clone()))
            });
            let state = ExecutionState::new().with_memory(memory);
            // Clause 0 is the only initially readable provider.  Put it last
            // and reverse the dependents so a fixed-point implementation must
            // rescan the whole pending suffix once per dependency depth.  An
            // event queue instead retries only the newly unblocked successor.
            let clauses = (1..size)
                .rev()
                .chain(std::iter::once(0))
                .map(|index| {
                    let base = if index == 0 {
                        crate::kernel::program_expression::pointer_value(pointers[index].clone())
                    } else {
                        load(pointers[index - 1].clone())
                    };
                    ResourceSpec::owned_memory(MemorySegment {
                        uninitialized: false,
                        value_runs: Default::default(),
                        base,
                        start: crate::kernel::program_expression::int32_literal(0),
                        end: crate::kernel::program_expression::int32_literal(1),
                        element_width: 4,
                        guard: None,
                    })
                })
                .collect::<Vec<_>>();
            let ((result, work), attempts) =
                crate::kernel::measure_resource_clause_attempts(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::functions::evaluate_function_resource_context(
                            &state,
                            &clauses,
                            &[],
                            &PureFactContext::new(),
                            &mut ExecutionBudget::default(),
                        )
                    })
                });
            let result = result.unwrap();
            assert!(
                result.is_ok(),
                "the dependency chain should evaluate: {result:?}"
            );
            assert_eq!(
                attempts,
                size * 2 - 1,
                "each blocked clause should be retried once after its provider: size={size}"
            );
            (size, work, attempts)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| { pair[1].1 <= pair[0].1.saturating_mul(4) + 256 }),
        "dependent clause work should stay bounded by the dependency graph: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn memory_invalidation_scales_with_affected_intervals_and_barrier_output() {
    let mut samples = Vec::new();
    for unrelated_count in [4_usize, 16, 64, 256, 1024] {
        let target_support = ResourceFact::own_composite("curve_target".into(), Vec::new());
        let target_view = ResourceFact::view_memory(MemoryRange::new(
            Pointer {
                block: "curve-block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ));
        let memory = Memory::new().with_block("curve-block", (8 * unrelated_count + 8) as u32);
        let mut resources = ResourceContext::new().unchecked_with_fact(target_support.clone());
        let target_occurrence = resources.owned_occurrences_for_fact(&target_support)[0];
        resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
            target_occurrence,
            &target_support,
            [target_view.clone()],
            &memory,
        );
        let mut unrelated_views = Vec::new();
        for index in 0..unrelated_count {
            let support =
                ResourceFact::own_composite(format!("curve_unrelated_{index}"), Vec::new());
            resources = resources.unchecked_with_fact(support.clone());
            let occurrence = resources.owned_occurrences_for_fact(&support)[0];
            let view = ResourceFact::view_memory(MemoryRange::new(
                Pointer {
                    block: "curve-block".into(),
                    offset: PointerOffsetTerm::Constant((8 + index * 8) as i64),
                },
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            ));
            resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
                occurrence,
                &support,
                [view.clone()],
                &memory,
            );
            unrelated_views.push(view);
        }
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context(resources);
        let before_allocations = crate::persistent::persistent_node_allocations();
        let (after, store_work) = crate::instrumentation::measure_deterministic_work(|| {
            state.clone().with_memory(memory.clone().store(
                Pointer {
                    block: "curve-block".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                int32(1),
            ))
        });
        let store_allocations =
            crate::persistent::persistent_node_allocations() - before_allocations;
        assert!(
            !after
                .resources()
                .contains_exact_representation(&target_view)
        );
        for view in &unrelated_views {
            assert!(after.resources().contains_exact_representation(view));
        }

        let before_barrier_allocations = crate::persistent::persistent_node_allocations();
        let (barrier_after, barrier_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                state
                    .clone()
                    .with_memory(memory.clone().with_loop_memory_havoc_preserving_loans(
                        Variable(820),
                        &BTreeSet::new(),
                        None,
                        None,
                    ))
            });
        let barrier_allocations =
            crate::persistent::persistent_node_allocations() - before_barrier_allocations;
        assert!(
            !barrier_after
                .resources()
                .contains_exact_representation(&target_view)
        );
        for view in &unrelated_views {
            assert!(
                !barrier_after
                    .resources()
                    .contains_exact_representation(view)
            );
        }
        let before_alias_allocations = crate::persistent::persistent_node_allocations();
        let (alias_after, alias_work) = crate::instrumentation::measure_deterministic_work(|| {
            state.with_memory(
                memory
                    .clone()
                    .store(Pointer::symbolic(Variable(821)), int32(1)),
            )
        });
        let alias_allocations =
            crate::persistent::persistent_node_allocations() - before_alias_allocations;
        assert!(
            !alias_after
                .resources()
                .contains_exact_representation(&target_view)
        );
        for view in &unrelated_views {
            assert!(!alias_after.resources().contains_exact_representation(view));
        }
        samples.push((
            unrelated_count,
            store_work,
            store_allocations,
            barrier_work,
            barrier_allocations,
            alias_work,
            alias_allocations,
        ));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 + 80 && pair[1].2 <= pair[0].2 + 256,
            "same-block disjoint intervals leaked unrelated work: {samples:?}"
        );
        assert!(
            pair[1].3 >= pair[0].3
                && pair[1].5 >= pair[0].5
                && pair[1].3 <= pair[0].3.saturating_mul(20).saturating_add(32)
                && pair[1].5 <= pair[0].5.saturating_mul(20).saturating_add(32)
                && pair[1].4 <= pair[0].4.saturating_mul(8).saturating_add(2048)
                && pair[1].6 <= pair[0].6.saturating_mul(8).saturating_add(2048),
            "barrier and alias fallback work/allocations must track affected output: {samples:?}"
        );
    }
}

/// A scalar-reference call carves four bytes from a padded field's eight-byte
/// slot. The returned scalar and preserved bytewise padding must rejoin even
/// when the object address is symbolic.
#[test]
#[ignore = "nightly: 2.8s in the parallel gate"]
fn returned_scalar_and_bytewise_padding_rejoin_over_symbolic_objects() {
    let mut samples = Vec::new();
    for size in [2usize, 8, 32, 128] {
        let mut pieces = Vec::new();
        let mut expected = Vec::new();
        for index in 0..size {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    MachineTerm::Variable(Variable(88_300 + index as u64)),
                    4,
                ),
            };
            pieces.push(ResourceFact::own_memory(MemoryRange::new(
                base.offset_by_bytes(8),
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )));
            pieces.push(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    base.clone(),
                    MachineTerm::constant(12),
                    MachineTerm::constant(16),
                    1,
                ),
            ));
            expected.push(ResourceFact::own_memory(MemoryRange::new(
                base,
                MachineTerm::constant(2),
                MachineTerm::constant(4),
            )));
        }
        let context = ResourceContext::new().unchecked_with_facts(pieces);
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            expected
                .iter()
                .all(|fact| context.satisfies_fact(fact, &PureFactContext::new()))
        });
        assert!(accepted);
        assert_eq!(
            context.facts().len(),
            2 * size,
            "a query preserves the held representation"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0] + 32),
        "{samples:?}"
    );
}

/// Frame queries never open recorded composites. Authors can expose the
/// selected owners explicitly; both refusal and that indexed success ignore
/// other folded compositions, even ones sharing the queried pointer argument.
#[test]
fn frame_queries_ignore_folded_compositions_until_explicitly_opened() {
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment {
            uninitialized: false,
            value_runs: Default::default(),
            base: crate::kernel::program_expression::variable("p"),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    let definitions = vec![definition.clone()];
    let _armed = crate::kernel::arm_frame_composite_definitions(definitions.clone());
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |index| Pointer::symbolic(Variable(910_000 + index));
            let head = |index| {
                ResourceFact::own_composite(
                    "cell".into(),
                    vec![ProgramValue::pointer(pointer(index))],
                )
            };
            let composition = |left, right| {
                ResourceContext::new().unchecked_with_facts([head(left), head(right)])
            };
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts = facts.assume_proposition(Proposition::ResourceComposition(composition(
                    if related { 0 } else { 2 * index + 2 },
                    2 * index + 3,
                )));
            }
            let selected = composition(0, 1);
            facts = facts.assume_proposition(Proposition::ResourceComposition(selected.clone()));
            let written = memory_range(pointer(1), 0, 1);
            let memory = Memory::new();
            let produced = crate::kernel::intern_memory(memory.clone().with_call_memory_havoc(
                Variable(919_000),
                std::slice::from_ref(&written),
                &facts,
                None,
            ));
            let derivation = produced
                .derivation()
                .expect("the call records its write set");
            let query = |facts: &PureFactContext, read: &Pointer| {
                use crate::kernel::resource_tracker::step_effect::{Evidence, StepEffect, affects};
                matches!(
                    affects(
                        &derivation,
                        &produced,
                        crate::kernel::resource_tracker::TrackedResource::Cell {
                            pointer: read,
                            bytes: 4
                        },
                        &Evidence {
                            assumptions: facts,
                            cross_loop_havoc: false
                        },
                    ),
                    StepEffect::Separate(_)
                )
            };
            let (found, miss) =
                crate::instrumentation::measure_deterministic_work(|| query(&facts, &pointer(0)));
            assert!(
                !found,
                "a recorded folded body is not automatic frame evidence"
            );

            // Open exactly the two selected heads, as explicit unfolding does,
            // then publish their composition. No other recorded head is read.
            let mut opened = selected;
            for index in [0, 1] {
                opened = crate::kernel::functions::expand_composite_resource_fact(
                    &opened,
                    &head(index),
                    &definitions,
                    &memory,
                    &facts,
                )
                .expect("the selected cell body opens");
            }
            let explicit = facts.assume_proposition(Proposition::ResourceComposition(opened));
            let (found, hit) = crate::instrumentation::measure_deterministic_work(|| {
                query(&explicit, &pointer(0))
            });
            assert!(found, "explicitly exposed owned ranges supply separation");
            assert!(
                !query(&explicit, &pointer(1)),
                "exposing a composition never frames an overlapping write"
            );
            samples.push((miss, hit));
        }
        eprintln!(
            "frame query beside 8/32/128 folded compositions, related={related}: {samples:?}"
        );
        assert!(
            samples.iter().all(|sample| *sample == samples[0]),
            "{samples:?}"
        );
    }
}

/// A contract section whose clauses all evaluate on the first pass needs no
/// read authority from the frame, so evaluating it does not expand the
/// composites the frame holds. In `examples/arena`'s pipeline the call rule
/// read `arena_destroy`'s `produces object(arena)` this way and expanded every
/// arena resource the caller held, which cost 45 million units once the frame
/// carried two allocations' worth of history.
#[test]
fn first_pass_resource_section_does_not_expand_the_frame() {
    let pointer = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(915_000 + index)), 4),
    };
    let cell = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment {
            uninitialized: false,
            value_runs: Default::default(),
            base: crate::kernel::program_expression::variable("p"),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    let produced = ResourceSpec::owned_memory(MemorySegment {
        uninitialized: false,
        value_runs: Default::default(),
        base: ProgramExpression::Value(ProgramValue::pointer(pointer(0))),
        start: crate::kernel::program_expression::int32_literal(0),
        end: crate::kernel::program_expression::int32_literal(1),
        element_width: 4,
        guard: None,
    });
    let samples = [4_u64, 16, 64]
        .into_iter()
        .map(|held| {
            // Keep term-bridge imports cold at every sample size.
            crate::kernel::clear_integer_bridge_memo();
            let frame = ResourceContext::new().unchecked_with_facts((1..=held).map(|index| {
                ResourceFact::own_composite(
                    "cell".to_string(),
                    vec![ProgramValue::pointer(pointer(index))],
                )
            }));
            let state = ExecutionState::new().with_resource_context(frame);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::evaluate_function_resource_context(
                    &state,
                    std::slice::from_ref(&produced),
                    std::slice::from_ref(&cell),
                    &PureFactContext::new(),
                    &mut ExecutionBudget::default(),
                )
                .expect("the section stays inside its budget")
            });
            assert!(result.is_ok(), "{held} held cells: {result:?}");
            (held, work)
        })
        .collect::<Vec<_>>();
    let base_work = samples[0].1;
    assert!(
        samples.iter().all(|(_, work)| *work == base_work),
        "evaluating a first-pass section grew with the frame's composites: {samples:?}"
    );
}

#[test]
fn returned_resource_prefix_consumes_only_selected_padded_field_fragments() {
    for width in [1u32, 4] {
        let mut samples = Vec::new();
        for size in [8usize, 32, 128, 512] {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(89_000)), 4),
            };
            let owned = |base, start, end, width| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base,
                    MachineTerm::constant(start),
                    MachineTerm::constant(end),
                    width,
                ))
            };
            let mut pieces = (0..size)
                .map(|index| {
                    owned(
                        Pointer {
                            block: PointerBlock::Heap(89_001 + index as u64),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        1,
                        4,
                    )
                })
                .collect::<Vec<_>>();
            pieces.push(owned(base.offset_by_bytes(8), 0, 1, 4));
            pieces.push(owned(base.clone(), 12 / width, 16 / width, width));
            let available = ResourceContext::new().unchecked_with_facts(pieces);
            let slot = owned(base.clone(), 2, 4, 4);
            let required = ResourceContext::new().unchecked_with_fact(slot.clone());
            let state = ExecutionState::new().with_resource_context(available.clone());
            let interface = FunctionContractInterface::new(ProgramType::Void, vec![]);
            let assumptions = PureFactContext::new();
            let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::jointly_consume_returned_resource_units(
                    &available,
                    &required,
                    &state,
                    &interface,
                    &assumptions,
                )
            });
            assert!(accepted, "{width}-byte units, {size} unrelated objects");
            samples.push(work);
            let duplicated = required.unchecked_with_fact(slot);
            assert!(
                !crate::kernel::functions::jointly_consume_returned_resource_units(
                    &available,
                    &duplicated,
                    &state,
                    &interface,
                    &assumptions
                )
            );
            let too_wide = ResourceContext::new().unchecked_with_fact(owned(base, 2, 5, 4));
            assert!(
                !crate::kernel::functions::jointly_consume_returned_resource_units(
                    &available,
                    &too_wide,
                    &state,
                    &interface,
                    &assumptions
                )
            );
        }
        assert!(
            samples.iter().all(|work| *work <= 4 * samples[0] + 64),
            "{samples:?}"
        );
    }
}

// Once a match supplies the constructor, opening its resource must not
// reevaluate an expanding list of predicates about that same model.
#[test]
fn known_resource_constructor_skips_predicate_refutation_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 850001);
    let constructor = arm_selection_constructor(&ty, "Filled", vec![int32(7).into()]);
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(850000),
        "choice".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let mut definition =
        CompositeResourceDefinition::new("choice", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            ResourceMatchArm {
                variant: "Empty".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            ResourceMatchArm {
                variant: "Filled".into(),
                bindings: vec!["value".into()],
                binding_types: vec![AlgebraicValueType::Program(ProgramType::Int32)],
                binding_variables: vec![None],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
        ],
    });
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
    );
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::ClickFunctionApplication {
                        name: format!("predicate{index}"),
                        arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
                    },
                    MachineTerm::constant(1),
                ),
                true,
            ));
        }
        let known = assumptions.clone().assume_proposition(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(constructor.clone()),
        ));
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_model_facts(
                &instance,
                std::slice::from_ref(&definition),
                &state,
                &known,
            )
        });
        assert!(facts.is_empty());
        costs.push(work);
        let (_, unresolved_work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_model_facts(
                &instance,
                std::slice::from_ref(&definition),
                &state,
                &assumptions,
            )
        });
        assert!(
            unresolved_work >= size,
            "unknown model must still consider its predicate premises"
        );
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
        "{costs:?}"
    );
}

// Once the only fieldless arm is known excluded, no arm can be published: the
// exclusion is already a fact, and refuting the remaining arm could not name
// the model's constructor. The call must not reevaluate the model's
// predicates at every step.
#[test]
fn known_exclusion_skips_refutation_of_unpublishable_arms() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 850101);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(850100),
        "choice".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let mut definition =
        CompositeResourceDefinition::new("choice", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            ResourceMatchArm {
                variant: "Empty".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            ResourceMatchArm {
                variant: "Filled".into(),
                bindings: vec!["value".into()],
                binding_types: vec![AlgebraicValueType::Program(ProgramType::Int32)],
                binding_variables: vec![None],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
        ],
    });
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
    );
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::ClickFunctionApplication {
                        name: format!("predicate{index}"),
                        arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
                    },
                    MachineTerm::constant(1),
                ),
                true,
            ));
        }
        let negation = Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(empty.clone()),
        )));
        let excluded = assumptions.assume_proposition(negation.clone());
        // The exact-fact index is built on its first query; a live context
        // has already paid for it.
        assert!(
            crate::kernel::reasoning::path_facts::required_obligation_is_exactly_discharged(
                &excluded, &negation,
            )
        );
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_model_facts(
                &instance,
                std::slice::from_ref(&definition),
                &state,
                &excluded,
            )
        });
        assert!(facts.is_empty(), "{facts:?}");
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
        "{costs:?}"
    );
}

#[test]
fn observable_projection_ignores_excluded_loan_bindings_when_hashing() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden_{index}")).collect(),
        );
        let base = context_with_one_loan_dependency(false);
        let expected = base.observable_composition();
        let mut context = base;
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        for index in 0..size {
            let range = MemoryRange::new(
                Memory::local_pointer(&format!("hidden_{index}")),
                0u32.into(),
                1u32.into(),
            );
            let support = ResourceFact::own_memory(range.clone());
            let view = ResourceFact::view_memory(range);
            context = context.unchecked_with_fact(support.clone());
            let support_occurrence = context.owned_occurrences_for_fact(&support)[0];
            let opening = ledger
                .lend(owner, reader, support_occurrence, support.clone())
                .unwrap();
            context = context.unchecked_with_supported_facts(&support, [view.clone()]);
            let occurrence = context.occurrences_for_fact(&view)[0];
            context = context.with_loan_dependency(
                occurrence,
                LoanViewBinding {
                    loan: opening.loan,
                    scope: opening.scope,
                    share: opening.root_share,
                    support: support_occurrence,
                    viewed: view,
                    hold: None,
                },
            );
        }
        let observed = context.observable_composition();
        assert_eq!(observed, expected);
        let (hash, work) =
            crate::instrumentation::measure_deterministic_work(|| resource_context_hash(&observed));
        assert_eq!(hash, resource_context_hash(&expected));
        assert_eq!(observed.live_loan_dependencies().count(), 1);
        assert!(work <= 16, "{size} excluded loans caused {work} hash units");
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work == costs[0]),
        "excluded loan costs: {costs:?}"
    );
}

#[test]
fn observable_projection_with_one_owner_and_borrow_does_not_scan_views() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let context =
            context_with_one_loan_dependency(false).unchecked_with_facts((0..size).map(|index| {
                ResourceFact::view_token(format!("ambient_observer_{index}"), Vec::new())
            }));
        let expected = context.observable_composition();
        let assumptions = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                let observed = context.observable_facts_assuming_valid(&assumptions);
                let [Proposition::ResourceComposition(composition)] = observed.as_slice() else {
                    panic!("one owner and a live borrow expose their composition");
                };
                assert!(std::sync::Arc::ptr_eq(
                    &composition.storage,
                    &expected.storage
                ));
            }
        });
        assert!(work <= 256, "one-owner borrow queries N={size}: {work}");
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work == costs[0]),
        "one-owner borrow query costs: {costs:?}"
    );
}

/// A base with N stated aliases (`q_i == b`, as a function requiring N
/// parameters equal to one it owns) must not cost N² to validate: every
/// alias's related roots are the same recorded-equality class, so walking
/// it once per alias re-walked one N-member class N times.
#[test]
fn owned_range_validity_is_linear_in_stated_aliases_of_its_base() {
    let parameter = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let samples = [16, 64, 256]
        .into_iter()
        .map(|size| {
            let owned = parameter(41_000);
            let assumptions = (0..size).fold(PureFactContext::new(), |assumptions, index| {
                assumptions.assume_condition(
                    ConditionTerm::pointer_equal(parameter(41_100 + index as u64), owned.clone()),
                    true,
                )
            });
            let context = ResourceContext::new().unchecked_with_facts(
                [41_001, 41_002, 41_000]
                    .map(|id| ResourceFact::own_memory(memory_range(parameter(id), 0, 4))),
            );
            let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.validity_error(&assumptions)
            });
            assert!(error.is_none(), "size-{size} owned ranges should be valid");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(6),
            "validity is superlinear in the base's stated aliases: {samples:?}"
        );
    }
}
#[test]
fn checked_child_read_definitions_scale_with_exchanges_not_ambient_facts() {
    let (instance, mut definition, state) = recursive_child_fixture();
    let arm = &mut definition.matched.as_mut().unwrap().arms[1];
    arm.contains[0].memory_segment_mut().unwrap().end =
        crate::kernel::program_expression::int32_literal(2);
    arm.children[0].arguments = vec![SpecExpression::ProgramExpression(
        ProgramExpression::TypedLoad {
            pointer: Box::new(crate::kernel::program_expression::variable("p")),
            value_type: ProgramType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
    )];
    let children = [
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let measure = |steps, unrelated| {
        let mut context = PureFactContext::new();
        for i in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(980_000 + i * 2)),
                    Pointer::symbolic(Variable(980_001 + i * 2)),
                ),
                true,
            );
        }
        let mut current = state.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..steps {
                for unfold in [true, false] {
                    let rewrite = crate::kernel::rewrite_resource_instance_selecting_children(
                        &current,
                        &instance,
                        &definition,
                        std::slice::from_ref(&definition),
                        &context,
                        unfold,
                        Some(&children),
                    )
                    .unwrap();
                    current = rewrite.state;
                    context = rewrite
                        .semantic_facts
                        .into_iter()
                        .fold(context.clone(), PureFactContext::assume_proposition);
                }
            }
        });
        assert!(
            current
                .owned_resource_instance(instance.identity())
                .is_some()
        );
        work
    };
    let related: Vec<_> = [8, 16, 32, 64]
        .into_iter()
        .map(|steps| measure(steps, 0))
        .collect();
    for pair in related.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 128,
            "repeated child exchanges: {related:?}"
        );
    }
    let unrelated: Vec<_> = [0, 16, 64, 256]
        .into_iter()
        .map(|size| measure(8, size))
        .collect();
    assert!(
        unrelated.iter().all(|work| *work <= unrelated[0] * 2 + 128),
        "child read publication scanned ambient facts: {unrelated:?}"
    );
}

/// Companion isolation for the owner selection used by observation: include
/// an exact first hit, a last hit, a miss, and repeated queries on one context.
#[test]
fn owned_support_lookup_ignores_same_shape_candidates() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = |i: usize| ResourceFact::own_composite("cell".into(), vec![int32(i as u32)]);
        let context = ResourceContext::new().unchecked_with_facts((0..count).map(owner));
        let facts = PureFactContext::new();
        let mut work = Vec::new();
        for query in [0, count - 1, count] {
            for _ in 0..3 {
                let (result, units) = crate::instrumentation::measure_deterministic_work(|| {
                    context.directly_supporting_owned_entry(&owner(query), &facts)
                });
                assert_eq!(result.is_some(), query < count);
                work.push(units);
            }
        }
        curves.push((count, work));
    }
    eprintln!("same-shape owner lookup (owners, first/last/miss x3 work): {curves:?}");
    assert!(
        curves
            .windows(2)
            .all(|pair| { pair[0].1.iter().zip(&pair[1].1).all(|(a, b)| *b <= *a + 32) }),
        "owner selection scans same-shape resources: {curves:?}"
    );
}

#[test]
fn exact_projection_support_ignores_duplicate_unbound_views() {
    let mut samples = Vec::new();
    for count in [4, 16, 64] {
        let owner = ResourceFact::own_composite("owner".into(), vec![]);
        let view = ResourceFact::view_composite("child".into(), vec![int32(7)]);
        let context = ResourceContext::new()
            .unchecked_with_facts((0..count).map(|_| view.clone()))
            .unchecked_with_fact(owner.clone())
            .unchecked_with_supported_facts(&owner, [view.clone()]);
        let facts = PureFactContext::new();
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.directly_supporting_owned_entry(&view, &facts)
        });
        assert_eq!(selected.map(|(_, fact)| fact), Some(&owner));
        samples.push(work);
        let child = context
            .clone()
            .without_exact_representation(&owner)
            .unwrap();
        assert!(
            child
                .directly_supporting_owned_entry(&view, &facts)
                .is_none()
        );
        assert!(
            context
                .directly_supporting_owned_entry(&view, &facts)
                .is_some()
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn nonexact_owner_selection_declines_crowded_quantity_buckets() {
    let resource = Resource::Token {
        name: "token".into(),
        arguments: vec![int32(7).into()].into(),
    };
    let required = ResourceFact::own(resource.clone());
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [4u32, 16, 64] {
        let context = ResourceContext::new().unchecked_with_facts(
            (2..count + 2)
                .map(|quantity| ResourceFact::own_quantity(resource.clone(), quantity.into())),
        );
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.directly_supporting_owned_entry(&required, &facts)
        });
        assert!(selected.is_none());
        samples.push(work);
        let exact = context.unchecked_with_fact(required.clone());
        assert_eq!(
            exact
                .directly_supporting_owned_entry(&required, &facts)
                .map(|(_, fact)| fact),
            Some(&required)
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
    let empty_owner = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_quantity(resource, 0u32.into()));
    assert!(
        empty_owner
            .directly_supporting_owned_entry(&required, &facts)
            .is_none()
    );
}

/// Call-view support selection must not walk other symbolic ranges sharing
/// the selected base. Prepare the index outside the measured query, then
/// measure exact early/late hits and a miss, both first and repeated.
#[test]
fn memory_owned_support_ignores_symbolic_range_bucket() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(995_000));
        let range = |i: usize| {
            MemoryRange::new(
                base.clone(),
                MachineTerm::Variable(Variable(995_100 + i as u64)),
                MachineTerm::Variable(Variable(995_101 + i as u64)),
            )
        };
        let assumptions = PureFactContext::new();
        let context = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_facts((0..count).map(|i| ResourceFact::own_memory(range(i))));
        context.synchronize_memory_equalities(&assumptions);
        let mut work = Vec::new();
        for query in [0, count - 1, count] {
            let required = ResourceFact::view_memory(range(query));
            for _ in 0..3 {
                let (selected, units) = crate::instrumentation::measure_deterministic_work(|| {
                    context.directly_supporting_owned_entry(&required, &assumptions)
                });
                assert_eq!(
                    selected.is_some(),
                    query < count,
                    "count {count}, query {query}"
                );
                if let Some((_, owner)) = selected {
                    assert_eq!(owner, &ResourceFact::own_memory(range(query)));
                }
                work.push(units);
            }
        }
        curves.push((count, work));
    }
    eprintln!("memory owner lookup (ranges, first/last/miss x3 work): {curves:?}");
    assert!(
        curves.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 32)),
        "memory support selection scans symbolic candidates: {curves:?}"
    );
}

/// A fixed-size read request cannot be backed by any of these short owners.
/// Reject it without enumerating the fragment frontier; exact early and late
/// hits are controls. Index preparation is outside all measured queries.
#[test]
fn memory_owned_support_miss_ignores_fragment_frontier() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(995_000));
        let range = |i: usize| {
            MemoryRange::new(
                base.clone(),
                MachineTerm::constant(i as u32),
                MachineTerm::constant(i as u32 + 1),
            )
        };
        let assumptions = PureFactContext::new();
        let context = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_facts((0..count).map(|i| ResourceFact::own_memory(range(i))));
        context.synchronize_memory_equalities(&assumptions);
        let mut work = Vec::new();
        for query in [0, count - 1, count] {
            let required = ResourceFact::view_memory(if query == count {
                MemoryRange::new(base.clone(), 0u32.into(), 128u32.into())
            } else {
                range(query)
            });
            for _ in 0..3 {
                let (selected, units) = crate::instrumentation::measure_deterministic_work(|| {
                    context.directly_supporting_owned_entry(&required, &assumptions)
                });
                assert_eq!(
                    selected.is_some(),
                    query < count,
                    "count {count}, query {query}"
                );
                if let Some((_, owner)) = selected {
                    assert_eq!(owner, &ResourceFact::own_memory(range(query)));
                }
                work.push(units);
            }
        }
        curves.push((count, work));
    }
    eprintln!("memory owner lookup (fragments, first/last/miss x3 work): {curves:?}");
    assert!(
        curves.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 32)),
        "memory support selection scans fragment candidates: {curves:?}"
    );
}

/// A fixed-size read request cannot be backed by any of these short owners.
/// Reject it without enumerating the fragment frontier; exact early and late
/// hits are controls. Index preparation is outside all measured queries.
#[test]
fn memory_direct_support_miss_ignores_fragment_frontier() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(995_000));
        let range = |i: usize| {
            MemoryRange::new(
                base.clone(),
                MachineTerm::constant(i as u32),
                MachineTerm::constant(i as u32 + 1),
            )
        };
        let assumptions = PureFactContext::new();
        let context = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_facts((0..count).map(|i| ResourceFact::own_memory(range(i))));
        context.synchronize_memory_equalities(&assumptions);
        let mut work = Vec::new();
        for query in [0, count - 1, count] {
            let required = ResourceFact::view_memory(if query == count {
                MemoryRange::new(base.clone(), 0u32.into(), 128u32.into())
            } else {
                range(query)
            });
            for _ in 0..3 {
                let (selected, units) = crate::instrumentation::measure_deterministic_work(|| {
                    context.directly_supporting_fact(&required, &assumptions)
                });
                assert_eq!(
                    selected.is_some(),
                    query < count,
                    "count {count}, query {query}"
                );
                if let Some(owner) = selected {
                    assert_eq!(owner, &ResourceFact::own_memory(range(query)));
                }
                work.push(units);
            }
        }
        curves.push((count, work));
    }
    eprintln!("memory direct support lookup (fragments, first/last/miss x3 work): {curves:?}");
    assert!(
        curves.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 32)),
        "memory support selection scans fragment candidates: {curves:?}"
    );
}

#[test]
fn memory_view_query_miss_ignores_fragment_frontier() {
    let mut curves = Vec::new();
    for owned in [false, true] {
        for count in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(995_000));
            let range = |i: usize| {
                MemoryRange::new(
                    base.clone(),
                    MachineTerm::constant(i as u32),
                    MachineTerm::constant(i as u32 + 1),
                )
            };
            let assumptions = PureFactContext::new();
            let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts(
                (0..count).map(|i| {
                    if owned {
                        ResourceFact::own_memory(range(i))
                    } else {
                        ResourceFact::view_memory(range(i))
                    }
                }),
            );
            context.synchronize_memory_equalities(&assumptions);
            let mut work = Vec::new();
            for query in [0, count - 1, count] {
                let required = ResourceFact::view_memory(if query == count {
                    MemoryRange::new(base.clone(), 0u32.into(), 128u32.into())
                } else {
                    range(query)
                });
                for _ in 0..3 {
                    let (selected, units) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            context.satisfies_fact(&required, &assumptions)
                        });
                    assert_eq!(selected, query < count, "count {count}, query {query}");
                    assert_eq!(context.facts().len(), count);
                    work.push(units);
                }
            }
            curves.push((count, work));
        }
    }
    eprintln!("memory view query lookup (fragments, first/last/miss x3 work): {curves:?}");
    assert!(
        curves
            .as_chunks::<3>()
            .0
            .iter()
            .all(|curve| curve.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 32))),
        "memory support selection scans fragment candidates: {curves:?}"
    );
}

#[test]
fn memory_view_consumption_miss_ignores_fragment_frontier() {
    let mut curves = Vec::new();
    for owned in [false, true] {
        for count in [4usize, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(995_000));
            let range = |i: usize| {
                MemoryRange::new(
                    base.clone(),
                    MachineTerm::constant(i as u32),
                    MachineTerm::constant(i as u32 + 1),
                )
            };
            let assumptions = PureFactContext::new();
            let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts(
                (0..count).map(|i| {
                    if owned {
                        ResourceFact::own_memory(range(i))
                    } else {
                        ResourceFact::view_memory(range(i))
                    }
                }),
            );
            context.synchronize_memory_equalities(&assumptions);
            let mut work = Vec::new();
            for query in [0, count - 1, count] {
                let required = ResourceFact::view_memory(if query == count {
                    MemoryRange::new(base.clone(), 0u32.into(), 128u32.into())
                } else {
                    range(query)
                });
                for _ in 0..3 {
                    let (selected, units) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            context
                                .clone()
                                .without_fact_incrementally(&required, &assumptions)
                                .is_some()
                        });
                    assert_eq!(selected, query < count, "count {count}, query {query}");
                    assert_eq!(context.facts().len(), count);
                    work.push(units);
                }
            }
            curves.push((count, work));
        }
    }
    eprintln!("memory view consumption lookup (fragments, first/last/miss x3 work): {curves:?}");
    assert!(
        curves
            .as_chunks::<3>()
            .0
            .iter()
            .all(|curve| curve.windows(2).all(|pair| pair[0]
                .1
                .iter()
                .zip(&pair[1].1)
                .all(|(small, large)| *large <= *small + 32))),
        "memory support selection scans fragment candidates: {curves:?}"
    );
}

/// Origin comparison must not inspect facts or other resource candidates.
/// Grow the former incident-bound frontier beside a constant-coordinate split.
#[test]
fn memory_split_origin_ignores_incident_bounds() {
    let mut curves = Vec::new();
    for count in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(996_000));
        let i = MachineTerm::Variable(Variable(996_001));
        let range =
            |start: MachineTerm, end: MachineTerm| MemoryRange::new(base.clone(), start, end);
        let slice = |start: u32, end: u32| {
            MemoryRange::new(
                base.offset_by_elements(i.clone(), 4),
                start.into(),
                end.into(),
            )
        };
        let owner = ResourceFact::own_memory(slice(0, 2));
        let required = ResourceFact::own_memory(slice(0, 1));
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_than(128u32.into(), i.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(i.clone(), 256u32.into()),
                true,
            );
        for k in 0..count {
            facts =
                facts.assume_condition(ConditionTerm::signed_less_than(k.into(), i.clone()), true);
        }
        let context = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_fact(owner.clone())
            .unchecked_with_facts(
                (0..count).map(|k| ResourceFact::own_memory(range((k + 1).into(), (k + 2).into()))),
            );
        context.synchronize_memory_equalities(&facts);
        let original = context.occurrences_for_fact(&owner)[0];
        let mut origins = crate::kernel::primitives::MemorySplitOrigins::default();
        let removed = ResourceFact::own_memory(slice(1, 2));
        let residual = context
            .without_fact_incrementally_with_origins(&removed, &facts, &mut origins)
            .expect("split the selected symbolic owner");
        let (support, _) = residual
            .directly_supporting_owned_entry(&required, &facts)
            .expect("the remaining slice keeps its ownership");
        let mut work = Vec::new();
        for _ in 0..3 {
            let (other, units) = crate::instrumentation::measure_deterministic_work(|| {
                origins.origin_of(support) == original
            });
            assert!(other, "the residual retains the original owner");
            work.push(units);
        }
        curves.push((count, work));
    }
    eprintln!("memory split origin (first/repeated work): {curves:?}");
    assert!(
        curves.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 32)),
        "split-origin lookup scans incident bounds: {curves:?}"
    );
}

#[test]
fn explicit_constant_fold_stops_at_a_gap_and_joins_mixed_width_pieces() {
    let mut curves = Vec::new();
    for (complete, native) in [(false, false), (true, false), (false, true), (true, true)] {
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let (instance, mut definition, _) = instance_memory_fixture();
            definition.contains = vec![ResourceSpec::owned_memory(MemorySegment {
                base: crate::kernel::program_expression::variable("p"),
                start: crate::kernel::program_expression::int32_literal(0),
                end: crate::kernel::program_expression::int32_literal(1024),
                element_width: 4,
                guard: None,
                uninitialized: false,
                value_runs: Default::default(),
            })];
            let ProgramValue::Pointer(value) = instance.arguments()[0].as_program_value().unwrap()
            else {
                unreachable!()
            };
            let piece = |start: u32, end: u32, width: u32| {
                let range = if native && width == 4 {
                    MemoryRange::new_wide(
                        value.pointer().clone(),
                        MachineTerm::uint64_constant(u64::from(start)),
                        MachineTerm::uint64_constant(u64::from(end)),
                        width,
                    )
                } else {
                    MemoryRange::new_with_element_width(
                        value.pointer().clone(),
                        start.into(),
                        end.into(),
                        width,
                    )
                };
                ResourceFact::own_memory(range)
            };
            let assumptions = PureFactContext::new();
            let mut resources = ResourceContext::new_with_equalities(&assumptions)
                .unchecked_with_fact(piece(0, if complete { 2048 } else { 4 }, 1));
            if complete {
                resources = resources.unchecked_with_fact(piece(512, 1024, 4));
            }
            for index in 0..count {
                let start = if complete { 2048 } else { 100 } + 2 * index;
                resources = resources.unchecked_with_fact(piece(start, start + 1, 4));
            }
            resources.synchronize_memory_equalities(&assumptions);
            let state = ExecutionState::new().with_resource_context(resources);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((result, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        rewrite_resource_instance(
                            &state,
                            &instance,
                            &definition,
                            &assumptions,
                            false,
                        )
                        .and_then(|(closed, _)| {
                            rewrite_resource_instance(
                                &closed,
                                &instance,
                                &definition,
                                &assumptions,
                                true,
                            )
                        })
                    })
                });
                assert_eq!(result.is_ok(), complete, "{complete}/{count}: {result:?}");
                assert!(state.resources().contains_exact_representation(&piece(
                    0,
                    if complete { 2048 } else { 4 },
                    1
                )));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("complete fold={complete}, native={native}, work/maps: {samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "{samples:?}"
        );
    }
}

/// A native-width fold has fixed input and a fixed early gap. Later disjoint
/// fragments cannot help; fixture/index construction is outside the measurement.
#[test]
fn native_fold_rejection_ignores_fragments_beyond_a_gap() {
    let mut curves = Vec::new();
    for case in ["gap", "owner", "joined"] {
        let complete = case != "gap";
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let (instance, mut definition, _) = instance_memory_fixture();
            let bound =
                |n| ProgramExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(n)));
            definition.contains = vec![ResourceSpec::owned_memory(MemorySegment {
                base: crate::kernel::program_expression::variable("p"),
                start: bound(0),
                end: bound(1024),
                element_width: 4,
                guard: None,
                uninitialized: false,
                value_runs: Default::default(),
            })];
            let ProgramValue::Pointer(value) = instance.arguments()[0].as_program_value().unwrap()
            else {
                unreachable!()
            };
            let piece = |start, end| {
                ResourceFact::own_memory(MemoryRange::new_wide(
                    value.pointer().clone(),
                    MachineTerm::uint64_constant(start),
                    MachineTerm::uint64_constant(end),
                    4,
                ))
            };
            let facts = PureFactContext::new();
            let first = piece(
                0,
                match case {
                    "owner" => 1024,
                    "joined" => 512,
                    _ => 1,
                },
            );
            let mut resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(first.clone());
            if case == "joined" {
                resources = resources.unchecked_with_fact(piece(512, 1024));
            }
            for index in 0..count {
                let start = if complete { 2048 } else { 100 } + 2 * u64::from(index);
                resources = resources.unchecked_with_fact(piece(start, start + 1));
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new().with_resource_context(resources);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((result, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        rewrite_resource_instance(&state, &instance, &definition, &facts, false)
                    })
                });
                assert_eq!(result.is_ok(), complete, "{complete}/{count}: {result:?}");
                assert_eq!(
                    state.resources().facts().len(),
                    count as usize + 1 + usize::from(case == "joined")
                );
                assert!(state.resources().contains_exact_representation(&first));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("native fold case={case}, count/work/maps: {samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "native fold scans rejected fragments: {samples:?}"
        );
    }
}

/// A non-consuming ownership check must not enumerate candidates after a gap.
#[test]
fn native_ownership_query_stops_at_a_fixed_gap() {
    constant_ownership_query_stops_at_a_fixed_gap(true);
}

#[test]
#[ignore = "nightly: multi-size constant narrow ownership scaling control"]
fn narrow_ownership_query_stops_at_a_fixed_gap() {
    constant_ownership_query_stops_at_a_fixed_gap(false);
}

fn constant_ownership_query_stops_at_a_fixed_gap(native: bool) {
    let mut curves = Vec::new();
    for case in ["gap", "owner", "joined", "views"] {
        let mut samples = Vec::new();
        for count in [4u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = PureFactContext::new();
            let p = Pointer::symbolic(Variable(989_970));
            let range = |start, end| constant_query_range(p.clone(), start, end, native);
            let own = |start, end| ResourceFact::own_memory(range(start, end));
            let first = own(
                0,
                match case {
                    "owner" => 1024,
                    "joined" => 512,
                    _ => 1,
                },
            );
            let mut context =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(first.clone());
            if case == "joined" {
                context = context.unchecked_with_fact(own(512, 1024));
            }
            for i in 0..count {
                let start = if matches!(case, "owner" | "joined") {
                    2048
                } else {
                    100
                } + 2 * i;
                context = context.unchecked_with_fact(if case == "views" {
                    ResourceFact::view_memory(range(start, start + 1))
                } else {
                    own(start, start + 1)
                });
            }
            context.synchronize_memory_equalities(&facts);
            let required = own(0, 1024);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((answer, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        context.satisfies_fact(&required, &facts)
                    })
                });
                assert_eq!(answer, matches!(case, "owner" | "joined"), "{case}/{count}");
                assert!(context.contains_exact_representation(&first));
                assert_eq!(
                    context.facts().len(),
                    count as usize + 1 + usize::from(case == "joined")
                );
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("constant ownership native={native} {case}, count/work/maps: {samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "query scans candidates: {samples:?}"
        );
    }
}

#[test]
fn native_ownership_query_scales_with_selected_pieces() {
    constant_ownership_query_scales_with_selected_pieces(true);
}

#[test]
#[ignore = "nightly: multi-size constant narrow ownership scaling control"]
fn narrow_ownership_query_scales_with_selected_pieces() {
    constant_ownership_query_scales_with_selected_pieces(false);
}

fn constant_ownership_query_scales_with_selected_pieces(native: bool) {
    let mut samples = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let p = Pointer::symbolic(Variable(989_971));
        let own = |start, end| {
            ResourceFact::own_memory(constant_query_range(p.clone(), start, end, native))
        };
        let mut context = ResourceContext::new_with_equalities(&facts);
        for i in 0..count {
            context = context.unchecked_with_fact(own(i, i + 1));
        }
        context.synchronize_memory_equalities(&facts);
        let required = own(0, count);
        let mut queries = Vec::new();
        for _ in 0..3 {
            let ((answer, work), maps) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    context.satisfies_fact(&required, &facts)
                })
            });
            assert!(answer);
            assert_eq!(context.facts().len(), count as usize);
            assert!(context.contains_exact_representation(&own(0, 1)));
            assert!(context.contains_exact_representation(&own(count - 1, count)));
            queries.push((work, maps));
        }
        samples.push((count, queries));
    }
    eprintln!("constant selected pieces native={native}, count/work/maps: {samples:?}");
    assert!(
        samples[3]
            .1
            .iter()
            .zip(&samples[0].1)
            .all(|(big, small)| big.0 <= small.0 * 96 + 256 && big.1 <= small.1 * 192 + 1024),
        "{samples:?}"
    );
}

fn constant_query_range(p: Pointer, start: u64, end: u64, native: bool) -> MemoryRange {
    if native {
        MemoryRange::new_wide(
            p,
            MachineTerm::uint64_constant(start),
            MachineTerm::uint64_constant(end),
            4,
        )
    } else {
        MemoryRange::new_with_element_width(p, (start as u32).into(), (end as u32).into(), 4)
    }
}

#[test]
fn native_symbolic_partition_ignores_unrelated_fragments() {
    for case in ["joined", "gap", "view", "ambiguous", "designation"] {
        let mut samples = Vec::new();
        for count in [4u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let p = Pointer::symbolic(Variable(989_972));
            let n = MachineTerm::Variable(Variable(989_973));
            let c = MachineTerm::uint64_constant;
            let facts = PureFactContext::new()
                .assume_condition(ConditionTerm::uint64_less_than(n.clone(), c(32)), true);
            let range = |lo, hi| MemoryRange::new_wide(p.clone(), lo, hi, 1);
            let first = ResourceFact::own_memory(range(c(0), n.clone()));
            let start = if case == "gap" {
                MachineTerm::uint64_add(n.clone(), c(1))
            } else {
                n.clone()
            };
            let suffix = range(start, c(32));
            let second =
                match case {
                    "view" => ResourceFact::view_memory(suffix),
                    "designation" => ResourceFact::own_memory(suffix.with_designation(
                        std::sync::Arc::new(Pointer::symbolic(Variable(989_974))),
                    )),
                    _ => ResourceFact::own_memory(suffix),
                };
            let mut context = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_facts([first.clone(), second.clone()]);
            if case == "ambiguous" {
                context =
                    context.unchecked_with_fact(ResourceFact::own_memory(range(n.clone(), c(31))));
            }
            for i in 0..count {
                context = context.unchecked_with_fact(ResourceFact::own_memory(range(
                    c(64 + i * 2),
                    c(65 + i * 2),
                )));
            }
            context.synchronize_memory_equalities(&facts);
            let required = ResourceFact::own_memory(range(c(0), c(32)).with_typed_carrier());
            let mut queries = Vec::new();
            for _ in 0..3 {
                let (((answer, consumed), work), maps) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| {
                            (
                                context.satisfies_fact(&required, &facts),
                                context
                                    .clone()
                                    .without_fact_incrementally(&required, &facts),
                            )
                        })
                    });
                assert_eq!(answer, case == "joined", "{case}/{count}");
                assert_eq!(consumed.is_some(), answer, "{case}/{count}");
                if let Some(rest) = consumed {
                    assert_eq!(rest.facts().len(), count as usize);
                    assert!(
                        rest.contains_exact_representation(&ResourceFact::own_memory(range(
                            c(64),
                            c(65)
                        )))
                    );
                }
                assert!(context.contains_exact_representation(&first));
                assert!(context.contains_exact_representation(&second));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("symbolic partition {case}: {samples:?}");
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "{case}: {samples:?}"
        );
    }
}

#[test]
fn symbolic_fold_consumption_ignores_unselected_fragments() {
    let mut curves = Vec::new();
    for case in ["gap", "owner", "joined"] {
        let complete = case != "gap";
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let (instance, mut definition, _) = instance_memory_fixture();
            let endpoint = MachineTerm::Variable(Variable(989_980));
            let bound =
                |n| ProgramExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(n)));
            definition.contains = vec![ResourceSpec::owned_memory(MemorySegment {
                base: crate::kernel::program_expression::variable("p"),
                start: bound(0),
                end: ProgramExpression::Value(ProgramValue::UInt64(endpoint.clone())),
                element_width: 4,
                guard: None,
                uninitialized: false,
                value_runs: Default::default(),
            })];
            let ProgramValue::Pointer(value) = instance.arguments()[0].as_program_value().unwrap()
            else {
                unreachable!()
            };
            let piece = |start: u64, end: MachineTerm| {
                ResourceFact::own_memory(MemoryRange::new_wide(
                    value.pointer().clone(),
                    MachineTerm::uint64_constant(start),
                    end,
                    4,
                ))
            };
            let facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::uint64_less_than(
                        MachineTerm::uint64_constant(2),
                        endpoint.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::uint64_less_than(
                        endpoint.clone(),
                        MachineTerm::uint64_constant(1024),
                    ),
                    true,
                );
            let first = piece(
                0,
                match case {
                    "owner" => endpoint.clone(),
                    _ => MachineTerm::uint64_constant(1),
                },
            );
            let mut resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(first.clone());
            if case == "joined" {
                resources = resources.unchecked_with_fact(piece(1, endpoint.clone()));
            }
            for index in 0..count {
                let start = 2048 + 2 * u64::from(index);
                resources = resources
                    .unchecked_with_fact(piece(start, MachineTerm::uint64_constant(start + 1)));
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new().with_resource_context(resources);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((result, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        rewrite_resource_instance(&state, &instance, &definition, &facts, false)
                    })
                });
                assert_eq!(result.is_ok(), complete, "{complete}/{count}: {result:?}");
                assert_eq!(
                    state.resources().facts().len(),
                    count as usize + 1 + usize::from(case == "joined")
                );
                assert!(state.resources().contains_exact_representation(&first));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("symbolic fold case={case}, count/work/maps: {samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "symbolic fold scans rejected fragments: {samples:?}"
        );
    }
}

#[test]
fn symbolic_offset_fold_stops_at_first_gap() {
    let mut curves = Vec::new();
    for case in ["gap", "owner", "joined"] {
        let complete = case != "gap";
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let (instance, mut definition, _) = instance_memory_fixture();
            let endpoint = MachineTerm::Variable(Variable(989_980));
            let shifted =
                |n| MachineTerm::uint64_add(endpoint.clone(), MachineTerm::uint64_constant(n));
            let bound = |n| ProgramExpression::Value(ProgramValue::UInt64(shifted(n)));
            definition.contains = vec![ResourceSpec::owned_memory(MemorySegment {
                base: crate::kernel::program_expression::variable("p"),
                start: bound(0),
                end: bound(1024),
                element_width: 4,
                guard: None,
                uninitialized: false,
                value_runs: Default::default(),
            })];
            let ProgramValue::Pointer(value) = instance.arguments()[0].as_program_value().unwrap()
            else {
                unreachable!()
            };
            let piece = |start: u64, end: u64| {
                ResourceFact::own_memory(MemoryRange::new_wide(
                    value.pointer().clone(),
                    shifted(start),
                    shifted(end),
                    4,
                ))
            };
            let facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::uint64_less_than(
                        MachineTerm::uint64_constant(2),
                        endpoint.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::uint64_less_than(
                        endpoint.clone(),
                        MachineTerm::uint64_constant(1024),
                    ),
                    true,
                );
            let first = piece(
                0,
                match case {
                    "owner" => 1024,
                    "joined" => 512,
                    _ => 1,
                },
            );
            let mut resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(first.clone());
            if case == "joined" {
                resources = resources.unchecked_with_fact(piece(512, 1024));
            }
            for index in 0..count {
                let start = if complete { 2048 } else { 100 } + 2 * u64::from(index);
                resources = resources.unchecked_with_fact(piece(start, start + 1));
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new().with_resource_context(resources);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((result, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        rewrite_resource_instance(&state, &instance, &definition, &facts, false)
                    })
                });
                assert_eq!(result.is_ok(), complete, "{complete}/{count}: {result:?}");
                assert_eq!(
                    state.resources().facts().len(),
                    count as usize + 1 + usize::from(case == "joined")
                );
                assert!(state.resources().contains_exact_representation(&first));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("symbolic offset fold case={case}, count/work/maps: {samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "symbolic offset fold scans rejected fragments: {samples:?}"
        );
    }
}

#[test]
fn symbolic_fold_does_not_scan_incident_order_bounds() {
    let mut curves = Vec::new();
    for case in ["gap", "owner", "joined", "rebased"] {
        let complete = case != "gap";
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let (instance, mut definition, _) = instance_memory_fixture();
            let endpoint = MachineTerm::Variable(Variable(989_980));
            let shifted = |n| MachineTerm::add(endpoint.clone(), MachineTerm::constant(n));
            let bound = |n| ProgramExpression::Value(ProgramValue::Int32(shifted(n)));
            definition.contains = vec![ResourceSpec::owned_memory(MemorySegment {
                base: crate::kernel::program_expression::variable("p"),
                start: bound(0),
                end: bound(1024),
                element_width: 4,
                guard: None,
                uninitialized: false,
                value_runs: Default::default(),
            })];
            let ProgramValue::Pointer(value) = instance.arguments()[0].as_program_value().unwrap()
            else {
                unreachable!()
            };
            let piece = |start: u32, end: u32| {
                ResourceFact::own_memory(MemoryRange::new(
                    value.pointer().clone(),
                    shifted(start),
                    shifted(end),
                ))
            };
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_less_than(MachineTerm::constant(2), endpoint.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(endpoint.clone(), MachineTerm::constant(1024)),
                    true,
                );
            let first = piece(
                0,
                match case {
                    "owner" => 1024,
                    "joined" => 512,
                    _ => 1,
                },
            );
            let first = if case == "rebased" {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    value.pointer().offset_by_elements(endpoint.clone(), 4),
                    0u32.into(),
                    1u32.into(),
                    4,
                ))
            } else {
                first
            };
            let mut resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(first.clone());
            if case == "joined" || case == "rebased" {
                resources = resources
                    .unchecked_with_fact(piece(if case == "joined" { 512 } else { 1 }, 1024));
            }
            for index in 0..count {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(990_000 + u64::from(index))),
                        endpoint.clone(),
                    ),
                    true,
                );
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new().with_resource_context(resources);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((result, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        rewrite_resource_instance(&state, &instance, &definition, &facts, false)
                    })
                });
                assert_eq!(result.is_ok(), complete, "{complete}/{count}: {result:?}");
                assert_eq!(
                    state.resources().facts().len(),
                    1 + usize::from(case == "joined" || case == "rebased")
                );
                assert!(state.resources().contains_exact_representation(&first));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!("symbolic incident-bound fold case={case}, count/work/maps: {samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "symbolic incident-bound fold scans rejected fragments: {samples:?}"
        );
    }
}

#[test]
fn symbolic_consumption_scales_with_selected_pieces() {
    let mut samples = Vec::new();
    for count in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let index = MachineTerm::Variable(Variable(989_981));
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_than(0u32.into(), index.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(index.clone(), 1024u32.into()),
                true,
            );
        let p = Pointer::symbolic(Variable(989_971));
        let own = |start: u32, end: u32| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                p.clone(),
                MachineTerm::add(index.clone(), start.into()),
                MachineTerm::add(index.clone(), end.into()),
                4,
            ))
        };
        let mut context = ResourceContext::new_with_equalities(&facts);
        for i in 0..count {
            context = context.unchecked_with_fact(own(i, i + 1));
        }
        context.synchronize_memory_equalities(&facts);
        let required = own(0, count);
        let mut queries = Vec::new();
        for _ in 0..3 {
            let ((answer, work), maps) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .clone()
                        .without_fact_incrementally(&required, &facts)
                })
            });
            assert!(answer.is_some(), "count={count}");
            assert_eq!(answer.unwrap().facts().len(), 0);
            assert_eq!(context.facts().len(), count as usize);
            assert!(context.contains_exact_representation(&own(0, 1)));
            assert!(context.contains_exact_representation(&own(count - 1, count)));
            queries.push((work, maps));
        }
        samples.push((count, queries));
    }
    eprintln!("symbolic selected pieces, count/work/maps: {samples:?}");
    assert!(
        samples[3]
            .1
            .iter()
            .zip(&samples[0].1)
            .all(|(big, small)| big.0 <= small.0 * 96 + 256 && big.1 <= small.1 * 192 + 1024),
        "{samples:?}"
    );
}

#[test]
fn symbolic_ownership_query_does_not_scan_incident_order_bounds() {
    let mut curves = Vec::new();
    for case in ["gap", "owner", "joined", "rebased"] {
        let complete = case != "gap";
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let endpoint = MachineTerm::Variable(Variable(989_980));
            let shifted = |n| MachineTerm::add(endpoint.clone(), MachineTerm::constant(n));
            let base = Pointer::symbolic(Variable(991_000));
            let piece = |start: u32, end: u32| {
                ResourceFact::own_memory(MemoryRange::new(
                    base.clone(),
                    shifted(start),
                    shifted(end),
                ))
            };
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_less_than(MachineTerm::constant(2), endpoint.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(endpoint.clone(), MachineTerm::constant(1024)),
                    true,
                );
            let first = piece(
                0,
                match case {
                    "owner" => 1024,
                    "joined" => 512,
                    _ => 1,
                },
            );
            let first = if case == "rebased" {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base.offset_by_elements(endpoint.clone(), 4),
                    0u32.into(),
                    1u32.into(),
                    4,
                ))
            } else {
                first
            };
            let mut resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(first.clone());
            if case == "joined" || case == "rebased" {
                resources = resources
                    .unchecked_with_fact(piece(if case == "joined" { 512 } else { 1 }, 1024));
            }
            for index in 0..count {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(990_000 + u64::from(index))),
                        endpoint.clone(),
                    ),
                    true,
                );
            }
            resources.synchronize_memory_equalities(&facts);
            let required = piece(0, 1024);
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((result, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        resources.satisfies_fact(&required, &facts)
                    })
                });
                assert_eq!(result, complete, "{complete}/{count}: {result:?}");
                assert_eq!(
                    resources.facts().len(),
                    1 + usize::from(case == "joined" || case == "rebased")
                );
                assert!(resources.contains_exact_representation(&first));
                queries.push((work, maps));
            }
            samples.push((count, queries));
        }
        eprintln!(
            "symbolic incident-bound ownership query case={case}, count/work/maps: {samples:?}"
        );
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.0 <= small.0 + 64 && big.1 <= small.1 * 3 + 512),
            "symbolic incident-bound ownership query scans rejected fragments: {samples:?}"
        );
    }
}

#[test]
fn symbolic_ownership_query_scales_with_selected_pieces() {
    let mut samples = Vec::new();
    for count in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let index = MachineTerm::Variable(Variable(989_981));
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_than(0u32.into(), index.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(index.clone(), 1024u32.into()),
                true,
            );
        let p = Pointer::symbolic(Variable(989_971));
        let own = |start: u32, end: u32| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                p.clone(),
                MachineTerm::add(index.clone(), start.into()),
                MachineTerm::add(index.clone(), end.into()),
                4,
            ))
        };
        let mut context = ResourceContext::new_with_equalities(&facts);
        for i in 0..count {
            context = context.unchecked_with_fact(own(i, i + 1));
        }
        context.synchronize_memory_equalities(&facts);
        let required = own(0, count);
        let mut queries = Vec::new();
        for _ in 0..3 {
            let ((answer, work), maps) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    context.satisfies_fact(&required, &facts)
                })
            });
            assert!(answer, "count={count}");
            assert_eq!(context.facts().len(), count as usize);
            assert!(context.contains_exact_representation(&own(0, 1)));
            assert!(context.contains_exact_representation(&own(count - 1, count)));
            queries.push((work, maps));
        }
        samples.push((count, queries));
    }
    eprintln!("symbolic ownership selected pieces, count/work/maps: {samples:?}");
    assert!(
        samples[3]
            .1
            .iter()
            .zip(&samples[0].1)
            .all(|(big, small)| big.0 <= small.0 * 96 + 256 && big.1 <= small.1 * 192 + 1024),
        "{samples:?}"
    );
}

/// Measure the selected exchange separately from the still-unmigrated raw
/// insertion and the rest of the complete kernel unfold.
fn instance_unfold_alias_work() -> Vec<[(usize, usize, usize, usize); 3]> {
    let mut curves = Vec::new();
    for overlap in [false, true] {
        let samples = [4_u64, 16, 64].map(|size| {
            let _session = crate::kernel::VerificationSession::enter();
            let (instance, definition, state) = instance_memory_fixture();
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(100)), 4),
            };
            let neighbor = Pointer::symbolic(Variable(9_810_000));
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::pointer_equal(
                        pointer.clone(),
                        Pointer::symbolic(Variable(9_810_000 + index)),
                    ),
                    true,
                );
            }
            let start = if overlap { 0u32 } else { 1u32 };
            let retained = ResourceFact::own_memory(MemoryRange::new(
                neighbor,
                start.into(),
                (start + 1).into(),
            ));
            let resources = state
                .resources()
                .clone()
                .unchecked_with_fact(retained.clone());
            resources.synchronize_memory_equalities(&assumptions);
            let state = state.with_resource_context(resources);
            let introduced = ResourceFact::own_memory(MemoryRange::new(
                pointer.clone(),
                0u32.into(),
                1u32.into(),
            ));
            let (replacement, replacement_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    state.resources().clone().unfold_instance_body(
                        &instance,
                        [introduced.clone()],
                        &assumptions,
                    )
                });
            let replacement = replacement
                .expect("exclusive identities are distinct")
                .expect("the selected parent is owned");
            assert!(replacement.owned_instance(instance.identity()).is_none());
            assert!(replacement.contains_exact_representation(&introduced));
            assert!(replacement.contains_exact_representation(&retained));
            let (result, unfold_work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite_resource_instance(&state, &instance, &definition, &assumptions, true)
            });
            assert!(result.is_ok(), "size={size}, overlap={overlap}: {result:?}");
            let (_, facts) = result.unwrap();
            // Keep the caller's stated index cold. Measure normal publication
            // and exact reinsertion too, so removing a producer-side lookup
            // cannot merely move its ambient work into fact admission.
            let ((published, repeated), publication_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let publish = |context: PureFactContext| {
                        facts
                            .iter()
                            .cloned()
                            .fold(context, PureFactContext::assume_proposition)
                    };
                    let published = publish(assumptions.clone());
                    let repeated = publish(published.clone());
                    (published, repeated)
                });
            assert_eq!(published.fact_counts(), repeated.fact_counts());
            for fact in &facts {
                assert!(published.contains_assumed_exact(fact));
                assert!(repeated.contains_assumed_exact(fact));
            }
            assert!(
                state
                    .resources()
                    .owned_instance(instance.identity())
                    .is_some()
            );
            assert_eq!(
                state.resources().facts().len(),
                2,
                "persistent parent is unchanged"
            );

            // Raw ownership admission still searches candidates. Measure that
            // separate operation as a control, not as part of unfold.
            let context =
                ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(retained);
            context.synchronize_memory_equalities(&assumptions);
            let introduced =
                ResourceFact::own_memory(MemoryRange::new(pointer, 0u32.into(), 1u32.into()));
            let (result, insertion_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .clone()
                        .try_compose_into_valid_context_delaying_normalization(
                            [introduced],
                            &assumptions,
                        )
                });
            assert_eq!(result.is_ok(), !overlap);
            assert_eq!(context.facts().len(), 1);
            (
                unfold_work,
                insertion_work,
                replacement_work,
                publication_work,
            )
        });
        eprintln!(
            "overlap={overlap}, aliases=[4,16,64], (unfold,raw insertion,replacement,publication twice)={samples:?}"
        );
        curves.push(samples);
    }
    curves
}

#[test]
fn instance_unfold_ignores_ambient_pointer_aliases() {
    for samples in instance_unfold_alias_work() {
        assert!(
            samples.iter().all(|sample| {
                sample.0 <= samples[0].0 + 16
                    && sample.2 <= samples[0].2 + 16
                    && sample.3 <= samples[0].3 + 16
            }),
            "unfold or fact publication walks aliases: {samples:?}"
        );
    }
}

#[test]
#[ignore = "red diagnostic: raw ownership admission still grows"]
fn raw_ownership_admission_must_not_search_ambient_pointer_aliases() {
    for samples in instance_unfold_alias_work() {
        assert!(
            samples.iter().all(|sample| sample.1 <= samples[0].1 + 32),
            "remaining raw-admission work: {samples:?}"
        );
    }
}
