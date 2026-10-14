use super::*;
use crate::kernel::VerificationSession;

fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}

fn eq(left: &Bitvector32Term, right: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::equal(left.clone(), right.clone())
}

fn unsigned_composition(value: Bitvector32Term) -> Bitvector32Term {
    Bitvector32Term::BitwiseXor(
        Box::new(Bitvector32Term::UnsignedRemainder(
            Box::new(value.clone()),
            Box::new(var(90_001)),
        )),
        Box::new(Bitvector32Term::UnsignedDivide(
            Box::new(value),
            Box::new(var(90_002)),
        )),
    )
}

#[test]
fn unsigned_congruence_propagates_late_aliases_without_injectivity_or_signed_coercion() {
    let (a, b) = (var(90_003), var(90_004));
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let parent = graph.clone();
    graph.add_int32_equality(&a, &b);
    assert!(graph.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let sibling = parent;
    assert!(!sibling.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let unsigned = Bitvector32Term::UnsignedRemainder(Box::new(a.clone()), Box::new(var(90_001)));
    let signed = Bitvector32Term::Remainder(Box::new(b.clone()), Box::new(var(90_001)));
    let quotient = Bitvector32Term::UnsignedDivide(Box::new(b.clone()), Box::new(var(90_001)));
    assert!(!graph.are_int32_equal(&unsigned, &signed));
    assert!(!graph.are_int32_equal(&unsigned, &quotient));
    let mut results_only = EqualityGraph::default();
    results_only.add_int32_equality(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone()),
    );
    assert!(!results_only.are_int32_equal(&a, &b));
    let undefined =
        Bitvector32Term::UnsignedDivide(Box::new(a), Box::new(Bitvector32Term::Constant(0)));
    assert!(!graph.are_int32_equal(&undefined, &Bitvector32Term::Constant(0)));
}

#[test]
fn unsigned_congruence_withdraws_with_its_operand_fact() {
    let (a, b) = (var(90_010), var(90_011));
    let fact = Proposition::ConditionIs(eq(&a, &b), true);
    let context = PureFactContext::new().assume_proposition(fact.clone());
    assert!(context.equality_graph.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let withdrawn = context.without_exact_fact(&fact);
    assert!(
        !withdrawn
            .equality_graph
            .are_int32_equal(&unsigned_composition(a), &unsigned_composition(b))
    );
}

#[test]
fn unsigned_congruence_keeps_load_snapshots_and_widths_distinct() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("unsigned", 4));
    let pointer = Pointer {
        block: "unsigned".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let after = intern_c_memory(before.memory().clone().store(
        pointer.clone(),
        CValue::UInt32(Bitvector32Term::Constant(9)),
    ));
    let load = |memory, kind| Bitvector32Term::MemoryLoad(memory, Box::new(pointer.clone()), kind);
    let old = load(before.clone(), LoadKind::Bits32);
    let value = var(90_012);
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&old, &value);
    assert!(graph.are_int32_equal(
        &unsigned_composition(old),
        &unsigned_composition(value.clone())
    ));
    assert!(!graph.are_int32_equal(
        &unsigned_composition(load(after, LoadKind::Bits32)),
        &unsigned_composition(value.clone())
    ));
    assert!(!graph.are_int32_equal(
        &unsigned_composition(load(before, LoadKind::UInt16)),
        &unsigned_composition(value)
    ));
}

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
fn int32_equality_is_transitive_symmetric_and_branch_local() {
    let (a, b, c) = (var(1), var(2), var(3));
    let mut parent = EqualityGraph::default();
    parent.add_int32_equality(&a, &b);
    let sibling = parent.clone();
    let mut branch = parent.clone();
    assert!(!branch.are_int32_equal(&a, &c));
    branch.add_int32_equality(&b, &c);
    assert!(branch.are_int32_equal(&c, &a));
    assert!(branch.are_int32_equal(&a, &a));
    assert!(!parent.are_int32_equal(&a, &c));
    assert!(!sibling.are_int32_equal(&a, &c));
    assert!(!branch.add_int32_equality(&c, &a));
}

#[test]
fn shallow_scalar_decision_uses_graph_congruence_and_keeps_branch_scope() {
    let (a, b) = (var(1), var(2));
    let plus_one =
        |value| Bitvector32Term::Add(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert_eq!(
        branch.decide_bitvector_equality_shallow(&plus_one(a.clone()), &plus_one(b.clone())),
        Some(true)
    );
    assert_eq!(
        branch.decide(&eq(&plus_one(a.clone()), &plus_one(b.clone()))),
        Some(true)
    );
    assert_ne!(
        parent.decide_bitvector_equality_shallow(&plus_one(a.clone()), &plus_one(b.clone())),
        Some(true)
    );
    assert_ne!(
        parent.decide(&eq(&plus_one(a.clone()), &plus_one(b.clone()))),
        Some(true)
    );
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert_ne!(
        withdrawn.decide_bitvector_equality_shallow(&plus_one(a), &plus_one(b)),
        Some(true)
    );
}

#[test]
fn fact_transport_uses_graph_int32_congruence_without_the_legacy_index() {
    let (a, b, limit) = (var(1), var(2), var(3));
    let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    let source = ConditionTerm::signed_less_than(sum(a.clone()), limit.clone());
    let target = ConditionTerm::signed_less_than(sum(b.clone()), limit);
    let premise = eq(&a, &b);
    let parent = PureFactContext::new().assume_condition(source.clone(), true);
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.condition_matches(&source, &target));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!parent.condition_matches(&source, &target));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(!withdrawn.condition_matches(&source, &target));
}

#[test]
fn fact_transport_uses_registered_load_congruence_only_in_one_snapshot() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("int32", 16));
    let pointer = |index| Pointer {
        block: "int32".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(11), var(12));
    let after = intern_c_memory(before.memory().clone().store(
        pointer(b.clone()),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let left = load(&before, a.clone());
    let right = load(&before, b.clone());
    let later = load(&after, b.clone());
    let fact = ConditionTerm::signed_less_than(left, Bitvector32Term::Constant(20));
    let target = ConditionTerm::signed_less_than(right, Bitvector32Term::Constant(20));
    let later_target = ConditionTerm::signed_less_than(later, Bitvector32Term::Constant(20));
    let context = PureFactContext::new().assume_condition(eq(&a, &b), true);
    assert!(context.condition_matches(&fact, &target));
    assert!(!context.condition_matches(&fact, &later_target));
}

#[test]
fn fact_transport_graph_queries_scale_without_building_the_legacy_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
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
fn resolved_four_byte_load_uses_graph_value_equality_but_keeps_snapshot_scope() {
    let _session = VerificationSession::enter();
    let pointer = Pointer {
        block: "resolved-int32".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let (a, b) = (var(31), var(32));
    let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    let before = intern_c_memory(
        CMemory::new()
            .with_block("resolved-int32", 4)
            .store(pointer.clone(), CValue::Int32(sum(a.clone()))),
    );
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let byte_memory = intern_c_memory(
        CMemory::new()
            .with_block("resolved-int32", 1)
            .store(pointer.clone(), CValue::UInt8(sum(a.clone()))),
    );
    let load = |memory: &SharedCMemory| {
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer,
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let old_load = load(&before);
    let new_load = load(&after);
    let byte_load = Bitvector32Term::Variable(load_variable_for_cell_with_origin(
        &byte_memory,
        &pointer,
        crate::kernel::LoadKind::UInt8,
        1,
        &byte_memory,
    ));
    let target = sum(b.clone());
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert_eq!(
        branch.resolve_memory_load_term(&old_load),
        Some(sum(a.clone()))
    );
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.memory_loads_proven_equal(&old_load, &target));
    assert!(branch.memory_loads_proven_equal(&target, &old_load));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!branch.memory_loads_proven_equal(&new_load, &target));
    assert_eq!(branch.resolve_memory_load_term(&byte_load), Some(sum(a)));
    assert!(!branch.memory_loads_proven_equal(&byte_load, &target));
    assert!(!parent.memory_loads_proven_equal(&old_load, &target));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(!withdrawn.memory_loads_proven_equal(&old_load, &target));
}

#[test]
fn resolved_four_byte_load_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "resolved-int32-scale".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let memory = intern_c_memory(
            CMemory::new()
                .with_block("resolved-int32-scale", 4)
                .store(pointer.clone(), CValue::Int32(sum(var(0)))),
        );
        let load = Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Bits32,
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
fn two_resolved_four_byte_loads_compare_values_with_snapshot_scope() {
    let _session = VerificationSession::enter();
    let pointer = |offset| Pointer {
        block: "two-resolved-int32".into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let (a, b) = (var(41), var(42));
    let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    let left_pointer = pointer(0);
    let right_pointer = pointer(4);
    let before = intern_c_memory(
        CMemory::new()
            .with_block("two-resolved-int32", 8)
            .store(left_pointer.clone(), CValue::Int32(sum(a.clone())))
            .store(right_pointer.clone(), CValue::Int32(sum(b.clone()))),
    );
    let after = intern_c_memory(before.memory().clone().store(
        right_pointer.clone(),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let byte_memory = intern_c_memory(
        CMemory::new()
            .with_block("two-resolved-int32", 8)
            .store(right_pointer.clone(), CValue::UInt8(sum(b.clone()))),
    );
    let load = |memory: &SharedCMemory, pointer: &Pointer, width| {
        let kind = if width == 1 {
            crate::kernel::LoadKind::UInt8
        } else {
            crate::kernel::LoadKind::Bits32
        };
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory, pointer, kind, width, memory,
        ))
    };
    let left = load(&before, &left_pointer, 4);
    let right = load(&before, &right_pointer, 4);
    let overwritten = load(&after, &right_pointer, 4);
    let byte_load = load(&byte_memory, &right_pointer, 1);
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert_eq!(branch.resolve_memory_load_term(&left), Some(sum(a)));
    assert_eq!(branch.resolve_memory_load_term(&right), Some(sum(b)));
    assert!(branch.resolve_memory_load_term(&byte_load).is_some());
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.memory_loads_proven_equal(&left, &right));
    assert!(branch.memory_loads_proven_equal(&right, &left));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!branch.memory_loads_proven_equal(&left, &overwritten));
    assert!(!branch.memory_loads_proven_equal(&left, &byte_load));
    assert!(!parent.memory_loads_proven_equal(&left, &right));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(!withdrawn.memory_loads_proven_equal(&left, &right));
}

#[test]
fn two_resolved_four_byte_load_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let pointer = |offset| Pointer {
            block: "two-resolved-int32-scale".into(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let memory = intern_c_memory(
            CMemory::new()
                .with_block("two-resolved-int32-scale", 8)
                .store(pointer(0), CValue::Int32(sum(var(0))))
                .store(pointer(4), CValue::Int32(sum(var(size)))),
        );
        let load = |offset| {
            Bitvector32Term::Variable(load_variable_for_cell_with_origin(
                &memory,
                &pointer(offset),
                crate::kernel::LoadKind::Bits32,
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
fn direct_composite_int32_argument_uses_graph_with_snapshot_scope() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("resource-value", 8));
    let pointer = |index| Pointer {
        block: "resource-value".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(51), var(52));
    let after = intern_c_memory(before.memory().clone().store(
        pointer(b.clone()),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let resource = |value| CResource::Composite {
        name: "indexed-value".into(),
        arguments: vec![CValue::Int32(value).into()].into(),
    };
    let left = resource(load(&before, a.clone()));
    let right = resource(load(&before, b.clone()));
    let later = resource(load(&after, b.clone()));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(crate::kernel::memory_provenance::c_resources_directly_match(&left, &right, &branch,));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!crate::kernel::memory_provenance::c_resources_directly_match(&left, &later, &branch,));
    assert!(!crate::kernel::memory_provenance::c_resources_directly_match(&left, &right, &parent,));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(
        !crate::kernel::memory_provenance::c_resources_directly_match(&left, &right, &withdrawn,)
    );
}

#[test]
fn direct_composite_int32_argument_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let resource = |value| CResource::Composite {
            name: "indexed-value-scale".into(),
            arguments: vec![CValue::Int32(sum(value)).into()].into(),
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
                assert!(
                    crate::kernel::memory_provenance::c_resources_directly_match(
                        &left,
                        &resource(var(index)),
                        &context,
                    )
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 250 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn resource_instance_int32_field_uses_graph_with_snapshot_scope() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("instance-value", 8));
    let pointer = |index| Pointer {
        block: "instance-value".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(61), var(62));
    let after = intern_c_memory(before.memory().clone().store(
        pointer(b.clone()),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let schema =
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let instance = |value| {
        CResource::Instance(
            ResourceInstance::new(
                Variable(6100),
                "instance-value".into(),
                vec![CValue::Int32(Bitvector32Term::Constant(3)).into()].into(),
                schema.clone(),
                vec![CValue::Int32(value).into()].into(),
            )
            .unwrap(),
        )
    };
    let left = instance(load(&before, a.clone()));
    let right = instance(load(&before, b.clone()));
    let later = instance(load(&after, b.clone()));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(crate::kernel::memory_provenance::c_resources_directly_match(&left, &right, &branch,));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!crate::kernel::memory_provenance::c_resources_directly_match(&left, &later, &branch,));
    assert!(!crate::kernel::memory_provenance::c_resources_directly_match(&left, &right, &parent,));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(
        !crate::kernel::memory_provenance::c_resources_directly_match(&left, &right, &withdrawn,)
    );
}

#[test]
fn resource_instance_int32_argument_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let schema =
            ResourceFieldSchema::new(vec![("stamp".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let instance = |value| {
            CResource::Instance(
                ResourceInstance::new(
                    Variable(6200),
                    "instance-value-scale".into(),
                    vec![CValue::Int32(sum(value)).into()].into(),
                    schema.clone(),
                    vec![CValue::Int32(Bitvector32Term::Constant(3)).into()].into(),
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
                assert!(
                    crate::kernel::memory_provenance::c_resources_directly_match(
                        &left,
                        &instance(var(index)),
                        &context,
                    )
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn typed_int32_value_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let left = CValue::Int32(sum(var(0)));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right = CValue::Int32(sum(var(index)));
                assert!(crate::kernel::reasoning::memory_resolution::c_values_proven_equal_for_memory_resolution(
                    &left, &right, &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn certification_uses_graph_int32_equality_with_snapshot_scope() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("certified-int32", 8));
    let pointer = |index| Pointer {
        block: "certified-int32".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(81), var(82));
    let after = intern_c_memory(before.memory().clone().store(
        pointer(b.clone()),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    let left = sum(load(&before, a.clone()));
    let right = sum(load(&before, b.clone()));
    let later = sum(load(&after, b.clone()));
    let goal = |right| Proposition::ConditionIs(eq(&left, &right), true);
    let certifies = |context: &PureFactContext, goal: &Proposition| {
        crate::kernel::PureFactContext::settles_exactly(context, goal)
    };
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(certifies(&branch, &goal(right.clone())));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!certifies(&branch, &goal(later)));
    assert!(!certifies(&parent, &goal(right.clone())));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(!certifies(&withdrawn, &goal(right)));
}

#[test]
fn certified_int32_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
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
fn reordered_sum_matches_graph_equal_load_addends_in_one_snapshot() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("int32", 16));
    let pointer = |index| Pointer {
        block: "int32".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedCMemory, index| {
        Bitvector32Term::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Bits32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(21), var(22));
    let after = intern_c_memory(before.memory().clone().store(
        pointer(b.clone()),
        CValue::Int32(Bitvector32Term::Constant(9)),
    ));
    let sum = |value, other| Bitvector32Term::add(value, other);
    let fixed = var(23);
    let left = sum(load(&before, a.clone()), fixed.clone());
    let right = sum(fixed.clone(), load(&before, b.clone()));
    let later = sum(fixed, load(&after, b.clone()));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert!(!branch.equality_graph.are_int32_equal(&left, &right));
    assert!(branch.bitvector_add_terms_proven_equal(&left, &right));
    assert_eq!(branch.decide(&eq(&left, &right)), Some(true));
    assert!(!branch.bitvector_add_terms_proven_equal(&left, &later));
    assert!(!parent.bitvector_add_terms_proven_equal(&left, &right));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
    assert!(!withdrawn.bitvector_add_terms_proven_equal(&left, &right));
}

#[test]
fn graph_equal_addend_matching_scales_without_the_legacy_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(eq(&var(index), &var(index + 1)), true);
        }
        let fixed = var(size + 2);
        let last = var(size + 3);
        let left = Bitvector32Term::add(Bitvector32Term::add(var(0), fixed.clone()), last.clone());
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right = Bitvector32Term::add(
                    var(index),
                    Bitvector32Term::add(fixed.clone(), last.clone()),
                );
                assert!(context.bitvector_add_terms_proven_equal(&left, &right));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn int32_classes_are_typed_and_only_supported_operators_have_congruence() {
    let (a, b) = (var(1), var(2));
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&a, &b);
    assert!(!graph.are_offsets_equal(
        &PointerOffsetTerm::Variable(Variable(1)),
        &PointerOffsetTerm::Variable(Variable(2)),
    ));
    assert!(!graph.are_equal(
        &Pointer::symbolic(Variable(1)),
        &Pointer::symbolic(Variable(2))
    ));
    assert!(graph.are_offsets_equal(
        &PointerOffsetTerm::scale_int32(a.clone(), 4),
        &PointerOffsetTerm::scale_int32(b.clone(), 4),
    ));
    let plus_one =
        |value| Bitvector32Term::Add(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
    assert!(graph.are_int32_equal(&plus_one(a.clone()), &plus_one(b.clone())));
    let minus_one =
        |value| Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
    assert!(!graph.are_int32_equal(&minus_one(a), &minus_one(b)));
    graph.add_offset_equality(
        &PointerOffsetTerm::Variable(Variable(3)),
        &PointerOffsetTerm::Variable(Variable(4)),
    );
    assert!(!graph.are_int32_equal(&var(3), &var(4)));
    assert!(!graph.are_int32_equal(&Bitvector32Term::Constant(0), &Bitvector32Term::Constant(1)));
}

#[test]
fn int32_withdrawal_restriction_and_replacement_keep_only_supported_edges() {
    let (a, b, c) = (var(10), var(11), var(12));
    let ab = eq(&a, &b);
    let bc = eq(&b, &c);
    let offset = |i| PointerOffsetTerm::Variable(Variable(i));
    let pq = ConditionTerm::pointer_equal(
        Pointer::symbolic(Variable(20)),
        Pointer::symbolic(Variable(21)),
    );
    let xy = ConditionTerm::pointer_offset_equal(offset(30), offset(31));
    let context = PureFactContext::new()
        .assume_condition(ab.clone(), true)
        .assume_condition(bc.clone(), true)
        .assume_condition(pq.clone(), true)
        .assume_condition(xy.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let weakened = context.without_exact_fact(&Proposition::ConditionIs(bc.clone(), true));
    assert!(!weakened.equality_graph.are_int32_equal(&a, &c));
    assert!(weakened.equality_graph.are_int32_equal(&a, &b));
    assert!(
        weakened
            .equality_graph
            .are_offsets_equal(&offset(30), &offset(31))
    );
    assert!(weakened.equality_graph.are_equal(
        &Pointer::symbolic(Variable(20)),
        &Pointer::symbolic(Variable(21))
    ));
    for fact in [pq, xy] {
        let weakened = context.without_exact_fact(&Proposition::ConditionIs(fact, true));
        assert!(weakened.equality_graph.are_int32_equal(&a, &c));
    }
    let restricted = context.restricted_to_facts(&[(ab, true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&a, &b));
    assert!(!restricted.equality_graph.are_int32_equal(&a, &c));
    let replaced = context.clone().assume_condition(bc, false);
    assert!(!replaced.equality_graph.are_int32_equal(&a, &c));
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let reversed = context.clone().assume_condition(eq(&b, &a), true);
    let once = reversed.without_exact_fact(&Proposition::ConditionIs(eq(&a, &b), true));
    assert!(once.equality_graph.are_int32_equal(&a, &c));
    let twice = once.without_exact_fact(&Proposition::ConditionIs(eq(&b, &a), true));
    assert!(!twice.equality_graph.are_int32_equal(&a, &c));
}

#[test]
fn int32_load_identity_keeps_snapshots_and_exact_support_separate() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("int32", 8));
    let pointer = Pointer::symbolic(Variable(40));
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let load = |memory: &SharedCMemory| {
        Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let named = Bitvector32Term::Variable(load_variable_for_cell_with_origin(
        &before,
        &pointer,
        crate::kernel::LoadKind::Bits32,
        4,
        &before,
    ));
    let a = var(41);
    let context = PureFactContext::new()
        .assume_condition(eq(&load(&before), &a), true)
        .assume_condition(eq(&named, &a), true);
    assert!(context.equality_graph.are_int32_equal(&load(&before), &a));
    assert!(!context.equality_graph.are_int32_equal(&load(&after), &a));
    let scale = |value| PointerOffsetTerm::scale_int32(value, 4);
    assert!(
        context
            .equality_graph
            .are_offsets_equal(&scale(load(&before)), &scale(a.clone()))
    );
    assert!(
        !context
            .equality_graph
            .are_offsets_equal(&scale(load(&after)), &scale(a.clone()))
    );
    let sum = |value| Bitvector32Term::Add(Box::new(value), Box::new(var(42)));
    assert!(
        context
            .equality_graph
            .are_int32_equal(&sum(load(&before)), &sum(a.clone()))
    );
    assert!(
        !context
            .equality_graph
            .are_int32_equal(&sum(load(&after)), &sum(a.clone()))
    );
    let once = context.without_exact_fact(&Proposition::ConditionIs(eq(&load(&before), &a), true));
    assert!(once.equality_graph.are_int32_equal(&named, &a));
    let twice = once.without_exact_fact(&Proposition::ConditionIs(eq(&named, &a), true));
    assert!(!twice.equality_graph.are_int32_equal(&load(&before), &a));
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
fn scalar_support_tracking_does_not_compare_unrelated_snapshot_contents_across_arenas() {
    fn sample(size: usize) -> (PureFactContext, usize) {
        std::thread::spawn(move || {
            let _session = VerificationSession::enter();
            let address = Pointer {
                block: "selected".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let mut memory = CMemory::new().with_block("selected", 4);
            for i in 0..size {
                memory = memory.with_block(format!("unrelated-{i}"), 4);
            }
            let memory = intern_c_memory(
                memory.store(address.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
            );
            let load = Bitvector32Term::MemoryLoad(
                memory,
                Box::new(address),
                crate::kernel::LoadKind::Bits32,
            );
            crate::instrumentation::measure_deterministic_work(|| {
                PureFactContext::new()
                    .assume_condition(eq(&load, &Bitvector32Term::Constant(7)), true)
            })
        })
        .join()
        .expect("independent verification arena")
    }
    for size in [16, 64, 256, 1024] {
        // Retain the first context while admitting the same raw load shape in
        // another arena. Global raw-term interning used to compare the two
        // complete, independently allocated snapshots during the second insert.
        let (held, _) = sample(size);
        let (_, work) = sample(size);
        assert!(work < 100, "size={size}, second-arena work={work}");
        drop(held);
    }
}

#[test]
fn offset_premises_support_scalar_graph_edges_and_withdrawal() {
    let (a, b, c) = (var(70), var(71), var(72));
    let offset_eq = |left: Bitvector32Term, right: Bitvector32Term| {
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(left, 4),
            PointerOffsetTerm::scale_int32(right, 4),
        )
    };
    let scaled = offset_eq(a.clone(), b.clone());
    let direct = eq(&a, &b);
    let bc = eq(&b, &c);
    let context = PureFactContext::new()
        .assume_condition(scaled.clone(), true)
        .assume_condition(direct.clone(), true)
        .assume_condition(bc.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let without_direct = context.without_exact_fact(&Proposition::ConditionIs(direct, true));
    assert!(without_direct.equality_graph.are_int32_equal(&a, &c));
    let without_scaled =
        without_direct.without_exact_fact(&Proposition::ConditionIs(scaled.clone(), true));
    assert!(!without_scaled.equality_graph.are_int32_equal(&a, &c));
    assert!(without_scaled.equality_graph.are_int32_equal(&b, &c));
    let restricted = context.restricted_to_facts(&[(scaled, true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&a, &b));
    assert!(!restricted.equality_graph.are_int32_equal(&a, &c));
    let mut context = PureFactContext::new();
    for width in [0, 1, 8] {
        context = context.assume_condition(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(a.clone()),
                    byte_width: width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(b.clone()),
                    byte_width: width,
                },
            ),
            true,
        );
    }
    assert!(
        !context.equality_graph.are_int32_equal(&a, &b),
        "this ingress only translates four-byte element-index premises"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn offset_premise_shallow_decision_and_forks_scale() {
    let add = |v| Bitvector32Term::Add(Box::new(v), Box::new(Bitvector32Term::Constant(1)));
    for size in [16u64, 64, 256, 1024] {
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
