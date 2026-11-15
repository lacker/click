// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::binary_node;
use crate::kernel::binary_term;

#[test]
fn rewritten_load_store_witness_binds_value_address_and_state() {
    // The load is an `int32` one: a stored value answers only for a read of
    // its own width, and an unrecorded width is the widest scalar access.
    crate::kernel::eval::declare_load_access_width(&arc_pointer(4), 4);
    let index = MachineTerm::Variable(Variable(971));
    let value = MachineTerm::Variable(Variable(972));
    let write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(index, MachineTerm::constant(1)), true);
    let memory = Memory::new()
        .with_block("arg-memory", 32)
        .store(write, ProgramValue::Int32(value.clone()));
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&memory),
        Box::new(arc_pointer(4)),
        crate::kernel::LoadKind::Int32,
    );
    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_stored_origin_equality(&value, &load, &assumptions));
    let witnesses = capture.finish();
    assert_eq!(witnesses.len(), 1);
    let witness = &witnesses[0];
    assert!(witness.checks(&assumptions));
    assert!(!witness.checks(&PureFactContext::new()));
    let events = crate::kernel::proof::CheckedCallEvents::default();
    assert!(!witness.checks_retargeted_for_test(
        MachineTerm::constant(7),
        load.clone(),
        &assumptions,
        &events
    ));
    let wrong_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&memory),
        Box::new(arc_pointer(8)),
        crate::kernel::LoadKind::Int32,
    );
    assert!(!witness.checks_retargeted_for_test(value.clone(), wrong_load, &assumptions, &events));
    let overwritten = memory.store(
        arc_pointer(4),
        ProgramValue::Int32(MachineTerm::constant(8)),
    );
    let overwritten_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&overwritten),
        Box::new(arc_pointer(4)),
        crate::kernel::LoadKind::Int32,
    );
    assert!(!witness.checks_retargeted_for_test(value, overwritten_load, &assumptions, &events));
}

#[test]
fn rewritten_integer_word_observations_retain_checked_store_evidence() {
    use crate::kernel::proof::ProofFacts;
    let pointer = arc_pointer(4);
    crate::kernel::eval::declare_load_access_width(&pointer, 4);
    let value = MachineTerm::Variable(Variable(989_001));
    // The `int32` read of a cell returns the stored word, or σ of it when the
    // cell stores a `uint32` value (R-mem through σ).
    let signed_read = MachineTerm::sign_cast32(
        MachineIntegerType::UInt32,
        MachineIntegerType::Int32,
        value.clone(),
    );
    for (stored, read) in [
        (ProgramValue::Int32(value.clone()), value.clone()),
        (ProgramValue::UInt32(value.clone()), signed_read),
    ] {
        let memory = Memory::new()
            .with_block("arg-memory", 16)
            .store(pointer.clone(), stored);
        let load = |memory: &Memory, pointer: Pointer| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(pointer),
                crate::kernel::LoadKind::Int32,
            )
        };
        let goal = |ty, bits| {
            Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    IntegerTerm::from_machine(ty, bits).unwrap(),
                    IntegerTerm::constant_i64(17),
                ),
                true,
            )
        };
        let facts = ProofFacts::default();
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let original = goal(ty, load(&memory, pointer.clone()));
            let presented = goal(ty, read.clone());
            assert!(
                facts
                    .with_checked_rewritten_loads(&original, &presented)
                    .is_some(),
                "the same stored word has the same observation in its fixed format"
            );
            let source = MachineTerm::Variable(Variable(989_003));
            let cited =
                Proposition::ConditionIs(ConditionTerm::equal(source.clone(), read.clone()), true);
            let mut rewrite = facts
                .clone()
                .with_fact(cited.clone())
                .check_equality_rewrite(&goal(ty, source), &cited)
                .unwrap();
            assert!(rewrite.try_present_as(&original));
            assert_eq!(rewrite.proposition(), &original);
            let other = match ty {
                MachineIntegerType::Int32 => MachineIntegerType::UInt32,
                _ => MachineIntegerType::Int32,
            };
            assert!(
                facts
                    .with_checked_rewritten_loads(&original, &goal(other, read.clone()))
                    .is_none(),
                "equal bits do not equate signed and unsigned mathematical values"
            );
            assert!(
                facts
                    .with_checked_rewritten_loads(
                        &goal(ty, load(&memory, arc_pointer(8))),
                        &presented,
                    )
                    .is_none(),
                "a different cell has no stored-value witness"
            );
            let overwritten = memory.clone().store(
                pointer.clone(),
                ProgramValue::Int32(MachineTerm::constant(8)),
            );
            assert!(
                facts
                    .with_checked_rewritten_loads(
                        &goal(ty, load(&overwritten, pointer.clone())),
                        &presented,
                    )
                    .is_none(),
                "a changed cell cannot use the old stored-value witness"
            );
        }
    }
}

#[test]
fn rewritten_goal_does_not_reuse_an_ambient_equality_for_a_bound_variable() {
    let variable = Variable(981);
    let term = MachineTerm::Variable(variable);
    let one = MachineTerm::constant(1);
    let premise = Proposition::ConditionIs(ConditionTerm::equal(term.clone(), one.clone()), true);
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&[premise]);
    let goal = |value| Proposition::ForAll {
        name: Default::default(),
        var: variable,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(value, MachineTerm::constant(2)),
            true,
        )),
    };
    assert!(
        facts
            .with_checked_rewritten_loads(&goal(term), &goal(one))
            .is_none()
    );
}

fn retained_memory_dag_path(cell: &MemoryDagCell) -> &[MemoryDagHop] {
    match cell {
        MemoryDagCell::Stored { path, .. } | MemoryDagCell::Unwritten { path, .. } => path,
    }
}

/// A load variable's origin is first-seen per verified function. A name the
/// naming cache returned from an earlier function must not carry that
/// function's origin into the next one: the later function's transport would
/// walk the earlier function's DAG history, so its cost would depend on what
/// was verified before it in the same session.
#[test]
fn a_new_load_origin_epoch_retires_cached_origins() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(733)), 4),
    };
    let memory = crate::kernel::intern_memory(Memory::new().with_block("arg-memory", 32));
    let load = MachineTerm::MemoryLoad(
        memory.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    crate::kernel::eval::begin_load_origin_epoch();
    let (variable, _) =
        crate::kernel::eval::load_variable_for_term(&load).expect("a load term has a name");
    assert_eq!(
        crate::kernel::eval::registered_load_origin_for_variable(&variable),
        Some((memory.clone(), pointer.clone()))
    );
    crate::kernel::eval::begin_load_origin_epoch();
    assert_eq!(
        crate::kernel::eval::registered_load_origin_for_variable(&variable),
        None,
        "an origin minted by an earlier function must not answer in this one"
    );
    let (renamed, _) =
        crate::kernel::eval::load_variable_for_term(&load).expect("a load term has a name");
    assert_eq!(renamed, variable, "ids stay session-wide");
    assert_eq!(
        crate::kernel::eval::registered_load_origin_for_variable(&variable),
        Some((memory, pointer)),
        "naming the load in the new epoch records its origin afresh"
    );
}

#[test]
fn origin_load_equality_retains_singleton_index_bounds() {
    let index = MachineTerm::Variable(Variable(710));
    let left_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            MachineTerm::add(MachineTerm::constant(5), index.clone()),
            4,
        ),
    };
    let right_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::constant(5), 4),
    };
    let memory = crate::kernel::intern_memory(Memory::new().with_block("arg-memory", 32));
    let left = MachineTerm::MemoryLoad(
        memory.clone(),
        Box::new(left_pointer),
        crate::kernel::LoadKind::Int32,
    );
    let right = MachineTerm::MemoryLoad(
        memory,
        Box::new(right_pointer),
        crate::kernel::LoadKind::Int32,
    );
    let lower = ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone());
    let upper = ConditionTerm::signed_less_than(index, MachineTerm::constant(1));
    let assumptions = PureFactContext::new()
        .assume_condition(lower, true)
        .assume_condition(upper, true);

    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_origin_load_equality(&left, &right, &assumptions));
    let equalities = capture.finish();
    let [equality] = equalities.as_slice() else {
        panic!("expected one retained origin equality, got {equalities:?}");
    };
    assert!(equality.checks(&assumptions));
    assert!(
        !equality.checks(&PureFactContext::new()),
        "the retained equality must recheck both named singleton bounds",
    );
}

#[test]
fn checked_call_event_equality_requires_one_proof_owned_event_and_exact_query() {
    let assumptions = PureFactContext::new();
    let loaded = arc_pointer(0);
    let mutable_ranges = [memory_range(loaded.clone(), 0, 1)];
    let base = Memory::new().with_block("arg-memory", 16);
    let left =
        base.clone()
            .with_call_memory_havoc(Variable(700), &mutable_ranges, &assumptions, None);
    let right = base
        .with_block_without_derivation("local:recomputed-view", 4)
        .with_call_memory_havoc(Variable(700), &mutable_ranges, &assumptions, None);
    assert_ne!(left, right);

    let left_memory = crate::kernel::intern_memory_ref(&left);
    let right_memory = crate::kernel::intern_memory_ref(&right);
    let event = crate::kernel::proof::CheckedCallEvent::new(left_memory.clone());
    let events = crate::kernel::proof::CheckedCallEvents::containing_for_test(&event);
    let left_load = MachineTerm::MemoryLoad(
        left_memory.clone(),
        Box::new(loaded.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let right_load = MachineTerm::MemoryLoad(
        right_memory.clone(),
        Box::new(loaded.clone()),
        crate::kernel::LoadKind::Int32,
    );
    {
        let _scope = CheckedCallEventScope::start(&events);
        assert!(
            !checked_call_event_load_equality_for_test(&left_load, &right_load, &assumptions),
            "a read-only scope cannot adopt a structurally matching recomputed view",
        );
    }
    let _scope = CheckedCallEventScope::start_registering_views(&events);
    let capture = CheckedLoadEqualityCapture::start_with_call_events(&events);
    assert!(checked_atomic_load_equality(
        &left_load,
        &right_load,
        &assumptions,
    ));
    let equalities = capture.finish();
    let [equality] = equalities.as_slice() else {
        panic!("expected one retained equality, got {equalities:?}");
    };
    assert!(equality.is_same_checked_call_event_for_test());
    assert!(equality.checks_with_call_events(&assumptions, &events));

    let distinct_event = crate::kernel::proof::CheckedCallEvent::new(right_memory.clone());
    let distinct_events =
        crate::kernel::proof::CheckedCallEvents::containing_for_test(&distinct_event);
    assert!(
        !equality.checks_with_call_events(&assumptions, &distinct_events),
        "matching numeric havoc variables in distinct events are not authority",
    );

    let retargeted = arc_pointer(4);
    assert!(
        !equality.checks_retargeted_for_test(
            MachineTerm::MemoryLoad(
                left_memory,
                Box::new(retargeted.clone()),
                crate::kernel::LoadKind::Int32
            ),
            MachineTerm::MemoryLoad(
                right_memory,
                Box::new(retargeted),
                crate::kernel::LoadKind::Int32
            ),
            &assumptions,
            &events,
        ),
        "checked call evidence is query-specific",
    );
}

#[test]
fn checked_load_equality_retains_canonical_projection_provenance() {
    let source = Memory::new()
        .with_block_without_derivation("arg-memory", 16)
        .with_block_without_derivation("local:i", 4);
    let source = crate::kernel::intern_memory_ref(&source);
    let pointer = arc_pointer(0);
    let original = MachineTerm::MemoryLoad(
        source.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let projected = canonicalize_atomic_loads_deep(&original);
    let MachineTerm::MemoryLoad(projected_memory, _, _) = &projected else {
        panic!("an unresolved load must remain a load");
    };
    assert_ne!(projected_memory, &source);

    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_atomic_load_equality(
        &projected,
        &original,
        &PureFactContext::new(),
    ));
    let equalities = capture.finish();
    let [equality] = equalities.as_slice() else {
        panic!("expected one retained load equality, got {equalities:?}");
    };
    let Some(AtomicMemoryLoadEqualityEvidence::SameCellViaCanonicalProjection {
        left_projection: Some(projection),
        right_projection: None,
        ..
    }) = equality.memory_dag_evidence_for_test()
    else {
        panic!("expected canonical-projection evidence, got {equality:?}");
    };
    assert!(equality.checks(&PureFactContext::new()));

    let mut retargeted = projection.clone();
    retargeted.pointer = arc_pointer(4);
    assert!(
        !retargeted.checks(projected_memory, &pointer),
        "projection evidence must not be reusable for another cell"
    );
}

#[test]
fn canonical_projection_evidence_survives_a_better_source_registration() {
    let older = crate::kernel::intern_memory_ref(
        &Memory::new()
            .with_block_without_derivation("arg-memory", 16)
            .with_block_without_derivation("local:older", 4),
    );
    let newer = crate::kernel::intern_memory_ref(
        &Memory::new()
            .with_block_without_derivation("arg-memory", 16)
            .with_block_without_derivation("local:newer", 4),
    );
    let pointer = arc_pointer(0);
    let newer_load = MachineTerm::MemoryLoad(
        newer.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let projected = canonicalize_atomic_loads_deep(&newer_load);
    let MachineTerm::MemoryLoad(projected_memory, _, _) = &projected else {
        panic!("an unresolved load must remain a load");
    };

    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_atomic_load_equality(
        &projected,
        &newer_load,
        &PureFactContext::new(),
    ));
    let equalities = capture.finish();
    let [equality] = equalities.as_slice() else {
        panic!("expected one retained equality");
    };
    assert_eq!(
        canonical_load_projection_source(projected_memory, &pointer).as_ref(),
        Some(&newer)
    );

    let older_load = MachineTerm::MemoryLoad(
        older.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    assert_eq!(canonicalize_atomic_loads_deep(&older_load), projected);
    assert_eq!(
        canonical_load_projection_source(projected_memory, &pointer).as_ref(),
        Some(&older),
        "lookup should prefer the oldest execution source"
    );
    assert!(
        equality.checks(&PureFactContext::new()),
        "the exact newer projection remains valid after the preference changes"
    );
}

#[test]
fn nested_checked_load_equality_captures_keep_evidence_with_the_inner_owner() {
    let before = Memory::new().with_block("arg-memory", 16);
    let after = before.clone().with_block("local:temporary", 4);
    let pointer = arc_pointer(0);
    let assumptions = PureFactContext::new();

    let outer = CheckedLoadEqualityCapture::start();
    let inner = CheckedLoadEqualityCapture::start();
    assert!(checked_memory_load_equality(
        &before,
        &after,
        &pointer,
        &assumptions,
    ));
    let inner_equalities = inner.finish();
    let outer_equalities = outer.finish();

    assert_eq!(inner_equalities.len(), 1);
    assert!(inner_equalities[0].checks(&assumptions));
    assert!(outer_equalities.is_empty());
}

// --- named-memory-states arc: the derivation DAG -------------------------
// See docs/internals/memory-dag.md. These pin the two invariants
// the arc's safety argument rests on (advisory-only, and parent id < child
// id) plus the havoc-identity property that must hold by construction.

#[test]
fn a_store_records_the_edge_from_the_state_it_wrote() {
    let base = Memory::new().with_block("arg-memory", 16);
    let after = base.clone().store(
        arc_pointer(4),
        ProgramValue::Int32(MachineTerm::constant(7)),
    );

    let derivation = crate::kernel::intern_memory_ref(&after)
        .derivation()
        .expect("a store records how the state was produced");
    match derivation.as_ref() {
        MemoryDerivation::Store {
            base: recorded_base,
            pointer,
            value,
            ..
        } => {
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(pointer, &arc_pointer(4));
            assert_eq!(value, &ProgramValue::Int32(MachineTerm::constant(7)));
        }
        other => panic!("expected a store edge, got {other:?}"),
    }
}

#[test]
fn retained_store_hops_carry_locally_checkable_distinctness_proofs() {
    let base = Memory::new().with_block("arg-memory", 32);
    let root = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(100)), 4),
    };

    let constant_write = root.offset_by_int32_elements(MachineTerm::constant(1));
    let constant_read = root.offset_by_int32_elements(MachineTerm::constant(2));
    let after_constant = base.clone().store(
        constant_write,
        ProgramValue::Int32(MachineTerm::constant(7)),
    );
    let constant_evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_memory_ref(&after_constant),
        &crate::kernel::intern_memory_ref(&base),
        &constant_read,
        crate::kernel::LoadKind::Int32,
        &PureFactContext::new(),
    )
    .expect("unequal constant indices retain a store-hop proof");
    let constant_hop = &retained_memory_dag_path(&constant_evidence.left)[0];
    assert!(
        matches!(
            constant_hop.justification,
            MemoryDagHopJustification::StoreCommonBaseUnequalConstants { .. }
        ),
        "unexpected retained reason: {:?}",
        constant_hop.justification
    );
    assert!(constant_hop.justification.checks(
        constant_hop.derivation.as_ref(),
        &constant_read,
        4,
        &PureFactContext::new(),
    ));
    let constant_left = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&after_constant),
        Box::new(constant_read.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let constant_right = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&base),
        Box::new(constant_read.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let constant_atomic = atomic_memory_load_equality_evidence(
        &constant_left,
        &constant_right,
        &PureFactContext::new(),
    )
    .expect("the atomic query retains the same typed walk");
    assert!(constant_atomic.checks(
        &Proposition::ConditionIs(ConditionTerm::equal(constant_left, constant_right), true,),
        &PureFactContext::new(),
    ));

    let write_index = MachineTerm::Variable(Variable(101));
    let read_index = MachineTerm::Variable(Variable(102));
    let symbolic_write = root.offset_by_int32_elements(write_index.clone());
    let symbolic_read = root.offset_by_int32_elements(read_index.clone());
    // An `int32` element read. A width-less load would stand in eight bytes
    // and reach into the next element, which `i != j` cannot separate.
    crate::kernel::eval::declare_load_access_width(&symbolic_read, 4);
    let inequality = ConditionTerm::equal(write_index, read_index);
    let assumptions = PureFactContext::new().assume_condition(inequality.clone(), false);
    let after_symbolic = base.store(
        symbolic_write,
        ProgramValue::Int32(MachineTerm::constant(9)),
    );
    let symbolic_evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_memory_ref(&after_symbolic),
        &crate::kernel::intern_memory_ref(&Memory::new().with_block("arg-memory", 32)),
        &symbolic_read,
        crate::kernel::LoadKind::Int32,
        &assumptions,
    )
    .expect("an exact index inequality retains its named premise");
    let symbolic_hop = &retained_memory_dag_path(&symbolic_evidence.left)[0];
    assert_eq!(
        symbolic_hop.justification,
        MemoryDagHopJustification::StoreCommonBaseExactInequality {
            condition: inequality,
        }
    );
    assert!(symbolic_hop.justification.checks(
        symbolic_hop.derivation.as_ref(),
        &symbolic_read,
        4,
        &assumptions,
    ));
    assert!(
        !symbolic_hop.justification.checks(
            symbolic_hop.derivation.as_ref(),
            &symbolic_read,
            4,
            &PureFactContext::new(),
        ),
        "the retained exact premise must still be present during check"
    );
    let symbolic_left = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&after_symbolic),
        Box::new(symbolic_read.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let symbolic_right = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&Memory::new().with_block("arg-memory", 32)),
        Box::new(symbolic_read),
        crate::kernel::LoadKind::Int32,
    );
    let symbolic_atomic =
        atomic_memory_load_equality_evidence(&symbolic_left, &symbolic_right, &assumptions)
            .expect("the atomic query retains the exact inequality proof");
    let symbolic_goal =
        Proposition::ConditionIs(ConditionTerm::equal(symbolic_left, symbolic_right), true);
    assert!(symbolic_atomic.checks(&symbolic_goal, &assumptions));
    assert!(
        !symbolic_atomic.checks(&symbolic_goal, &PureFactContext::new()),
        "atomic check cannot borrow the missing exact inequality"
    );
    let derivation = crate::kernel::search::ProofSearch::derive_atomic_proposition(
        &(assumptions),
        &symbolic_goal,
    )
    .expect("atomic search returns the retained typed memory proof");
    assert!(matches!(
        &derivation.rule,
        PropositionDerivationRule::ContextualAtomic {
            evidence: AtomicPropositionDerivationEvidence::MemoryDag(_),
            ..
        }
    ));
    assert!(derivation.check(&assumptions));
    assert!(
        !derivation.check(&PureFactContext::new()),
        "the proof object still checks its exact premise context"
    );
}

#[test]
fn retained_common_base_store_hop_uses_a_stated_endpoint_order() {
    let base = Memory::new().with_block("arg-memory", 64);
    let root = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(109)), 4),
    };
    let write_index = MachineTerm::Variable(Variable(110));
    let middle = MachineTerm::Variable(Variable(111));
    let read_index = MachineTerm::Variable(Variable(112));
    let first = ConditionTerm::signed_less_than(write_index.clone(), middle.clone());
    let second = ConditionTerm::signed_less_equal(middle, read_index.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(first.clone(), true)
        .assume_condition(second.clone(), true);
    let write = root.offset_by_int32_elements(write_index.clone());
    let read = root.offset_by_int32_elements(read_index.clone());
    let after = base
        .clone()
        .store(write, ProgramValue::Int32(MachineTerm::constant(7)));
    assert!(
        memory_load_equality_evidence_at(
            &crate::kernel::intern_memory_ref(&after),
            &crate::kernel::intern_memory_ref(&base),
            &read,
            crate::kernel::LoadKind::Int32,
            &assumptions,
        )
        .is_none(),
        "byte-gap checking does not derive the endpoint order"
    );
    let endpoint = ConditionTerm::signed_less_than(write_index.clone(), read_index.clone());
    let assumptions = assumptions.assume_condition(endpoint.clone(), true);
    let evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_memory_ref(&after),
        &crate::kernel::intern_memory_ref(&base),
        &read,
        crate::kernel::LoadKind::Int32,
        &assumptions,
    )
    .expect("the stated endpoint order crosses the store");
    let hop = &retained_memory_dag_path(&evidence.left)[0];
    let MemoryDagHopJustification::StoreCommonBaseSignedOrder {
        condition,
        path,
        reversed: false,
    } = &hop.justification
    else {
        panic!(
            "expected a retained signed-order path, got {:?}",
            hop.justification
        );
    };
    assert_eq!(condition, &ConditionTerm::equal(write_index, read_index));
    assert_eq!(
        path.iter()
            .map(OrderDerivationStep::premise)
            .cloned()
            .collect::<Vec<_>>(),
        vec![
            Proposition::ConditionIs(first, true),
            Proposition::ConditionIs(second.clone(), true)
        ]
    );
    assert!(
        hop.justification
            .checks(hop.derivation.as_ref(), &read, 4, &assumptions)
    );
    assert!(
        !hop.justification.checks(
            hop.derivation.as_ref(),
            &read,
            4,
            &PureFactContext::new().assume_condition(second, true),
        ),
        "the retained path must still have every named premise"
    );
}

#[test]
fn store_hop_retains_direct_or_composed_separated_range_authority() {
    let base = Memory::new().with_block("arg-memory", 64);
    let range_base = |variable| Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    };
    let write_base = range_base(110);
    let load_base = range_base(111);
    let write_range = memory_range(write_base.clone(), 0, 2);
    let load_range = memory_range(load_base.clone(), 0, 2);
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(write_range.clone())),
        right: Box::new(Resource::Memory(load_range.clone())),
    };
    let resources = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(write_range.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(load_range.clone()));
    let direct_assumptions = PureFactContext::new().assume_proposition(separation.clone());
    let composed_assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceComposition(resources.clone()));
    let write = write_base.offset_by_int32_elements(MachineTerm::constant(1));
    let load = load_base.offset_by_int32_elements(MachineTerm::constant(0));
    let after = base
        .clone()
        .store(write, ProgramValue::Int32(MachineTerm::constant(7)));
    let left = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&after),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let right = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&base),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let retained_hop = |assumptions: &PureFactContext| {
        let capture = CheckedLoadEqualityCapture::start();
        assert!(checked_atomic_load_equality(&left, &right, assumptions));
        let equalities = capture.finish();
        let [equality] = equalities.as_slice() else {
            panic!("expected one retained load equality, got {equalities:?}");
        };
        assert!(equality.checks(assumptions));
        let Some(AtomicMemoryLoadEqualityEvidence::SameCell(evidence)) =
            equality.memory_dag_evidence_for_test()
        else {
            panic!("expected typed same-cell evidence, got {equality:?}");
        };
        retained_memory_dag_path(&evidence.left)[0]
            .justification
            .clone()
    };

    let direct = retained_hop(&direct_assumptions);
    let MemoryDagHopJustification::StoreSeparatedRanges {
        authority,
        left,
        right,
        orientation,
        ..
    } = &direct
    else {
        panic!("expected retained separated-range evidence, got {direct:?}");
    };
    assert_eq!(
        authority,
        &StoreSeparatedRangesAuthority::ExactProposition(separation)
    );
    assert_eq!(left, &write_range);
    assert_eq!(right, &load_range);
    assert_eq!(
        orientation,
        &StoreSeparatedRangeOrientation::WriteLeftLoadRight
    );
    let composed = retained_hop(&composed_assumptions);
    let MemoryDagHopJustification::StoreSeparatedRanges {
        authority,
        left,
        right,
        orientation,
        ..
    } = &composed
    else {
        panic!("expected retained separated-range evidence, got {composed:?}");
    };
    assert_eq!(
        authority,
        &StoreSeparatedRangesAuthority::ResourceComposition(resources)
    );
    assert_eq!(left, &write_range);
    assert_eq!(right, &load_range);
    assert_eq!(
        orientation,
        &StoreSeparatedRangeOrientation::WriteLeftLoadRight
    );
    let derivation = crate::kernel::intern_memory_ref(&after)
        .derivation()
        .expect("the written state retains its store");
    assert!(
        !composed.checks(derivation.as_ref(), &load, 4, &PureFactContext::new()),
        "the retained composition must still be present during checking"
    );
}

#[test]
fn entry_separation_does_not_frame_a_store_after_its_bases_become_equal() {
    let base = Memory::new().with_block("arg-memory", 16);
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(130_001)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(130_002)), 4),
    };
    let bridge = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(130_003)), 4),
    };
    let left_range = memory_range(left.clone(), 0, 1);
    let right_range = memory_range(right.clone(), 0, 1);
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(left_range.clone())),
        right: Box::new(Resource::Memory(right_range.clone())),
    };
    let entry_assumptions = PureFactContext::new().assume_proposition(separation);
    let retained = crate::kernel::memory_provenance::typed_store_separated_ranges_evidence(
        &left,
        4,
        &right,
        4,
        &entry_assumptions,
    )
    .expect("the entry-time partition initially supplies the hop");
    let assumptions = entry_assumptions
        .assume_condition(
            ConditionTerm::pointer_equal(left.clone(), bridge.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(bridge, right.clone()), true);
    assert_eq!(
        assumptions
            .exact_condition_value(&ConditionTerm::pointer_equal(left.clone(), right.clone())),
        None,
        "the alias is established through the intermediate pointer, not a direct fact"
    );
    assert!(
        crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            &left,
            &right,
            &assumptions,
        )
    );
    assert!(assumptions.memory_ranges_overlap_after_base_equality(&left_range, &right_range));
    assert!(
        !assumptions.proves_resource_separate(
            &Resource::Memory(left_range.clone()),
            &Resource::Memory(right_range.clone()),
        ),
        "a stale entry partition cannot prove overlapping ranges separate"
    );
    assert!(
        crate::kernel::memory_provenance::typed_store_separated_ranges_evidence(
            &left,
            4,
            &right,
            4,
            &assumptions,
        )
        .is_none(),
        "a stale entry partition cannot frame equal store and load addresses"
    );
    let after = base
        .clone()
        .store(left.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
    let derivation = crate::kernel::intern_memory_ref(&after)
        .derivation()
        .expect("the written state retains its store");
    assert!(
        !retained.checks(derivation.as_ref(), &right, 4, &assumptions),
        "a retained hop must be refused after its own ranges become overlapping"
    );
}

#[test]
fn equal_range_bases_keep_a_separation_for_disjoint_byte_intervals() {
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(130_011)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(130_012)), 4),
    };
    let left_range = memory_range(left.clone(), 0, 1);
    let right_range = memory_range(right.clone(), 1, 2);
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(left_range.clone())),
        right: Box::new(Resource::Memory(right_range.clone())),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(separation)
        .assume_condition(ConditionTerm::pointer_equal(left, right), true);

    assert!(
        !assumptions.memory_ranges_overlap_after_base_equality(&left_range, &right_range),
        "adjacent element intervals remain separate when their bases are equal"
    );
    assert!(assumptions.proves_resource_separate(
        &Resource::Memory(left_range),
        &Resource::Memory(right_range),
    ));
}

#[test]
fn separated_range_store_hop_retains_symbolic_membership_bounds() {
    let base = Memory::new().with_block("arg-memory", 64);
    let range_base = |variable| Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    };
    let write_base = range_base(120);
    let load_base = range_base(121);
    let write_range = memory_range(write_base.clone(), 0, 3);
    let load_range = memory_range(load_base.clone(), 0, 3);
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(write_range)),
        right: Box::new(Resource::Memory(load_range)),
    };
    let write_index = MachineTerm::Variable(Variable(122));
    let load_index = MachineTerm::Variable(Variable(123));
    let zero_le_write =
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), write_index.clone());
    let write_lt_three =
        ConditionTerm::signed_less_than(write_index.clone(), MachineTerm::constant(3));
    let zero_le_load =
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), load_index.clone());
    let load_lt_write_successor = ConditionTerm::signed_less_than(
        load_index.clone(),
        MachineTerm::add(write_index.clone(), MachineTerm::constant(1)),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(separation.clone())
        .assume_condition(zero_le_write.clone(), true)
        .assume_condition(write_lt_three.clone(), true)
        .assume_condition(zero_le_load.clone(), true)
        .assume_condition(load_lt_write_successor.clone(), true);
    let write = write_base.offset_by_int32_elements(write_index);
    let load = load_base.offset_by_int32_elements(load_index.clone());
    let after = base
        .clone()
        .store(write, ProgramValue::Int32(MachineTerm::constant(7)));
    // An `Int32` read also encodes LP64 pointers. These terms represent int32 reads,
    // so use the typed producer to record their four-byte access width.
    crate::kernel::eval::symbolic_load_value(&base, &load, ProgramType::Int32).unwrap();
    crate::kernel::eval::symbolic_load_value(&after, &load, ProgramType::Int32).unwrap();
    let left = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&after),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let right = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&base),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_atomic_load_equality(&left, &right, &assumptions));
    let equalities = capture.finish();
    let [equality] = equalities.as_slice() else {
        panic!("expected one retained load equality, got {equalities:?}");
    };
    let Some(AtomicMemoryLoadEqualityEvidence::SameCell(evidence)) =
        equality.memory_dag_evidence_for_test()
    else {
        panic!("expected typed same-cell evidence, got {equality:?}");
    };
    let hop = &retained_memory_dag_path(&evidence.left)[0];
    assert!(matches!(
        hop.justification,
        MemoryDagHopJustification::StoreSeparatedRanges { .. }
    ));
    assert!(
        hop.justification
            .checks(hop.derivation.as_ref(), &load, 4, &assumptions)
    );

    let missing_successor = PureFactContext::new()
        .assume_proposition(separation)
        .assume_condition(zero_le_write, true)
        .assume_condition(write_lt_three, true)
        .assume_condition(zero_le_load, true);
    assert!(
        !hop.justification
            .checks(hop.derivation.as_ref(), &load, 4, &missing_successor),
        "the retained successor bound must still be present"
    );
    let retargeted =
        load_base.offset_by_int32_elements(MachineTerm::add(load_index, MachineTerm::constant(1)));
    assert!(
        !hop.justification
            .checks(hop.derivation.as_ref(), &retargeted, 4, &assumptions),
        "the membership evidence must remain tied to its exact index"
    );
}

#[test]
fn derivation_bases_are_strictly_older_so_the_dag_cannot_cycle() {
    // Storing a value and then storing it back re-interns the original
    // state, which is the shortest cycle the DAG could otherwise grow.
    // First-wins recording keeps the older edge, so following `base` still
    // strictly decreases and terminates.
    let base = Memory::new().with_block("arg-memory", 16);
    let written = base.clone().store(
        arc_pointer(0),
        ProgramValue::Int32(MachineTerm::constant(1)),
    );
    let restored = written
        .clone()
        .store(
            arc_pointer(0),
            ProgramValue::Int32(MachineTerm::constant(0)),
        )
        .store(
            arc_pointer(0),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
    assert_eq!(restored, written, "the round trip returns the same value");

    let mut node = crate::kernel::intern_memory_ref(&restored);
    let mut hops = 0;
    while let Some(derivation) = node.derivation() {
        let next = derivation.base().clone();
        assert!(
            next.arena_id() < node.arena_id(),
            "a derivation base must be strictly older than what it derives"
        );
        node = next;
        hops += 1;
        assert!(hops < 64, "walking derivation bases must terminate");
    }
}

#[test]
fn call_havoc_cannot_reuse_another_paths_frozen_empty_range() {
    // Reuse the same source identities in independent sessions as well as
    // both construction orders within each session. Neither arena insertion
    // order nor a previous verification may supply preservation evidence.
    for empty_first in [true, false, true, false] {
        let _session = crate::kernel::VerificationSession::enter();
        check_call_havoc_path_local_evidence(empty_first);
    }
}

fn check_call_havoc_path_local_evidence(empty_first: bool) {
    let before = Memory::new().with_block("arg-memory", 32);
    let length = MachineTerm::Variable(Variable(70_021));
    let range = MemoryRange::new(arc_pointer(0), MachineTerm::constant(0), length.clone());
    let empty = PureFactContext::new().assume_condition(
        ConditionTerm::equal(length.clone(), MachineTerm::constant(0)),
        true,
    );
    let positive = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(length, MachineTerm::constant(1)), true);
    let make_call = |context: &PureFactContext| {
        before.clone().with_call_memory_havoc(
            Variable(70_020),
            std::slice::from_ref(&range),
            context,
            None,
        )
    };
    let load = |memory: &Memory| {
        canonicalize_atomic_loads_deep(&MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(arc_pointer(0)),
            crate::kernel::LoadKind::Int32,
        ))
    };
    let (first_context, second_context) = if empty_first {
        (&empty, &positive)
    } else {
        (&positive, &empty)
    };
    let first = make_call(first_context);
    let first_load = load(&first);
    let second = make_call(second_context);
    let second_load = load(&second);
    // Context-free canonicalization must not use either path's assumptions.
    // A valid empty-range crossing instead requires checked contextual proof.
    assert_ne!(
        first_load,
        load(&before),
        "context-free loads cannot inherit a path's empty-range evidence"
    );
    assert_ne!(
        second_load,
        load(&before),
        "a later path cannot inherit the first path's empty-range evidence"
    );
}

#[test]
fn call_havoc_marker_identity_includes_symbolic_write_set() {
    let base = Memory::new().with_block("arg-memory", 32);
    let first_range = MemoryRange::new(
        arc_pointer(0),
        MachineTerm::Variable(Variable(70_001)),
        MachineTerm::Variable(Variable(70_002)),
    );
    let second_range = MemoryRange::new(
        arc_pointer(0),
        MachineTerm::Variable(Variable(70_003)),
        MachineTerm::Variable(Variable(70_004)),
    );

    // The marker variable and parent state intentionally match. A
    // lossy hash of only constant bounds and the base block would make these
    // two derived memories equal and let first-wins attach the first range
    // list to the second call.
    let first = base.clone().with_call_memory_havoc(
        Variable(70_000),
        std::slice::from_ref(&first_range),
        &PureFactContext::new(),
        None,
    );
    let second = base.with_call_memory_havoc(
        Variable(70_000),
        std::slice::from_ref(&second_range),
        &PureFactContext::new(),
        None,
    );
    assert_ne!(
        first, second,
        "different symbolic write sets need distinct states"
    );

    let first = crate::kernel::intern_memory_ref(&first);
    let second = crate::kernel::intern_memory_ref(&second);
    assert_ne!(first.arena_id(), second.arena_id());
    let MemoryDerivation::CallHavoc { mutable_ranges, .. } = second
        .derivation()
        .expect("the second state retains its own call-havoc edge")
        .as_ref()
        .clone()
    else {
        panic!("expected a call-havoc derivation");
    };
    assert_eq!(mutable_ranges, vec![second_range]);
}

#[test]
fn a_store_that_changes_nothing_records_no_edge_to_itself() {
    let base = Memory::new().with_block("arg-memory", 16).store(
        arc_pointer(0),
        ProgramValue::Int32(MachineTerm::constant(3)),
    );
    let again = base.clone().store(
        arc_pointer(0),
        ProgramValue::Int32(MachineTerm::constant(3)),
    );
    assert_eq!(again, base);

    let node = crate::kernel::intern_memory_ref(&again);
    if let Some(derivation) = node.derivation() {
        assert_ne!(
            derivation.base().arena_id(),
            node.arena_id(),
            "a state must never be recorded as derived from itself"
        );
    }
}

#[test]
fn loop_havoc_is_its_own_edge_kind_and_keeps_its_marker_block() {
    let base = Memory::new().with_block("arg-memory", 16).store(
        arc_pointer(0),
        ProgramValue::Int32(MachineTerm::constant(5)),
    );
    let after = base.clone().with_loop_memory_havoc_preserving_loans(
        Variable(0),
        &BTreeSet::new(),
        None,
        None,
    );

    assert!(
        after.has_block(&"havoc:0".into()),
        "the freshness marker block must survive the arc untouched"
    );
    let derivation = crate::kernel::intern_memory_ref(&after)
        .derivation()
        .expect("loop havoc records how the state was produced");
    match derivation.as_ref() {
        MemoryDerivation::LoopHavoc {
            base: recorded_base,
            variable,
            mutable_ranges,
            kept_by_function,
        } => {
            assert!(kept_by_function.is_none());
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(*variable, Variable(0));
            assert_eq!(*mutable_ranges, None);
        }
        other => panic!("expected a loop-havoc edge, got {other:?}"),
    }
}

#[test]
fn derivations_carry_a_load_across_a_distinct_store_but_not_across_havoc() {
    // The first consumer of the DAG: load preservation answered from the
    // recorded history rather than from effect facts. A store to a provably
    // distinct cell is crossable; a loop havoc between the same endpoints is
    // not, because it has no write set to be disjoint from.
    //
    // Only the positive direction is the DAG's to add. The havoc refusals
    // are soundness properties that must hold with the arc switched off too,
    // so they run under both settings.
    let base = Memory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);

    // A call havoc changes the block set (it adds its marker block), so
    // the state-diff matcher refuses to look at the cells at all. The
    // recorded edge carries the call's mutable ranges, so the walk can
    // still cross it for a pointer provably outside them. This is the
    // case the DAG answers and value bridging cannot.
    let called = base.clone().with_call_memory_havoc(
        Variable(3),
        &[memory_range(arc_pointer(8), 0, 8)],
        &PureFactContext::new(),
        None,
    );
    assert!(
        !memories_match_for_pointer_load_under_assumptions(
            &base,
            &called,
            &read,
            &PureFactContext::new()
        ),
        "the state-diff matcher is expected not to cross the marker block"
    );
    assert!(
        checked_memory_load_equality(&base, &called, &read, &PureFactContext::new()),
        "a call that may only write a disjoint range preserves the load"
    );

    let havoced = base.clone().with_loop_memory_havoc_preserving_loans(
        Variable(7),
        &BTreeSet::new(),
        None,
        None,
    );
    assert!(
        !checked_memory_load_equality(&base, &havoced, &read, &PureFactContext::new()),
        "loop havoc must never be crossed without explicit frame evidence"
    );

    let havoced_then_stored = havoced.clone().store(
        arc_pointer(4),
        ProgramValue::Int32(MachineTerm::constant(9)),
    );
    assert!(
        !checked_memory_load_equality(&base, &havoced_then_stored, &read, &PureFactContext::new(),),
        "a crossable store must not smuggle a walk past an intervening havoc"
    );
}

#[test]
fn loop_havoc_carries_a_verified_write_set_for_disjoint_loads() {
    let base = Memory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let ranges = [memory_range(arc_pointer(8), 0, 8)];
    let havoced = base.clone().with_loop_memory_havoc_preserving_loans(
        Variable(8),
        &BTreeSet::new(),
        Some(&ranges),
        None,
    );

    let derivation = crate::kernel::intern_memory_ref(&havoced)
        .derivation()
        .expect("verified loop havoc records its write set");
    let MemoryDerivation::LoopHavoc {
        mutable_ranges: Some(recorded),
        ..
    } = derivation.as_ref()
    else {
        panic!("expected a loop-havoc edge with ranges, got {derivation:?}");
    };
    assert_eq!(recorded, &ranges);

    let load = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    assert!(
        crate::kernel::explicit_atomic_equality_from_memory_derivations(
            &load(&havoced),
            &load(&base),
            &PureFactContext::new(),
        )
    );

    let overlapping_ranges = [memory_range(arc_pointer(0), 0, 8)];
    let overlapping = base.clone().with_loop_memory_havoc_preserving_loans(
        Variable(9),
        &BTreeSet::new(),
        Some(&overlapping_ranges),
        None,
    );
    assert!(!checked_memory_load_equality(
        &base,
        &overlapping,
        &read,
        &PureFactContext::new()
    ));
}

#[test]
fn loop_kept_frame_preserves_only_complete_pointer_reads() {
    let _session = crate::kernel::VerificationSession::enter();
    let field = arc_pointer(0);
    let base = Memory::new()
        .with_block("arg-memory", 16)
        .store(field.clone(), ProgramValue::Int32(7u32.into()));
    let before = crate::kernel::intern_memory_ref(&base);
    let ranges = [memory_range(field.clone(), 0, 16)];
    let havoc = |kept_bytes: u32| {
        let kept = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(field.clone(), 0u32.into(), kept_bytes.into(), 1),
        ));
        base.clone().with_loop_memory_havoc_preserving_frame(
            Variable(980114),
            &BTreeSet::new(),
            Some(&ranges),
            None,
            Some(CallKeptRanges::new(kept, vec![], None)),
        )
    };
    let complete = havoc(8);
    let prefix = havoc(4);
    assert_ne!(
        complete, prefix,
        "different retained frames need different states"
    );
    let unchanged = |after: &Memory| {
        crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
            &Pointer::loaded_value(&before, &field),
            &Pointer::loaded_value(&crate::kernel::intern_memory_ref(after), &field),
            &PureFactContext::new(),
        )
    };
    assert!(unchanged(&complete));
    assert!(!unchanged(&prefix));
    let unframed = base.clone().with_loop_memory_havoc_preserving_loans(
        Variable(980114),
        &BTreeSet::new(),
        Some(&ranges),
        None,
    );
    assert!(!unchanged(&unframed));
    let overwritten = complete.store(field.offset_by_bytes(4), ProgramValue::Int32(9u32.into()));
    assert!(
        !unchanged(&overwritten),
        "the upper pointer half was overwritten"
    );
}

#[test]
fn loan_preserving_havoc_uses_the_full_cell_footprint() {
    let pointer = arc_pointer(0);
    let base = Memory::new().with_block("arg-memory", 16).store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(5)),
    );
    let fact = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        pointer.clone(),
        MachineTerm::constant(2),
        MachineTerm::constant(3),
        1,
    ));
    let support = ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(&fact)
        .expect("memory backing")
        .0;
    let ledger = crate::kernel::loans::LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let opening = ledger
        .lend(owner, reader, support, fact)
        .expect("memory loan");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("memory loan transition");

    let retained = base.with_loop_memory_havoc_preserving_loans(
        Variable(10),
        &BTreeSet::new(),
        None,
        Some(&ledger),
    );
    assert!(retained.cells.contains_key(&pointer));
}

#[test]
fn loan_havoc_may_forget_a_run_crossing_the_interval_index_boundary() {
    let pointer = Pointer {
        block: "local:loan-index-boundary".into(),
        offset: PointerOffsetTerm::Constant(i64::from(i32::MAX) - 7),
    };
    let fact = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        pointer.clone(),
        0u32.into(),
        1u32.into(),
        4,
    ));
    let support = ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(&fact)
        .unwrap()
        .0;
    let ledger = crate::kernel::loans::LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger.lend(owner, reader, support, fact.clone()).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    assert!(ledger.has_indexed_memory_overlap(fact.memory_range().unwrap()));
    let original = intern_memory(Memory::new());
    let run = CellRun::new(
        pointer.clone(),
        4,
        ProgramType::Int32,
        2,
        original.clone(),
        crate::kernel::primitives::IndexIntervals::default(),
    );
    let mut memory = original.memory().clone();
    std::sync::Arc::make_mut(&mut memory.cells).add_run(run);
    let after = memory.with_loop_memory_havoc_preserving_loans(
        Variable(980115),
        &BTreeSet::new(),
        None,
        Some(&ledger),
    );
    assert!(!after.has_known_cell_at(&pointer));
    assert!(after.has_initialized_bytes_at(&pointer, 8));
    assert!(
        ledger
            .permits_memory_access(fact.memory_range().unwrap())
            .is_err()
    );
}

/// Stage 4: the DAG-guided cell lookup answers load equality for states
/// that are *siblings*, which the stage-2 walk cannot do because it only ever
/// asks whether one state is reachable from the other.
///
/// Two calls, each havocking a range disjoint from the loaded cell, produce
/// two states neither of which derives from the other. Value bridging
/// refuses them outright — each carries its own `call-havoc:N` marker block,
/// so the block sets differ and the state matcher stops before looking at
/// any cell. Resolving both against the write history lands them on one
/// common ancestor, and the loads are equal with no state comparison.
#[test]
fn sibling_states_resolve_one_cell_to_a_common_ancestor() {
    let base = Memory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let load_in = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let call_havoc = |variable| {
        base.clone().with_call_memory_havoc(
            Variable(variable),
            &[memory_range(arc_pointer(8), 0, 8)],
            &PureFactContext::new(),
            None,
        )
    };
    let (left, right) = (call_havoc(3), call_havoc(4));

    assert!(
        !memories_match_for_pointer_load_under_assumptions(
            &left,
            &right,
            &read,
            &PureFactContext::new()
        ),
        "the two marker blocks are expected to stop the state matcher"
    );
    assert!(
        PureFactContext::new().memory_loads_proven_equal(&load_in(&left), &load_in(&right)),
        "the common-ancestor lookup is exactly what the DAG adds here"
    );
    let evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_memory_ref(&left),
        &crate::kernel::intern_memory_ref(&right),
        &read,
        crate::kernel::LoadKind::Int32,
        &PureFactContext::new(),
    )
    .expect("a successful equality decision retains both traversed walks");
    assert_eq!(evidence.reason, MemoryDagLoadEqualityReason::CommonSource);
    assert_eq!(retained_memory_dag_path(&evidence.left).len(), 1);
    assert_eq!(retained_memory_dag_path(&evidence.right).len(), 1);
    assert_eq!(
        retained_memory_dag_path(&evidence.left)[0].derived.as_ref(),
        &left,
        "the left proof names the exact derived state"
    );
    assert_eq!(
        retained_memory_dag_path(&evidence.right)[0]
            .derived
            .as_ref(),
        &right,
        "the right proof names the exact derived state"
    );
    assert_eq!(
        evidence.left.node(),
        evidence.right.node(),
        "both retained walks end at their common source"
    );
    let first = with_extended_dag_bridging(|| {
        atomic_memory_load_equality_evidence(
            &load_in(&left),
            &load_in(&right),
            &PureFactContext::new(),
        )
    })
    .expect("the atomic decision returns retained evidence");
    let cached = with_extended_dag_bridging(|| {
        atomic_memory_load_equality_evidence(
            &load_in(&left),
            &load_in(&right),
            &PureFactContext::new(),
        )
    })
    .expect("a positive memo hit returns the retained evidence");
    assert_eq!(cached, first);
    assert!(first.is_fully_typed());
    let goal =
        Proposition::ConditionIs(ConditionTerm::equal(load_in(&left), load_in(&right)), true);
    assert!(first.checks(&goal, &PureFactContext::new()));
    let derivation = with_extended_dag_bridging(|| {
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(PureFactContext::new()),
            &goal,
        )
    })
    .expect("call-havoc range evidence flows out of the original decision");
    assert!(matches!(
        &derivation.rule,
        PropositionDerivationRule::ContextualAtomic {
            evidence: AtomicPropositionDerivationEvidence::MemoryDag(_),
            ..
        }
    ));
    assert!(derivation.check(&PureFactContext::new()));

    // Soundness, and so asserted in both modes: an intervening loop havoc has
    // no write set, so no walk may resolve through one.
    let havoced = left.clone().with_loop_memory_havoc_preserving_loans(
        Variable(9),
        &BTreeSet::new(),
        None,
        None,
    );
    assert!(
        !PureFactContext::new().memory_loads_proven_equal(&load_in(&left), &load_in(&havoced)),
        "loop havoc must stop the cell lookup"
    );
}

#[test]
fn call_havoc_retains_exact_separation_and_positive_offset_steps() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(201)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(202)), 4),
    };
    // An `int32` element read. The forward-offset route proves the havoc
    // range starts one element later, which clears a four-byte access; a
    // width-less load would stand in eight bytes and reach into it.
    crate::kernel::eval::declare_load_access_width(&data, 4);
    let len = MachineTerm::Variable(Variable(203));
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(owner.clone(), 0, 4))),
        right: Box::new(Resource::Memory(memory_range(data.clone(), 0, 16))),
    };
    let lower_bound = ConditionTerm::signed_less_equal(MachineTerm::constant(1), len.clone());
    let assumptions = PureFactContext::new()
        .assume_proposition(separation.clone())
        .assume_condition(lower_bound.clone(), true);
    let mutable_ranges = vec![
        memory_range(owner, 0, 1),
        memory_range(data.offset_by_int32_elements(len), 0, 2),
    ];
    let base = Memory::new().with_block("arg-memory", 64);
    let called =
        base.clone()
            .with_call_memory_havoc(Variable(204), &mutable_ranges, &assumptions, None);
    let load = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(data.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let evidence = with_extended_dag_bridging(|| {
        atomic_memory_load_equality_evidence(&load(&called), &load(&base), &assumptions)
    })
    .expect("the framed load retains its call-havoc path");
    let AtomicMemoryLoadEqualityEvidence::SameCell(equality) = &evidence else {
        panic!("expected a common-cell proof");
    };
    let hop = &retained_memory_dag_path(&equality.left)[0];
    let MemoryDagHopJustification::CallHavocRanges { ranges } = &hop.justification else {
        panic!(
            "expected typed call-havoc ranges, got {:?}",
            hop.justification
        );
    };
    assert_eq!(ranges.len(), 2);
    assert!(
        matches!(&ranges[0], RangeDisjointFromPointerEvidence::ExactSeparationFact(frame) if frame.fact == separation)
    );
    assert_eq!(
        ranges[1],
        RangeDisjointFromPointerEvidence::ForwardOffset {
            offset: MachineOperandView::Legacy(&MachineTerm::Variable(Variable(203)))
                .retain(MachineIntegerType::Int32),
            positive: PositiveTermEvidence::OneLowerBound(lower_bound),
        }
    );
    assert!(evidence.is_fully_typed());
    let goal = Proposition::ConditionIs(ConditionTerm::equal(load(&called), load(&base)), true);
    assert!(evidence.checks(&goal, &assumptions));
    assert!(
        !evidence.checks(&goal, &PureFactContext::new()),
        "neither separation nor positivity may be borrowed from ambient search"
    );
    let left_offset = PointerOffsetTerm::scale_int32(load(&called), 4);
    let right_offset = PointerOffsetTerm::scale_int32(load(&base), 4);
    let offset_goal = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(left_offset.clone(), right_offset.clone()),
        true,
    );
    let offset_derivation = with_extended_dag_bridging(|| {
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &offset_goal)
    })
    .expect("pointer-offset structure retains the child load proof");
    assert!(matches!(
        &offset_derivation.rule,
        PropositionDerivationRule::ContextualAtomic {
            evidence: AtomicPropositionDerivationEvidence::PointerOffsetMemoryDag(_),
            ..
        }
    ));
    assert!(offset_derivation.check(&assumptions));
    // The state is not a certificate for another path's assumptions.
    assert!(
        !offset_derivation.check(&PureFactContext::new()),
        "pointer-offset certificate checking must also require the separation and order premises"
    );
}

/// The owned-string loadable shape: the loadability fact and its bound facts
/// write `len` as a load at contract
/// entry, while the index the goal extracts writes it at a later state
/// separated by a block declaration, stores, and a cell-forgetting prune —
/// exactly the edges (`BlockDeclared`, `CellsForgotten`) that used to leave
/// the two forms in disjoint DAG components. The loadable prover's
/// extended bridging connects them; everywhere outside that prover the new
/// edges must stay invisible (pinned by the frame-evidence test above and
/// the byte-identical check of the certified corpus).
#[test]
fn loadable_bound_check_bridges_len_forms_across_block_and_prune_edges() {
    let entry = Memory::new().with_block("arg-memory", 64);
    let len_pointer = arc_pointer(0);
    // `len` is an `int32` field. A width-less load stands in eight bytes,
    // which the neighbouring store at offset four overlaps.
    crate::kernel::eval::declare_load_access_width(&len_pointer, 4);
    let len_at_entry = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&entry),
        Box::new(len_pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );

    // The recorded facts: the buffer loadability range and both `len` bounds, all
    // written at entry.
    let assumptions = PureFactContext::new()
        // Same-block loadability ranges that cannot cover `buffer[len]`. These used
        // to trigger costly general equality searches before the matching
        // symbolic range was considered.
        .assume_proposition(Proposition::MemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(0),
            bytes: MachineTerm::constant(4),
            wide: false,
        })
        .assume_proposition(Proposition::MemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(8),
            bytes: MachineTerm::constant(4),
            wide: false,
        })
        .assume_proposition(Proposition::MemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(12),
            bytes: MachineTerm::constant(4),
            wide: false,
        })
        .assume_proposition(Proposition::MemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(16),
            bytes: MachineTerm::constant(32),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), len_at_entry.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(len_at_entry, MachineTerm::constant(8)),
            true,
        );

    // The later state: a local declared, a distinct cell written, and the
    // write-path prune that forgets it again. Its `len` load is a different
    // form of the same cell.
    let later = entry
        .clone()
        .with_block("local:i", 4)
        .store(
            arc_pointer(4),
            ProgramValue::Int32(MachineTerm::constant(9)),
        )
        .store(
            arc_pointer(8),
            ProgramValue::Int32(MachineTerm::constant(2)),
        )
        .without_possible_aliasing_cells(&arc_pointer(4), 4, &assumptions);
    let len_at_later = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&later),
        Box::new(len_pointer),
        crate::kernel::LoadKind::Int32,
    );

    // loadable(buffer[len]) with `len` written at the later state.
    let goal_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(16)),
            Box::new(PointerOffsetTerm::scaled_int32_node(len_at_later, 4)),
        ),
    };
    assert!(
        assumptions.proves_memory_loadable(&later, &goal_base, &MachineTerm::constant(4)),
        "the viewable bound check must connect the two len forms along \
         the recorded block-declaration and cell-forgetting edges"
    );
}

#[test]
fn a_store_to_the_loaded_cell_is_not_crossable() {
    // A soundness property, so it must hold with the arc switched off too.
    let base = Memory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let stored = base
        .clone()
        .store(read.clone(), ProgramValue::Int32(MachineTerm::constant(9)));

    assert!(
        !checked_memory_load_equality(&base, &stored, &read, &PureFactContext::new()),
        "the walk must refuse the very cell that was written"
    );
}

/// The premise-availability path matches two forms of one fact whose load
/// atoms carry different memory states. The match is decided by proof, not
/// by ignoring the states: an unframed call havoc between the two states
/// blocks it, and an effect summary that frames the loaded pointer restores it.
#[test]
fn conditions_equal_modulo_proven_states_needs_frame_evidence() {
    let before = Memory::new()
        .with_block("arg-memory", 8)
        .with_block("call-havoc:0", 0);
    let after = before.clone().with_block("call-havoc:1", 0);
    let loaded = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let elsewhere = Pointer {
        block: "other-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let condition = |memory: &Memory| {
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(77)),
            MachineTerm::add(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory.clone()),
                    Box::new(loaded.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::constant(1),
            ),
        )
    };

    // Same state: the two forms are literally one condition.
    assert!(
        PureFactContext::new()
            .conditions_equal_modulo_proven_states(&condition(&before), &condition(&before))
    );

    // A call havoc stands between the states and nothing frames the load,
    // so the later form is a different fact, not another form.
    assert!(
        !PureFactContext::new()
            .conditions_equal_modulo_proven_states(&condition(&before), &condition(&after)),
        "an unframed call havoc must not be matched away"
    );

    // With an effect summary whose mutable range misses the loaded pointer,
    // the two states provably agree there and the forms match.
    let effect = Proposition::MemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![MemoryRange::new(
            elsewhere,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
    };
    let (_, _, equality) = explicit_frame(
        &before,
        &after,
        &loaded,
        ProgramType::Int32,
        &[effect],
        &PureFactContext::new(),
    )
    .expect("the selected call footprint is separate");
    let source = Proposition::ConditionIs(condition(&before), true);
    let premises = vec![source, equality];
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &Proposition::ConditionIs(condition(&after), true),
            &premises,
            &facts,
        )
        .is_ok(),
        "the explicit read equality transports the compound condition"
    );

    // Framing never relaxes the structure: a different condition stays
    // different however well the states are framed.
    let other = ConditionTerm::equal(
        MachineTerm::Variable(Variable(78)),
        MachineTerm::add(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(after.clone()),
                Box::new(loaded.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::constant(1),
        ),
    );
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &Proposition::ConditionIs(other, true),
            &premises,
            &facts,
        )
        .is_err()
    );
}

/// A soundness property: load canonicalization may follow materialization
/// cells to their common source, but the jump must not erase a havoc that
/// could have written the loaded pointer. Here the loaded cell sits inside
/// the havoc's mutable range while a sibling materialization cell provably
/// survives; treating the post-havoc load as unchanged would transport a
/// stale fact across the mutation.
#[test]
fn sibling_materialization_cells_must_not_launder_a_havoc() {
    let pristine = Memory::new().with_block("arg-memory", 16);
    let loaded = arc_pointer(0);
    let sibling = arc_pointer(4);
    let materialized = pristine
        .clone()
        .store(sibling.clone(), pristine.symbolic_int32_load(&sibling));
    let havocked = materialized.clone().with_call_memory_havoc(
        Variable(9000),
        &[MemoryRange::new(
            loaded.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
        &PureFactContext::new(),
        None,
    );

    assert!(
        !checked_memory_load_equality(&materialized, &havocked, &loaded, &PureFactContext::new(),),
        "a havoc of the loaded pointer must not be laundered by sibling \
         materialization cells jumping to their common source"
    );
}

/// A load projection that jumps to the common source of the surviving
/// materialization cells keeps only the cells the projected memory itself
/// holds. A cell the source holds but a later havoc erased was written over:
/// carrying it across the jump would record the havocked cell's old value
/// in the state the load names (bounded-pool's `pool_transfer` call read
/// `source->checked_out` as its value before `pool_checkout`).
#[test]
fn a_load_projection_jump_does_not_restore_a_havocked_cell() {
    let pristine = Memory::new().with_block("arg-memory", 32);
    let loaded = symbolic_descriptor(93_000);
    let sibling = symbolic_descriptor(93_001);
    let source = pristine.clone().store(
        loaded.clone(),
        ProgramValue::Int32(MachineTerm::constant(7)),
    );
    let materialized = source
        .clone()
        .store(sibling.clone(), source.symbolic_int32_load(&sibling));
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(loaded.clone(), 0, 1))),
        right: Box::new(Resource::Memory(memory_range(sibling.clone(), 0, 1))),
    };
    let assumptions = PureFactContext::new().assume_proposition(separation);
    let havocked = materialized.with_call_memory_havoc(
        Variable(9001),
        &[memory_range(loaded.clone(), 0, 1)],
        &assumptions,
        None,
    );
    assert_eq!(
        havocked.known_value(&loaded),
        None,
        "the havoc erases the cell"
    );
    assert!(
        havocked.known_value(&sibling).is_some(),
        "the separated sibling's materialization survives the havoc"
    );
    let projected = crate::kernel::reasoning::memory_resolution::canonical_memory_for_pointer_load(
        &havocked, &loaded,
    );
    assert_eq!(
        projected.known_value(&loaded),
        None,
        "the projection must not restore the havocked cell from the source"
    );
    assert_ne!(
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_memory_ref(&havocked),
            loaded,
            crate::kernel::LoadKind::Int32,
        ),
        MachineTerm::constant(7),
        "a read of the havocked cell is not its value before the havoc"
    );
}

fn symbolic_descriptor(identity: u64) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(identity)), 4),
    }
}

/// A pointer cell holding exactly the pointer a load of that cell reads is a
/// materialization like an integer one: the cell is named at its source, so a
/// load of a neighbouring cell through the materialized state keeps the
/// name it has at the source. Only the pointer a typed load of *this* cell
/// produces qualifies: another cell's load, or the same load scaled at a
/// width other than the pointee's, is a write the load cannot pass over.
#[test]
fn a_materialized_pointer_cell_is_named_at_its_source() {
    let pristine = Memory::new().with_block("arg-memory", 32);
    // Two descriptors at unrelated symbolic addresses: nothing structural
    // separates their cells, so only the materialization rule passes over.
    let loaded = symbolic_descriptor(92_000);
    let sibling = symbolic_descriptor(92_001);
    let name = |memory: &Memory, pointer: &Pointer| {
        crate::kernel::eval::canonical_cell_load(
            crate::kernel::intern_memory_ref(memory),
            pointer.clone(),
            ProgramType::Int32Pointer,
        )
    };
    let pointer_value =
        |read: Pointer| ProgramValue::typed_pointer(read, ProgramType::Int32Pointer);
    let own = name(&pristine, &sibling);
    assert!(matches!(own, MachineTerm::MemoryLoad(..)));
    let own_read = Pointer::loaded(&own).expect("the cell's load names its read");

    let materialized = pristine
        .clone()
        .store(sibling.clone(), pointer_value(own_read.clone()));
    assert_eq!(
        name(&materialized, &loaded),
        name(&pristine, &loaded),
        "a pointer cell holding its own load is passed over"
    );

    let foreign = name(&pristine, &symbolic_descriptor(92_002));
    for (value, why) in [
        (
            pointer_value(Pointer::loaded(&foreign).expect("a load names its read")),
            "another cell's load is a real write",
        ),
        (
            pointer_value(own_read.offset_by_bytes(4)),
            "a pointer displaced from the cell's load is not that load",
        ),
    ] {
        let written = pristine.clone().store(sibling.clone(), value);
        assert_ne!(name(&written, &loaded), name(&pristine, &loaded), "{why}");
    }
}

/// The pointer form of `sibling_materialization_cells_must_not_launder_a_havoc`:
/// a materialized pointer cell that survives a havoc must not carry a load
/// the havoc may have written back to the pre-havoc state.
#[test]
fn a_materialized_pointer_cell_must_not_launder_a_havoc() {
    let pristine = Memory::new().with_block("arg-memory", 32);
    let loaded = symbolic_descriptor(92_010);
    let sibling = symbolic_descriptor(92_011);
    let own = crate::kernel::eval::canonical_form_of_load(
        crate::kernel::intern_memory_ref(&pristine),
        sibling.clone(),
        crate::kernel::LoadKind::Int32,
    );
    let materialized = pristine.clone().store(
        sibling.clone(),
        ProgramValue::typed_pointer(
            Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(own, 4),
            },
            ProgramType::Int32Pointer,
        ),
    );
    let havocked = materialized.clone().with_call_memory_havoc(
        Variable(9001),
        &[MemoryRange::new(
            loaded.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
        &PureFactContext::new(),
        None,
    );
    assert!(
        !checked_memory_load_equality(&materialized, &havocked, &loaded, &PureFactContext::new()),
        "a havoc of the loaded pointer must not be laundered by a materialized pointer cell"
    );
}

// --- store edge: frozen-context crossing ---------------------------------
// A store at a symbolic index keeps every cell a strict order recorded in
// the transition's context separates from the written one: the naming walk
// crosses the edge by that frozen context through one indexed lookup, never
// by reasoning. `CallHavoc` crosses by the same mechanism for ranges.

fn symbolic_element_pointer(index: &MachineTerm) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(91_000)), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    }
}

#[test]
fn a_symbolic_store_requires_the_current_paths_separation_order() {
    let index = MachineTerm::Variable(Variable(91_001));
    let length = MachineTerm::Variable(Variable(91_002));
    let written = symbolic_element_pointer(&index);
    let kept = symbolic_element_pointer(&length);
    // `kept` is never materialized: the observable is the canonical form of
    // its load, which only a crossed store edge keeps at the base state.
    let base = Memory::new().with_block("arg-memory", 64);
    let ordered = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(index.clone(), length.clone()),
        true,
    );

    let separated = base
        .clone()
        .store_with_context(written.clone(), int32(7), &ordered);
    let load = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(kept.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let evidence = with_extended_dag_bridging(|| {
        atomic_memory_load_equality_evidence(&load(&separated), &load(&base), &ordered)
    })
    .expect("the current path's strict order proves preservation");
    let goal = Proposition::ConditionIs(ConditionTerm::equal(load(&separated), load(&base)), true);
    assert!(evidence.checks(&goal, &ordered));
    assert!(!evidence.checks(&goal, &PureFactContext::new()));

    // Equal stored values must not import another path's order through the
    // arena's first-wins derivation. Keep the exact same endpoint shape.
    let unordered = base
        .clone()
        .store_with_context(written, int32(7), &PureFactContext::new());
    assert_ne!(
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_memory_ref(&unordered),
            kept.clone(),
            crate::kernel::LoadKind::Int32
        ),
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_memory_ref(&base),
            kept,
            crate::kernel::LoadKind::Int32
        ),
        "without a recorded order the write may alias the loaded cell"
    );
}

#[test]
fn direct_strict_order_is_an_indexed_lookup() {
    let a = MachineTerm::Variable(Variable(91_101));
    let b = MachineTerm::Variable(Variable(91_102));
    let c = MachineTerm::Variable(Variable(91_103));
    let context = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(a.clone(), b.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(b.clone(), c.clone()), true);
    assert!(context.direct_strict_order_recorded(&a, &b));
    assert!(context.direct_strict_order_recorded(&b, &a));
    assert!(
        !context.direct_strict_order_recorded(&b, &c),
        "a non-strict bound does not separate the terms"
    );
    assert!(
        !context.direct_strict_order_recorded(&a, &c),
        "the lookup is direct: no chaining through `b`"
    );
}

/// Canonicalization has no depth cut: its explicit worklist reaches a
/// materialized cell however deeply the load sits in the term, with work
/// linear in the term it traverses.
#[test]
fn canonical_form_resolves_loads_at_any_depth() {
    let memory = Memory::new().with_block("arg-memory", 16).store(
        arc_pointer(4),
        ProgramValue::Int32(MachineTerm::constant(7)),
    );
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory),
        Box::new(arc_pointer(4)),
        crate::kernel::LoadKind::Int32,
    );
    let mut samples = Vec::new();
    for depth in [64, 128, 256, 512] {
        let mut term = load.clone();
        for _ in 0..depth {
            term = binary_node!(
                Int32,
                Add,
                Box::new(term),
                Box::new(MachineTerm::constant(1))
            );
        }
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        crate::kernel::memory_provenance::reset_atomic_canonicalization_term_visits();
        let canonical = crate::kernel::api::canonicalize_atomic_loads(&term);
        let visits = crate::kernel::memory_provenance::atomic_canonicalization_term_visits();
        assert!(
            visits <= 2 * depth + 2,
            "canonicalization should visit each explicit term node once: depth={depth}, visits={visits}",
        );
        let mut leaf = &canonical;
        while let binary_term!(Int32, Add, left, _) = leaf {
            leaf = left;
        }
        assert_eq!(
            leaf,
            &MachineTerm::constant(7),
            "the load at depth {depth} should resolve to its cell"
        );
        samples.push((depth, visits));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 9,
        "eight times the term depth must take near-linear work: {samples:?}",
    );
}

/// A call havoc that provably missed a materialized cell must not rename the
/// cell's load.
///
/// The naming walk behind a load variable is assumption-free, so it stops at
/// a call-havoc edge whose write set is separated from the cell only by an
/// explicit `separate` premise. The retained cell is what carries the answer
/// across: the havoc kept it precisely because the premise proved the write
/// set disjoint, so the load resolves through the cell to the variable that
/// already names this value. Without that, a function pointer read out of a
/// table after one call through it loses the contract established for it
/// (`mdtests/rb_augment_callbacks_helper_owns.md`).
#[test]
fn a_retained_cell_keeps_its_load_variable_across_a_call_havoc() {
    let cell = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(88_002)), 4),
    };
    let written = memory_range(
        Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(88_001)), 4),
        },
        0,
        2,
    );
    let separated = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(written.clone())),
        right: Box::new(Resource::Memory(memory_range(cell.clone(), 0, 2))),
    });

    let load_in = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(cell.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let base = Memory::new().with_block("arg-memory", 64);
    let (name, _) = load_variable_for_term(&load_in(&base)).expect("a load term has a name");
    // Materializing a viewed cell records its own load variable in the cell,
    // which is the state the callback fixtures reach before their first call.
    let materialized = base.store(
        cell.clone(),
        ProgramValue::Int32(MachineTerm::Variable(name)),
    );

    let retained = materialized.clone().with_call_memory_havoc(
        Variable(88_100),
        std::slice::from_ref(&written),
        &separated,
        None,
    );
    assert!(
        retained.cells.contains_key(&cell),
        "the separation premise is what keeps this cell across the havoc"
    );
    assert_eq!(
        load_variable_for_term(&load_in(&retained))
            .expect("a load term has a name")
            .0,
        name,
        "a retained cell names the same load after the call as before it"
    );

    // The premise is load-bearing: with nothing separating the write set from
    // the cell, the havoc forgets it and the reload is a different value.
    let forgotten = materialized.with_call_memory_havoc(
        Variable(88_101),
        std::slice::from_ref(&written),
        &PureFactContext::new(),
        None,
    );
    assert!(!forgotten.cells.contains_key(&cell));
    assert_ne!(
        load_variable_for_term(&load_in(&forgotten))
            .expect("a load term has a name")
            .0,
        name,
        "a forgotten cell must not keep the name of the value it held"
    );
}

/// The epoch an array argument names is bounded by the kernel's separation
/// rule, not by whether two blocks are spelled differently. `arg-memory` and
/// `global:g` are both fully known identities that differ, and a caller may
/// still pass `g` as the argument, so the store to `g` has to stop the walk.
/// A store to one of the function's own locals, or to another global when the
/// subject is a global, is proven distinct and still crosses.
#[test]
fn an_array_refs_epoch_stops_at_a_store_that_may_alias_it() {
    let at = |block: PointerBlock, offset: i64| Pointer {
        block,
        offset: PointerOffsetTerm::Constant(offset),
    };
    let global = || PointerBlock::Concrete("global:g".to_string());
    let other_global = || PointerBlock::Concrete("global:h".to_string());
    let local = || PointerBlock::Concrete("local:f:i".to_string());
    let one = || ProgramValue::Int32(MachineTerm::constant(1));
    let epoch = |memory: &Memory, block: PointerBlock| {
        crate::kernel::resource_tracker::last_same_version_point(
            crate::kernel::resource_tracker::TrackedResource::Block(&block),
            &crate::kernel::resource_tracker::VersionPoint::at(&crate::kernel::intern_memory(
                memory.clone(),
            )),
        )
        .expect("a block always has a last-same point")
        .memory()
        .clone()
    };

    // Declaring an object writes nothing, and a declaration proven distinct
    // from the subject is crossed too, so an epoch reaches back past the
    // declarations that precede it. The assertions below name the state the
    // walk actually reaches rather than "the entry state".
    let just_g = Memory::new().with_block(global(), 16);
    let globals = just_g.clone().with_block(other_global(), 16);
    let entry = globals.clone().with_block(local(), 4);

    // The hole this closes: `g` may be the array the caller passed as `a`.
    let after_global_store = entry.clone().store(at(global(), 0), one());
    assert_eq!(
        epoch(&after_global_store, PointerBlock::ExternalArgument),
        after_global_store,
        "a store to a global may write the array argument, so the epoch is the live state"
    );
    // The same for the opaque object identity a parameter can carry.
    assert_eq!(
        epoch(
            &after_global_store,
            PointerBlock::ExternalObject(Variable(5))
        ),
        after_global_store
    );

    // A function's own local is storage it declared, so memory reached
    // through a parameter is not it and the fact survives the step.
    let after_local_store = entry.clone().store(at(local(), 0), one());
    assert_eq!(
        epoch(&after_local_store, PointerBlock::ExternalArgument),
        globals,
        "a store to a local, and the local's own declaration, cannot touch an array argument"
    );

    // Two file-scope declarations are two objects.
    assert_eq!(
        epoch(&entry.clone().store(at(other_global(), 0), one()), global()),
        just_g,
        "a store to another global cannot touch this one, and neither can either \
         declaration that follows this one's"
    );
    // A store into the subject's own block always stops the walk.
    assert_eq!(
        epoch(&after_global_store, global()),
        after_global_store,
        "a store into the subject's own block is exactly what the epoch must see"
    );

    // A symbolic write target may be any object, and a symbolic subject is
    // separated from nothing, so neither crosses.
    let after_symbolic_store = entry.store(at(PointerBlock::Symbolic(Variable(77)), 0), one());
    assert_eq!(
        epoch(&after_symbolic_store, PointerBlock::ExternalArgument),
        after_symbolic_store
    );
    assert_eq!(
        epoch(&after_local_store, PointerBlock::Symbolic(Variable(77))),
        after_local_store
    );
}

/// The block-epoch memo is keyed by interned state, and interning dedups
/// by content, so an entry left behind by one verification would answer a
/// content-equal query in the next one — from a DAG history that
/// verification never built. `VerificationSession` clears it with the other
/// canonical-form caches, which is what keeps a result from depending on
/// what was verified earlier in the process.
#[test]
fn a_session_reset_empties_the_block_epoch_memo() {
    let memory = Memory::new()
        .with_block(PointerBlock::Concrete("local:f:i".to_string()), 4)
        .store(
            Pointer {
                block: PointerBlock::Concrete("local:f:i".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
    crate::kernel::resource_tracker::last_same_version_point(
        crate::kernel::resource_tracker::TrackedResource::Block(&PointerBlock::ExternalArgument),
        &crate::kernel::resource_tracker::VersionPoint::at(&crate::kernel::intern_memory(memory)),
    );
    assert!(
        crate::kernel::resource_tracker::block_version_memo_len() > 0,
        "the walk should have recorded its epoch"
    );

    crate::kernel::memory_provenance::clear_canonical_form_caches();
    assert_eq!(
        crate::kernel::resource_tracker::block_version_memo_len(),
        0,
        "a session reset must not leave one verification's epochs for the next"
    );
}

/// A store forgets every cell whose bytes it overwrites, not only the cell at
/// its own address. Both widths are exact here — the store's from the value it
/// writes, the cell's from the value it holds — so the cells that survive are
/// the ones the written bytes provably miss.
///
/// Without this, a one-byte write four bytes into an `int64` cell left the
/// whole `int64` readable at its old value, because `p + 4` is a different
/// address from `p` by every address-separation test there is.
#[test]
fn a_store_forgets_the_wider_cell_whose_bytes_it_overwrites() {
    let bare = PureFactContext::new();
    let wide = Memory::new().with_block("arg-memory", 32).store(
        arc_pointer(0),
        ProgramValue::Int64(MachineTerm::int64_constant(5)),
    );

    // Above the base, where the address test alone says "separate": the
    // int64 must still be gone, and nothing takes its place.
    for offset in 1..8 {
        let after = wide
            .clone()
            .without_possible_aliasing_cells(&arc_pointer(offset), 1, &bare)
            .store(arc_pointer(offset), crate::kernel::uint8(7));
        assert_eq!(
            after.known_value(&arc_pointer(0)),
            None,
            "a one-byte write {offset} bytes into an int64 cell overwrites \
             part of it, so the int64 must not stay readable"
        );
    }
    // At the base itself the write replaces the cell, so what is readable
    // there is the byte just written and not the int64.
    let after = wide
        .clone()
        .without_possible_aliasing_cells(&arc_pointer(0), 1, &bare)
        .store(arc_pointer(0), crate::kernel::uint8(7));
    assert_eq!(
        after.known_value(&arc_pointer(0)),
        Some(crate::kernel::uint8(7)),
        "a one-byte write at the base leaves its own byte, not the int64"
    );

    // Outside the cell's own bytes, the cell stays: this is what makes the
    // forgetting worth doing rather than dropping every cell on every store.
    let after = wide
        .clone()
        .without_possible_aliasing_cells(&arc_pointer(8), 1, &bare)
        .store(arc_pointer(8), crate::kernel::uint8(7));
    assert_eq!(
        after.known_value(&arc_pointer(0)),
        Some(ProgramValue::Int64(MachineTerm::int64_constant(5))),
        "a write past the int64's last byte leaves it readable"
    );

    // The symmetric direction: a wide write over the narrow cells it covers.
    let narrow = Memory::new()
        .with_block("arg-memory", 32)
        .store(
            arc_pointer(0),
            ProgramValue::Int32(MachineTerm::constant(1)),
        )
        .store(
            arc_pointer(4),
            ProgramValue::Int32(MachineTerm::constant(2)),
        )
        .store(
            arc_pointer(8),
            ProgramValue::Int32(MachineTerm::constant(3)),
        );
    let after = narrow
        .without_possible_aliasing_cells(&arc_pointer(0), 8, &bare)
        .store(
            arc_pointer(0),
            ProgramValue::Int64(MachineTerm::int64_constant(9)),
        );
    assert_eq!(
        after.known_value(&arc_pointer(4)),
        None,
        "an eight-byte write at the base overwrites the int32 four bytes up"
    );
    assert_eq!(
        after.known_value(&arc_pointer(8)),
        Some(ProgramValue::Int32(MachineTerm::constant(3))),
        "an eight-byte write at the base stops before the int32 eight bytes up"
    );
}

/// Canonicalization for a load drops a cell it decides the load cannot
/// observe, which makes two states compare equal at that load. The
/// interval it decides that by has to admit the widest load the kernel
/// performs, because the `MemoryLoad` term it is answering for carries no
/// width of its own.
///
/// Both polarities, over the widths that meet at one address: a cell four
/// bytes above the load is inside an eight-byte read and must survive, and a
/// cell eight bytes above it is outside every scalar read and may go.
#[test]
fn canonical_load_form_keeps_a_cell_a_wide_read_covers() {
    let base = Memory::new().with_block("arg-memory", 32);
    let read = arc_pointer(0);
    let canonical_equal_across_store_at = |offset: i64, value: ProgramValue| {
        let stored = base.clone().store(arc_pointer(offset), value);
        crate::kernel::reasoning::canonical_memory_for_pointer_load(&base, &read)
            == crate::kernel::reasoning::canonical_memory_for_pointer_load(&stored, &read)
    };

    // Inside the widest scalar read at `read`: every one of these cells is a
    // byte a sixteen-byte load of `read` returns.
    for offset in 1..16 {
        assert!(
            !canonical_equal_across_store_at(offset, crate::kernel::uint8(7)),
            "a one-byte cell {offset} bytes above the load is inside an \
             sixteen-byte read of it and must not be dropped"
        );
    }
    assert!(
        !canonical_equal_across_store_at(4, ProgramValue::Int32(MachineTerm::constant(7))),
        "an int32 cell four bytes above the load is inside a \
         sixteen-byte read of it and must not be dropped"
    );
    assert!(
        !canonical_equal_across_store_at(6, crate::kernel::int16(7)),
        "an int16 cell six bytes above the load is inside an eight-byte read"
    );
    assert!(
        !canonical_equal_across_store_at(0, ProgramValue::Int64(MachineTerm::int64_constant(7))),
        "a cell at the loaded pointer itself is never disjoint from the load"
    );

    // Below the load: the cell's own width decides, and it is known exactly.
    assert!(
        canonical_equal_across_store_at(-1, crate::kernel::uint8(7)),
        "a one-byte cell one byte below the load ends where the load starts"
    );
    assert!(
        !canonical_equal_across_store_at(-4, ProgramValue::Int64(MachineTerm::int64_constant(7))),
        "an int64 cell four bytes below the load covers the load's first four \
         bytes and must not be dropped"
    );
    assert!(
        canonical_equal_across_store_at(-8, ProgramValue::Int64(MachineTerm::int64_constant(7))),
        "an int64 cell eight bytes below the load ends where the load starts"
    );
    assert!(
        !canonical_equal_across_store_at(
            -4,
            ProgramValue::Pointer(PointerValue::new(arc_pointer(0), ProgramType::Int32Pointer))
        ),
        "a stored pointer is eight bytes, so one four bytes below the load \
         covers the load's first four bytes"
    );

    // Eight bytes remains inside an unknown read; sixteen is outside every
    // scalar read and may be dropped.
    assert!(
        !canonical_equal_across_store_at(8, ProgramValue::Int32(MachineTerm::constant(7))),
        "a cell eight bytes above an unknown load is still inside its maximum width"
    );
    assert!(
        canonical_equal_across_store_at(16, crate::kernel::uint8(7)),
        "a cell well above the load is outside every scalar read"
    );
}

/// Two states a store separates do not agree about a load whose bytes it
/// wrote, however clean the two addresses look.
///
/// "Do these states hold one value for this load" is answered by scanning
/// the cells they differ on and asking whether each is separate from the
/// load. That question used to be asked of the *addresses* alone, and `p + 1`
/// is a different address from `p` under every test the kernel has while
/// holding the second byte a four-byte read at `p` returns. With the address
/// answer standing in for the byte answer, an `unsigned char` write one byte
/// into an `int32` left the whole `int32` readable at its old value.
///
/// Both directions are pinned: a write the read's bytes cover blocks the
/// agreement, and one past its last byte still does not.
#[test]
fn a_store_inside_a_read_stops_two_states_agreeing_about_it() {
    let bare = PureFactContext::new();
    let read = arc_pointer(0);
    crate::kernel::eval::declare_load_access_width(&read, 4);
    let base = Memory::new().with_block("arg-memory", 32);
    let byte_written_at = |offset: i64| {
        base.clone()
            .without_possible_aliasing_cells(&arc_pointer(offset), 1, &bare)
            .store(arc_pointer(offset), crate::kernel::uint8(7))
    };

    for offset in 1..4 {
        let after = byte_written_at(offset);
        assert!(
            !crate::kernel::reasoning::memory_states_proven_equal_at_pointer(
                &base, &after, &read, &bare
            ),
            "a one-byte write {offset} bytes into a four-byte read is a byte the read \
             returns, so the two states do not agree about it"
        );
    }

    let after = byte_written_at(4);
    assert!(
        crate::kernel::reasoning::memory_states_proven_equal_at_pointer(
            &base, &after, &read, &bare
        ),
        "a write past the read's last byte leaves the two states agreeing about it"
    );
}

/// A recorded store inside a read refutes the equality of the two loads
/// around it, at every offset its bytes reach, whatever the states kept.
///
/// This is the rule the state comparisons and the canonical-form
/// comparison now answer to. Both are read from *state*: a cell map records
/// what is known at a point, and a canonical form drops what it can prove
/// irrelevant. Neither records that a store happened, and a store into the
/// middle of a cell drops the cell it partly overwrites, so the two
/// states around it can be identical where it is concerned. The recorded
/// history has the store either way, and one walk over it is all three
/// routes' answer.
///
/// The sweep is the whole width of each access: a one-byte write at any
/// offset a four-byte read covers, and at any offset an eight-byte read
/// covers, is a byte that read returns. The offset one past the last is the
/// negative control, and it must stay unrefuted — that is the adjacent
/// element every framing proof in the corpus rests on.
#[test]
fn a_store_inside_a_read_refutes_the_load_equality_at_every_offset() {
    let bare = PureFactContext::new();
    for (block, read_bytes) in [("narrow-arg-memory", 4u32), ("wide-arg-memory", 8u32)] {
        let read = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        crate::kernel::eval::declare_load_access_width(&read, read_bytes);
        let base = Memory::new().with_block(block, 32);
        let byte_written_at = |offset: i64| {
            let write = Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(offset),
            };
            base.clone()
                .without_possible_aliasing_cells(&write, 1, &bare)
                .store(write, crate::kernel::uint8(7))
        };
        let history_about = |after: &Memory| {
            crate::kernel::memory_provenance::recorded_load_history(
                &crate::kernel::intern_memory_ref(&base),
                &crate::kernel::intern_memory_ref(after),
                &read,
                crate::kernel::LoadKind::Int32,
                &bare,
            )
        };
        let load_in = |memory: &Memory| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(read.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };

        for offset in 1..i64::from(read_bytes) {
            let after = byte_written_at(offset);
            assert_eq!(
                with_extended_dag_bridging(|| history_about(&after)),
                crate::kernel::memory_provenance::LoadHistory::DifferentVersions,
                "a one-byte write {offset} bytes into a {read_bytes}-byte read is a byte that \
                 read returns, so the history holds two versions of the cell"
            );
            assert_eq!(
                with_extended_dag_bridging(|| history_about(&after)),
                crate::kernel::memory_provenance::LoadHistory::DifferentVersions,
                "the memoized answer to the repeated question is the same answer"
            );
            assert!(
                !crate::kernel::reasoning::memory_states_proven_equal_at_pointer(
                    &base, &after, &read, &bare
                ),
                "the state comparison answers to that history"
            );
            assert!(
                !bare.proves_atomic_without_search(&Proposition::ConditionIs(
                    ConditionTerm::equal(load_in(&base), load_in(&after)),
                    true
                )),
                "the canonical-form comparison answers to that history"
            );
        }

        let past_the_end = byte_written_at(i64::from(read_bytes));
        assert_ne!(
            with_extended_dag_bridging(|| history_about(&past_the_end)),
            crate::kernel::memory_provenance::LoadHistory::DifferentVersions,
            "a write past the read's last byte writes none of its bytes"
        );
        assert!(
            crate::kernel::reasoning::memory_states_proven_equal_at_pointer(
                &base,
                &past_the_end,
                &read,
                &bare
            ),
            "and the two states still agree about the read"
        );
    }
}

/// The gate the load-side distinct-cell reduction now applies before dropping
/// a cell: dropping it names the load at a state that no longer records it,
/// so the cell's bytes have to miss the read. The reduction had only
/// `pointers_proven_distinct_for_memory_resolution`, which is about addresses.
#[test]
fn a_cell_clears_a_read_only_outside_its_bytes() {
    use crate::kernel::reasoning::memory_resolution::{AccessByteOverlap, access_byte_overlap};

    let bare = PureFactContext::new();
    let at = |offset: i64| Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let read = at(0);
    for read_bytes in [4u32, 8] {
        for cell_bytes in [1u32, 4, 8] {
            for offset in -8..=8i64 {
                let separate =
                    access_byte_overlap(&at(offset), cell_bytes, &read, read_bytes, &bare)
                        == AccessByteOverlap::Separate;
                let overlaps = offset < i64::from(read_bytes) && -offset < i64::from(cell_bytes);
                assert_eq!(
                    separate, !overlaps,
                    "a {cell_bytes}-byte cell {offset} bytes from a {read_bytes}-byte read"
                );
            }
        }
    }
}

/// The same exact byte test at anchors the 32-bit byte rebuild cannot spell:
/// an `int64` scaled index and an opaque offset variable, each with constant
/// displacements on both sides, and constants beyond the int32 range. The gap
/// is the difference of the constants, exactly, so every offset from -16 to
/// 16 is decided as the plain constant case decides it.
#[test]
fn an_exact_constant_gap_decides_bytes_at_every_anchor() {
    use crate::kernel::reasoning::memory_resolution::{AccessByteOverlap, access_byte_overlap};

    let bare = PureFactContext::new();
    let anchors = [
        PointerOffsetTerm::scaled_int64_node(MachineTerm::Variable(Variable(97_101)), 8, false),
        PointerOffsetTerm::Variable(Variable(97_102)),
        PointerOffsetTerm::Constant(1 << 40),
    ];
    let at = |anchor: &PointerOffsetTerm, shift: i64| Pointer {
        block: "wide-anchor-memory".into(),
        offset: PointerOffsetTerm::Add(
            Box::new(anchor.clone()),
            Box::new(PointerOffsetTerm::Constant(shift)),
        ),
    };
    for anchor in &anchors {
        for (write_bytes, read_bytes) in [(1u32, 8u32), (4, 4), (8, 8), (8, 1)] {
            for shift in -16..=16i64 {
                let decided = access_byte_overlap(
                    &at(anchor, 8 + shift),
                    write_bytes,
                    &at(anchor, 8),
                    read_bytes,
                    &bare,
                );
                let overlaps = shift < i64::from(read_bytes) && -shift < i64::from(write_bytes);
                let expected = if overlaps {
                    AccessByteOverlap::Overlaps
                } else {
                    AccessByteOverlap::Separate
                };
                assert_eq!(
                    decided, expected,
                    "{write_bytes} bytes at {shift} from {read_bytes} at {anchor:?}"
                );
            }
        }
    }
    // A constant beyond the int32 range is not its low word: 2^32 bytes
    // apart is apart, where the wrapped distance was zero.
    let far = Pointer {
        block: "wide-anchor-memory".into(),
        offset: PointerOffsetTerm::Constant(1 << 32),
    };
    let near = Pointer {
        block: "wide-anchor-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert_eq!(
        access_byte_overlap(&far, 8, &near, 8, &bare),
        AccessByteOverlap::Separate
    );
}

/// Where the gap is not an exact constant, only its stride decides. Two
/// different `int64` indices of eight-byte elements are a nonzero multiple
/// of eight apart, which clears two eight-byte accesses once their addresses
/// differ; two indices of different element widths share only the smaller
/// stride, which clears nothing wider. An `int32` index `i + 1` is one
/// element past `i` only when that addition does not wrap, so the summand is
/// compared whole rather than split into `i` plus one element.
#[test]
fn a_gap_that_may_wrap_or_differ_is_not_decided() {
    use crate::kernel::reasoning::memory_resolution::{AccessByteOverlap, access_byte_overlap};

    let bare = PureFactContext::new();
    let block = "wrap-anchor-memory";
    let scaled64 = |id: u64, byte_width: i64| {
        PointerOffsetTerm::scaled_int64_node(MachineTerm::Variable(Variable(id)), byte_width, false)
    };
    let pointer = |offset: PointerOffsetTerm| Pointer {
        block: block.into(),
        offset,
    };
    assert_eq!(
        access_byte_overlap(
            &pointer(scaled64(97_201, 8)),
            8,
            &pointer(scaled64(97_202, 8)),
            8,
            &bare
        ),
        AccessByteOverlap::Separate
    );
    assert_eq!(
        access_byte_overlap(
            &pointer(scaled64(97_201, 8)),
            8,
            &pointer(scaled64(97_202, 4)),
            8,
            &bare
        ),
        AccessByteOverlap::Unknown
    );
    let i = MachineTerm::Variable(Variable(97_203));
    let next = pointer(PointerOffsetTerm::scaled_int32_node(
        MachineTerm::add(i.clone(), MachineTerm::constant(1)),
        4,
    ));
    let beside = pointer(PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::scaled_int32_node(i, 4)),
        Box::new(PointerOffsetTerm::Constant(2)),
    ));
    // `i + 1` sits 4 bytes past `i` when it does not wrap, so a 4-byte access
    // two bytes past `i` overlaps it then; wrapped, the two are 2^34 bytes
    // apart. Neither answer may be given for both.
    assert_ne!(
        access_byte_overlap(&next, 4, &beside, 4, &bare),
        AccessByteOverlap::Separate
    );
}

/// Two states that differ on a cell inside a read do not hold one value for
/// it. `memories_directly_match_for_pointer_load` decided each differing cell
/// from the two *addresses* — a constant nonzero byte offset was enough — and
/// an address is not the question: a four-byte cell at `q + 4` is a different
/// address from `q` under every test the kernel has while holding the upper
/// half of an eight-byte read there.
#[test]
fn a_differing_cell_inside_a_read_stops_the_two_states_matching() {
    let bare = PureFactContext::new();
    for (block, read_bytes) in [("narrow-cell-memory", 4u32), ("wide-cell-memory", 8)] {
        let read = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        crate::kernel::eval::declare_load_access_width(&read, read_bytes);
        let base = Memory::new().with_block(block, 32);
        let cell_holding = |offset: i64, value: u32| {
            base.clone().store(
                Pointer {
                    block: block.into(),
                    offset: PointerOffsetTerm::Constant(offset),
                },
                crate::kernel::uint8(value),
            )
        };
        for offset in 1..i64::from(read_bytes) {
            assert!(
                !crate::kernel::memory_provenance::memories_directly_match_for_pointer_load(
                    &cell_holding(offset, 1),
                    &cell_holding(offset, 2),
                    &read,
                    &bare,
                ),
                "a cell {offset} bytes into a {read_bytes}-byte read is a byte that read \
                 returns, so the two states do not hold one value for it"
            );
        }
        assert!(
            crate::kernel::memory_provenance::memories_directly_match_for_pointer_load(
                &cell_holding(i64::from(read_bytes), 1),
                &cell_holding(i64::from(read_bytes), 2),
                &read,
                &bare,
            ),
            "a cell past the read's last byte holds none of its bytes"
        );
    }
}

/// A contract call that leaves allocation continuity undecided records a
/// `ContractAllocationRetired` edge right after its own `CallHavoc`. When one
/// havoc range covers the whole retired allocation, the retirement is
/// transparent to a cell's value: an unrelated cell is named where the call
/// left it, and a cell of the allocation still stops at the havoc, never at a
/// value from before the call. A retirement the havoc does not cover, or one
/// separated from the havoc by another edge, still stops every cell it
/// shares a block with.
#[test]
fn a_retirement_inside_its_calls_havoc_names_cells_at_the_call() {
    let pointer = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    };
    let owner = pointer(211);
    let data = pointer(212);
    let int32_range = |base: &Pointer| {
        MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
            4,
        )
    };
    let ranges = vec![int32_range(&owner), int32_range(&data)];
    let assumptions = PureFactContext::new();
    let named = |memory: &Memory, cell: &Pointer| {
        crate::kernel::resource_tracker::last_same_version_point(
            crate::kernel::resource_tracker::TrackedResource::Cell {
                pointer: cell,
                bytes: 4,
            },
            &crate::kernel::resource_tracker::VersionPoint::at(&intern_memory_ref(memory)),
        )
        .map(|point| point.shared_memory().clone())
    };
    // The allocation's claim is live before the call, so retiring it changes
    // the state and records the edge.
    let havoc = |variable| {
        Memory::new()
            .with_heap_allocation_claim(data.clone(), HeapExtent::int32(4))
            .expect("a fresh claim")
            .with_call_memory_havoc(Variable(variable), &ranges, &assumptions, None)
    };

    let called = havoc(213);
    let retired = called.clone().retire_contract_heap_allocation_claim(
        &data,
        &MachineTerm::constant(4),
        &assumptions,
    );
    assert_eq!(named(&retired, &owner), Some(intern_memory_ref(&called)));
    assert_eq!(
        named(&retired, &data),
        Some(intern_memory_ref(&called)),
        "a byte of the retired allocation is named by the call's own havoc"
    );
    let cell = with_extended_dag_bridging(|| {
        memory_dag_cell_source(&intern_memory_ref(&retired), &owner, 4, &assumptions, false)
    })
    .expect("the walk has an answer");
    // The bounded check records the retirement's actual rule, even when
    // the history lookup above has already warmed a version summary.
    assert!(matches!(
        retained_memory_dag_path(&cell)[0].justification,
        MemoryDagHopJustification::RetirementInsideItsCallHavoc
    ));
    let retired_state = intern_memory_ref(&retired);
    let derivation = retired_state.derivation().expect("the retirement edge");
    let crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
        crate::kernel::resource_tracker::step_effect::Separation::Cell(justification),
    ) = with_extended_dag_bridging(|| {
        crate::kernel::resource_tracker::step_effect::affects(
            &derivation,
            &retired_state,
            crate::kernel::resource_tracker::TrackedResource::Cell {
                pointer: &owner,
                bytes: 4,
            },
            &crate::kernel::resource_tracker::step_effect::Evidence {
                assumptions: &assumptions,
                cross_loop_havoc: false,
            },
        )
    })
    else {
        panic!("the retirement inside its call's havoc is separate from the owner cell");
    };
    assert_eq!(
        justification,
        MemoryDagHopJustification::RetirementInsideItsCallHavoc
    );
    assert!(justification.checks(&derivation, &owner, 4, &assumptions));

    // The havoc covers four bytes of an eight-byte allocation.
    let called = havoc(214);
    let wider = called.clone().retire_contract_heap_allocation_claim(
        &data,
        &MachineTerm::constant(8),
        &assumptions,
    );
    assert_eq!(named(&wider, &owner), Some(intern_memory_ref(&wider)));

    // Another edge stands between the havoc and the retirement.
    let declared = havoc(215).with_block("arg-memory", 4);
    let separated = declared.clone().retire_contract_heap_allocation_claim(
        &data,
        &MachineTerm::constant(4),
        &assumptions,
    );
    assert_eq!(
        named(&separated, &owner),
        Some(intern_memory_ref(&separated))
    );
}

/// A disjoint call preserves the cell's version. Constant normalization
/// reads the established relation without searching pairs of load states,
/// both for the read and for a value explicitly equated to it.
#[test]
fn constant_normalization_bridges_a_load_across_a_call() {
    let base = Memory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let load_in = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let after_call = base.clone().with_call_memory_havoc(
        Variable(930_101),
        &[memory_range(arc_pointer(8), 0, 8)],
        &PureFactContext::new(),
        None,
    );
    let copy = MachineTerm::Variable(Variable(930_102));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(load_in(&base), MachineTerm::constant(5)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(copy.clone(), load_in(&after_call)),
            true,
        );

    assert_eq!(
        assumptions.known_signed_constant_after_normalization(&load_in(&after_call)),
        Some(5),
        "the post-call load is proved equal to the pinned pre-call load"
    );
    assert_eq!(
        assumptions.known_signed_constant_after_normalization(&copy),
        Some(5),
        "a term equal to the post-call load reaches the constant through it"
    );
    assert_eq!(
        assumptions.known_signed_constant_after_normalization(&MachineTerm::add(copy, 1u32.into())),
        Some(6),
        "an unrecorded sum folds from its bridged operand"
    );
}

fn seeded_pointer_read_context(
    old: &SharedMemory,
    current: &SharedMemory,
    address: &Pointer,
    alias: &Pointer,
) -> (PureFactContext, Pointer, Pointer) {
    let context = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(address.clone(), alias.clone()),
        true,
    );
    let left = Pointer::loaded_value(old, alias);
    let right = Pointer::loaded_value(current, address);
    context
        .equality_graph
        .register_pointer_read_definition(&left, old, alias);
    context
        .equality_graph
        .register_pointer_read_definition(&right, current, address);
    assert!(!context.pointers_known_equal(&left, &right));
    (context, left, right)
}

#[test]
fn seeded_pointer_read_evidence_is_local_full_width_and_retargeting_safe() {
    let a = Pointer::symbolic(Variable(98_300));
    let b = Pointer::symbolic(Variable(98_301));
    let old = intern_memory(Memory::new());
    let seeded = old
        .memory()
        .clone()
        .store(a.offset_by_bytes(32), int32(1))
        .with_seeded_cells(a.clone(), 4, ProgramType::Int32, 0, 2, old.clone());
    let current = intern_memory(seeded);
    let (context, left, right) = seeded_pointer_read_context(&old, &current, &a, &b);
    let sibling = context.clone();
    let branch = context.clone();
    let _scope = branch.enter_id_scope();
    assert!(!pointers_proven_equal_for_memory_resolution(
        &left, &right, &branch
    ));
    branch.register_pointer_read(&right, &current, &a);
    assert!(branch.pointers_known_equal(&left, &right));
    assert!(pointers_proven_equal_for_memory_resolution(
        &left, &right, &branch
    ));
    assert!(!sibling.pointers_known_equal(&left, &right));
    assert!(!context.pointers_known_equal(&left, &right));
    assert_eq!(branch.pure_facts().len(), context.pure_facts().len());
    assert!(!ResourceContext::new().permits_memory_read(&right, 8, &branch));
    // Footprint lookup cannot be retargeted to the second half of the slot.
    let derivation = current.derivation().unwrap();
    let MemoryDerivation::CellsSeeded { run, .. } = derivation.as_ref() else {
        panic!("seed edge");
    };
    assert!(run.read_source(&a.offset_by_bytes(4), 8).is_none());
}

#[test]
fn seeded_pointer_read_evidence_refuses_partial_changed_and_unknown_footprints() {
    let a = Pointer::symbolic(Variable(98_310));
    let b = Pointer::symbolic(Variable(98_311));
    let unknown = Pointer::symbolic(Variable(98_312));
    let old = intern_memory(Memory::new());
    let full = old
        .memory()
        .clone()
        .store(a.offset_by_bytes(32), int32(1))
        .with_seeded_cells(a.clone(), 4, ProgramType::Int32, 0, 2, old.clone());
    let changed_source = intern_memory(old.memory().clone().store(a.clone(), int32(7)));
    for (case, current) in [
        old.memory()
            .clone()
            .store(a.offset_by_bytes(32), int32(1))
            .with_seeded_cells(a.clone(), 4, ProgramType::Int32, 0, 1, old.clone()),
        old.memory()
            .clone()
            .store(a.offset_by_bytes(32), int32(1))
            .with_seeded_cells(a.clone(), 4, ProgramType::Int32, 1, 2, old.clone()),
        old.memory()
            .clone()
            .with_constant_run(a.clone(), ProgramType::Int32, 2, int32(0))
            .unwrap(),
        full.clone().store(a.offset_by_bytes(4), int32(7)),
        full.store(unknown, int32(7)),
        old.memory()
            .clone()
            .store(a.offset_by_bytes(32), int32(1))
            .with_seeded_cells(a.clone(), 4, ProgramType::Int32, 0, 2, changed_source),
    ]
    .into_iter()
    .enumerate()
    {
        let current = intern_memory(current);
        let (context, left, right) = seeded_pointer_read_context(&old, &current, &a, &b);
        context.register_pointer_read(&right, &current, &a);

        assert!(!context.pointers_known_equal(&left, &right), "case={case}");
    }
}

#[test]
fn direct_pointer_reads_retain_their_projection_definitions() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(98_340));
    let alias = Pointer::symbolic(Variable(98_341));
    let source = intern_memory(Memory::new().with_block_without_derivation("local:projection", 4));
    let projected = crate::kernel::memory_provenance::canonical_value_load_memory(
        &source,
        &address,
        crate::kernel::C_POINTER_BYTE_WIDTH,
    );
    assert_ne!(projected, source);
    let named = Pointer::loaded_value(&projected, &address);
    let observed = Pointer::loaded_value(&source, &alias);
    let context = PureFactContext::new();
    assert!(!context.pointers_known_equal(&named, &observed));
    let context =
        context.assume_condition(ConditionTerm::pointer_equal(address.clone(), alias), true);
    assert!(
        context.pointers_known_equal(&named, &observed),
        "direct read names must use their producer-recorded projection edge"
    );
    assert!(context.equality_graph.knows_condition(
        &ConditionTerm::pointer_value_equal(
            PointerValue::new(named.clone(), ProgramType::Int32Pointer),
            PointerValue::new(observed.clone(), ProgramType::Int32Pointer),
        ),
        true
    ));
    let shifted = context.clone();
    assert!(shifted.pointers_known_equal(&named.offset_by_bytes(8), &observed.offset_by_bytes(8)));
    assert!(!shifted.pointers_known_equal(&named.offset_by_bytes(8), &observed));
    let changed = intern_memory(
        source
            .memory()
            .clone()
            .store(address.clone(), ProgramValue::pointer(Pointer::null())),
    );
    assert!(
        !context.pointers_known_equal(&named, &Pointer::loaded_value(&changed, &address)),
        "projection metadata does not cross an actual store"
    );
}

#[test]
fn pointer_read_producer_closes_seeded_state_equality_in_the_shared_graph() {
    let a = Pointer::symbolic(Variable(98_330));
    let b = Pointer::symbolic(Variable(98_331));
    let old = intern_memory(Memory::new());
    let seeded =
        old.memory()
            .clone()
            .with_seeded_cells(a.clone(), 4, ProgramType::Int32, 0, 2, old.clone());
    let current = intern_memory(seeded);
    let context = PureFactContext::new();
    let left = Pointer::loaded_value(&old, &b);
    let right = Pointer::loaded_value(&current, &a);
    context.register_pointer_read(&left, &old, &b);
    context.register_pointer_read(&right, &current, &a);
    assert!(!context.pointers_known_equal(&left, &right));
    // Source normalization precedes the address alias. Ordinary congruence
    // must propagate this later fact, with no producer retry or fold hook.
    let context =
        context.assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
    assert!(
        context.pointers_known_equal(&left, &right),
        "producer evidence should power the ordinary graph query without a fold-specific rule"
    );
    assert!(pointers_proven_equal_for_memory_resolution(
        &left, &right, &context
    ));
    let third = Pointer::loaded_value(&current, &b);
    assert!(context.pointers_known_equal(&right, &third));
    assert!(context.pointers_known_equal(&left, &third));
}

#[test]
fn pointer_read_producer_admits_one_separate_store_into_the_shared_graph() {
    let address = Pointer::symbolic(Variable(98_350));
    let old = intern_memory(Memory::new());
    let current = intern_memory(
        old.memory()
            .clone()
            .store(address.offset_by_bytes(16), int32(1)),
    );
    let context = PureFactContext::new();
    let left = Pointer::loaded_value(&old, &address);
    let right = Pointer::loaded_value(&current, &address);
    context.register_pointer_read(&left, &old, &address);
    context.register_pointer_read(&right, &current, &address);
    assert!(
        context.pointers_known_equal(&left, &right),
        "a checked immediate store must feed the ordinary graph equality query"
    );
    assert!(pointers_proven_equal_for_memory_resolution(
        &left, &right, &context
    ));
    let argument = |value| {
        AlgebraicValue::Program(ProgramValue::typed_pointer(
            value,
            ProgramType::Int32Pointer,
        ))
    };
    assert!(
        resource_arguments_proven_equal(&argument(left), &argument(right), &context),
        "fold's existing argument checker must see the same graph equality"
    );
}

#[test]
fn pointer_read_single_store_refuses_changed_partial_and_unknown_accesses() {
    let address = Pointer::symbolic(Variable(98_360));
    let unknown = Pointer::symbolic(Variable(98_361));
    let old = intern_memory(Memory::new());
    for write in [
        address.clone(),
        address.offset_by_bytes(4),
        address.offset_by_bytes(7),
        unknown,
    ] {
        let current = intern_memory(old.memory().clone().store(write, uint8(1)));
        let context = PureFactContext::new();
        let left = Pointer::loaded_value(&old, &address);
        let right = Pointer::loaded_value(&current, &address);
        context.register_pointer_read(&left, &old, &address);
        context.register_pointer_read(&right, &current, &address);
        assert!(!context.pointers_known_equal(&left, &right));
    }
    // A four-byte store inside an eight-byte read overlaps it even though
    // their starting addresses differ. Address inequality is insufficient.
    let current = intern_memory(
        old.memory()
            .clone()
            .store(address.offset_by_bytes(4), int32(7)),
    );
    let context = PureFactContext::new();
    let left = Pointer::loaded_value(&old, &address);
    let right = Pointer::loaded_value(&current, &address);
    context.register_pointer_read(&left, &old, &address);
    context.register_pointer_read(&right, &current, &address);
    assert!(!context.pointers_known_equal(&left, &right));
    let adjacent = intern_memory(
        old.memory()
            .clone()
            .store(address.offset_by_bytes(8), int32(7)),
    );
    let value = Pointer::loaded_value(&adjacent, &address);
    context.register_pointer_read(&value, &adjacent, &address);
    assert!(context.pointers_known_equal(&left, &value));
}

#[test]
fn pointer_read_single_store_uses_only_its_branch_address_equality() {
    let read = Pointer::symbolic(Variable(98_370));
    let write = Pointer::symbolic(Variable(98_371));
    let old = intern_memory(Memory::new());
    let current = intern_memory(old.memory().clone().store(write.clone(), int32(7)));
    let context = PureFactContext::new();
    let left = Pointer::loaded_value(&old, &read);
    let right = Pointer::loaded_value(&current, &read);
    context.register_pointer_read(&left, &old, &read);
    context.register_pointer_read(&right, &current, &read);
    let sibling = context.clone();
    let branch = context.clone().assume_condition(
        ConditionTerm::pointer_equal(write, read.offset_by_bytes(16)),
        true,
    );
    assert!(!pointers_proven_equal_for_memory_resolution(
        &left, &right, &context
    ));
    let _scope = branch.enter_id_scope();
    // The branch's address equality puts the store beside the read's cell,
    // so its bounded cell walk proves the reads equal before registration.
    assert!(pointers_proven_equal_for_memory_resolution(
        &left, &right, &branch
    ));
    branch.register_pointer_read(&right, &current, &read);
    assert!(pointers_proven_equal_for_memory_resolution(
        &left, &right, &branch
    ));
    assert!(!sibling.pointers_known_equal(&left, &right));
    assert!(!context.pointers_known_equal(&left, &right));
    assert_eq!(branch.pure_facts().len(), context.pure_facts().len() + 1);
    assert!(!ResourceContext::new().permits_memory_read(&read, 8, &branch));
}

#[test]
fn pointer_read_single_store_preservation_propagates_late_read_aliases() {
    let address = Pointer::symbolic(Variable(98_380));
    let alias = Pointer::symbolic(Variable(98_381));
    let old = intern_memory(Memory::new());
    let current = intern_memory(
        old.memory()
            .clone()
            .store(address.offset_by_bytes(16), int32(1)),
    );
    let context = PureFactContext::new();
    let left = Pointer::loaded_value(&old, &alias);
    let right = Pointer::loaded_value(&current, &address);
    context.register_pointer_read(&left, &old, &alias);
    context.register_pointer_read(&right, &current, &address);
    assert!(!context.pointers_known_equal(&left, &right));
    let context = context.assume_condition(ConditionTerm::pointer_equal(address, alias), true);
    assert!(context.pointers_known_equal(&left, &right));
}

#[test]
fn pointer_read_producer_admits_recorded_cache_forgetting() {
    let address = arc_pointer(0);
    let seeded = intern_memory(Memory::new().with_block("arg-memory", 32).store(
        address.clone(),
        ProgramValue::Int64(MachineTerm::int64_constant(7)),
    ));
    let context = PureFactContext::new();
    let forgotten = intern_memory(seeded.memory().without_possible_aliasing_cells(
        &address.offset_by_bytes(4),
        1,
        &context,
    ));
    assert!(matches!(
        forgotten.derivation().unwrap().as_ref(),
        MemoryDerivation::CellsForgotten { .. }
    ));
    let left = Pointer::loaded_value(&seeded, &address);
    let right = Pointer::loaded_value(&forgotten, &address);
    context.register_pointer_read(&left, &seeded, &address);
    let branch = context.clone();
    let sibling = context.clone();
    assert!(branch.pointers_known_equal(&left, &right));
    branch.register_pointer_read(&right, &forgotten, &address);
    assert!(
        branch.pointers_known_equal(&left, &right),
        "forgetting cached cells changes no bytes"
    );
    assert!(pointers_proven_equal_for_memory_resolution(
        &left, &right, &branch
    ));
    assert!(context.pointers_known_equal(&left, &right));
    assert!(sibling.pointers_known_equal(&left, &right));
    assert_eq!(branch.pure_facts().len(), context.pure_facts().len());
    assert!(!ResourceContext::new().permits_memory_read(&address, 8, &branch));
    let alias = Pointer::symbolic(Variable(98_400));
    let alias_read = Pointer::loaded_value(&forgotten, &alias);
    branch.register_pointer_read(&alias_read, &forgotten, &alias);
    let branch = branch.assume_condition(ConditionTerm::pointer_equal(address, alias), true);
    assert!(branch.pointers_known_equal(&left, &alias_read));
}

#[test]
fn pointer_read_cache_forgetting_does_not_bridge_writes_havoc_or_unrecorded_pruning() {
    let address = arc_pointer(0);
    let seeded = intern_memory(Memory::new().with_block("arg-memory", 32).store(
        address.clone(),
        ProgramValue::Int64(MachineTerm::int64_constant(9)),
    ));
    let context = PureFactContext::new();
    let forgotten = intern_memory(seeded.memory().without_possible_aliasing_cells(
        &address.offset_by_bytes(4),
        1,
        &context,
    ));
    let left = Pointer::loaded_value(&seeded, &address);
    context.register_pointer_read(&left, &seeded, &address);
    let forgotten_read = Pointer::loaded_value(&forgotten, &address);
    context.register_pointer_read(&forgotten_read, &forgotten, &address);
    assert!(context.pointers_known_equal(&left, &forgotten_read));
    for changed in [
        forgotten
            .memory()
            .clone()
            .store(address.offset_by_bytes(4), crate::kernel::uint8(1u32)),
        forgotten
            .memory()
            .clone()
            .store(Pointer::symbolic(Variable(98_401)), int32(1)),
        seeded
            .memory()
            .clone()
            .with_loop_memory_havoc_preserving_loans(
                Variable(98_402),
                &BTreeSet::new(),
                None,
                None,
            ),
        seeded.memory().without_cell(&address),
    ] {
        let changed = intern_memory(changed);
        let right = Pointer::loaded_value(&changed, &address);
        context.register_pointer_read(&right, &changed, &address);
        assert!(!context.pointers_known_equal(&left, &right));
    }
}

#[test]
fn pointer_read_congruence_composes_materialization_and_forgetting_at_production() {
    let address = Pointer::symbolic(Variable(98_420));
    let unknown_write = Pointer::symbolic(Variable(98_421));
    let original = intern_memory(Memory::new());
    let memory = original
        .memory()
        .clone()
        .with_seeded_cells(
            address.clone(),
            4,
            ProgramType::Int32,
            0,
            2,
            original.clone(),
        )
        .with_seeded_cells(
            address.offset_by_bytes(8),
            4,
            ProgramType::Int32,
            0,
            2,
            original.clone(),
        )
        .with_seeded_cells(
            address.offset_by_bytes(16),
            4,
            ProgramType::Int32,
            0,
            1,
            original.clone(),
        );
    let context = PureFactContext::new();
    let forgotten =
        intern_memory(memory.without_possible_aliasing_cells(&unknown_write, 4, &context));
    assert!(matches!(
        forgotten.derivation().unwrap().as_ref(),
        MemoryDerivation::CellsForgotten { .. }
    ));
    let left = Pointer::loaded_value(&original, &address);
    let right = Pointer::loaded_value(&forgotten, &address);
    assert!(
        context.pointers_known_equal(&left, &right),
        "producer-recorded byte-preserving transitions must compose without intermediate reads"
    );
}

#[test]
fn initialization_metadata_keeps_complete_pointer_identity_without_access_authority() {
    let address = Pointer {
        block: "local:initialized-descriptor".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = intern_memory(Memory::new().with_uninitialized_block(address.block.clone(), 8));
    let after = intern_memory(
        before
            .memory()
            .clone()
            .with_initialized_object(&address, 8)
            .with_block("local:unrelated-getter-temporary", 4),
    );
    assert_ne!(before, after);
    assert!(!before.memory().has_initialized_bytes_at(&address, 8));
    assert!(after.memory().has_initialized_bytes_at(&address, 8));

    let read = |memory: &SharedMemory| {
        PointerValue::from_read(
            Pointer::loaded_value(memory, &address),
            ProgramType::Int32Pointer,
            memory,
            &address,
        )
    };
    let facts = PureFactContext::new();
    let original = read(&before);
    assert_eq!(original.designation(), read(&after).designation());
    assert!(facts.pointer_designations_match(&original, &read(&after)));
    assert!(facts.pointers_known_equal(original.pointer(), read(&after).pointer()));
    assert!(!ResourceContext::new().permits_memory_read(&address, 8, &facts));

    let overwritten = intern_memory(
        after
            .memory()
            .clone()
            .store(address.offset_by_bytes(4), crate::kernel::uint8(1u32)),
    );
    assert!(!facts.pointer_designations_match(&original, &read(&overwritten)));
    assert!(!facts.pointers_known_equal(original.pointer(), read(&overwritten).pointer()));
}

#[test]
fn read_identity_refuses_changed_sources_constant_runs_and_unrecorded_pruning() {
    let address = Pointer::symbolic(Variable(98_430));
    let original = intern_memory(Memory::new());
    let changed = intern_memory(original.memory().clone().store(address.clone(), int32(7)));
    let from_changed = intern_memory(original.memory().clone().with_seeded_cells(
        address.clone(),
        4,
        ProgramType::Int32,
        0,
        2,
        changed.clone(),
    ));
    let after_changed = intern_memory(changed.memory().clone().with_seeded_cells(
        address.offset_by_bytes(8),
        4,
        ProgramType::Int32,
        0,
        2,
        original.clone(),
    ));
    let constant = intern_memory(
        original
            .memory()
            .clone()
            .with_constant_run(address.clone(), ProgramType::Int32, 2, int32(0))
            .unwrap(),
    );
    let context = PureFactContext::new();
    let old_read = Pointer::loaded_value(&original, &address);
    for memory in [from_changed, after_changed, constant] {
        assert_ne!(memory.read_identity(), original.read_identity());
        assert!(
            !context.pointers_known_equal(&old_read, &Pointer::loaded_value(&memory, &address))
        );
    }
    let forgotten = intern_memory(changed.memory().without_cell(&address));
    assert_ne!(forgotten.read_identity(), changed.read_identity());
}

#[test]
fn read_identity_is_immutable_when_a_state_was_interned_before_its_edge() {
    let address = Pointer::symbolic(Variable(98_450));
    let original = intern_memory(Memory::new());
    let run = CellRun::new(
        address,
        4,
        ProgramType::Int32,
        2,
        original.clone(),
        crate::kernel::primitives::IndexIntervals::default(),
    );
    let mut memory = original.memory().clone();
    std::sync::Arc::make_mut(&mut memory.cells).add_run(run.clone());
    let current = intern_memory(memory.clone());
    let before = current.read_identity();
    record_memory_derivation(
        &mut memory,
        MemoryDerivation::CellsSeeded {
            base: original.clone(),
            run: std::sync::Arc::new(run),
        },
    );
    assert_ne!(current.read_identity(), original.read_identity());
    assert_eq!(
        current.read_identity(),
        before,
        "late annotation cannot change existing graph keys"
    );
}

/// A store the cell walk stops at answers for a read only when it starts at
/// the read's address and is exactly as wide: a one-byte store inside a
/// four-byte read, and a four-byte store around a one-byte read, write bytes
/// the read returns without being its value. The exact store is the positive
/// control.
#[test]
fn a_stored_value_resolves_only_a_read_of_its_own_address_and_width() {
    let bare = PureFactContext::new();
    let block = "resolved-width-memory";
    let at = |offset: i64| Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let base = Memory::new().with_block(block, 16);
    let stored_at = |write: Pointer, value: ProgramValue| {
        crate::kernel::intern_memory_ref(
            &base
                .clone()
                .without_possible_aliasing_cells(&write, value.byte_width(), &bare)
                .store(write, value),
        )
    };
    let resolves_to_seven = |memory: &SharedMemory, read: &Pointer| {
        let seven = MachineTerm::constant(7);
        let load = MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let resolved = crate::kernel::memory_provenance::resolve_load_along_memory_derivations(
            memory,
            read,
            crate::kernel::LoadKind::Int32,
            &bare,
        );
        let equal =
            crate::kernel::explicit_atomic_equality_from_memory_derivations(&load, &seven, &bare);
        assert_eq!(
            resolved.as_ref() == Some(&seven),
            equal,
            "both explicit routes read one answer off one walk"
        );
        equal
    };

    let wide_read = at(0);
    crate::kernel::eval::declare_load_access_width(&wide_read, 4);
    let narrow_store = stored_at(at(1), crate::kernel::uint8(7));
    assert!(
        !resolves_to_seven(&narrow_store, &wide_read),
        "a byte stored inside a four-byte read is one of its bytes, not its value"
    );

    let narrow_read = at(9);
    crate::kernel::eval::declare_load_access_width(&narrow_read, 1);
    let wide_store = stored_at(at(8), ProgramValue::Int32(MachineTerm::constant(7)));
    assert!(
        !resolves_to_seven(&wide_store, &narrow_read),
        "a four-byte store around a one-byte read holds other bytes than that read returns"
    );

    let exact_read = at(4);
    crate::kernel::eval::declare_load_access_width(&exact_read, 4);
    let exact_store = stored_at(at(4), ProgramValue::Int32(MachineTerm::constant(7)));
    assert!(
        resolves_to_seven(&exact_store, &exact_read),
        "a store of the read's own address and width is the read's value"
    );
}

#[test]
fn canonical_load_naming_retains_the_live_memory_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: "local:origin-cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let live =
        crate::kernel::intern_memory(Memory::new().with_block("unrelated-origin-storage", 16));
    let read = crate::kernel::canonical_form_of_load(
        live.clone(),
        pointer.clone(),
        crate::kernel::LoadKind::Int32,
    );
    let observed = crate::kernel::eval::scalar_read_observation(
        crate::kernel::MachineOperandView::Legacy(&read),
    )
    .unwrap();
    assert_eq!((observed.origin, observed.pointer), (Some(live), pointer));
    assert_eq!(crate::kernel::eval::load_variable_registry_len(), 0);
}

#[test]
fn an_unknown_pointer_call_drops_a_local_cache_without_separation() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Pointer {
        block: "local:unknown-call-target".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let base = Memory::new()
        .with_block("local:unknown-call-target", 16)
        .store(cell.clone(), ProgramValue::Int32(MachineTerm::constant(1)));
    let ranges = [memory_range(Pointer::symbolic(Variable(977_002)), 0, 1)];
    let assumptions = PureFactContext::new();
    let after = base
        .clone()
        .with_call_memory_havoc(Variable(977_003), &ranges, &assumptions, None);
    assert!(!after.has_known_cell_at(&cell));
    assert!(after.matches_call_memory_havoc_result(&base, &ranges, &assumptions, None));
    let forged = after.store(cell, ProgramValue::Int32(MachineTerm::constant(1)));
    assert!(!forged.matches_call_memory_havoc_result(&base, &ranges, &assumptions, None));
}

#[test]
fn kept_constant_offset_fields_have_checkable_call_havoc_evidence() {
    let _session = crate::kernel::VerificationSession::enter();
    let owner = Pointer {
        block: "local:kept-offset-owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let cell = owner.offset_by_bytes(8);
    crate::kernel::eval::declare_load_access_width(&cell, 4);
    let assumptions = PureFactContext::new();
    let residual = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(owner.clone(), 0, 4)));
    let kept = CallKeptOwnership::new(
        residual,
        CallKeptRanges::new(ResourceContext::new(), vec![], None),
        &assumptions,
    );
    let base = Memory::new().with_block("local:kept-offset-owner", 16);
    let ranges = [memory_range(Pointer::symbolic(Variable(977_004)), 0, 1)];
    let after =
        base.clone()
            .with_call_memory_havoc(Variable(977_005), &ranges, &assumptions, Some(&kept));
    let recorded = CallKeptRanges::recorded_on(&after).unwrap();
    assert!(recorded.holds_access(&cell, 4, &assumptions));
    assert!(!recorded.holds_access(&owner.offset_by_bytes(16), 4, &assumptions));
    let load = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(memory),
            Box::new(cell.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let equality = Proposition::ConditionIs(ConditionTerm::equal(load(&after), load(&base)), true);
    let evidence = with_extended_dag_bridging(|| {
        atomic_memory_load_equality_evidence(&load(&after), &load(&base), &assumptions)
    })
    .expect("the caller's kept object preserves its offset field");
    assert!(evidence.is_fully_typed());
    assert!(evidence.checks(&equality, &assumptions));
    let without_kept =
        base.clone()
            .with_call_memory_havoc(Variable(977_006), &ranges, &assumptions, None);
    assert!(
        with_extended_dag_bridging(|| atomic_memory_load_equality_evidence(
            &load(&without_kept),
            &load(&base),
            &assumptions
        ))
        .is_none()
    );
    let overwritten = after.store(cell.clone(), ProgramValue::Int32(MachineTerm::constant(43)));
    assert!(!evidence.checks(
        &Proposition::ConditionIs(ConditionTerm::equal(load(&overwritten), load(&base)), true),
        &assumptions
    ));
}

#[test]
fn two_edge_pointer_alias_witness_rechecks_each_named_premise() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = Pointer {
        block: "local:two-edge-alias".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let middle = Pointer::symbolic(Variable(977_102));
    let right = Pointer::symbolic(Variable(977_103));
    for pointer in [&left, &right] {
        crate::kernel::eval::declare_load_access_width(pointer, 4);
    }
    let memory = crate::kernel::intern_memory(Memory::new());
    let first = ConditionTerm::pointer_equal(left.clone(), middle.clone());
    let second = ConditionTerm::pointer_equal(middle, right.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(first.clone(), true)
        .assume_condition(second.clone(), true);
    let left_load = MachineTerm::MemoryLoad(
        memory.clone(),
        Box::new(left),
        crate::kernel::LoadKind::Int32,
    );
    let right_load =
        MachineTerm::MemoryLoad(memory, Box::new(right), crate::kernel::LoadKind::Int32);
    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_origin_load_equality(
        &left_load,
        &right_load,
        &assumptions
    ));
    let witnesses = capture.finish();
    let [witness] = witnesses.as_slice() else {
        panic!("expected one retained alias witness");
    };
    assert!(witness.checks(&assumptions));
    let MachineTerm::MemoryLoad(memory, pointer, _) = &left_load else {
        unreachable!();
    };
    let byte_read = MachineTerm::MemoryLoad(
        memory.clone(),
        pointer.clone(),
        crate::kernel::LoadKind::UInt8,
    );
    let mismatched_capture = CheckedLoadEqualityCapture::start();
    assert!(!checked_origin_load_equality(
        &byte_read,
        &right_load,
        &assumptions,
    ));
    assert!(mismatched_capture.finish().is_empty());
    for remaining in [first, second] {
        let partial = PureFactContext::new().assume_condition(remaining, true);
        assert!(!witness.checks(&partial));
    }
    assert!(!witness.checks(&PureFactContext::new()));
}

#[test]
fn unrelated_symbolic_kept_bases_do_not_trigger_range_placement() {
    let input = |name| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(name)), 4),
    };
    let pointer = input(977_199).offset_by_bytes(8);
    let assumptions = PureFactContext::new();
    for count in [16, 64, 256, 1024] {
        let mut ranges = ResourceContext::new();
        for index in 0..count {
            ranges = ranges.unchecked_with_fact(ResourceFact::own_memory(memory_range(
                input(978_000 + index),
                0,
                4,
            )));
        }
        let placements = std::cell::Cell::new(0);
        assert!(
            assumptions
                .kept_range_holding_access(
                    &ranges,
                    || {
                        placements.set(placements.get() + 1);
                        Some(assumptions.clone())
                    },
                    &pointer,
                    4,
                )
                .is_none()
        );
        assert_eq!(placements.get(), 0, "unrelated kept bases: {count}");
    }
}

#[test]
fn initialized_array_copy_preserves_source_history_with_constant_work() {
    let mut samples = Vec::new();
    for (count, unrelated) in [(4u32, 0), (1024, 32), (1_000_000, 1024)] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer {
            block: "local:copy-source".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer {
            block: "local:copy-target".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = Memory::new()
            .with_block(source.block.clone(), count * 4)
            .with_block(target.block.clone(), count * 4)
            .with_initialized_object(&source, count * 4);
        for index in 0..unrelated {
            memory = memory.with_block(format!("local:unrelated-{index}"), 4);
        }
        let assumptions = PureFactContext::new();
        // A checked helper leaves initialized storage with unknown values.
        let written = memory.with_storage_memory_havoc(
            Variable(978_000),
            &[MemoryRange::new_with_element_width(
                source.clone(),
                0u32.into(),
                count.into(),
                4,
            )],
            &assumptions,
        );
        let load = |memory: &Memory| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(source.clone()),
                LoadKind::Int32,
            )
        };
        crate::kernel::eval::declare_load_access_width(&source, 4);
        let before = load(&written);
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            let copied = written
                .clone()
                .write_scalar_array_region(
                    &target,
                    ProgramType::UInt32,
                    count,
                    ProgramValue::pointer(source.clone()),
                    true,
                    false,
                    &assumptions,
                )
                .unwrap();
            let capture = CheckedLoadEqualityCapture::start();
            assert!(checked_origin_load_equality(
                &before,
                &load(&copied),
                &assumptions
            ));
            let equalities = capture.finish();
            assert_eq!(equalities.len(), 1);
            assert!(equalities[0].checks(&assumptions));
            copied
        });
        assert!(matches!(
            crate::kernel::intern_memory_ref(&copied)
                .derivation()
                .as_deref(),
            Some(MemoryDerivation::ObjectInitializationRecorded { .. })
        ));
        // Metadata records cannot hide an actual overwrite of the source.
        let changed = copied
            .clone()
            .store(source.clone(), ProgramValue::UInt32(9u32.into()));
        assert!(!checked_origin_load_equality(
            &before,
            &load(&changed),
            &assumptions
        ));
        let repeated = copied.clone().with_initialized_object(&target, count * 4);
        assert_eq!(
            crate::kernel::intern_memory_ref(&repeated),
            crate::kernel::intern_memory_ref(&copied)
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "{samples:?}"
    );
}

/// A retained no-write witness must reject another source, constant writes,
/// copied cells, normalized bools and overlapping representations.
#[test]
fn seeded_scalar_no_write_witness_rejects_changed_or_represented_values() {
    use crate::kernel::primitives::{IndexIntervals, RunValueMode};
    let anchor = Pointer::symbolic(Variable(98_480));
    let other = Pointer::symbolic(Variable(98_481));
    let original = intern_memory(Memory::new());
    let changed = intern_memory(original.memory().clone().store(anchor.clone(), int32(7)));
    let assumptions = PureFactContext::new();
    let witness = MemoryDagHopJustification::SeededLoadsOfBase;
    for (source, mode, ty, width) in [
        (changed.clone(), RunValueMode::Load, ProgramType::Int32, 4),
        (changed, RunValueMode::Load, ProgramType::Int32Pointer, 8),
        (
            original.clone(),
            RunValueMode::Load,
            ProgramType::Int32Pointer,
            4,
        ),
        (
            original.clone(),
            RunValueMode::Constant(ProgramValue::typed_pointer(
                other.clone(),
                ProgramType::Int32Pointer,
            )),
            ProgramType::Int32Pointer,
            8,
        ),
        (
            original.clone(),
            RunValueMode::Copy {
                source_base: other.clone(),
            },
            ProgramType::Int32Pointer,
            8,
        ),
        (
            original.clone(),
            RunValueMode::Constant(int32(7)),
            ProgramType::Int32,
            4,
        ),
        (
            original.clone(),
            RunValueMode::Copy {
                source_base: other.clone(),
            },
            ProgramType::Int32,
            4,
        ),
        (original.clone(), RunValueMode::Load, ProgramType::Bool, 1),
        (original.clone(), RunValueMode::Load, ProgramType::Int32, 1),
    ] {
        let edge = MemoryDerivation::CellsSeeded {
            base: original.clone(),
            run: std::sync::Arc::new(CellRun::new_with_mode(
                anchor.clone(),
                width,
                ty,
                16,
                source,
                mode,
                IndexIntervals::default(),
            )),
        };
        assert!(!witness.checks(&edge, &other, 4, &assumptions));
    }
    let write = MemoryDerivation::Store {
        base: original,
        pointer: anchor,
        value: int32(7).into(),
    };
    assert!(!witness.checks(&write, &other, 4, &assumptions));
}

/// Recording the edge of a state the recording itself interns cannot
/// change any earlier answer, since no earlier question could name that
/// state, so it leaves the derivation generation that keys negative memos
/// alone. Bumping it at every program step emptied those memos at every step.
#[test]
fn recording_a_fresh_state_keeps_the_derivation_generation() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Pointer {
        block: "generation-block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = Memory::new().with_block("generation-block", 8);
    let before = crate::kernel::primitives::memory_derivation_generation();
    let stored = base.store(cell.clone(), ProgramValue::Int32(MachineTerm::constant(1)));
    assert!(
        crate::kernel::intern_memory_ref(&stored)
            .derivation()
            .is_some(),
        "the store recorded its edge"
    );
    assert_eq!(
        crate::kernel::primitives::memory_derivation_generation(),
        before,
        "a fresh state's edge invalidates no earlier answer"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/memory_dag_tests.rs");
}

#[test]
fn full_pointer_read_survives_a_join_of_stores_to_its_sibling() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = intern_memory(Memory::new());
    let p = Pointer::symbolic(Variable(998_710));
    let q = PointerValue::new(
        Pointer::symbolic(Variable(998_711)),
        ProgramType::Int32Pointer,
    );
    let Some(ProgramValue::Pointer(child)) =
        crate::kernel::eval::symbolic_load_value(&before, &p, ProgramType::Int32Pointer)
    else {
        panic!("pointer load")
    };
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_value_equal(child.clone(), q.clone()),
        true,
    );
    let beside = Pointer {
        block: child.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            child.pointer().offset.clone(),
            PointerOffsetTerm::Constant(8),
        ),
    };
    let left = before.memory().clone().store(beside.clone(), int32(0));
    let right = before.memory().clone().store(beside.clone(), int32(1));
    let joined = intern_memory(
        left.clone()
            .with_interface_memory_havoc(Variable(998_712), &BTreeSet::new(), &[&left, &right])
            .unwrap(),
    );
    // The explicit proof selects the disjoint byte ranges after rewriting
    // child == q: [q + 8, q + 12) is separate from [q, q + 8).
    let facts = facts.assume_proposition(Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
            beside.clone(),
            0u32.into(),
            4u32.into(),
            1,
        ))),
        right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
            q.pointer().clone(),
            0u32.into(),
            8u32.into(),
            1,
        ))),
    });
    // The explicit join summary names the common write footprint of both arms.
    // Comparing the distant states alone no longer searches their histories.
    let effect = Proposition::MemoryEffectSummary {
        before: before.memory().clone(),
        after: joined.memory().clone(),
        mutable_ranges: vec![MemoryRange::new(beside, 0u32.into(), 1u32.into())],
    };
    let (old, new, equality) = super::explicit_frame(
        before.memory(),
        joined.memory(),
        q.pointer(),
        ProgramType::Int32Pointer,
        &[effect],
        &facts,
    )
    .expect("the selected join footprint preserves the complete pointer");
    let (ProgramValue::Pointer(old), ProgramValue::Pointer(new)) = (old, new) else {
        panic!("complete pointer observations");
    };
    let preserved = facts.clone().assume_proposition(equality);
    assert!(preserved.pointer_designations_match(&old, &new));
    let earlier = Pointer::loaded_value(&before, q.pointer());
    let upper_half = Pointer {
        block: q.pointer().block.clone(),
        offset: PointerOffsetTerm::add(q.pointer().offset.clone(), PointerOffsetTerm::Constant(4)),
    };
    let changed = intern_memory(joined.memory().clone().store(upper_half, int32(5)));
    let projection = intern_memory(
        crate::kernel::memory_provenance::canonical_program_memory_for_pointer_load(
            &changed,
            q.pointer(),
        ),
    );
    crate::kernel::reasoning::record_canonical_load_projection(&changed, &projection, q.pointer());
    let overwritten = Pointer::loaded_value(&projection, q.pointer());
    assert!(
        !crate::kernel::memory_provenance::pointer_read_designations_equal(
            &earlier,
            &overwritten,
            &facts
        )
    );
    assert!(
        !crate::kernel::memory_provenance::pointer_read_extents_equal(
            &earlier,
            &overwritten,
            &facts
        )
    );
}

/// Caching a scalar read of the predecessor is not a write, including when
/// the access exactly matches the seeded slot's address and width.
#[test]
fn seeded_scalar_read_keeps_its_predecessor_cell_version() {
    use crate::kernel::memory_provenance::{LoadHistory, recorded_load_history};
    let assumptions = PureFactContext::new();
    for (ty, bytes, kind) in [
        (ProgramType::Int32, 4, crate::kernel::LoadKind::Int32),
        (ProgramType::UInt64, 8, crate::kernel::LoadKind::Bits64),
    ] {
        let pointer = Pointer::symbolic(Variable(98_610 + u64::from(bytes)));
        crate::kernel::eval::declare_load_access_width(&pointer, bytes);
        let original = intern_memory(Memory::new());
        let cached = intern_memory(original.memory().clone().with_seeded_cells(
            pointer.clone(),
            bytes,
            ty,
            0,
            1,
            original.clone(),
        ));
        let history = with_extended_dag_bridging(|| {
            recorded_load_history(&original, &cached, &pointer, kind, &assumptions)
        });
        assert!(
            matches!(history, LoadHistory::OneVersion(_)),
            "{ty:?}: {history:?}"
        );
        let overwritten = intern_memory(
            cached
                .memory()
                .clone()
                .store(pointer.offset_by_bytes(bytes - 1), crate::kernel::uint8(9)),
        );
        let history = with_extended_dag_bridging(|| {
            recorded_load_history(&original, &overwritten, &pointer, kind, &assumptions)
        });
        assert!(
            matches!(history, LoadHistory::DifferentVersions),
            "{ty:?}: {history:?}"
        );
    }
}

#[test]
fn numeric_address_byte_gaps_preserve_cache_and_read_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(970_101));
    let q = Pointer::symbolic(Variable(970_102));
    for shift in [0, 4, 8, 16] {
        let premise = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::pointer_address(q.clone()),
                MachineTerm::pointer_address(p.offset_by_bytes(shift)),
            ),
            true,
        );
        let context = PureFactContext::new().assume_proposition(premise.clone());
        // Equal physical addresses do not grant pointer provenance.
        assert!(!context.pointers_known_equal(&q, &p.offset_by_bytes(shift)));
        let before = intern_memory(Memory::new().store(
            p.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(17)),
        ));
        let cache = before
            .memory()
            .without_possible_aliasing_cells(&q, 8, &context);
        assert_eq!(cache.has_known_cell_at(&p), shift >= 8, "gap {shift}");
        let after = intern_memory(cache.store(
            q.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
        ));
        let history = recorded_load_history(&before, &after, &p, LoadKind::Bits64, &context);
        assert_eq!(
            matches!(history, LoadHistory::OneVersion(_)),
            shift >= 8,
            "gap {shift}: {history:?}"
        );
        if shift >= 8 {
            let missing = PureFactContext::new();
            assert!(
                crate::kernel::memory_provenance::indexed_store_byte_separation_evidence(
                    &q, 8, &p, 8, &missing,
                )
                .is_none()
            );
        }
    }
}

#[test]
fn anchored_byte_separation_checks_full_width_and_scope() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(970_111)),
    };
    let q = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(970_112)),
    };
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(p.clone(), 0, 2))),
        right: Box::new(Resource::Memory(memory_range(q.clone(), 0, 2))),
    };
    let context = PureFactContext::new().assume_proposition(separation.clone());
    let check = |context: &PureFactContext, bytes| {
        crate::kernel::memory_provenance::indexed_store_byte_separation_evidence(
            &q, 8, &p, bytes, context,
        )
        .is_some()
    };
    assert!(check(&context, 8));
    assert!(!check(&context, 16));
    assert!(!check(&PureFactContext::new(), 8));
    assert!(!check(&PureFactContext::new(), 8));
    let overlapping = context.assume_condition(
        ConditionTerm::uint64_equal(
            MachineTerm::pointer_address(q.clone()),
            MachineTerm::pointer_address(p.offset_by_bytes(4)),
        ),
        true,
    );
    assert!(!check(&overlapping, 8));
}

#[test]
fn owned_byte_separation_survives_an_unknown_numeric_displacement() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(970_141));
    let q = Pointer::symbolic(Variable(970_142));
    let owners = Proposition::ResourceComposition(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(memory_range(p.clone(), 0, 2)))
            .unchecked_with_fact(ResourceFact::own_memory(memory_range(q.clone(), 0, 2))),
    );
    let address = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(
            MachineTerm::pointer_address(q.clone()),
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(MachineTerm::pointer_address(p.clone())),
                right: Box::new(MachineTerm::Variable(Variable(970_143))),
            },
        ),
        true,
    );
    let context = address.clone().assume_proposition(owners.clone());
    assert!(!context.address_connected_objects(&q).is_empty());
    let before = intern_memory(Memory::new().store(
        p.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(17)),
    ));
    let cache = before
        .memory()
        .without_possible_aliasing_cells(&q, 8, &context);
    assert!(cache.has_known_cell_at(&p));
    let after = intern_memory(cache.store(
        q.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
    ));
    assert!(matches!(
        recorded_load_history(&before, &after, &p, LoadKind::Bits64, &context),
        LoadHistory::OneVersion(_)
    ));
    assert!(
        crate::kernel::memory_provenance::indexed_store_byte_separation_evidence(
            &q, 8, &p, 8, &address
        )
        .is_none()
    );
}

#[test]
fn seeded_mixed_width_runs_match_per_cell_caching() {
    use crate::kernel::primitives::{CellRun, IndexIntervals};
    for reverse in [false, true] {
        for shift in [None, Some(0), Some(1), Some(8)] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(98_760)),
            };
            let other = match shift {
                Some(shift) => base.offset_by_bytes(shift),
                None => Pointer {
                    block: base.block.clone(),
                    offset: PointerOffsetTerm::Variable(Variable(98_761)),
                },
            };
            let source = intern_memory(Memory::new());
            let word = CellRun::new(
                base,
                8,
                ProgramType::UInt64,
                12,
                source.clone(),
                IndexIntervals::default(),
            );
            let bytes = CellRun::new(
                other,
                1,
                ProgramType::UInt8,
                12,
                source,
                IndexIntervals::default(),
            );
            let runs = if reverse {
                [&bytes, &word, &bytes]
            } else {
                [&word, &bytes, &word]
            };
            let mut expected = std::collections::BTreeMap::new();
            let mut memory = Memory::new();
            for run in runs {
                memory = memory.with_seeded_cells(
                    run.base().clone(),
                    run.element_width(),
                    run.element_type(),
                    0,
                    run.count(),
                    run.source().clone(),
                );
                for index in 0..run.count() {
                    expected
                        .entry(run.slot_pointer(index))
                        .or_insert_with(|| run.value(index));
                }
                assert_eq!(memory.cells.len(), expected.len());
                for (pointer, value) in &expected {
                    assert_eq!(
                        memory.cells.get(pointer).as_ref(),
                        Some(value),
                        "reverse {reverse}, shift {shift:?}, {pointer:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn seeded_mixed_width_aliases_still_invalidate_overlapping_reads() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(variable)),
    };
    let word = address(98_770);
    let bytes = address(98_771);
    let source = intern_memory(Memory::new());
    let memory = Memory::new()
        .with_seeded_cells(bytes.clone(), 1, ProgramType::UInt8, 0, 16, source.clone())
        .with_seeded_cells(word.clone(), 8, ProgramType::UInt64, 0, 1, source);
    assert!(memory.cells.contains_key(&word));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(word.clone(), bytes.clone()),
        true,
    );
    let written = bytes.offset_by_bytes(4);
    let memory = memory
        .without_possible_aliasing_cells(&written, 1, &assumptions)
        .store_with_context(written.clone(), crate::kernel::uint8(9u32), &assumptions);
    assert!(
        !memory.cells.contains_key(&word),
        "a byte written through an alias overlaps the cached word"
    );
    assert_eq!(memory.cells.get(&written), Some(crate::kernel::uint8(9u32)));
}

#[test]
fn equal_object_origins_frame_neighbor_fields_without_equating_index_atoms() {
    let _session = crate::kernel::VerificationSession::enter();
    let origin = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(variable)), 4),
    };
    let left = origin(9_882_101);
    let right = origin(9_882_102);
    let parent = Pointer::symbolic(Variable(9_882_103));
    let first = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(left.clone(), parent.clone()),
        true,
    );
    let second =
        Proposition::ConditionIs(ConditionTerm::pointer_equal(parent, right.clone()), true);
    let context = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone());
    assert!(context.pointers_known_equal(&left, &right));
    let before = intern_memory(Memory::new());
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(right, ProgramValue::UInt64(MachineTerm::uint64_constant(0))),
    );
    let read = left.offset_by_bytes(8);
    let load = |memory: &SharedMemory, pointer: &Pointer| {
        MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Bits64)
    };
    let old = load(&before, &read);
    let new = load(&after, &read);
    let proof =
        with_extended_dag_bridging(|| atomic_memory_load_equality_evidence(&new, &old, &context))
            .expect("equal object origins preserve the neighboring eight-byte field");
    let goal = Proposition::ConditionIs(ConditionTerm::equal(new, old), true);
    assert!(proof.checks(&goal, &context));
    for remaining in [first, second] {
        let partial = PureFactContext::new().assume_proposition(remaining);
        assert!(!proof.checks(&goal, &partial));
    }
    let overlapping = left.offset_by_bytes(4);
    assert!(
        with_extended_dag_bridging(|| {
            atomic_memory_load_equality_evidence(
                &load(&after, &overlapping),
                &load(&before, &overlapping),
                &context,
            )
        })
        .is_none(),
        "the same alias geometry must reject a partial overwrite"
    );
}

#[test]
fn stated_separation_frames_equal_model_and_program_origins() {
    let _session = crate::kernel::VerificationSession::enter();
    let origin = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(variable)), 4),
    };
    let entry = origin(9_883_101);
    let parent = Pointer::symbolic(Variable(9_883_102));
    let bridge = Pointer::symbolic(Variable(9_883_103));
    let node = origin(9_883_104);
    let first = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(parent.clone(), bridge.clone()),
        true,
    );
    let second =
        Proposition::ConditionIs(ConditionTerm::pointer_equal(bridge, entry.clone()), true);
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(
            parent.offset_by_bytes(8),
            0,
            2,
        ))),
        right: Box::new(Resource::Memory(memory_range(
            node.offset_by_bytes(16),
            0,
            2,
        ))),
    };
    let before = intern_memory(Memory::new());
    let after = intern_memory(before.memory().clone().store(
        node.offset_by_bytes(16),
        ProgramValue::UInt64(MachineTerm::uint64_constant(19)),
    ));
    let read = entry.offset_by_bytes(8);
    let load = |memory: &SharedMemory| {
        MachineTerm::MemoryLoad(memory.clone(), Box::new(read.clone()), LoadKind::Bits64)
    };
    let original = PureFactContext::new().assume_proposition(separation.clone());
    for separation_first in [true, false] {
        let mut context = if separation_first {
            original.clone()
        } else {
            PureFactContext::new()
        };
        context = context
            .assume_proposition(first.clone())
            .assume_proposition(second.clone());
        if !separation_first {
            context = context.assume_proposition(separation.clone());
        }
        assert!(context.pointers_known_equal(&entry, &parent));
        let proof = with_extended_dag_bridging(|| {
            atomic_memory_load_equality_evidence(&load(&after), &load(&before), &context)
        })
        .expect("stated separation follows checked origin equality");
        let goal =
            Proposition::ConditionIs(ConditionTerm::equal(load(&after), load(&before)), true);
        assert!(proof.checks(&goal, &context));
        assert!(typed_read_has_same_memory_source(
            before.memory(),
            after.memory(),
            &read,
            8,
            &context
        ));
        let facts = [&first, &second, &separation];
        for removed in facts {
            let missing = facts
                .into_iter()
                .filter(|fact| *fact != removed)
                .fold(PureFactContext::new(), |missing, fact| {
                    missing.assume_proposition(fact.clone())
                });
            assert!(!proof.checks(&goal, &missing));
            assert!(!typed_read_has_same_memory_source(
                before.memory(),
                after.memory(),
                &read,
                8,
                &missing
            ));
        }
        assert!(
            !typed_read_has_same_memory_source(
                before.memory(),
                after.memory(),
                &read,
                16,
                &context
            ),
            "authority covers only eight bytes"
        );
        assert!(
            !typed_read_has_same_memory_source(
                before.memory(),
                after.memory(),
                &entry.offset_by_bytes(4),
                8,
                &context
            ),
            "partial membership in a separated field does not protect the whole read"
        );
    }
    assert!(
        !typed_read_has_same_memory_source(before.memory(), after.memory(), &read, 8, &original),
        "a sibling context must not inherit equalities or cached class payloads"
    );
}

#[test]
fn an_abstract_value_seeded_unchanged_is_its_source_states_load() {
    let address = Pointer::symbolic(Variable(98_470));
    let original = intern_memory(Memory::new());
    let seeded = original.memory().clone().with_seeded_cells(
        address.clone(),
        4,
        ProgramType::Int32,
        0,
        4,
        original.clone(),
    );
    assert_eq!(
        crate::kernel::eval::abstract_value_source(&seeded, &address),
        Some(original.clone())
    );
    // A word written since is not the source's, so neither is the value.
    let changed = seeded.clone().store(address.offset_by_bytes(4), int32(7));
    assert_eq!(
        crate::kernel::eval::abstract_value_source(&changed, &address),
        None
    );
    // Only the value's first word was seeded: its second is unknown.
    let partial = original.memory().clone().with_seeded_cells(
        address.clone(),
        4,
        ProgramType::Int32,
        0,
        1,
        original.clone(),
    );
    assert_eq!(
        crate::kernel::eval::abstract_value_source(&partial, &address),
        None
    );
}

/// The abstract-value counterpart of
/// `conditions_equal_modulo_proven_states_needs_frame_evidence`: a fact
/// stating the value a field of abstract type holds at one state proves
/// the same equality read at another state only when the two states
/// are proven to agree at the field.
#[test]
fn an_abstract_value_fact_carries_across_states_only_with_frame_evidence() {
    let before = Memory::new()
        .with_block("arg-memory", 16)
        .with_block("call-havoc:0", 0);
    let after = before.clone().with_block("call-havoc:1", 0);
    let field = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(98_480)), 4),
    };
    let parameter = TypeParameterName::intern("T");
    let value = AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::Variable(Variable(98_481)),
    };
    let read = |memory: &Memory| {
        let ProgramValue::Parameter(load) = AlgebraicTermNode::parameter_load(
            crate::kernel::intern_memory(memory.clone()),
            field.clone(),
            parameter,
        ) else {
            unreachable!("a parameter load is a parameter value");
        };
        ConditionTerm::AlgebraicEqual(load, Box::new(value.clone()))
    };
    let stated = |context: PureFactContext| context.assume_condition(read(&before), true);

    assert!(
        !stated(PureFactContext::new())
            .proves_algebraic_condition_modulo_states(&read(&after), true),
        "an unframed call havoc must not carry the value"
    );

    let effect = Proposition::MemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![MemoryRange::new(
            Pointer {
                block: "other-memory".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            0u32.into(),
            1u32.into(),
        )],
    };
    let (_, _, equality) = super::explicit_frame(
        &before,
        &after,
        &field,
        ProgramType::Parameter(parameter),
        &[effect],
        &PureFactContext::new(),
    )
    .expect("the explicit footprint preserves the abstract typed read");
    let premises = vec![Proposition::ConditionIs(read(&before), true), equality];
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
    for expected in [true, false] {
        let result = crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &Proposition::ConditionIs(read(&after), expected),
            &premises,
            &facts,
        );
        assert_eq!(
            result.is_ok(),
            expected,
            "explicit abstract equality must transport only the stated value"
        );
    }
}

#[test]
fn abstract_reads_follow_address_equalities_in_the_shared_graph() {
    let memory = intern_memory(Memory::new());
    let left = Pointer::symbolic(Variable(98_490));
    let right = Pointer::symbolic(Variable(98_491));
    let parameter = TypeParameterName::intern("ReadCongruenceT");
    let read = |pointer: &Pointer, memory: &SharedMemory| AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::MemoryLoad {
            memory: memory.clone(),
            pointer: Box::new(pointer.clone()),
        },
    };
    let a = read(&left, &memory);
    let b = read(&right, &memory);
    let context = PureFactContext::new();
    assert!(!context.equality_graph.are_algebraic_equal(&a, &b));
    let context = context.assume_condition(
        ConditionTerm::pointer_equal(left.clone(), right.clone()),
        true,
    );
    assert!(
        context.equality_graph.are_algebraic_equal(&a, &b),
        "equal addresses give equal abstract reads of the same state"
    );
    let changed = intern_memory(memory.memory().clone().store(left.clone(), int32(9)));
    assert!(
        !context
            .equality_graph
            .are_algebraic_equal(&a, &read(&left, &changed))
    );
    let source = intern_memory(
        Memory::new().with_block_without_derivation("local:abstract-read-projection", 4),
    );
    let projected = crate::kernel::memory_provenance::canonical_value_load_memory(
        &source,
        &left,
        crate::kernel::ABSTRACT_VALUE_WIDTH,
    );
    assert_ne!(projected, source);
    assert!(
        context
            .equality_graph
            .are_algebraic_equal(&read(&left, &projected), &read(&right, &source),)
    );
    // The read's address may itself be a named pointer read. Its producer
    // definitions must be registered by the common expression operand walk.
    let nested_left = Pointer::loaded_value(&projected, &left);
    let nested_right = Pointer::loaded_value(&source, &right);
    assert!(
        context
            .equality_graph
            .are_algebraic_equal(&read(&nested_left, &memory), &read(&nested_right, &memory),)
    );
    let other_type = AlgebraicTerm {
        algebraic_type: TypeParameterName::intern("ReadCongruenceU").algebraic_type(),
        node: a.node.clone(),
    };
    assert!(!context.equality_graph.are_algebraic_equal(&a, &other_type));
    assert!(
        !context
            .restricted_to_facts(&[], &[])
            .equality_graph
            .are_algebraic_equal(&a, &b)
    );
}

#[test]
fn abstract_read_naming_retains_its_selected_width_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(98_499));
    let source = intern_memory(
        Memory::new()
            .with_block_without_derivation("local:abstract-origin", 4)
            .store(
                Pointer {
                    block: "local:abstract-origin".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                int32(7),
            ),
    );
    let parameter = TypeParameterName::intern("ReadOriginT");
    let ProgramValue::Parameter(named) =
        AlgebraicTermNode::parameter_load(source.clone(), address.clone(), parameter)
    else {
        panic!("parameter read");
    };
    let observed = AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::MemoryLoad {
            memory: source.clone(),
            pointer: Box::new(address.clone()),
        },
    };
    assert_ne!(*named, observed);
    let context = PureFactContext::new();
    assert!(
        context
            .equality_graph
            .are_algebraic_equal(&named, &observed)
    );
    let AlgebraicTermNode::MemoryLoad { memory, .. } = &named.node else {
        unreachable!()
    };
    assert!(crate::kernel::prelude::value_load_origin(memory, &address, 16).is_none());
    let changed = intern_memory(
        source
            .memory()
            .clone()
            .store(address.offset_by_bytes(4), int32(9)),
    );
    let changed_read = AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::MemoryLoad {
            memory: changed,
            pointer: Box::new(address),
        },
    };
    assert!(
        !context
            .equality_graph
            .are_algebraic_equal(&named, &changed_read)
    );
}

#[test]
fn program_store_cache_cleanup_records_only_the_original_store_edge() {
    for partial in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = arc_pointer(0);
        let root = Memory::new().with_block("arg-memory", 32);
        let before = intern_memory(root.clone().store(
            field.clone(),
            ProgramValue::Int64(MachineTerm::int64_constant(7)),
        ));
        let write = if partial {
            field.offset_by_bytes(4)
        } else {
            Pointer::symbolic(Variable(998_950))
        };
        let after = intern_memory(before.memory().clone().store_classed_with_context(
            write.clone(),
            int32(2),
            &PureFactContext::new(),
            None,
        ));
        let edge = after.derivation().expect("completed store has an edge");
        assert!(matches!(edge.as_ref(), MemoryDerivation::Store { base, .. } if base == &before));
        assert!(
            after.known_value(&field).is_none(),
            "possibly overwritten cached value is discarded"
        );
        assert!(
            before.known_value(&field).is_some(),
            "the persistent parent retains its value"
        );
        assert_ne!(
            after.memory(),
            &root.store(write, int32(2)),
            "losing a possible value must retain the original memory identity"
        );
    }
}
