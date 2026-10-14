// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[test]
fn rewritten_load_store_witness_binds_value_address_and_snapshot() {
    // The load is an `int32` one: a stored value answers only for a read of
    // its own width, and an unrecorded width is the widest scalar access.
    crate::kernel::eval::declare_load_access_width(&arc_pointer(4), 4);
    let index = Bitvector32Term::Variable(Variable(971));
    let value = Bitvector32Term::Variable(Variable(972));
    let write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index, Bitvector32Term::Constant(1)),
        true,
    );
    let memory = CMemory::new()
        .with_block("arg-memory", 32)
        .store(write, CValue::Int32(value.clone()));
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(arc_pointer(4)),
        crate::kernel::LoadKind::Bits32,
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
        Bitvector32Term::Constant(7),
        load.clone(),
        &assumptions,
        &events
    ));
    let wrong_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(arc_pointer(8)),
        crate::kernel::LoadKind::Bits32,
    );
    assert!(!witness.checks_retargeted_for_test(value.clone(), wrong_load, &assumptions, &events));
    let overwritten = memory.store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(8)));
    let overwritten_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&overwritten),
        Box::new(arc_pointer(4)),
        crate::kernel::LoadKind::Bits32,
    );
    assert!(!witness.checks_retargeted_for_test(value, overwritten_load, &assumptions, &events));
}

#[test]
fn rewritten_integer_word_observations_retain_checked_store_evidence() {
    use crate::kernel::proof::ProofFacts;
    let pointer = arc_pointer(4);
    crate::kernel::eval::declare_load_access_width(&pointer, 4);
    let value = Bitvector32Term::Variable(Variable(989_001));
    for stored in [CValue::Int32(value.clone()), CValue::UInt32(value.clone())] {
        let memory = CMemory::new()
            .with_block("arg-memory", 16)
            .store(pointer.clone(), stored);
        let load = |memory: &CMemory, pointer: Pointer| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(pointer),
                crate::kernel::LoadKind::Bits32,
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
            let presented = goal(ty, value.clone());
            assert!(
                facts
                    .with_checked_rewritten_loads(&original, &presented)
                    .is_some(),
                "the same stored word has the same observation in its fixed format"
            );
            let source = Bitvector32Term::Variable(Variable(989_003));
            let cited =
                Proposition::ConditionIs(ConditionTerm::equal(source.clone(), value.clone()), true);
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
                    .with_checked_rewritten_loads(&original, &goal(other, value.clone()))
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
            let overwritten = memory
                .clone()
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(8)));
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
fn rewritten_integer_observations_preserve_binders_and_selected_goal_work() {
    use crate::kernel::proof::ProofFacts;
    let variable = Variable(989_002);
    let word = Bitvector32Term::Variable(variable);
    let one = Bitvector32Term::Constant(1);
    let facts = ProofFacts::from_ordered(&[Proposition::ConditionIs(
        ConditionTerm::equal(word.clone(), one.clone()),
        true,
    )]);
    let observed = |bits| IntegerTerm::from_machine(MachineIntegerType::Int32, bits).unwrap();
    let goal = |bits| Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::integer_equal(observed(bits), IntegerTerm::constant_i64(1)),
            true,
        )),
    };
    assert!(
        facts
            .with_checked_rewritten_loads(&goal(word.clone()), &goal(one))
            .is_none()
    );
    let leaf = Proposition::ConditionIs(
        ConditionTerm::integer_equal(observed(word.clone()), observed(word)),
        true,
    );
    // Corresponding-leaf validation must not scan unrelated premises or
    // revisit a goal's growing conjunction prefix.
    for size in [4, 8, 16, 32] {
        let mut proposition = leaf.clone();
        for _ in 0..size {
            proposition = Proposition::And(Box::new(leaf.clone()), Box::new(proposition));
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.with_checked_rewritten_loads(&proposition, &proposition)
        });
        assert!(checked.is_some());
        assert_eq!(work, 2 * size + 1);
    }
}

#[test]
fn rewritten_goal_comparison_visits_only_the_selected_proposition() {
    let facts = crate::kernel::proof::ProofFacts::default();
    for size in [4, 8, 16, 32] {
        let leaf = Proposition::ConditionIs(
            ConditionTerm::equal(Bitvector32Term::Constant(0), Bitvector32Term::Constant(0)),
            true,
        );
        let mut goal = leaf.clone();
        for _ in 0..size {
            goal = Proposition::And(Box::new(leaf.clone()), Box::new(goal));
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.with_checked_rewritten_loads(&goal, &goal)
        });
        assert!(checked.is_some());
        assert_eq!(work, 2 * size + 1);
    }
}

#[test]
fn rewritten_goal_does_not_reuse_an_ambient_equality_for_a_bound_variable() {
    let variable = Variable(981);
    let term = Bitvector32Term::Variable(variable);
    let one = Bitvector32Term::Constant(1);
    let premise = Proposition::ConditionIs(ConditionTerm::equal(term.clone(), one.clone()), true);
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&[premise]);
    let goal = |value| Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(value, Bitvector32Term::Constant(2)),
            true,
        )),
    };
    assert!(
        facts
            .with_checked_rewritten_loads(&goal(term), &goal(one))
            .is_none()
    );
}

#[test]
fn rewritten_store_witness_work_scales_with_selected_memory_path() {
    crate::kernel::eval::declare_load_access_width(&arc_pointer(4), 4);
    for size in [1, 2, 4, 8] {
        let value = Bitvector32Term::Constant(17);
        let mut memory = CMemory::new()
            .with_block("arg-memory", 128)
            .store(arc_pointer(4), CValue::Int32(value.clone()));
        for index in 0..size {
            memory = memory.with_block(format!("unrelated-{size}-{index}"), 4);
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(arc_pointer(4)),
            crate::kernel::LoadKind::Bits32,
        );
        let assumptions = PureFactContext::new();
        let capture = CheckedLoadEqualityCapture::start();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            checked_stored_origin_equality(&value, &load, &assumptions)
        });
        assert!(equal);
        assert!(
            work >= size && work <= 40 * (size + 1),
            "size {size}: {work}"
        );
        let witnesses = capture.finish();
        assert_eq!(witnesses.len(), 1);
        assert!(witnesses[0].checks(&assumptions));
    }
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
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(733)), 4),
    };
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("arg-memory", 32));
    let load = Bitvector32Term::MemoryLoad(
        memory.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
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
    let index = Bitvector32Term::Variable(Variable(710));
    let left_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::add(Bitvector32Term::Constant(5), index.clone()),
            4,
        ),
    };
    let right_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Constant(5), 4),
    };
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("arg-memory", 32));
    let left = Bitvector32Term::MemoryLoad(
        memory.clone(),
        Box::new(left_pointer),
        crate::kernel::LoadKind::Bits32,
    );
    let right = Bitvector32Term::MemoryLoad(
        memory,
        Box::new(right_pointer),
        crate::kernel::LoadKind::Bits32,
    );
    let lower = ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone());
    let upper = ConditionTerm::signed_less_than(index, Bitvector32Term::Constant(1));
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
    let base = CMemory::new().with_block("arg-memory", 16);
    let left =
        base.clone()
            .with_call_memory_havoc(Variable(700), &mutable_ranges, &assumptions, None);
    let right = base
        .with_block_without_derivation("local:recomputed-view", 4)
        .with_call_memory_havoc(Variable(700), &mutable_ranges, &assumptions, None);
    assert_ne!(left, right);

    let left_memory = crate::kernel::intern_c_memory_ref(&left);
    let right_memory = crate::kernel::intern_c_memory_ref(&right);
    let event = crate::kernel::proof::CheckedCallEvent::new(left_memory.clone());
    let events = crate::kernel::proof::CheckedCallEvents::containing_for_test(&event);
    let left_load = Bitvector32Term::MemoryLoad(
        left_memory.clone(),
        Box::new(loaded.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let right_load = Bitvector32Term::MemoryLoad(
        right_memory.clone(),
        Box::new(loaded.clone()),
        crate::kernel::LoadKind::Bits32,
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
            Bitvector32Term::MemoryLoad(
                left_memory,
                Box::new(retargeted.clone()),
                crate::kernel::LoadKind::Bits32
            ),
            Bitvector32Term::MemoryLoad(
                right_memory,
                Box::new(retargeted),
                crate::kernel::LoadKind::Bits32
            ),
            &assumptions,
            &events,
        ),
        "checked call evidence is query-specific",
    );
}

#[test]
fn checked_load_equality_retains_canonical_projection_provenance() {
    let source = CMemory::new()
        .with_block_without_derivation("arg-memory", 16)
        .with_block_without_derivation("local:i", 4);
    let source = crate::kernel::intern_c_memory_ref(&source);
    let pointer = arc_pointer(0);
    let original = Bitvector32Term::MemoryLoad(
        source.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let projected = canonicalize_atomic_loads_deep(&original);
    let Bitvector32Term::MemoryLoad(projected_memory, _, _) = &projected else {
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
    let older = crate::kernel::intern_c_memory_ref(
        &CMemory::new()
            .with_block_without_derivation("arg-memory", 16)
            .with_block_without_derivation("local:older", 4),
    );
    let newer = crate::kernel::intern_c_memory_ref(
        &CMemory::new()
            .with_block_without_derivation("arg-memory", 16)
            .with_block_without_derivation("local:newer", 4),
    );
    let pointer = arc_pointer(0);
    let newer_load = Bitvector32Term::MemoryLoad(
        newer.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let projected = canonicalize_atomic_loads_deep(&newer_load);
    let Bitvector32Term::MemoryLoad(projected_memory, _, _) = &projected else {
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

    let older_load = Bitvector32Term::MemoryLoad(
        older.clone(),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Bits32,
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
    let before = CMemory::new().with_block("arg-memory", 16);
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

#[test]
fn reinterning_retained_memory_uses_shallow_component_identity() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut memory = CMemory::new();
            for index in 0..size {
                memory = memory.with_block(format!("shallow-memory-{size}-{index}"), 4);
            }
            let first = crate::kernel::intern_c_memory_ref(&memory);
            let (second, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::intern_c_memory_ref(&memory)
            });
            assert_eq!(first.arena_id(), second.arena_id());
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.iter().all(|(_, work)| *work == 0),
        "reinterning retained memory should not hash its contents: {samples:?}"
    );
}

// --- named-memory-states arc: the derivation DAG -------------------------
// See docs/internals/memory-dag.md. These pin the two invariants
// the arc's safety argument rests on (advisory-only, and parent id < child
// id) plus the havoc-identity property that must hold by construction.

#[test]
fn a_store_records_the_edge_from_the_snapshot_it_wrote() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let after = base
        .clone()
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(7)));

    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("a store records how the snapshot was produced");
    match derivation.as_ref() {
        CMemoryDerivation::Store {
            base: recorded_base,
            pointer,
            value,
            ..
        } => {
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(pointer, &arc_pointer(4));
            assert_eq!(value, &CValue::Int32(Bitvector32Term::Constant(7)));
        }
        other => panic!("expected a store edge, got {other:?}"),
    }
}

#[test]
fn retained_store_hops_carry_locally_checkable_distinctness_proofs() {
    let base = CMemory::new().with_block("arg-memory", 32);
    let root = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100))),
            byte_width: 4,
        },
    };

    let constant_write = root.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let constant_read = root.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let after_constant = base
        .clone()
        .store(constant_write, CValue::Int32(Bitvector32Term::Constant(7)));
    let constant_evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_c_memory_ref(&after_constant),
        &crate::kernel::intern_c_memory_ref(&base),
        &constant_read,
        crate::kernel::LoadKind::Bits32,
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
    let constant_left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_constant),
        Box::new(constant_read.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let constant_right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&base),
        Box::new(constant_read.clone()),
        crate::kernel::LoadKind::Bits32,
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

    let write_index = Bitvector32Term::Variable(Variable(101));
    let read_index = Bitvector32Term::Variable(Variable(102));
    let symbolic_write = root.offset_by_int32_elements(write_index.clone());
    let symbolic_read = root.offset_by_int32_elements(read_index.clone());
    // An `int32` element read. A width-less load would stand in eight bytes
    // and reach into the next element, which `i != j` cannot separate.
    crate::kernel::eval::declare_load_access_width(&symbolic_read, 4);
    let inequality = ConditionTerm::equal(write_index, read_index);
    let assumptions = PureFactContext::new().assume_condition(inequality.clone(), false);
    let after_symbolic = base.store(symbolic_write, CValue::Int32(Bitvector32Term::Constant(9)));
    let symbolic_evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_c_memory_ref(&after_symbolic),
        &crate::kernel::intern_c_memory_ref(&CMemory::new().with_block("arg-memory", 32)),
        &symbolic_read,
        crate::kernel::LoadKind::Bits32,
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
    let symbolic_left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_symbolic),
        Box::new(symbolic_read.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let symbolic_right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&CMemory::new().with_block("arg-memory", 32)),
        Box::new(symbolic_read),
        crate::kernel::LoadKind::Bits32,
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
    let derivation = assumptions
        .derive_atomic_proposition(&symbolic_goal)
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
fn retained_common_base_store_hop_carries_a_signed_order_path() {
    let base = CMemory::new().with_block("arg-memory", 64);
    let root = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(109))),
            byte_width: 4,
        },
    };
    let write_index = Bitvector32Term::Variable(Variable(110));
    let middle = Bitvector32Term::Variable(Variable(111));
    let read_index = Bitvector32Term::Variable(Variable(112));
    let first = ConditionTerm::signed_less_than(write_index.clone(), middle.clone());
    let second = ConditionTerm::signed_less_equal(middle, read_index.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(first.clone(), true)
        .assume_condition(second.clone(), true);
    let write = root.offset_by_int32_elements(write_index.clone());
    let read = root.offset_by_int32_elements(read_index.clone());
    let after = base
        .clone()
        .store(write, CValue::Int32(Bitvector32Term::Constant(7)));
    let evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_c_memory_ref(&after),
        &crate::kernel::intern_c_memory_ref(&base),
        &read,
        crate::kernel::LoadKind::Bits32,
        &assumptions,
    )
    .expect("the derived index inequality crosses the store");
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
            .map(SignedOrderDerivationStep::premise)
            .cloned()
            .collect::<Vec<_>>(),
        vec![
            Proposition::ConditionIs(first, true),
            Proposition::ConditionIs(second.clone(), true),
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
    let base = CMemory::new().with_block("arg-memory", 64);
    let range_base = |variable| Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let write_base = range_base(110);
    let load_base = range_base(111);
    let write_range = memory_range(write_base.clone(), 0, 2);
    let load_range = memory_range(load_base.clone(), 0, 2);
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(write_range.clone())),
        right: Box::new(CResource::Memory(load_range.clone())),
    };
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(write_range.clone()))
        .unchecked_with_fact(CResourceFact::own_memory(load_range.clone()));
    let direct_assumptions = PureFactContext::new().assume_proposition(separation.clone());
    let composed_assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceComposition(resources.clone()));
    let write = write_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let load = load_base.offset_by_int32_elements(Bitvector32Term::Constant(0));
    let after = base
        .clone()
        .store(write, CValue::Int32(Bitvector32Term::Constant(7)));
    let left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&base),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Bits32,
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
    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("the written snapshot retains its store");
    assert!(
        !composed.checks(derivation.as_ref(), &load, 4, &PureFactContext::new()),
        "the retained composition must still be present during checking"
    );
}

#[test]
fn entry_separation_does_not_frame_a_store_after_its_bases_become_equal() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(130_001)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(130_002)), 4),
    };
    let bridge = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(130_003)), 4),
    };
    let left_range = memory_range(left.clone(), 0, 1);
    let right_range = memory_range(right.clone(), 0, 1);
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(left_range.clone())),
        right: Box::new(CResource::Memory(right_range.clone())),
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
            &CResource::Memory(left_range.clone()),
            &CResource::Memory(right_range.clone()),
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
        .store(left.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("the written snapshot retains its store");
    assert!(
        !retained.checks(derivation.as_ref(), &right, 4, &assumptions),
        "a retained hop must be refused after its own ranges become overlapping"
    );
}

#[test]
fn equal_range_bases_keep_a_separation_for_disjoint_byte_intervals() {
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(130_011)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(130_012)), 4),
    };
    let left_range = memory_range(left.clone(), 0, 1);
    let right_range = memory_range(right.clone(), 1, 2);
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(left_range.clone())),
        right: Box::new(CResource::Memory(right_range.clone())),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(separation)
        .assume_condition(ConditionTerm::pointer_equal(left, right), true);

    assert!(
        !assumptions.memory_ranges_overlap_after_base_equality(&left_range, &right_range),
        "adjacent element intervals remain separate when their bases are equal"
    );
    assert!(assumptions.proves_resource_separate(
        &CResource::Memory(left_range),
        &CResource::Memory(right_range),
    ));
}

#[test]
fn separated_range_store_hop_retains_symbolic_membership_bounds() {
    let base = CMemory::new().with_block("arg-memory", 64);
    let range_base = |variable| Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let write_base = range_base(120);
    let load_base = range_base(121);
    let write_range = memory_range(write_base.clone(), 0, 3);
    let load_range = memory_range(load_base.clone(), 0, 3);
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(write_range)),
        right: Box::new(CResource::Memory(load_range)),
    };
    let write_index = Bitvector32Term::Variable(Variable(122));
    let load_index = Bitvector32Term::Variable(Variable(123));
    let zero_le_write =
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), write_index.clone());
    let write_lt_three =
        ConditionTerm::signed_less_than(write_index.clone(), Bitvector32Term::Constant(3));
    let zero_le_load =
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), load_index.clone());
    let load_lt_write_successor = ConditionTerm::signed_less_than(
        load_index.clone(),
        Bitvector32Term::add(write_index.clone(), Bitvector32Term::Constant(1)),
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
        .store(write, CValue::Int32(Bitvector32Term::Constant(7)));
    // Bits32 also encodes LP64 pointers. These terms represent int32 reads,
    // so use the typed producer to record their four-byte access width.
    crate::kernel::eval::symbolic_load_value(&base, &load, CType::Int32).unwrap();
    crate::kernel::eval::symbolic_load_value(&after, &load, CType::Int32).unwrap();
    let left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&base),
        Box::new(load.clone()),
        crate::kernel::LoadKind::Bits32,
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
    let retargeted = load_base.offset_by_int32_elements(Bitvector32Term::add(
        load_index,
        Bitvector32Term::Constant(1),
    ));
    assert!(
        !hop.justification
            .checks(hop.derivation.as_ref(), &retargeted, 4, &assumptions),
        "the membership evidence must remain tied to its exact index"
    );
}

#[test]
fn derivation_bases_are_strictly_older_so_the_dag_cannot_cycle() {
    // Storing a value and then storing it back re-interns the original
    // snapshot, which is the shortest cycle the DAG could otherwise grow.
    // First-wins recording keeps the older edge, so following `base` still
    // strictly decreases and terminates.
    let base = CMemory::new().with_block("arg-memory", 16);
    let written = base
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)));
    let restored = written
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(0)))
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)));
    assert_eq!(restored, written, "the round trip returns the same value");

    let mut node = crate::kernel::intern_c_memory_ref(&restored);
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
    let before = CMemory::new().with_block("arg-memory", 32);
    let length = Bitvector32Term::Variable(Variable(70_021));
    let range = CMemoryRange::new(arc_pointer(0), Bitvector32Term::Constant(0), length.clone());
    let empty = PureFactContext::new().assume_condition(
        ConditionTerm::equal(length.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let positive = PureFactContext::new().assume_condition(
        ConditionTerm::equal(length, Bitvector32Term::Constant(1)),
        true,
    );
    let make_call = |context: &PureFactContext| {
        before.clone().with_call_memory_havoc(
            Variable(70_020),
            std::slice::from_ref(&range),
            context,
            None,
        )
    };
    let load = |memory: &CMemory| {
        canonicalize_atomic_loads_deep(&Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(arc_pointer(0)),
            crate::kernel::LoadKind::Bits32,
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
    let base = CMemory::new().with_block("arg-memory", 32);
    let first_range = CMemoryRange::new(
        arc_pointer(0),
        Bitvector32Term::Variable(Variable(70_001)),
        Bitvector32Term::Variable(Variable(70_002)),
    );
    let second_range = CMemoryRange::new(
        arc_pointer(0),
        Bitvector32Term::Variable(Variable(70_003)),
        Bitvector32Term::Variable(Variable(70_004)),
    );

    // The marker variable and parent snapshot intentionally match. A
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
        "different symbolic write sets need distinct snapshots"
    );

    let first = crate::kernel::intern_c_memory_ref(&first);
    let second = crate::kernel::intern_c_memory_ref(&second);
    assert_ne!(first.arena_id(), second.arena_id());
    let CMemoryDerivation::CallHavoc { mutable_ranges, .. } = second
        .derivation()
        .expect("the second snapshot retains its own call-havoc edge")
        .as_ref()
        .clone()
    else {
        panic!("expected a call-havoc derivation");
    };
    assert_eq!(mutable_ranges, vec![second_range]);
}

#[test]
fn a_store_that_changes_nothing_records_no_edge_to_itself() {
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(3)));
    let again = base
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(3)));
    assert_eq!(again, base);

    let node = crate::kernel::intern_c_memory_ref(&again);
    if let Some(derivation) = node.derivation() {
        assert_ne!(
            derivation.base().arena_id(),
            node.arena_id(),
            "a snapshot must never be recorded as derived from itself"
        );
    }
}

#[test]
fn loop_havoc_is_its_own_edge_kind_and_keeps_its_marker_block() {
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(5)));
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
    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("loop havoc records how the snapshot was produced");
    match derivation.as_ref() {
        CMemoryDerivation::LoopHavoc {
            base: recorded_base,
            variable,
            mutable_ranges,
        } => {
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
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);

    // A call havoc changes the block set (it adds its marker block), so
    // the snapshot-diff matcher refuses to look at the cells at all. The
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
        "the snapshot-diff matcher is expected not to cross the marker block"
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

    let havoced_then_stored = havoced
        .clone()
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(9)));
    assert!(
        !checked_memory_load_equality(&base, &havoced_then_stored, &read, &PureFactContext::new(),),
        "a crossable store must not smuggle a walk past an intervening havoc"
    );
}

#[test]
fn loop_havoc_carries_a_verified_write_set_for_disjoint_loads() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let ranges = [memory_range(arc_pointer(8), 0, 8)];
    let havoced = base.clone().with_loop_memory_havoc_preserving_loans(
        Variable(8),
        &BTreeSet::new(),
        Some(&ranges),
        None,
    );

    let derivation = crate::kernel::intern_c_memory_ref(&havoced)
        .derivation()
        .expect("verified loop havoc records its write set");
    let CMemoryDerivation::LoopHavoc {
        mutable_ranges: Some(recorded),
        ..
    } = derivation.as_ref()
    else {
        panic!("expected a loop-havoc edge with ranges, got {derivation:?}");
    };
    assert_eq!(recorded, &ranges);

    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Bits32,
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
fn loan_preserving_havoc_uses_the_full_cell_footprint() {
    let pointer = arc_pointer(0);
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(5)));
    let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        pointer.clone(),
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(3),
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

/// Stage 4: the DAG-guided cell lookup answers load equality for snapshots
/// that are *siblings*, which the stage-2 walk cannot do because it only ever
/// asks whether one snapshot is reachable from the other.
///
/// Two calls, each havocking a range disjoint from the loaded cell, produce
/// two snapshots neither of which derives from the other. Value bridging
/// refuses them outright — each carries its own `call-havoc:N` marker block,
/// so the block sets differ and the snapshot matcher stops before looking at
/// any cell. Resolving both against the write history lands them on one
/// common ancestor, and the loads are equal with no snapshot comparison.
#[test]
fn sibling_snapshots_resolve_one_cell_to_a_common_ancestor() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let load_in = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Bits32,
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
        "the two marker blocks are expected to stop the snapshot matcher"
    );
    assert!(
        PureFactContext::new().memory_loads_proven_equal(&load_in(&left), &load_in(&right)),
        "the common-ancestor lookup is exactly what the DAG adds here"
    );
    let evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_c_memory_ref(&left),
        &crate::kernel::intern_c_memory_ref(&right),
        &read,
        crate::kernel::LoadKind::Bits32,
        &PureFactContext::new(),
    )
    .expect("a successful equality decision retains both traversed walks");
    assert_eq!(evidence.reason, MemoryDagLoadEqualityReason::CommonSource);
    assert_eq!(retained_memory_dag_path(&evidence.left).len(), 1);
    assert_eq!(retained_memory_dag_path(&evidence.right).len(), 1);
    assert_eq!(
        retained_memory_dag_path(&evidence.left)[0].derived.as_ref(),
        &left,
        "the left proof names the exact derived snapshot"
    );
    assert_eq!(
        retained_memory_dag_path(&evidence.right)[0]
            .derived
            .as_ref(),
        &right,
        "the right proof names the exact derived snapshot"
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
    let derivation =
        with_extended_dag_bridging(|| PureFactContext::new().derive_atomic_proposition(&goal))
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
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(201))),
            byte_width: 4,
        },
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(202))),
            byte_width: 4,
        },
    };
    // An `int32` element read. The forward-offset route proves the havoc
    // range starts one element later, which clears a four-byte access; a
    // width-less load would stand in eight bytes and reach into it.
    crate::kernel::eval::declare_load_access_width(&data, 4);
    let len = Bitvector32Term::Variable(Variable(203));
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(memory_range(owner.clone(), 0, 4))),
        right: Box::new(CResource::Memory(memory_range(data.clone(), 0, 16))),
    };
    let lower_bound = ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), len.clone());
    let assumptions = PureFactContext::new()
        .assume_proposition(separation.clone())
        .assume_condition(lower_bound.clone(), true);
    let mutable_ranges = vec![
        memory_range(owner, 0, 1),
        memory_range(data.offset_by_int32_elements(len), 0, 2),
    ];
    let base = CMemory::new().with_block("arg-memory", 64);
    let called =
        base.clone()
            .with_call_memory_havoc(Variable(204), &mutable_ranges, &assumptions, None);
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(data.clone()),
            crate::kernel::LoadKind::Bits32,
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
    assert!(matches!(
        &ranges[0],
        RangeDisjointFromPointerEvidence::SeparatedRanges {
            authority: StoreSeparatedRangesAuthority::ExactProposition(fact), ..
        } if fact == &separation
    ));
    assert_eq!(
        ranges[1],
        RangeDisjointFromPointerEvidence::ForwardOffset {
            offset: Bitvector32Term::Variable(Variable(203)),
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
    let offset_derivation =
        with_extended_dag_bridging(|| assumptions.derive_atomic_proposition(&offset_goal))
            .expect("pointer-offset structure retains the child load proof");
    assert!(matches!(
        &offset_derivation.rule,
        PropositionDerivationRule::ContextualAtomic {
            evidence: AtomicPropositionDerivationEvidence::PointerOffsetMemoryDag(_),
            ..
        }
    ));
    assert!(offset_derivation.check(&assumptions));
    // The snapshot is not a certificate for another path's assumptions.
    assert!(
        !offset_derivation.check(&PureFactContext::new()),
        "pointer-offset certificate checking must also require the separation and order premises"
    );
}

/// The owned-string loadable shape: the loadability fact and its bound facts
/// write `len` as a load at contract
/// entry, while the index the goal extracts writes it at a later snapshot
/// separated by a block declaration, stores, and a cell-forgetting prune —
/// exactly the edges (`BlockDeclared`, `CellsForgotten`) that used to leave
/// the two forms in disjoint DAG components. The loadable prover's
/// extended bridging connects them; everywhere outside that prover the new
/// edges must stay invisible (pinned by the frame-evidence test above and
/// the byte-identical check of the certified corpus).
#[test]
fn loadable_bound_check_bridges_len_forms_across_block_and_prune_edges() {
    let entry = CMemory::new().with_block("arg-memory", 64);
    let len_pointer = arc_pointer(0);
    // `len` is an `int32` field. A width-less load stands in eight bytes,
    // which the neighbouring store at offset four overlaps.
    crate::kernel::eval::declare_load_access_width(&len_pointer, 4);
    let len_at_entry = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry),
        Box::new(len_pointer.clone()),
        crate::kernel::LoadKind::Bits32,
    );

    // The recorded facts: the buffer loadability range and both `len` bounds, all
    // written at entry.
    let assumptions = PureFactContext::new()
        // Same-block loadability ranges that cannot cover `buffer[len]`. These used
        // to trigger costly general equality searches before the matching
        // symbolic range was considered.
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(0),
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(8),
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(12),
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(16),
            bytes: Bitvector32Term::Constant(32),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), len_at_entry.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(len_at_entry, Bitvector32Term::Constant(8)),
            true,
        );

    // The later snapshot: a local declared, a distinct cell written, and the
    // write-path prune that forgets it again. Its `len` load is a different
    // form of the same cell.
    let later = entry
        .clone()
        .with_block("local:i", 4)
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(9)))
        .store(arc_pointer(8), CValue::Int32(Bitvector32Term::Constant(2)))
        .without_possible_aliasing_cells(&arc_pointer(4), 4, &assumptions);
    let len_at_later = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&later),
        Box::new(len_pointer),
        crate::kernel::LoadKind::Bits32,
    );

    // loadable(buffer[len]) with `len` written at the later snapshot.
    let goal_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(16)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(len_at_later),
                byte_width: 4,
            }),
        ),
    };
    assert!(
        assumptions.proves_memory_loadable(&later, &goal_base, &Bitvector32Term::Constant(4)),
        "the viewable bound check must connect the two len forms along \
         the recorded block-declaration and cell-forgetting edges"
    );
}

#[test]
fn a_store_to_the_loaded_cell_is_not_crossable() {
    // A soundness property, so it must hold with the arc switched off too.
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let stored = base
        .clone()
        .store(read.clone(), CValue::Int32(Bitvector32Term::Constant(9)));

    assert!(
        !checked_memory_load_equality(&base, &stored, &read, &PureFactContext::new()),
        "the walk must refuse the very cell that was written"
    );
}

/// The premise-availability path matches two forms of one fact whose load
/// atoms carry different memory snapshots. The match is decided by proof, not
/// by ignoring the snapshots: an unframed call havoc between the two snapshots
/// blocks it, and an effect summary that frames the loaded pointer restores it.
#[test]
fn conditions_equal_modulo_proven_snapshots_needs_frame_evidence() {
    let before = CMemory::new()
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
    let condition = |memory: &CMemory| {
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(77)),
            Bitvector32Term::add(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory.clone()),
                    Box::new(loaded.clone()),
                    crate::kernel::LoadKind::Bits32,
                ),
                Bitvector32Term::Constant(1),
            ),
        )
    };

    // Same snapshot: the two forms are literally one condition.
    assert!(
        PureFactContext::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&before))
    );

    // A call havoc stands between the snapshots and nothing frames the load,
    // so the later form is a different fact, not another form.
    assert!(
        !PureFactContext::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
        "an unframed call havoc must not be matched away"
    );

    // With an effect summary whose mutable range misses the loaded pointer,
    // the two snapshots provably agree there and the forms match.
    let framed = PureFactContext::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            elsewhere,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });
    assert!(
        framed.conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
        "a framed load should match across the effect"
    );

    // Framing never relaxes the structure: a different condition stays
    // different however well the snapshots are framed.
    let other = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(78)),
        Bitvector32Term::add(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after.clone()),
                Box::new(loaded.clone()),
                crate::kernel::LoadKind::Bits32,
            ),
            Bitvector32Term::Constant(1),
        ),
    );
    assert!(!framed.conditions_equal_modulo_proven_snapshots(&condition(&before), &other));
}

/// A soundness property: load canonicalization may follow materialization
/// cells to their common source, but the jump must not erase a havoc that
/// could have written the loaded pointer. Here the loaded cell sits inside
/// the havoc's mutable range while a sibling materialization cell provably
/// survives; treating the post-havoc load as unchanged would transport a
/// stale fact across the mutation.
#[test]
fn sibling_materialization_cells_must_not_launder_a_havoc() {
    let pristine = CMemory::new().with_block("arg-memory", 16);
    let loaded = arc_pointer(0);
    let sibling = arc_pointer(4);
    let materialized = pristine
        .clone()
        .store(sibling.clone(), pristine.symbolic_int32_load(&sibling));
    let havocked = materialized.clone().with_call_memory_havoc(
        Variable(9000),
        &[CMemoryRange::new(
            loaded.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
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

fn symbolic_descriptor(identity: u64) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(identity)), 4),
    }
}

/// A pointer cell holding exactly the pointer a load of that cell reads is a
/// materialization like an integer one: the cell is named at its source, so a
/// load of a neighbouring cell through the materialized snapshot keeps the
/// name it has at the source. Only the pointer a typed load of *this* cell
/// produces qualifies: another cell's load, or the same load scaled at a
/// width other than the pointee's, is a write the load cannot pass over.
#[test]
fn a_materialized_pointer_cell_is_named_at_its_source() {
    let pristine = CMemory::new().with_block("arg-memory", 32);
    // Two descriptors at unrelated symbolic addresses: nothing structural
    // separates their cells, so only the materialization rule passes over.
    let loaded = symbolic_descriptor(92_000);
    let sibling = symbolic_descriptor(92_001);
    let name = |memory: &CMemory, pointer: &Pointer| {
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory_ref(memory),
            pointer.clone(),
            crate::kernel::LoadKind::Pointer,
        )
    };
    let pointer_value = |index: Bitvector32Term, width: i64, c_type: CType| {
        CValue::typed_pointer(
            Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(index, width),
            },
            c_type,
        )
    };
    let own = name(&pristine, &sibling);
    assert!(matches!(own, Bitvector32Term::Variable(_)));

    let materialized = pristine.clone().store(
        sibling.clone(),
        pointer_value(own.clone(), 4, CType::Int32Pointer),
    );
    assert_eq!(
        name(&materialized, &loaded),
        name(&pristine, &loaded),
        "a pointer cell holding its own load is passed over"
    );

    let foreign = name(&pristine, &symbolic_descriptor(92_002));
    for (value, why) in [
        (
            pointer_value(foreign, 4, CType::Int32Pointer),
            "another cell's load is a real write",
        ),
        (
            pointer_value(own, 4, CType::Int16Pointer),
            "a scale other than the pointee width is not this cell's load",
        ),
    ] {
        let written = pristine.clone().store(sibling.clone(), value);
        assert_ne!(name(&written, &loaded), name(&pristine, &loaded), "{why}");
    }
}

/// The pointer form of `sibling_materialization_cells_must_not_launder_a_havoc`:
/// a materialized pointer cell that survives a havoc must not carry a load
/// the havoc may have written back to the pre-havoc snapshot.
#[test]
fn a_materialized_pointer_cell_must_not_launder_a_havoc() {
    let pristine = CMemory::new().with_block("arg-memory", 32);
    let loaded = symbolic_descriptor(92_010);
    let sibling = symbolic_descriptor(92_011);
    let own = crate::kernel::eval::canonical_form_of_load(
        crate::kernel::intern_c_memory_ref(&pristine),
        sibling.clone(),
        crate::kernel::LoadKind::Bits32,
    );
    let materialized = pristine.clone().store(
        sibling.clone(),
        CValue::typed_pointer(
            Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(own, 4),
            },
            CType::Int32Pointer,
        ),
    );
    let havocked = materialized.clone().with_call_memory_havoc(
        Variable(9001),
        &[CMemoryRange::new(
            loaded.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
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

fn symbolic_element_pointer(index: &Bitvector32Term) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91_000)), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    }
}

#[test]
fn a_symbolic_store_requires_the_current_paths_separation_order() {
    let index = Bitvector32Term::Variable(Variable(91_001));
    let length = Bitvector32Term::Variable(Variable(91_002));
    let written = symbolic_element_pointer(&index);
    let kept = symbolic_element_pointer(&length);
    // `kept` is never materialized: the observable is the canonical form of
    // its load, which only a crossed store edge keeps at the base snapshot.
    let base = CMemory::new().with_block("arg-memory", 64);
    let ordered = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(index.clone(), length.clone()),
        true,
    );

    let separated = base
        .clone()
        .store_with_context(written.clone(), int32(7), &ordered);
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(kept.clone()),
            crate::kernel::LoadKind::Bits32,
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
            crate::kernel::intern_c_memory_ref(&unordered),
            kept.clone(),
            crate::kernel::LoadKind::Bits32
        ),
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory_ref(&base),
            kept,
            crate::kernel::LoadKind::Bits32
        ),
        "without a recorded order the write may alias the loaded cell"
    );
}

#[test]
fn direct_strict_order_is_an_indexed_lookup() {
    let a = Bitvector32Term::Variable(Variable(91_101));
    let b = Bitvector32Term::Variable(Variable(91_102));
    let c = Bitvector32Term::Variable(Variable(91_103));
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

#[test]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn checked_order_store_crossing_ignores_unrelated_order_facts() {
    let samples = [16_u64, 64, 256, 1024, 4096]
        .into_iter()
        .map(|size| {
            let index = Bitvector32Term::Variable(Variable(92_000_000 + size * 10 + 1));
            let length = Bitvector32Term::Variable(Variable(92_000_000 + size * 10 + 2));
            let written = symbolic_element_pointer(&index);
            let kept = symbolic_element_pointer(&length);
            let mut context = PureFactContext::new();
            for unrelated in 0..size {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(93_000_000 + unrelated * 2)),
                        Bitvector32Term::Variable(Variable(93_000_000 + unrelated * 2 + 1)),
                    ),
                    true,
                );
            }
            let context =
                context.assume_condition(ConditionTerm::signed_less_than(index, length), true);
            let base = CMemory::new().with_block(format!("arg-memory-{size}"), 64);
            let separated = base.clone().store_with_context(written, int32(7), &context);
            let load = |memory: &CMemory| {
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory_ref(memory),
                    Box::new(kept.clone()),
                    crate::kernel::LoadKind::Bits32,
                )
            };
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_extended_dag_bridging(|| {
                    atomic_memory_load_equality_evidence(&load(&separated), &load(&base), &context)
                })
            });
            assert!(
                resolved.is_some(),
                "the store must be crossed at size {size}"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let first = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= first.saturating_mul(4).max(first + 64)),
        "crossing a store by its frozen order must not scale with unrelated facts: {samples:?}"
    );
}

/// The derivation walk has no hop cap: a load of an untouched cell is
/// framed across any number of stores to other cells, and the walk's work
/// grows with the chain's length.
#[test]
fn memory_dag_walks_follow_chains_of_any_length() {
    let samples = [32, 64, 128, 256]
        .into_iter()
        .map(|size| {
            let entry = CMemory::new().with_block("arg-memory", 4096);
            let mut memory = entry.clone();
            for index in 0..size {
                memory = memory.store(
                    arc_pointer(8 + 4 * index),
                    CValue::Int32(Bitvector32Term::Constant(index as u32)),
                );
            }
            let read = arc_pointer(0);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                checked_memory_load_equality(&entry, &memory, &read, &PureFactContext::new())
            });
            assert!(equal, "the cell is untouched across {size} stores");
            (size, work)
        })
        .collect::<Vec<_>>();
    let (small, large) = (samples[0].1.max(1), samples[3].1);
    assert!(
        large <= small * 16,
        "the walk's work should grow linearly with the chain: {samples:?}"
    );
}

/// Canonicalization has no depth cut: its explicit worklist reaches a
/// materialized cell however deeply the load sits in the term, with work
/// linear in the term it traverses.
#[test]
fn canonical_form_resolves_loads_at_any_depth() {
    let memory = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(7)));
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(arc_pointer(4)),
        crate::kernel::LoadKind::Bits32,
    );
    let mut samples = Vec::new();
    for depth in [64, 128, 256, 512] {
        let mut term = load.clone();
        for _ in 0..depth {
            term = Bitvector32Term::Add(Box::new(term), Box::new(Bitvector32Term::Constant(1)));
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
        while let Bitvector32Term::Add(left, _) = leaf {
            leaf = left;
        }
        assert_eq!(
            leaf,
            &Bitvector32Term::Constant(7),
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
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(88_002)), 4),
    };
    let written = memory_range(
        Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(88_001)), 4),
        },
        0,
        2,
    );
    let separated = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(written.clone())),
        right: Box::new(CResource::Memory(memory_range(cell.clone(), 0, 2))),
    });

    let load_in = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(cell.clone()),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let base = CMemory::new().with_block("arg-memory", 64);
    let (name, _) = load_variable_for_term(&load_in(&base)).expect("a load term has a name");
    // Materializing a viewed cell records its own load variable in the cell,
    // which is the state the callback fixtures reach before their first call.
    let materialized = base.store(cell.clone(), CValue::Int32(Bitvector32Term::Variable(name)));

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
    let one = || CValue::Int32(Bitvector32Term::Constant(1));
    let epoch = |memory: &CMemory, block: PointerBlock| {
        crate::kernel::resource_tracker::last_same_point(
            crate::kernel::resource_tracker::Resource::Block(&block),
            &crate::kernel::resource_tracker::ProgramPoint::at(&crate::kernel::intern_c_memory(
                memory.clone(),
            )),
        )
        .expect("a block always has a last-same point")
        .memory()
        .clone()
    };

    // Declaring an object writes nothing, and a declaration proven distinct
    // from the subject is crossed too, so an epoch reaches back past the
    // declarations that precede it. The assertions below name the snapshot the
    // walk actually reaches rather than "the entry state".
    let just_g = CMemory::new().with_block(global(), 16);
    let globals = just_g.clone().with_block(other_global(), 16);
    let entry = globals.clone().with_block(local(), 4);

    // The hole this closes: `g` may be the array the caller passed as `a`.
    let after_global_store = entry.clone().store(at(global(), 0), one());
    assert_eq!(
        epoch(&after_global_store, PointerBlock::ExternalArgument),
        after_global_store,
        "a store to a global may write the array argument, so the epoch is the live snapshot"
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

/// The block-epoch memo is keyed by interned snapshot, and interning dedups
/// by content, so an entry left behind by one verification would answer a
/// content-equal query in the next one — from a DAG history that
/// verification never built. `VerificationSession` clears it with the other
/// canonical-form caches, which is what keeps a result from depending on
/// what was verified earlier in the process.
#[test]
fn a_session_reset_empties_the_block_epoch_memo() {
    let memory = CMemory::new()
        .with_block(PointerBlock::Concrete("local:f:i".to_string()), 4)
        .store(
            Pointer {
                block: PointerBlock::Concrete("local:f:i".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Constant(1)),
        );
    crate::kernel::resource_tracker::last_same_point(
        crate::kernel::resource_tracker::Resource::Block(&PointerBlock::ExternalArgument),
        &crate::kernel::resource_tracker::ProgramPoint::at(&crate::kernel::intern_c_memory(memory)),
    );
    assert!(
        crate::kernel::resource_tracker::block_epoch_memo_len() > 0,
        "the walk should have recorded its epoch"
    );

    crate::kernel::memory_provenance::clear_canonical_form_caches();
    assert_eq!(
        crate::kernel::resource_tracker::block_epoch_memo_len(),
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
    let wide = CMemory::new().with_block("arg-memory", 32).store(
        arc_pointer(0),
        CValue::Int64(Bitvector32Term::Int64Constant(5)),
    );

    // Above the base, where the address test alone says "separate": the
    // int64 must still be gone, and nothing takes its place.
    for offset in 1..8 {
        let after = wide
            .clone()
            .without_possible_aliasing_cells(&arc_pointer(offset), 1, &bare)
            .store(
                arc_pointer(offset),
                CValue::UInt8(Bitvector32Term::Constant(7)),
            );
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
        .store(arc_pointer(0), CValue::UInt8(Bitvector32Term::Constant(7)));
    assert_eq!(
        after.known_value(&arc_pointer(0)),
        Some(CValue::UInt8(Bitvector32Term::Constant(7))),
        "a one-byte write at the base leaves its own byte, not the int64"
    );

    // Outside the cell's own bytes, the cell stays: this is what makes the
    // forgetting worth doing rather than dropping every cell on every store.
    let after = wide
        .clone()
        .without_possible_aliasing_cells(&arc_pointer(8), 1, &bare)
        .store(arc_pointer(8), CValue::UInt8(Bitvector32Term::Constant(7)));
    assert_eq!(
        after.known_value(&arc_pointer(0)),
        Some(CValue::Int64(Bitvector32Term::Int64Constant(5))),
        "a write past the int64's last byte leaves it readable"
    );

    // The symmetric direction: a wide write over the narrow cells it covers.
    let narrow = CMemory::new()
        .with_block("arg-memory", 32)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)))
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(2)))
        .store(arc_pointer(8), CValue::Int32(Bitvector32Term::Constant(3)));
    let after = narrow
        .without_possible_aliasing_cells(&arc_pointer(0), 8, &bare)
        .store(
            arc_pointer(0),
            CValue::Int64(Bitvector32Term::Int64Constant(9)),
        );
    assert_eq!(
        after.known_value(&arc_pointer(4)),
        None,
        "an eight-byte write at the base overwrites the int32 four bytes up"
    );
    assert_eq!(
        after.known_value(&arc_pointer(8)),
        Some(CValue::Int32(Bitvector32Term::Constant(3))),
        "an eight-byte write at the base stops before the int32 eight bytes up"
    );
}

/// Canonicalization for a load drops a cell it decides the load cannot
/// observe, which makes two snapshots compare equal at that load. The
/// interval it decides that by has to admit the widest load the kernel
/// performs, because the `MemoryLoad` term it is answering for carries no
/// width of its own.
///
/// Both polarities, over the widths that meet at one address: a cell four
/// bytes above the load is inside an eight-byte read and must survive, and a
/// cell eight bytes above it is outside every scalar read and may go.
#[test]
fn canonical_load_form_keeps_a_cell_a_wide_read_covers() {
    let base = CMemory::new().with_block("arg-memory", 32);
    let read = arc_pointer(0);
    let canonical_equal_across_store_at = |offset: i64, value: CValue| {
        let stored = base.clone().store(arc_pointer(offset), value);
        crate::kernel::reasoning::canonical_memory_for_pointer_load(&base, &read)
            == crate::kernel::reasoning::canonical_memory_for_pointer_load(&stored, &read)
    };

    // Inside the widest scalar read at `read`: every one of these cells is a
    // byte a sixteen-byte load of `read` returns.
    for offset in 1..16 {
        assert!(
            !canonical_equal_across_store_at(offset, CValue::UInt8(Bitvector32Term::Constant(7))),
            "a one-byte cell {offset} bytes above the load is inside an \
             sixteen-byte read of it and must not be dropped"
        );
    }
    assert!(
        !canonical_equal_across_store_at(4, CValue::Int32(Bitvector32Term::Constant(7))),
        "an int32 cell four bytes above the load is inside a \
         sixteen-byte read of it and must not be dropped"
    );
    assert!(
        !canonical_equal_across_store_at(6, CValue::Int16(Bitvector32Term::Constant(7))),
        "an int16 cell six bytes above the load is inside an eight-byte read"
    );
    assert!(
        !canonical_equal_across_store_at(0, CValue::Int64(Bitvector32Term::Int64Constant(7))),
        "a cell at the loaded pointer itself is never disjoint from the load"
    );

    // Below the load: the cell's own width decides, and it is known exactly.
    assert!(
        canonical_equal_across_store_at(-1, CValue::UInt8(Bitvector32Term::Constant(7))),
        "a one-byte cell one byte below the load ends where the load starts"
    );
    assert!(
        !canonical_equal_across_store_at(-4, CValue::Int64(Bitvector32Term::Int64Constant(7))),
        "an int64 cell four bytes below the load covers the load's first four \
         bytes and must not be dropped"
    );
    assert!(
        canonical_equal_across_store_at(-8, CValue::Int64(Bitvector32Term::Int64Constant(7))),
        "an int64 cell eight bytes below the load ends where the load starts"
    );
    assert!(
        !canonical_equal_across_store_at(
            -4,
            CValue::Pointer(CPointerValue::new(arc_pointer(0), CType::Int32Pointer))
        ),
        "a stored pointer is eight bytes, so one four bytes below the load \
         covers the load's first four bytes"
    );

    // Eight bytes remains inside an unknown read; sixteen is outside every
    // scalar read and may be dropped.
    assert!(
        !canonical_equal_across_store_at(8, CValue::Int32(Bitvector32Term::Constant(7))),
        "a cell eight bytes above an unknown load is still inside its maximum width"
    );
    assert!(
        canonical_equal_across_store_at(16, CValue::UInt8(Bitvector32Term::Constant(7))),
        "a cell well above the load is outside every scalar read"
    );
}

/// Two snapshots a store separates do not agree about a load whose bytes it
/// wrote, however clean the two addresses look.
///
/// "Do these snapshots hold one value for this load" is answered by scanning
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
fn a_store_inside_a_read_stops_two_snapshots_agreeing_about_it() {
    let bare = PureFactContext::new();
    let read = arc_pointer(0);
    crate::kernel::eval::declare_load_access_width(&read, 4);
    let base = CMemory::new().with_block("arg-memory", 32);
    let byte_written_at = |offset: i64| {
        base.clone()
            .without_possible_aliasing_cells(&arc_pointer(offset), 1, &bare)
            .store(
                arc_pointer(offset),
                CValue::UInt8(Bitvector32Term::Constant(7)),
            )
    };

    for offset in 1..4 {
        let after = byte_written_at(offset);
        assert!(
            !crate::kernel::reasoning::memory_snapshots_proven_equal_at_pointer(
                &base, &after, &read, &bare
            ),
            "a one-byte write {offset} bytes into a four-byte read is a byte the read \
             returns, so the two snapshots do not agree about it"
        );
    }

    let after = byte_written_at(4);
    assert!(
        crate::kernel::reasoning::memory_snapshots_proven_equal_at_pointer(
            &base, &after, &read, &bare
        ),
        "a write past the read's last byte leaves the two snapshots agreeing about it"
    );
}

/// A recorded store inside a read refutes the equality of the two loads
/// around it, at every offset its bytes reach, whatever the snapshots kept.
///
/// This is the rule the snapshot comparisons and the canonical-form
/// comparison now answer to. Both are read from *state*: a cell map records
/// what is known at a point, and a canonical form drops what it can prove
/// irrelevant. Neither records that a store happened, and a store into the
/// middle of a cell drops the cell it partly overwrites, so the two
/// snapshots around it can be identical where it is concerned. The recorded
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
        let kind = if read_bytes == 4 {
            LoadKind::Bits32
        } else {
            LoadKind::Pointer
        };
        crate::kernel::eval::declare_load_access_width(&read, read_bytes);
        let base = CMemory::new().with_block(block, 32);
        let byte_written_at = |offset: i64| {
            let write = Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(offset),
            };
            base.clone()
                .without_possible_aliasing_cells(&write, 1, &bare)
                .store(write, CValue::UInt8(Bitvector32Term::Constant(7)))
        };
        let history_about = |after: &CMemory| {
            crate::kernel::memory_provenance::recorded_load_history(
                &crate::kernel::intern_c_memory_ref(&base),
                &crate::kernel::intern_c_memory_ref(after),
                &read,
                kind,
                &bare,
            )
        };
        let load_in = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(read.clone()),
                kind,
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
                !crate::kernel::reasoning::memory_snapshots_proven_equal_at_pointer(
                    &base, &after, &read, &bare
                ),
                "the snapshot comparison answers to that history"
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
            crate::kernel::reasoning::memory_snapshots_proven_equal_at_pointer(
                &base,
                &past_the_end,
                &read,
                &bare
            ),
            "and the two snapshots still agree about the read"
        );
    }
}

/// The gate the load-side distinct-cell reduction now applies before dropping
/// a cell: dropping it names the load at a snapshot that no longer records it,
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
        PointerOffsetTerm::Int64Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(97_101))),
            byte_width: 8,
            unsigned: false,
        },
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
    let scaled64 = |id: u64, byte_width: i64| PointerOffsetTerm::Int64Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(id))),
        byte_width,
        unsigned: false,
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
    let i = Bitvector32Term::Variable(Variable(97_203));
    let next = pointer(PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::add(
            i.clone(),
            Bitvector32Term::Constant(1),
        )),
        byte_width: 4,
    });
    let beside = pointer(PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::Int32Scaled {
            value: Box::new(i),
            byte_width: 4,
        }),
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

/// Two snapshots that differ on a cell inside a read do not hold one value for
/// it. `memories_directly_match_for_pointer_load` decided each differing cell
/// from the two *addresses* — a constant nonzero byte offset was enough — and
/// an address is not the question: a four-byte cell at `q + 4` is a different
/// address from `q` under every test the kernel has while holding the upper
/// half of an eight-byte read there.
#[test]
fn a_differing_cell_inside_a_read_stops_the_two_snapshots_matching() {
    let bare = PureFactContext::new();
    for (block, read_bytes) in [("narrow-cell-memory", 4u32), ("wide-cell-memory", 8)] {
        let read = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        crate::kernel::eval::declare_load_access_width(&read, read_bytes);
        let base = CMemory::new().with_block(block, 32);
        let cell_holding = |offset: i64, value: u32| {
            base.clone().store(
                Pointer {
                    block: block.into(),
                    offset: PointerOffsetTerm::Constant(offset),
                },
                CValue::UInt8(Bitvector32Term::Constant(value)),
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
                 returns, so the two snapshots do not hold one value for it"
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
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let owner = pointer(211);
    let data = pointer(212);
    let int32_range = |base: &Pointer| {
        CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
            4,
        )
    };
    let ranges = vec![int32_range(&owner), int32_range(&data)];
    let assumptions = PureFactContext::new();
    let named = |memory: &CMemory, cell: &Pointer| {
        crate::kernel::resource_tracker::last_same_point(
            crate::kernel::resource_tracker::Resource::Cell {
                pointer: cell,
                bytes: 4,
            },
            &crate::kernel::resource_tracker::ProgramPoint::at(&intern_c_memory_ref(memory)),
        )
        .map(|point| point.snapshot().clone())
    };
    // The allocation's claim is live before the call, so retiring it changes
    // the snapshot and records the edge.
    let havoc = |variable| {
        CMemory::new()
            .with_heap_allocation_claim(data.clone(), Bitvector32Term::Constant(4))
            .expect("a fresh claim")
            .with_call_memory_havoc(Variable(variable), &ranges, &assumptions, None)
    };

    let called = havoc(213);
    let retired = called.clone().retire_contract_heap_allocation_claim(
        &data,
        &Bitvector32Term::Constant(4),
        &assumptions,
    );
    assert_eq!(named(&retired, &owner), Some(intern_c_memory_ref(&called)));
    assert_eq!(
        named(&retired, &data),
        Some(intern_c_memory_ref(&called)),
        "a byte of the retired allocation is named by the call's own havoc"
    );
    let cell = with_extended_dag_bridging(|| {
        memory_dag_cell_source(
            &intern_c_memory_ref(&retired),
            &owner,
            4,
            &assumptions,
            false,
        )
    })
    .expect("the walk has an answer");
    let hop = &retained_memory_dag_path(&cell)[0];
    assert_eq!(
        hop.justification,
        MemoryDagHopJustification::RetirementInsideItsCallHavoc
    );
    assert!(
        hop.justification
            .checks(&hop.derivation, &owner, 4, &assumptions)
    );

    // The havoc covers four bytes of an eight-byte allocation.
    let called = havoc(214);
    let wider = called.clone().retire_contract_heap_allocation_claim(
        &data,
        &Bitvector32Term::Constant(8),
        &assumptions,
    );
    assert_eq!(named(&wider, &owner), Some(intern_c_memory_ref(&wider)));

    // Another edge stands between the havoc and the retirement.
    let declared = havoc(215).with_block("arg-memory", 4);
    let separated = declared.clone().retire_contract_heap_allocation_claim(
        &data,
        &Bitvector32Term::Constant(4),
        &assumptions,
    );
    assert_eq!(
        named(&separated, &owner),
        Some(intern_c_memory_ref(&separated))
    );
}

/// A constant established only through a load equality across a call: the
/// caller pinned a cell before a call that havocs a disjoint range, and no
/// fact relates the two snapshots' loads. Constant normalization must still
/// find the constant by proving the loads equal from the memory history --
/// for the post-call load itself, and for a term an equality fact connects
/// to it, whose class has no constant of its own.
#[test]
fn constant_normalization_bridges_a_load_across_a_call() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let load_in = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let after_call = base.clone().with_call_memory_havoc(
        Variable(930_101),
        &[memory_range(arc_pointer(8), 0, 8)],
        &PureFactContext::new(),
        None,
    );
    let copy = Bitvector32Term::Variable(Variable(930_102));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(load_in(&base), Bitvector32Term::Constant(5)),
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
        assumptions
            .known_signed_constant_after_normalization(&Bitvector32Term::add(copy, 1u32.into())),
        Some(6),
        "an unrecorded sum folds from its bridged operand"
    );
}

fn seeded_pointer_read_context(
    old: &SharedCMemory,
    current: &SharedCMemory,
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
    let old = intern_c_memory(CMemory::new());
    let seeded = old
        .memory()
        .clone()
        .store(a.offset_by_bytes(32), int32(1))
        .with_seeded_cells(a.clone(), 4, CType::Int32, 0, 2, old.clone());
    let current = intern_c_memory(seeded);
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
    let CMemoryDerivation::CellsSeeded { run, .. } = derivation.as_ref() else {
        panic!("seed edge");
    };
    assert!(run.read_source(&a.offset_by_bytes(4), 8).is_none());
}

#[test]
fn seeded_pointer_read_evidence_refuses_partial_changed_and_unknown_footprints() {
    let a = Pointer::symbolic(Variable(98_310));
    let b = Pointer::symbolic(Variable(98_311));
    let unknown = Pointer::symbolic(Variable(98_312));
    let old = intern_c_memory(CMemory::new());
    let full = old
        .memory()
        .clone()
        .store(a.offset_by_bytes(32), int32(1))
        .with_seeded_cells(a.clone(), 4, CType::Int32, 0, 2, old.clone());
    let changed_source = intern_c_memory(old.memory().clone().store(a.clone(), int32(7)));
    for (case, current) in [
        old.memory()
            .clone()
            .store(a.offset_by_bytes(32), int32(1))
            .with_seeded_cells(a.clone(), 4, CType::Int32, 0, 1, old.clone()),
        old.memory()
            .clone()
            .store(a.offset_by_bytes(32), int32(1))
            .with_seeded_cells(a.clone(), 4, CType::Int32, 1, 2, old.clone()),
        old.memory()
            .clone()
            .with_constant_run(a.clone(), CType::Int32, 2, int32(0))
            .unwrap(),
        full.clone().store(a.offset_by_bytes(4), int32(7)),
        full.store(unknown, int32(7)),
        old.memory()
            .clone()
            .store(a.offset_by_bytes(32), int32(1))
            .with_seeded_cells(a.clone(), 4, CType::Int32, 0, 2, changed_source),
    ]
    .into_iter()
    .enumerate()
    {
        let current = intern_c_memory(current);
        let (context, left, right) = seeded_pointer_read_context(&old, &current, &a, &b);
        context.register_pointer_read(&right, &current, &a);

        assert!(!context.pointers_known_equal(&left, &right), "case={case}");
    }
}

#[test]
fn seeded_pointer_read_evidence_does_not_enumerate_large_runs_or_alias_classes() {
    for size in [16u32, 64, 256, 1024] {
        let base = Pointer::symbolic(Variable(98_320));
        let address = base.offset_by_bytes((size - 2) * 4);
        let alias = Pointer::symbolic(Variable(98_321));
        let old = intern_c_memory(CMemory::new());
        let current = intern_c_memory(
            old.memory()
                .clone()
                .store(base.offset_by_bytes(size * 4 + 16), int32(1))
                .with_seeded_cells(base, 4, CType::Int32, 0, size, old.clone()),
        );
        let (mut context, left, right) =
            seeded_pointer_read_context(&old, &current, &address, &alias);
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    address.clone(),
                    Pointer::symbolic(Variable(99_000 + u64::from(i))),
                ),
                true,
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&right, &current, &address);
        });
        assert!(context.pointers_known_equal(&left, &right));
        assert!(work < 500, "size={size}, work={work}");
    }
}

#[test]
fn pointer_read_producer_closes_seeded_snapshot_equality_in_the_shared_graph() {
    let a = Pointer::symbolic(Variable(98_330));
    let b = Pointer::symbolic(Variable(98_331));
    let old = intern_c_memory(CMemory::new());
    let seeded =
        old.memory()
            .clone()
            .with_seeded_cells(a.clone(), 4, CType::Int32, 0, 2, old.clone());
    let current = intern_c_memory(seeded);
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
fn pointer_read_source_registration_does_not_walk_growing_store_histories() {
    for size in [8u32, 32, 128, 512] {
        let address = Pointer::symbolic(Variable(98_340));
        let old = intern_c_memory(CMemory::new());
        let mut memory = old.memory().clone().with_seeded_cells(
            address.clone(),
            4,
            CType::Int32,
            0,
            2,
            old.clone(),
        );
        let context = PureFactContext::new();
        for i in 0..size {
            memory = memory.store(address.offset_by_bytes(16), int32(i));
        }
        let current = intern_c_memory(memory);
        let left = Pointer::loaded_value(&old, &address);
        let right = Pointer::loaded_value(&current, &address);
        context.register_pointer_read(&left, &old, &address);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&right, &current, &address);
        });
        assert!(!context.pointers_known_equal(&left, &right));
        assert!(work < 100, "size={size}, work={work}");
    }
}

#[test]
fn pointer_read_producer_admits_one_separate_store_into_the_shared_graph() {
    let address = Pointer::symbolic(Variable(98_350));
    let old = intern_c_memory(CMemory::new());
    let current = intern_c_memory(
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
    let argument = |value| AlgebraicValue::C(CValue::typed_pointer(value, CType::Int32Pointer));
    assert!(
        resource_arguments_proven_equal(&argument(left), &argument(right), &context),
        "fold's existing argument checker must see the same graph equality"
    );
}

#[test]
fn pointer_read_single_store_refuses_changed_partial_and_unknown_accesses() {
    let address = Pointer::symbolic(Variable(98_360));
    let unknown = Pointer::symbolic(Variable(98_361));
    let old = intern_c_memory(CMemory::new());
    for write in [
        address.clone(),
        address.offset_by_bytes(4),
        address.offset_by_bytes(7),
        unknown,
    ] {
        let current = intern_c_memory(old.memory().clone().store(write, uint8(1)));
        let context = PureFactContext::new();
        let left = Pointer::loaded_value(&old, &address);
        let right = Pointer::loaded_value(&current, &address);
        context.register_pointer_read(&left, &old, &address);
        context.register_pointer_read(&right, &current, &address);
        assert!(!context.pointers_known_equal(&left, &right));
    }
    // A four-byte store inside an eight-byte read overlaps it even though
    // their starting addresses differ. Address inequality is insufficient.
    let current = intern_c_memory(
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
    let adjacent = intern_c_memory(
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
    let old = intern_c_memory(CMemory::new());
    let current = intern_c_memory(old.memory().clone().store(write.clone(), int32(7)));
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
    let _scope = branch.enter_id_scope();
    assert!(!pointers_proven_equal_for_memory_resolution(
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
    let old = intern_c_memory(CMemory::new());
    let current = intern_c_memory(
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
fn pointer_read_single_store_edges_compose_with_near_linear_work() {
    let mut previous_work = None;
    for size in [8u32, 32, 128, 512] {
        let address = Pointer::symbolic(Variable(98_390));
        let mut memory = intern_c_memory(CMemory::new());
        let context = PureFactContext::new();
        let original = Pointer::loaded_value(&memory, &address);
        context.register_pointer_read(&original, &memory, &address);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                memory = intern_c_memory(
                    memory
                        .memory()
                        .clone()
                        .store(address.offset_by_bytes(16), int32(i)),
                );
                let value = Pointer::loaded_value(&memory, &address);
                context.register_pointer_read(&value, &memory, &address);
                assert!(context.pointers_known_equal(&original, &value));
            }
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
        if let Some(previous) = previous_work {
            assert!(
                work <= 5 * previous,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous_work = Some(work);
    }
}

#[test]
fn pointer_read_producer_admits_recorded_cache_forgetting() {
    let address = arc_pointer(0);
    let seeded = intern_c_memory(CMemory::new().with_block("arg-memory", 32).store(
        address.clone(),
        CValue::Int64(Bitvector32Term::Int64Constant(7)),
    ));
    let context = PureFactContext::new();
    let forgotten = intern_c_memory(seeded.memory().without_possible_aliasing_cells(
        &address.offset_by_bytes(4),
        1,
        &context,
    ));
    assert!(matches!(
        forgotten.derivation().unwrap().as_ref(),
        CMemoryDerivation::CellsForgotten { .. }
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
    let seeded = intern_c_memory(CMemory::new().with_block("arg-memory", 32).store(
        address.clone(),
        CValue::Int64(Bitvector32Term::Int64Constant(9)),
    ));
    let context = PureFactContext::new();
    let forgotten = intern_c_memory(seeded.memory().without_possible_aliasing_cells(
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
            .store(address.offset_by_bytes(4), CValue::UInt8(1u32.into())),
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
        let changed = intern_c_memory(changed);
        let right = Pointer::loaded_value(&changed, &address);
        context.register_pointer_read(&right, &changed, &address);
        assert!(!context.pointers_known_equal(&left, &right));
    }
}

#[test]
fn pointer_read_cache_forgetting_registration_does_not_search_older_history() {
    for size in [8u32, 32, 128, 512] {
        let address = arc_pointer(0);
        let mut memory = CMemory::new().with_block("arg-memory", 32);
        let original = intern_c_memory(memory.clone());
        for i in 0..size {
            memory = memory.store(
                address.clone(),
                CValue::Int64(Bitvector32Term::Int64Constant(i as i64)),
            );
        }
        let before = intern_c_memory(memory.clone());
        let context = PureFactContext::new();
        let forgotten = intern_c_memory(memory.without_possible_aliasing_cells(
            &address.offset_by_bytes(4),
            1,
            &context,
        ));
        let old_read = Pointer::loaded_value(&original, &address);
        let before_read = Pointer::loaded_value(&before, &address);
        let after_read = Pointer::loaded_value(&forgotten, &address);
        context.register_pointer_read(&old_read, &original, &address);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&after_read, &forgotten, &address);
        });
        assert!(context.pointers_known_equal(&before_read, &after_read));
        assert!(!context.pointers_known_equal(&old_read, &after_read));
        assert!(work < 100, "size={size}, work={work}");
    }
}

#[test]
fn pointer_read_congruence_composes_materialization_and_forgetting_at_production() {
    let address = Pointer::symbolic(Variable(98_420));
    let unknown_write = Pointer::symbolic(Variable(98_421));
    let original = intern_c_memory(CMemory::new());
    let memory = original
        .memory()
        .clone()
        .with_seeded_cells(address.clone(), 4, CType::Int32, 0, 2, original.clone())
        .with_seeded_cells(
            address.offset_by_bytes(8),
            4,
            CType::Int32,
            0,
            2,
            original.clone(),
        )
        .with_seeded_cells(
            address.offset_by_bytes(16),
            4,
            CType::Int32,
            0,
            1,
            original.clone(),
        );
    let context = PureFactContext::new();
    let forgotten =
        intern_c_memory(memory.without_possible_aliasing_cells(&unknown_write, 4, &context));
    assert!(matches!(
        forgotten.derivation().unwrap().as_ref(),
        CMemoryDerivation::CellsForgotten { .. }
    ));
    let left = Pointer::loaded_value(&original, &address);
    let right = Pointer::loaded_value(&forgotten, &address);
    assert!(
        context.pointers_known_equal(&left, &right),
        "producer-recorded byte-preserving transitions must compose without intermediate reads"
    );
}

#[test]
fn read_identity_refuses_changed_sources_constant_runs_and_unrecorded_pruning() {
    let address = Pointer::symbolic(Variable(98_430));
    let original = intern_c_memory(CMemory::new());
    let changed = intern_c_memory(original.memory().clone().store(address.clone(), int32(7)));
    let from_changed = intern_c_memory(original.memory().clone().with_seeded_cells(
        address.clone(),
        4,
        CType::Int32,
        0,
        2,
        changed.clone(),
    ));
    let after_changed = intern_c_memory(changed.memory().clone().with_seeded_cells(
        address.offset_by_bytes(8),
        4,
        CType::Int32,
        0,
        2,
        original.clone(),
    ));
    let constant = intern_c_memory(
        original
            .memory()
            .clone()
            .with_constant_run(address.clone(), CType::Int32, 2, int32(0))
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
    let forgotten = intern_c_memory(changed.memory().without_cell(&address));
    assert_ne!(forgotten.read_identity(), changed.read_identity());
}

#[test]
fn read_identity_production_is_linear_and_endpoint_queries_do_not_walk_history() {
    let mut previous_work = None;
    for size in [8u32, 32, 128, 512] {
        let address = Pointer::symbolic(Variable(98_440));
        let unknown = Pointer::symbolic(Variable(98_441));
        let original = intern_c_memory(CMemory::new());
        let mut memory = original.memory().clone();
        let context = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                memory = memory
                    .clone()
                    .with_seeded_cells(address.clone(), 4, CType::Int32, 0, 2, original.clone())
                    .without_possible_aliasing_cells(&unknown, 4, &context);
            }
        });
        let current = intern_c_memory(memory);
        assert_eq!(current.read_identity(), original.read_identity());
        let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.pointers_known_equal(
                &Pointer::loaded_value(&original, &address),
                &Pointer::loaded_value(&current, &address),
            ));
        });
        assert!(query_work < 100, "size={size}, query_work={query_work}");
        assert!(work < 500 * size as usize, "size={size}, work={work}");
        if let Some(previous) = previous_work {
            assert!(
                work <= 5 * previous,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous_work = Some(work);
    }
}

#[test]
fn read_identity_is_immutable_when_a_snapshot_was_interned_before_its_edge() {
    let address = Pointer::symbolic(Variable(98_450));
    let original = intern_c_memory(CMemory::new());
    let run = CellRun::new(
        address,
        4,
        CType::Int32,
        2,
        original.clone(),
        crate::kernel::primitives::IndexIntervals::default(),
    );
    let mut memory = original.memory().clone();
    std::sync::Arc::make_mut(&mut memory.cells).add_run(run.clone());
    let current = intern_c_memory(memory.clone());
    let before = current.read_identity();
    record_c_memory_derivation(
        &mut memory,
        CMemoryDerivation::CellsSeeded {
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
    let base = CMemory::new().with_block(block, 16);
    let stored_at = |write: Pointer, value: CValue| {
        crate::kernel::intern_c_memory_ref(
            &base
                .clone()
                .without_possible_aliasing_cells(&write, value.byte_width(), &bare)
                .store(write, value),
        )
    };
    let resolves_to_seven = |memory: &SharedCMemory, read: &Pointer| {
        let seven = Bitvector32Term::Constant(7);
        let load = Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(read.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let resolved = crate::kernel::memory_provenance::resolve_load_along_memory_derivations(
            memory,
            read,
            crate::kernel::LoadKind::Bits32,
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
    let narrow_store = stored_at(at(1), CValue::UInt8(Bitvector32Term::Constant(7)));
    assert!(
        !resolves_to_seven(&narrow_store, &wide_read),
        "a byte stored inside a four-byte read is one of its bytes, not its value"
    );

    let narrow_read = at(9);
    crate::kernel::eval::declare_load_access_width(&narrow_read, 1);
    let wide_store = stored_at(at(8), CValue::Int32(Bitvector32Term::Constant(7)));
    assert!(
        !resolves_to_seven(&wide_store, &narrow_read),
        "a four-byte store around a one-byte read holds other bytes than that read returns"
    );

    let exact_read = at(4);
    crate::kernel::eval::declare_load_access_width(&exact_read, 4);
    let exact_store = stored_at(at(4), CValue::Int32(Bitvector32Term::Constant(7)));
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
        crate::kernel::intern_c_memory(CMemory::new().with_block("unrelated-origin-storage", 16));
    let Bitvector32Term::Variable(variable) = crate::kernel::canonical_form_of_load(
        live.clone(),
        pointer.clone(),
        crate::kernel::LoadKind::Bits32,
    ) else {
        panic!("an unresolved scalar read has a load name");
    };
    assert_eq!(
        crate::kernel::eval::registered_load_origin_for_variable(&variable),
        Some((live, pointer))
    );
}

#[test]
fn an_unknown_pointer_call_drops_a_local_cache_without_separation() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Pointer {
        block: "local:unknown-call-target".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let base = CMemory::new()
        .with_block("local:unknown-call-target", 16)
        .store(cell.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
    let ranges = [memory_range(Pointer::symbolic(Variable(977_002)), 0, 1)];
    let assumptions = PureFactContext::new();
    let after = base
        .clone()
        .with_call_memory_havoc(Variable(977_003), &ranges, &assumptions, None);
    assert!(!after.has_known_cell_at(&cell));
    assert!(after.matches_call_memory_havoc_result(&base, &ranges, &assumptions, None));
    let forged = after.store(cell, CValue::Int32(Bitvector32Term::Constant(1)));
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
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(owner.clone(), 0, 4)));
    let kept = CallKeptOwnership::new(
        residual,
        CallKeptRanges::new(ResourceContext::new(), vec![]),
        &assumptions,
    );
    let base = CMemory::new().with_block("local:kept-offset-owner", 16);
    let ranges = [memory_range(Pointer::symbolic(Variable(977_004)), 0, 1)];
    let after =
        base.clone()
            .with_call_memory_havoc(Variable(977_005), &ranges, &assumptions, Some(&kept));
    let recorded = CallKeptRanges::recorded_on(&after).unwrap();
    assert!(recorded.holds_access(&cell, 4, &assumptions));
    assert!(!recorded.holds_access(&owner.offset_by_bytes(16), 4, &assumptions));
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(cell.clone()),
            crate::kernel::LoadKind::Bits32,
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
    let overwritten = after.store(cell.clone(), CValue::Int32(Bitvector32Term::Constant(43)));
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
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let first = ConditionTerm::pointer_equal(left.clone(), middle.clone());
    let second = ConditionTerm::pointer_equal(middle, right.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(first.clone(), true)
        .assume_condition(second.clone(), true);
    let left_load = Bitvector32Term::MemoryLoad(
        memory.clone(),
        Box::new(left),
        crate::kernel::LoadKind::Bits32,
    );
    let right_load =
        Bitvector32Term::MemoryLoad(memory, Box::new(right), crate::kernel::LoadKind::Bits32);
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
    let Bitvector32Term::MemoryLoad(memory, pointer, _) = &left_load else {
        unreachable!();
    };
    let byte_read = Bitvector32Term::MemoryLoad(
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
    for premise in [first, second] {
        let withdrawn = assumptions.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!witness.checks(&withdrawn));
    }
    assert!(!witness.checks(&PureFactContext::new()));
}

#[test]
fn named_snapshot_alias_equality_does_not_depend_on_sibling_observation_origins() {
    let mut samples = Vec::new();
    for unrelated in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let left = Pointer::symbolic(Variable(977_110));
        let middle = Pointer::symbolic(Variable(977_111));
        let right = Pointer::symbolic(Variable(977_112));
        let first = ConditionTerm::pointer_equal(left.clone(), middle.clone());
        let second = ConditionTerm::pointer_equal(middle, right.clone());
        let mut assumptions = PureFactContext::new()
            .assume_condition(first.clone(), true)
            .assume_condition(second.clone(), true);
        for index in 0..unrelated {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(978_100 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        let named = crate::kernel::intern_c_memory(CMemory::new());
        let origins = ["local:first-arm", "local:second-arm"]
            .map(|block| crate::kernel::intern_c_memory(CMemory::new().with_block(block, 4)));
        let variables = [(&left, &origins[0]), (&right, &origins[1])].map(|(pointer, origin)| {
            crate::kernel::eval::load_variable_for_cell_with_origin(
                &named,
                pointer,
                LoadKind::Bits32,
                4,
                origin,
            )
        });
        let [left_load, right_load] = variables.map(Bitvector32Term::Variable);
        let (witness, work) = crate::instrumentation::measure_deterministic_work(|| {
            let capture = CheckedLoadEqualityCapture::start();
            assert!(checked_origin_load_equality(
                &left_load,
                &right_load,
                &assumptions
            ));
            let witnesses = capture.finish();
            let [witness] = witnesses.as_slice() else {
                panic!("expected one named-snapshot alias witness");
            };
            assert!(witness.checks(&assumptions));
            witness.clone()
        });
        // Withdrawal constructs a new assumption context and is outside the
        // measurement of the selected equality check.
        for premise in [first.clone(), second.clone()] {
            let withdrawn =
                assumptions.without_exact_fact(&Proposition::ConditionIs(premise, true));
            assert!(!witness.checks(&withdrawn));
        }
        // The witness names the exact snapshot, address, and read kind.
        let changed = crate::kernel::intern_c_memory(
            CMemory::new().with_block("local:different-snapshot", 4),
        );
        for retargeted in [
            Bitvector32Term::MemoryLoad(changed, Box::new(right.clone()), LoadKind::Bits32),
            Bitvector32Term::MemoryLoad(
                named.clone(),
                Box::new(right.offset_by_bytes(4)),
                LoadKind::Bits32,
            ),
            Bitvector32Term::MemoryLoad(named.clone(), Box::new(right.clone()), LoadKind::UInt8),
        ] {
            assert!(!witness.checks_retargeted_for_test(
                left_load.clone(),
                retargeted,
                &assumptions,
                &crate::kernel::proof::CheckedCallEvents::default(),
            ));
        }
        // A pointer read has its own immutable eight-byte identity. Registering
        // it does not widen or invalidate the existing four-byte scalar rule.
        let pointer_read = crate::kernel::eval::load_variable_for_cell_with_origin(
            &named,
            &right,
            LoadKind::Pointer,
            8,
            &origins[1],
        );
        assert_ne!(Bitvector32Term::Variable(pointer_read), right_load);
        assert!(witness.checks(&assumptions));
        assert!(checked_origin_load_equality(
            &left_load,
            &right_load,
            &assumptions
        ));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn kept_range_lookup_follows_exact_aliases_without_scanning_unrelated_members() {
    let input = |name| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(name)), 4),
    };
    let base = input(979_000);
    let model_base = Pointer {
        block: PointerBlock::Symbolic(Variable(979_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = ConditionTerm::pointer_equal(base.clone(), model_base.clone());
    let assumptions = PureFactContext::new().assume_condition(alias.clone(), true);
    let field = memory_range(model_base, 2, 4);
    let pointer = base.offset_by_bytes(8);
    let mut previous = None;
    for count in [16, 64, 256, 1024] {
        let mut ranges =
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(field.clone()));
        for index in 0..count {
            ranges = ranges.unchecked_with_fact(CResourceFact::own_memory(memory_range(
                input(980_000 + index),
                0,
                2,
            )));
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.kept_range_holding_access(&ranges, || None, &pointer, 8)
        });
        assert_eq!(found, Some(&field));
        if let Some(previous) = previous {
            assert!(
                work <= previous + 32,
                "{count} unrelated members: {work} after {previous}"
            );
        }
        previous = Some(work);
    }
    let ranges = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(field));
    for (pointer, bytes) in [
        (pointer.clone(), 12),
        (base.offset_by_bytes(12), 8),
        (base.offset_by_bytes(4), 8),
    ] {
        assert!(
            assumptions
                .kept_range_holding_access(&ranges, || None, &pointer, bytes)
                .is_none()
        );
    }
    let withdrawn = assumptions.without_exact_fact(&Proposition::ConditionIs(alias, true));
    assert!(
        withdrawn
            .kept_range_holding_access(&ranges, || None, &pointer, 8)
            .is_none()
    );
}

#[test]
fn unrelated_symbolic_kept_bases_do_not_trigger_range_placement() {
    let input = |name| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(name)), 4),
    };
    let pointer = input(977_199).offset_by_bytes(8);
    let assumptions = PureFactContext::new();
    for count in [16, 64, 256, 1024] {
        let mut ranges = ResourceContext::new();
        for index in 0..count {
            ranges = ranges.unchecked_with_fact(CResourceFact::own_memory(memory_range(
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
        let mut memory = CMemory::new()
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
            &[CMemoryRange::new_with_element_width(
                source.clone(),
                0u32.into(),
                count.into(),
                4,
            )],
            &assumptions,
        );
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(source.clone()),
                LoadKind::Bits32,
            )
        };
        crate::kernel::eval::declare_load_access_width(&source, 4);
        let before = load(&written);
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            let copied = written
                .clone()
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::pointer(source.clone()),
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
            crate::kernel::intern_c_memory_ref(&copied)
                .derivation()
                .as_deref(),
            Some(CMemoryDerivation::ObjectInitializationRecorded { .. })
        ));
        // Metadata records cannot hide an actual overwrite of the source.
        let changed = copied
            .clone()
            .store(source.clone(), CValue::UInt32(9u32.into()));
        assert!(!checked_origin_load_equality(
            &before,
            &load(&changed),
            &assumptions
        ));
        let repeated = copied.clone().with_initialized_object(&target, count * 4);
        assert_eq!(
            crate::kernel::intern_c_memory_ref(&repeated),
            crate::kernel::intern_c_memory_ref(&copied)
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "{samples:?}"
    );
}

/// A materialized run writes back its own source loads. Framing an unknown
/// address across it must not enumerate the run or require a disjointness fact.
#[test]
fn seeded_scalar_loads_frame_unknown_cells_with_constant_work() {
    let anchor = Pointer::symbolic(Variable(98_470));
    let other = Pointer::symbolic(Variable(98_471));
    let assumptions = PureFactContext::new();
    let mut previous_work = None;
    for size in [16, 256, 4096, 65536] {
        let original = intern_c_memory(CMemory::new());
        let first = original.memory().clone().with_seeded_cells(
            anchor.clone(),
            4,
            CType::Int32,
            0,
            size,
            original.clone(),
        );
        let current = intern_c_memory(first.with_seeded_cells(
            anchor.offset_by_bytes(size * 4),
            4,
            CType::Int32,
            0,
            size,
            original.clone(),
        ));
        let (cell, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory_dag_cell_source(&current, &other, 4, &assumptions, false).unwrap()
        });
        let MemoryDagCell::Unwritten { node, path } = cell else {
            panic!("naming must not invent a stored value for the other address");
        };
        assert_eq!(node, original);
        assert_eq!(path.len(), 2);
        for hop in path {
            assert_eq!(
                hop.justification,
                MemoryDagHopJustification::SeededLoadsOfBase
            );
            assert!(
                hop.justification
                    .checks(&hop.derivation, &other, 4, &assumptions)
            );
        }
        assert!(work < 100, "size={size}, work={work}");
        if let Some(previous) = previous_work {
            assert_eq!(work, previous, "framing work must not grow with the run");
        }
        previous_work = Some(work);
    }
}

/// A retained no-write witness must reject another source, constant writes,
/// copied cells, normalized bools and overlapping representations.
#[test]
fn seeded_scalar_no_write_witness_rejects_changed_or_represented_values() {
    use crate::kernel::primitives::{IndexIntervals, RunValueMode};
    let anchor = Pointer::symbolic(Variable(98_480));
    let other = Pointer::symbolic(Variable(98_481));
    let original = intern_c_memory(CMemory::new());
    let changed = intern_c_memory(original.memory().clone().store(anchor.clone(), int32(7)));
    let assumptions = PureFactContext::new();
    let witness = MemoryDagHopJustification::SeededLoadsOfBase;
    for (source, mode, ty, width) in [
        (changed, RunValueMode::Load, CType::Int32, 4),
        (
            original.clone(),
            RunValueMode::Constant(int32(7)),
            CType::Int32,
            4,
        ),
        (
            original.clone(),
            RunValueMode::Copy {
                source_base: other.clone(),
            },
            CType::Int32,
            4,
        ),
        (original.clone(), RunValueMode::Load, CType::Bool, 1),
        (original.clone(), RunValueMode::Load, CType::Int32, 1),
    ] {
        let edge = CMemoryDerivation::CellsSeeded {
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
    let write = CMemoryDerivation::Store {
        base: original,
        pointer: anchor,
        value: int32(7),
    };
    assert!(!witness.checks(&write, &other, 4, &assumptions));
}

/// Named struct unfolds cache pointer storage as narrower scalar slots. A
/// full-width read must cross those no-write edges without reading the last
/// partial slot as a write. The witness stays constant-size as the run grows.
#[test]
fn seeded_scalar_slots_preserve_overlapping_wide_reads() {
    let pointer = Pointer::symbolic(Variable(98_490));
    let assumptions = PureFactContext::new();
    let mut previous_work = None;
    for count in [2, 16, 256, 4096] {
        let original = intern_c_memory(CMemory::new());
        let current = intern_c_memory(original.memory().clone().with_seeded_cells(
            pointer.clone(),
            4,
            CType::Int32,
            0,
            count,
            original.clone(),
        ));
        let (cell, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory_dag_cell_source(&current, &pointer, 8, &assumptions, false).unwrap()
        });
        let MemoryDagCell::Unwritten { node, path } = cell else {
            panic!("partial scalar cache slots cannot supply a whole pointer");
        };
        assert_eq!(node, original);
        assert_eq!(path.len(), 1);
        let hop = &path[0];
        assert_eq!(
            hop.justification,
            MemoryDagHopJustification::SeededLoadsOfBase
        );
        assert!(
            hop.justification
                .checks(&hop.derivation, &pointer, 8, &assumptions)
        );
        assert!(work < 100, "count={count}, work={work}");
        if let Some(previous) = previous_work {
            assert_eq!(work, previous);
        }
        previous_work = Some(work);

        // A real four-byte overwrite of the pointer's upper half must still
        // stop the wide read, even after the resulting bytes are cached.
        let changed = intern_c_memory(
            original
                .memory()
                .clone()
                .store(pointer.offset_by_bytes(4), int32(7)),
        );
        let cached = intern_c_memory(changed.memory().clone().with_seeded_cells(
            pointer.clone(),
            4,
            CType::Int32,
            0,
            count,
            changed.clone(),
        ));
        let (cell, stop) =
            memory_dag_cell_source_with_stop(&cached, &pointer, 8, &assumptions, false).unwrap();
        assert_eq!(cell.node(), &changed);
        assert_eq!(stop, CellWalkStop::Affected);
    }
}

/// A base-pointer alias applies to the same field offset. The exact-store
/// predicate must use that indexed equality without scanning unrelated facts
/// or accepting a different field, partial store, or an unproved alias.
#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn stored_field_value_uses_indexed_base_aliases() {
    use crate::kernel::resource_tracker::cell_source::write_supplies_read;
    use crate::kernel::resource_tracker::step_effect::write_is_at_read_address;
    let _session = crate::kernel::VerificationSession::enter();
    let left = Pointer::loaded(
        PointerBlock::ExternalArgument,
        Bitvector32Term::Variable(Variable(105_001)),
        4,
    );
    let right = Pointer::loaded(
        PointerBlock::ExternalArgument,
        Bitvector32Term::Variable(Variable(105_002)),
        4,
    );
    let write = left.offset_by_bytes(16);
    let read = right.offset_by_bytes(16);
    let stored = CValue::typed_pointer(Pointer::symbolic(Variable(105_003)), CType::Int32Pointer);
    let bare = PureFactContext::new();
    assert!(!write_is_at_read_address(&write, &read, &bare));
    let mut samples = Vec::new();
    for count in [16u64, 256, 4096] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(110_000 + index * 2)),
                    Pointer::symbolic(Variable(110_001 + index * 2)),
                ),
                true,
            );
        }
        context = context.assume_condition(
            ConditionTerm::pointer_equal(left.clone(), right.clone()),
            true,
        );
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            write_is_at_read_address(&write, &read, &context)
        });
        assert!(equal);
        samples.push(work);
        assert!(write_supplies_read(&write, &stored, &read, 8, &context));
        assert!(!write_is_at_read_address(
            &write,
            &read.offset_by_bytes(4),
            &context
        ));
        assert!(!write_supplies_read(&write, &stored, &read, 4, &context));
        assert!(!write_supplies_read(
            &write,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            &read,
            8,
            &context
        ));
    }
    assert!(samples[2] <= samples[0] * 4 + 32, "{samples:?}");
}

/// A transitive base alias must frame a different pointer field without an
/// alias scan. The retained hop must refuse missing aliases and every partial
/// overlap, including a later check made with a wider read.
#[test]
fn aliased_store_byte_frame_checks_width_context_and_scales() {
    use crate::kernel::resource_tracker::Resource;
    use crate::kernel::resource_tracker::cell_source::MemoryDagHopJustification;
    use crate::kernel::resource_tracker::step_effect::{Evidence, Separation, StepEffect, affects};
    let _session = crate::kernel::VerificationSession::enter();
    let base = |id| {
        Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(id)),
            4,
        )
    };
    let left = base(106_001);
    let right = base(106_002);
    let bridge = Pointer::symbolic(Variable(106_003));
    let read = right.offset_by_bytes(16);
    let value = CValue::typed_pointer(Pointer::symbolic(Variable(106_004)), CType::Int32Pointer);
    let memory = intern_c_memory(CMemory::new());
    let classify = |write: Pointer, bytes, context: &PureFactContext| {
        let step = CMemoryDerivation::Store {
            base: memory.clone(),
            pointer: write,
            value: value.clone(),
        };
        let result = affects(
            &step,
            &memory,
            Resource::Cell {
                pointer: &read,
                bytes,
            },
            &Evidence {
                assumptions: context,
                cross_loop_havoc: false,
            },
        );
        (step, result)
    };
    let mut samples = Vec::new();
    for count in [16u64, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(120_000 + index * 2)),
                    Pointer::symbolic(Variable(120_001 + index * 2)),
                ),
                true,
            );
        }
        context = context
            .assume_condition(
                ConditionTerm::pointer_equal(left.clone(), bridge.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(bridge.clone(), right.clone()),
                true,
            );
        let ((step, result), work) = crate::instrumentation::measure_deterministic_work(|| {
            classify(left.offset_by_bytes(8), 8, &context)
        });
        samples.push(work);
        let StepEffect::Separate(Separation::Cell(
            hop @ MemoryDagHopJustification::StoreAliasedByteSeparation { .. },
        )) = result
        else {
            panic!("expected checked aliased byte separation: {result:?}");
        };
        assert!(hop.checks(&step, &read, 8, &context));
        assert!(!hop.checks(&step, &read, 8, &PureFactContext::new()));
        // The same certificate cannot be moved onto a different store or a
        // read wide enough to reach a store on its other side.
        for offset in [12, 16, 20] {
            let (changed, effect) = classify(left.offset_by_bytes(offset), 8, &context);
            assert!(
                !matches!(effect, StepEffect::Separate(_)),
                "overlap at {offset}"
            );
            assert!(!hop.checks(&changed, &read, 8, &context));
        }
        let (after, effect) = classify(left.offset_by_bytes(24), 8, &context);
        let StepEffect::Separate(Separation::Cell(after_hop)) = effect else {
            panic!("the adjacent field is separate");
        };
        assert!(after_hop.checks(&after, &read, 8, &context));
        assert!(!after_hop.checks(&after, &read, 12, &context));
        let (_, bare_effect) = classify(left.offset_by_bytes(8), 8, &PureFactContext::new());
        assert!(!matches!(bare_effect, StepEffect::Separate(_)));
    }
    assert!(samples[3] <= samples[0] * 4 + 32, "{samples:?}");
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn graph_aliased_range_membership_checks_complete_access_and_scales() {
    // A named call can leave a store's pointer connected to the selected
    // range by two equalities. Check that local graph evidence frames the
    // complete access without enumerating unrelated aliases.
    use crate::kernel::memory_provenance::typed_store_separated_ranges_evidence;
    let _session = crate::kernel::VerificationSession::enter();
    let base = |id| {
        Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(id)),
            4,
        )
    };
    let write_base = base(160_001);
    let write_model = base(160_002);
    let read_base = base(160_003);
    let read_model = base(160_004);
    let write_bridge = Pointer::symbolic(Variable(160_005));
    let read_bridge = Pointer::symbolic(Variable(160_006));
    let write = write_base.offset_by_bytes(8);
    let read = read_base.offset_by_bytes(8);
    let range = |base: &Pointer, end| {
        CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(8),
            Bitvector32Term::Constant(end),
            1,
        )
    };
    let separation = |end| Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(range(&write_model, end))),
        right: Box::new(CResource::Memory(range(&read_model, end))),
    };
    let aliases = [
        ConditionTerm::pointer_equal(write_base.clone(), write_bridge.clone()),
        ConditionTerm::pointer_equal(write_bridge, write_model.clone()),
        ConditionTerm::pointer_equal(read_base.clone(), read_bridge.clone()),
        ConditionTerm::pointer_equal(read_bridge, read_model.clone()),
    ];
    let step = CMemoryDerivation::Store {
        base: intern_c_memory(CMemory::new()),
        pointer: write.clone(),
        value: CValue::typed_pointer(Pointer::symbolic(Variable(160_007)), CType::Int32Pointer),
    };
    let mut samples = Vec::new();
    for count in [16u64, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(base(170_000 + index * 2), base(170_001 + index * 2)),
                true,
            );
        }
        for alias in &aliases {
            context = context.assume_condition(alias.clone(), true);
        }
        let no_separation = context.clone();
        context = context.assume_proposition(separation(16));
        let (witness, work) = crate::instrumentation::measure_deterministic_work(|| {
            let witness = typed_store_separated_ranges_evidence(&write, 8, &read, 8, &context)
                .expect("the graph aligns both accesses to the selected ranges");
            assert!(witness.checks(&step, &read, 8, &context));
            witness
        });
        samples.push(work);
        // Scale the producer and checker at every size. The invalid
        // certificates are independent of unrelated context size.
        if count != 16 {
            continue;
        }
        assert!(!witness.checks(&step, &read, 8, &no_separation));
        for alias in &aliases {
            let missing =
                context.without_exact_fact(&Proposition::ConditionIs(alias.clone(), true));
            assert!(!witness.checks(&step, &read, 8, &missing));
            assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 8, &missing).is_none());
        }
        assert!(!witness.checks(&step, &read, 9, &context));
        assert!(typed_store_separated_ranges_evidence(&write, 9, &read, 8, &context).is_none());
        assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 9, &context).is_none());
        let partial = no_separation.assume_proposition(separation(12));
        assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 8, &partial).is_none());
        let overlapping = context.assume_condition(
            ConditionTerm::pointer_equal(write_model.clone(), read_model.clone()),
            true,
        );
        assert!(!witness.checks(&step, &read, 8, &overlapping));
        assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 8, &overlapping).is_none());
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 64),
        "{samples:?}"
    );
}

#[test]
fn local_lifetime_end_retains_complete_separated_range_evidence_and_scales() {
    let mut costs = Vec::new();
    for count in [16u32, 64, 256] {
        crate::kernel::eval::clear_load_variable_registry();
        let retired = CMemory::frame_local_pointer(u64::from(count), "span");
        let read = Pointer::symbolic(Variable(140_000 + u64::from(count)));
        let bytes = |base, end| CMemoryRange::new_with_element_width(base, 0u32.into(), end, 1);
        let retired_range = bytes(retired.clone(), 16u32.into());
        let read_range = bytes(read.clone(), 8u32.into());
        let mut memory = CMemory::new()
            .with_block(retired.block.clone(), 16)
            .with_block(read.block.clone(), 16);
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(retired_range.clone()))
            .unchecked_with_fact(CResourceFact::own_memory(read_range.clone()));
        for index in 0..count {
            let other = CMemory::frame_local_pointer(u64::from(count + index + 1), "unrelated");
            memory = memory.with_block(other.block.clone(), 16);
            resources = resources
                .unchecked_with_fact(CResourceFact::own_memory(bytes(other, 16u32.into())));
        }
        let assumptions =
            PureFactContext::new().assume_proposition(Proposition::CResourceComposition(resources));
        crate::kernel::eval::declare_load_access_width(&read, 8);
        let before = crate::kernel::intern_c_memory_ref(&memory);
        let after = crate::kernel::intern_c_memory_ref(&memory.without_local_block(&retired.block));
        let load = |memory| {
            Bitvector32Term::MemoryLoad(
                memory,
                Box::new(read.clone()),
                crate::kernel::LoadKind::Pointer,
            )
        };
        // Measure this selected cleanup edge's decision and certificate check,
        // excluding the pre-existing walks through the fixture's declarations.
        let (effect, cost) = crate::instrumentation::measure_deterministic_work(|| {
            with_extended_dag_bridging(|| {
                use crate::kernel::resource_tracker::step_effect;
                let effect = step_effect::affects(
                    after.derivation().unwrap().as_ref(),
                    &after,
                    crate::kernel::resource_tracker::Resource::Cell {
                        pointer: &read,
                        bytes: 8,
                    },
                    &step_effect::Evidence {
                        assumptions: &assumptions,
                        cross_loop_havoc: true,
                    },
                );
                if let step_effect::StepEffect::Separate(step_effect::Separation::Cell(hop)) =
                    &effect
                {
                    assert!(hop.checks(
                        after.derivation().unwrap().as_ref(),
                        &read,
                        8,
                        &assumptions
                    ));
                } else {
                    panic!("expected a checked cell separation: {effect:?}");
                }
                effect
            })
        });
        assert!(matches!(
            effect,
            crate::kernel::resource_tracker::step_effect::StepEffect::Separate(_)
        ));
        let capture = CheckedLoadEqualityCapture::start();
        let equal =
            checked_atomic_load_equality(&load(after.clone()), &load(before.clone()), &assumptions);
        assert!(
            equal,
            "a separated caller pointer survives private-object cleanup"
        );
        costs.push(cost);
        let equalities = capture.finish();
        let [equality] = equalities.as_slice() else {
            panic!("expected one equality: {equalities:?}");
        };
        assert!(equality.checks(&assumptions));
        assert!(!equality.checks(&PureFactContext::new()));
        let Some(AtomicMemoryLoadEqualityEvidence::SameCell(evidence)) =
            equality.memory_dag_evidence_for_test()
        else {
            panic!("expected typed DAG evidence");
        };
        let hop = &retained_memory_dag_path(&evidence.left)[0];
        assert!(matches!(
            hop.justification,
            MemoryDagHopJustification::LocalLifetimeEndedSeparatedRanges { .. }
        ));
        assert!(
            hop.justification
                .checks(hop.derivation.as_ref(), &read, 8, &assumptions)
        );
        assert!(
            !hop.justification
                .checks(hop.derivation.as_ref(), &read, 16, &assumptions)
        );
        assert!(
            !hop.justification
                .checks(hop.derivation.as_ref(), &retired, 8, &assumptions)
        );
        let larger = CMemory::new().with_block(retired.block.clone(), 32);
        let larger_end =
            crate::kernel::intern_c_memory_ref(&larger.without_local_block(&retired.block));
        assert!(!hop.justification.checks(
            larger_end.derivation().unwrap().as_ref(),
            &read,
            8,
            &assumptions
        ));
        for (retired_bytes, read_bytes) in [(8u32, 8u32), (16, 4)] {
            let partial = ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own_memory(bytes(
                    retired.clone(),
                    retired_bytes.into(),
                )))
                .unchecked_with_fact(CResourceFact::own_memory(bytes(
                    read.clone(),
                    read_bytes.into(),
                )));
            let partial = PureFactContext::new()
                .assume_proposition(Proposition::CResourceComposition(partial));
            assert!(!checked_atomic_load_equality(
                &load(after.clone()),
                &load(before.clone()),
                &partial
            ));
        }
        assert!(!checked_atomic_load_equality(
            &load(after.clone()),
            &load(before.clone()),
            &PureFactContext::new()
        ));
    }
    assert!(
        costs.iter().all(|cost| *cost <= 250),
        "indexed lifetime separation grew with unrelated members: {costs:?}"
    );
}

#[test]
fn cross_block_narrow_owners_do_not_separate_wider_accesses() {
    let _session = crate::kernel::VerificationSession::enter();
    use crate::kernel::memory_provenance::{
        typed_store_separated_ranges_evidence, write_access_is_disjoint_from_load,
    };
    let write = Pointer::symbolic(Variable(945_100));
    let read = Pointer::symbolic(Variable(945_101));
    let bytes = |base, count| CMemoryRange::new_with_element_width(base, 0u32.into(), count, 1);
    let mut costs = Vec::new();
    for count in [16u64, 128, 1024] {
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(bytes(write.clone(), 1u32.into())))
            .unchecked_with_fact(CResourceFact::own_memory(bytes(read.clone(), 1u32.into())))
            .unchecked_with_fact(CResourceFact::view_memory(bytes(read.clone(), 8u32.into())));
        for index in 0..count {
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(bytes(
                CMemory::frame_local_pointer(index + 1, "unrelated-width-owner"),
                8u32.into(),
            )));
        }
        let narrow =
            PureFactContext::new().assume_proposition(Proposition::CResourceComposition(resources));
        assert!(pointers_proven_distinct_for_memory_resolution(
            &write, &read, &narrow
        ));
        let ((), cost) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                access_byte_overlap(&write, 1, &read, 8, &narrow),
                AccessByteOverlap::Unknown,
            );
            assert!(!write_access_is_disjoint_from_load(
                &write, 1, &read, 8, &narrow
            ));
            assert!(typed_store_separated_ranges_evidence(&write, 1, &read, 8, &narrow).is_none());
        });
        costs.push(cost);
        crate::kernel::eval::declare_load_access_width(&read, 8);
        let before = CMemory::new();
        let after = before
            .clone()
            .store(write.clone(), CValue::UInt8(7u32.into()));
        assert!(
            !crate::kernel::reasoning::memories_match_for_pointer_load_under_assumptions(
                &before, &after, &read, &narrow,
            )
        );
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(read.clone()),
                crate::kernel::LoadKind::Bits64,
            )
        };
        assert!(!with_extended_dag_bridging(
            || checked_atomic_load_equality(&load(&before), &load(&after), &narrow,)
        ));
        let cached = CMemory::new().store(
            read.clone(),
            CValue::Int64(Bitvector32Term::Int64Constant(0)),
        );
        let stored = cached.without_possible_aliasing_cells(&write, 1, &narrow);
        assert_eq!(stored.known_value(&read), None);
        let union = CMemory::new().store_union(
            read.clone(),
            CType::Int64,
            CValue::Int64(Bitvector32Term::Int64Constant(0)),
        );
        assert_eq!(
            union
                .without_possible_aliasing_cells(&write, 1, &narrow)
                .known_union_value(&read, CType::Int64),
            None
        );

        let full = PureFactContext::new().assume_proposition(Proposition::CResourceComposition(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own_memory(bytes(write.clone(), 1u32.into())))
                .unchecked_with_fact(CResourceFact::own_memory(bytes(read.clone(), 8u32.into()))),
        ));
        assert!(write_access_is_disjoint_from_load(
            &write, 1, &read, 8, &full
        ));
        let proof = typed_store_separated_ranges_evidence(&write, 1, &read, 8, &full).unwrap();
        let step = crate::kernel::intern_c_memory_ref(&after)
            .derivation()
            .unwrap();
        assert!(proof.checks(step.as_ref(), &read, 8, &full));
        assert!(!proof.checks(step.as_ref(), &read, 8, &narrow));
        assert_eq!(
            cached
                .without_possible_aliasing_cells(&write, 1, &full)
                .known_value(&read),
            Some(CValue::Int64(Bitvector32Term::Int64Constant(0)))
        );
        assert_eq!(
            union
                .without_possible_aliasing_cells(&write, 1, &full)
                .known_union_value(&read, CType::Int64),
            Some(CValue::Int64(Bitvector32Term::Int64Constant(0)))
        );
    }
    assert!(
        costs.iter().all(|cost| *cost <= costs[0] + 32),
        "unrelated ownership scan: {costs:?}"
    );
}

#[test]
fn havoc_and_effect_summaries_require_complete_separated_read_extents() {
    let _session = crate::kernel::VerificationSession::enter();
    use crate::kernel::memory_provenance::typed_ranges_disjoint_from_pointer_evidence;
    let write = Pointer::symbolic(Variable(945_200));
    let read = Pointer::symbolic(Variable(945_201));
    let bytes = |base, count| CMemoryRange::new_with_element_width(base, 0u32.into(), count, 1);
    let write_range = bytes(write.clone(), 1u32.into());
    crate::kernel::eval::declare_load_access_width(&read, 8);
    for composition in [false, true] {
        for extent in [1u32, 8] {
            let read_range = bytes(read.clone(), extent.into());
            let authority = if composition {
                Proposition::CResourceComposition(
                    ResourceContext::new()
                        .unchecked_with_fact(CResourceFact::own_memory(write_range.clone()))
                        .unchecked_with_fact(CResourceFact::own_memory(read_range.clone()))
                        .unchecked_with_fact(CResourceFact::view_memory(bytes(
                            read.clone(),
                            8u32.into(),
                        ))),
                )
            } else {
                Proposition::CResourceSeparate {
                    left: Box::new(CResource::Memory(write_range.clone())),
                    right: Box::new(CResource::Memory(read_range)),
                }
            };
            let assumptions = PureFactContext::new().assume_proposition(authority);
            let full = extent == 8;
            let evidence = typed_ranges_disjoint_from_pointer_evidence(
                std::slice::from_ref(&write_range),
                &read,
                8,
                &assumptions,
            );
            assert_eq!(evidence.is_some(), full);
            if let Some(evidence) = evidence {
                assert!(evidence[0].checks(&write_range, &read, 8, &assumptions));
                assert!(!evidence[0].checks(&write_range, &read, 16, &assumptions));
                assert!(!evidence[0].checks(&write_range, &read, 8, &PureFactContext::new()));
            }
            let before = CMemory::new();
            let load = |memory: &CMemory| {
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory_ref(memory),
                    Box::new(read.clone()),
                    crate::kernel::LoadKind::Bits64,
                )
            };
            let called = before.clone().with_call_memory_havoc(
                Variable(945_202),
                std::slice::from_ref(&write_range),
                &assumptions,
                None,
            );
            assert_eq!(
                with_extended_dag_bridging(|| checked_atomic_load_equality(
                    &load(&before),
                    &load(&called),
                    &assumptions,
                )),
                full
            );
            let cached = before.clone().store(
                read.clone(),
                CValue::Int64(Bitvector32Term::Int64Constant(9)),
            );
            let called_cache = cached.with_call_memory_havoc(
                Variable(945_203),
                std::slice::from_ref(&write_range),
                &assumptions,
                None,
            );
            assert_eq!(called_cache.known_value(&read).is_some(), full);
            let looped = before.clone().with_loop_memory_havoc_preserving_loans(
                Variable(945_204),
                &BTreeSet::new(),
                Some(std::slice::from_ref(&write_range)),
                None,
            );
            assert_eq!(
                crate::kernel::explicit_atomic_equality_from_memory_derivations(
                    &load(&before),
                    &load(&looped),
                    &assumptions,
                ),
                full
            );
            // These marker snapshots have no havoc edge. Only the explicit
            // effect summary can transport the observation between them.
            let after = before.clone().with_block("call-havoc:extent-summary", 0);
            let summaries = assumptions.assume_proposition(Proposition::CMemoryEffectSummary {
                before: before.clone(),
                after: after.clone(),
                mutable_ranges: vec![write_range.clone()],
            });
            let condition =
                |memory| ConditionTerm::equal(load(memory), Bitvector32Term::Int64Constant(9));
            assert_eq!(
                summaries.conditions_equal_modulo_proven_snapshots(
                    &condition(&before),
                    &condition(&after),
                ),
                full
            );
        }
    }
}

#[test]
fn retained_range_separation_ignores_unrelated_fact_buckets() {
    let _session = crate::kernel::VerificationSession::enter();
    use crate::kernel::memory_provenance::typed_ranges_disjoint_from_pointer_evidence;
    let write = Pointer::symbolic(Variable(945_210));
    let read = Pointer::symbolic(Variable(945_211));
    let bytes = |base, count| CMemoryRange::new_with_element_width(base, 0u32.into(), count, 1);
    let written = bytes(write, 1u32.into());
    let mut costs = Vec::new();
    for count in [16u64, 128, 1024] {
        let mut assumptions =
            PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(written.clone())),
                right: Box::new(CResource::Memory(bytes(read.clone(), 8u32.into()))),
            });
        for index in 0..count {
            assumptions = assumptions.assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(bytes(
                    Pointer::symbolic(Variable(950_000 + index * 2)),
                    1u32.into(),
                ))),
                right: Box::new(CResource::Memory(bytes(
                    Pointer::symbolic(Variable(950_001 + index * 2)),
                    1u32.into(),
                ))),
            });
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let evidence = typed_ranges_disjoint_from_pointer_evidence(
                std::slice::from_ref(&written),
                &read,
                8,
                &assumptions,
            )
            .unwrap();
            assert!(evidence[0].checks(&written, &read, 8, &assumptions));
            assert!(
                typed_ranges_disjoint_from_pointer_evidence(
                    std::slice::from_ref(&written),
                    &read,
                    16,
                    &assumptions,
                )
                .is_none()
            );
        });
        costs.push(work);
    }
    assert!(
        costs[2] <= costs[0].saturating_mul(2).saturating_add(40),
        "selected range evidence must not scan unrelated facts: {costs:?}"
    );
}

#[test]
fn pointer_read_single_store_aligns_same_block_parameter_aliases() {
    let mut samples = Vec::new();
    for unrelated in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let parameter = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 4),
        };
        let p = parameter(98_480);
        let q = parameter(98_481);
        let original = intern_c_memory(CMemory::new());
        let materialized = intern_c_memory(
            original
                .memory()
                .clone()
                .with_seeded_cells(p.clone(), 4, CType::Int32, 0, 2, original.clone())
                .with_seeded_cells(
                    p.offset_by_bytes(8),
                    4,
                    CType::Int32,
                    0,
                    2,
                    original.clone(),
                )
                .with_seeded_cells(
                    p.offset_by_bytes(16),
                    4,
                    CType::Int32,
                    0,
                    2,
                    original.clone(),
                ),
        );
        let current = intern_c_memory(materialized.memory().clone().store(
            q.offset_by_bytes(8),
            CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
        ));
        let mut context = PureFactContext::new();
        for index in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(98_500 + index * 2)),
                    Pointer::symbolic(Variable(98_501 + index * 2)),
                ),
                true,
            );
        }
        let sibling = context.clone();
        let context = context.assume_condition(ConditionTerm::pointer_equal(p.clone(), q), true);
        let before = Pointer::loaded_value(&original, &p);
        let after = Pointer::loaded_value(&current, &p);
        let argument =
            |pointer| AlgebraicValue::C(CValue::typed_pointer(pointer, CType::Int32Pointer));
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&before, &original, &p);
            context.register_pointer_read(&after, &current, &p);
            resource_arguments_proven_equal(
                &argument(before.clone()),
                &argument(after.clone()),
                &context,
            )
        });
        assert!(
            equal,
            "a full eight-byte read survives an adjacent alias store after scalar materialization"
        );
        samples.push(work);
        sibling.register_pointer_read(&before, &original, &p);
        sibling.register_pointer_read(&after, &current, &p);
        assert!(!sibling.pointers_known_equal(&before, &after));
        // An eight-byte read at either offset overlaps the written right field.
        for address in [p.offset_by_bytes(4), p.offset_by_bytes(8)] {
            let before = Pointer::loaded_value(&original, &address);
            let after = Pointer::loaded_value(&current, &address);
            context.register_pointer_read(&before, &original, &address);
            context.register_pointer_read(&after, &current, &address);
            assert!(!context.pointers_known_equal(&before, &after));
        }
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "one-store alias admission visited unrelated facts: {samples:?}"
    );
}

/// Recording the edge of a snapshot the recording itself interns cannot
/// change any earlier answer, since no earlier question could name that
/// snapshot, so it leaves the derivation generation that keys negative memos
/// alone. Bumping it at every program step emptied those memos at every step.
#[test]
fn recording_a_fresh_snapshot_keeps_the_derivation_generation() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Pointer {
        block: "generation-block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = CMemory::new().with_block("generation-block", 8);
    let before = crate::kernel::primitives::c_memory_derivation_generation();
    let stored = base.store(cell.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
    assert!(
        crate::kernel::intern_c_memory_ref(&stored)
            .derivation()
            .is_some(),
        "the store recorded its edge"
    );
    assert_eq!(
        crate::kernel::primitives::c_memory_derivation_generation(),
        before,
        "a fresh snapshot's edge invalidates no earlier answer"
    );
}

/// A kept range's base is asked about by every walk that crosses its call,
/// each inside lookups of its own. A negative answer that no in-progress
/// lookup cut holds under any lookups, so the next walk reuses it instead of
/// proving the same failing equality again.
#[test]
fn a_failed_kept_base_equality_is_reused_across_cell_lookups() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = |variable: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let assumptions = PureFactContext::new();
    let memory = crate::kernel::intern_c_memory_ref(&CMemory::new());
    let ask = |lookup: u64| {
        let _lookup = crate::kernel::resource_tracker::cell_source::CellLookupGuard::enter(
            &memory,
            &base(lookup),
        )
        .expect("a fresh lookup enters");
        crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::memory_resolution::kept_range_bases_proven_equal(
                &base(998_001),
                &base(998_002),
                &assumptions,
            )
        })
    };
    let (first, _) = ask(998_100);
    let (second, reused) = ask(998_101);
    assert!(
        !first && !second,
        "distinct parameters are not proven equal"
    );
    assert_eq!(reused, 0, "the second walk reuses the first walk's answer");
}
