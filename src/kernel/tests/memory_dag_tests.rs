use super::*;

fn retained_memory_dag_path(cell: &MemoryDagCell) -> &[MemoryDagHop] {
    match cell {
        MemoryDagCell::Stored { path, .. } | MemoryDagCell::Unwritten { path, .. } => path,
    }
}

#[test]
fn checked_load_equality_capture_retains_and_rechecks_the_exact_query() {
    let before = CMemory::new().with_block("arg-memory", 16);
    let after = before.clone().with_block("local:temporary", 4);
    let pointer = arc_pointer(0);
    let assumptions = PureFactContext::new();

    let capture = CheckedLoadEqualityCapture::start();
    assert!(checked_memory_load_equality(
        &before,
        &after,
        &pointer,
        &assumptions,
    ));
    let equalities = capture.finish();

    assert_eq!(equalities.len(), 1);
    assert!(equalities[0].checks(&assumptions));
}

#[test]
fn checked_load_equality_retains_canonical_projection_provenance() {
    let source = CMemory::new()
        .with_block_without_derivation("arg-memory", 16)
        .with_block_without_derivation("local:i", 4);
    let source = crate::kernel::intern_c_memory_ref(&source);
    let pointer = arc_pointer(0);
    let original = Bitvector32Term::MemoryLoad(source.clone(), Box::new(pointer.clone()));
    let projected = canonicalize_atomic_loads_deep(&original);
    let Bitvector32Term::MemoryLoad(projected_memory, _) = &projected else {
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
    let newer_load = Bitvector32Term::MemoryLoad(newer.clone(), Box::new(pointer.clone()));
    let projected = canonicalize_atomic_loads_deep(&newer_load);
    let Bitvector32Term::MemoryLoad(projected_memory, _) = &projected else {
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

    let older_load = Bitvector32Term::MemoryLoad(older.clone(), Box::new(pointer.clone()));
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
        &PureFactContext::new(),
    ));
    let constant_left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_constant),
        Box::new(constant_read.clone()),
    );
    let constant_right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&base),
        Box::new(constant_read.clone()),
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
    let inequality = ConditionTerm::equal(write_index, read_index);
    let assumptions = PureFactContext::new().assume_condition(inequality.clone(), false);
    let after_symbolic = base.store(symbolic_write, CValue::Int32(Bitvector32Term::Constant(9)));
    let symbolic_evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_c_memory_ref(&after_symbolic),
        &crate::kernel::intern_c_memory_ref(&CMemory::new().with_block("arg-memory", 32)),
        &symbolic_read,
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
        &assumptions,
    ));
    assert!(
        !symbolic_hop.justification.checks(
            symbolic_hop.derivation.as_ref(),
            &symbolic_read,
            &PureFactContext::new(),
        ),
        "the retained exact premise must still be present during check"
    );
    let symbolic_left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_symbolic),
        Box::new(symbolic_read.clone()),
    );
    let symbolic_right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&CMemory::new().with_block("arg-memory", 32)),
        Box::new(symbolic_read),
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
            .checks(hop.derivation.as_ref(), &read, &assumptions,)
    );
    assert!(
        !hop.justification.checks(
            hop.derivation.as_ref(),
            &read,
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
        left: CResource::Memory(write_range.clone()),
        right: CResource::Memory(load_range.clone()),
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
    );
    let right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&base),
        Box::new(load.clone()),
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
        !composed.checks(derivation.as_ref(), &load, &PureFactContext::new(),),
        "the retained composition must still be present during checking"
    );
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
        left: CResource::Memory(write_range),
        right: CResource::Memory(load_range),
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
    let left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after),
        Box::new(load.clone()),
    );
    let right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&base),
        Box::new(load.clone()),
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
            .checks(hop.derivation.as_ref(), &load, &assumptions)
    );

    let missing_successor = PureFactContext::new()
        .assume_proposition(separation)
        .assume_condition(zero_le_write, true)
        .assume_condition(write_lt_three, true)
        .assume_condition(zero_le_load, true);
    assert!(
        !hop.justification
            .checks(hop.derivation.as_ref(), &load, &missing_successor),
        "the retained successor bound must still be present"
    );
    let retargeted = load_base.offset_by_int32_elements(Bitvector32Term::add(
        load_index,
        Bitvector32Term::Constant(1),
    ));
    assert!(
        !hop.justification
            .checks(hop.derivation.as_ref(), &retargeted, &assumptions),
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
    );
    let second = base.with_call_memory_havoc(
        Variable(70_000),
        std::slice::from_ref(&second_range),
        &PureFactContext::new(),
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
    let after = base
        .clone()
        .with_loop_memory_havoc(Variable(0), &BTreeSet::new(), None);

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

    let havoced = base
        .clone()
        .with_loop_memory_havoc(Variable(7), &BTreeSet::new(), None);
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
    let havoced = base
        .clone()
        .with_loop_memory_havoc(Variable(8), &BTreeSet::new(), Some(&ranges));

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
    let overlapping = base.clone().with_loop_memory_havoc(
        Variable(9),
        &BTreeSet::new(),
        Some(&overlapping_ranges),
    );
    assert!(!checked_memory_load_equality(
        &base,
        &overlapping,
        &read,
        &PureFactContext::new()
    ));
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
        )
    };
    let call_havoc = |variable| {
        base.clone().with_call_memory_havoc(
            Variable(variable),
            &[memory_range(arc_pointer(8), 0, 8)],
            &PureFactContext::new(),
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
    assert_eq!(
        PureFactContext::new().memory_loads_proven_equal(&load_in(&left), &load_in(&right)),
        true,
        "the common-ancestor lookup is exactly what the DAG adds here"
    );
    let evidence = memory_load_equality_evidence_at(
        &crate::kernel::intern_c_memory_ref(&left),
        &crate::kernel::intern_c_memory_ref(&right),
        &read,
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
    let havoced = left
        .clone()
        .with_loop_memory_havoc(Variable(9), &BTreeSet::new(), None);
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
    let len = Bitvector32Term::Variable(Variable(203));
    let separation = Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
        right: CResource::Memory(memory_range(data.clone(), 0, 16)),
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
    let called = base
        .clone()
        .with_call_memory_havoc(Variable(204), &mutable_ranges, &assumptions);
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(data.clone()),
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
    assert_eq!(
        ranges,
        &vec![
            RangeDisjointFromPointerEvidence::ExactSeparationFact(separation),
            RangeDisjointFromPointerEvidence::ForwardOffset {
                offset: Bitvector32Term::Variable(Variable(203)),
                positive: PositiveTermEvidence::OneLowerBound(lower_bound),
            },
        ]
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
    // The call-havoc edge froze the context in force when it was recorded,
    // so crossing it is checked from the edge alone.
    assert!(
        offset_derivation.check(&PureFactContext::new()),
        "the havoc edge's frozen context decides the crossing without ambient premises"
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
    let len_at_entry = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry),
        Box::new(len_pointer.clone()),
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
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(8),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(12),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(16),
            bytes: Bitvector32Term::Constant(32),
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
        .without_possible_aliasing_cells(&arc_pointer(4), &assumptions);
    let len_at_later = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&later),
        Box::new(len_pointer),
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
        "the loadable bound check must connect the two len forms along \
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
    );

    assert!(
        !checked_memory_load_equality(&materialized, &havocked, &loaded, &PureFactContext::new(),),
        "a havoc of the loaded pointer must not be laundered by sibling \
         materialization cells jumping to their common source"
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
fn a_store_at_a_symbolic_index_keeps_a_cell_its_frozen_order_separates() {
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
    assert_eq!(
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory_ref(&separated),
            kept.clone()
        ),
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory_ref(&base),
            kept.clone()
        ),
        "the frozen order `index < length` separates the loaded cell from the written one"
    );

    // Interning is first-wins on equal content, so the unordered store
    // writes a different value to get its own edge.
    let unordered = base
        .clone()
        .store_with_context(written, int32(8), &PureFactContext::new());
    assert_ne!(
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory_ref(&unordered),
            kept.clone()
        ),
        crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory_ref(&base),
            kept
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
fn frozen_order_store_crossing_ignores_unrelated_order_facts() {
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
            let expected = crate::kernel::eval::canonical_form_of_load(
                crate::kernel::intern_c_memory_ref(&base),
                kept.clone(),
            );
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::eval::canonical_form_of_load(
                    crate::kernel::intern_c_memory_ref(&separated),
                    kept.clone(),
                )
            });
            assert_eq!(
                resolved, expected,
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
