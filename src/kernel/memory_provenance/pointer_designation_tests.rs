use super::*;
use crate::kernel::api::int32;

fn slot() -> Pointer {
    Pointer {
        block: PointerBlock::from("global:designation_slots"),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn selected(member: &str) -> CPointerValue {
    let root = Pointer::symbolic(Variable(986_100));
    CPointerValue::new(root.offset_by_bytes(4), CType::Int32Pointer).with_designation(
        PointerDesignation::Object {
            root: root.clone(),
            base: root,
            path: vec![PointerDomainSelection::Member(member.into())].into(),
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::constant_i64(1).into(),
        },
    )
}

fn loaded(memory: &CMemory, cell: &Pointer) -> CPointerValue {
    CPointerValue::new(selected("first").pointer().clone(), CType::Int32Pointer).with_designation(
        PointerDesignation::Loaded(PointerLoadIdentity::new(
            intern_c_memory_ref(memory),
            cell.clone(),
        )),
    )
}

fn equal(left: &CPointerValue, right: &CPointerValue, context: &PureFactContext) -> bool {
    pointer_designations_proven_equal(left, right, context)
}

#[test]
fn loaded_pointer_designation_transports_complete_stores_and_checked_frames() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let cell = slot();
    let first = selected("first");
    let memory = CMemory::new()
        .with_block(cell.block.clone(), 32)
        .store(cell.clone(), CValue::Pointer(first.clone()));
    let read = loaded(&memory, &cell);
    assert!(equal(&read, &first, &context));
    assert!(equal(&first, &read, &context));
    assert!(c_values_proven_equal_for_memory_resolution(
        &CValue::Pointer(read.clone()),
        &CValue::Pointer(first.clone()),
        &context,
    ));
    let frame = memory.clone().store(cell.offset_by_bytes(16), int32(7));
    let framed_read = loaded(&frame, &cell);
    assert!(equal(&read, &framed_read, &context));
    assert!(equal(&framed_read, &first, &context));
    assert!(loaded_pointer_designations_equal(
        read.designation().cloned(),
        framed_read.designation().cloned(),
        &context,
    ));
    // A complete pointer store can itself retain an earlier unknown pair.
    let copied = frame.store(cell.offset_by_bytes(8), CValue::Pointer(read));
    assert!(equal(
        &loaded(&copied, &cell.offset_by_bytes(8)),
        &first,
        &context
    ));
}

#[test]
fn loaded_pointer_value_equality_recovers_an_exact_stored_legacy_carrier() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let cell = slot();
    let legacy = CPointerValue::new(
        Pointer {
            block: PointerBlock::Heap(986_210),
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::Int32Pointer,
    );
    let memory = CMemory::new()
        .with_block(cell.block.clone(), 16)
        .store(cell.clone(), CValue::Pointer(legacy.clone()));
    let snapshot = intern_c_memory_ref(&memory);
    let read = CPointerValue::new(Pointer::loaded_value(&snapshot, &cell), CType::Int32Pointer)
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            snapshot,
            cell.clone(),
        )));
    assert!(equal(&read, &legacy, &context));
    assert!(c_values_proven_equal_for_memory_resolution(
        &CValue::Pointer(read.clone()),
        &CValue::Pointer(legacy.clone()),
        &context
    ));
    assert!(
        resolve_loaded_pointer_carrier(&read, &context).is_none(),
        "a stored legacy value grants no native domain"
    );
    let unknown_memory = CMemory::new().with_block(cell.block.clone(), 16);
    let snapshot = intern_c_memory_ref(&unknown_memory);
    let unknown = CPointerValue::new(Pointer::loaded_value(&snapshot, &cell), CType::Int32Pointer)
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            snapshot,
            cell.clone(),
        )));
    let alias = context.clone().assume_condition(
        ConditionTerm::pointer_equal(unknown.pointer().clone(), legacy.pointer().clone()),
        true,
    );
    assert!(!equal(&unknown, &legacy, &alias));
    let partial = memory.store(cell, int32(7));
    let snapshot = intern_c_memory_ref(&partial);
    let read = CPointerValue::new(
        Pointer::loaded_value(&snapshot, &slot()),
        CType::Int32Pointer,
    )
    .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
        snapshot,
        slot(),
    )));
    assert!(!equal(&read, &legacy, &context));
}

#[test]
fn unknown_pointer_designation_frames_keep_the_pair_instead_of_becoming_legacy() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let cell = slot();
    let memory = CMemory::new().with_block(cell.block.clone(), 32);
    let read = loaded(&memory, &cell);
    let frame = memory.clone().store(cell.offset_by_bytes(16), int32(7));
    let framed_read = loaded(&frame, &cell);
    assert!(equal(&read, &framed_read, &context));
    let legacy = CPointerValue::new(read.pointer().clone(), read.c_type());
    assert!(!equal(&read, &legacy, &context));
    assert!(!equal(&framed_read, &selected("first"), &context));
    // Reading the sibling storage cell is a different unresolved pair even
    // when a numeric equation says the resulting addresses coincide.
    let sibling = loaded(&frame, &cell.offset_by_bytes(8));
    assert!(!equal(&read, &sibling, &context));
}

#[test]
fn unknown_full_pointer_values_frame_only_through_their_exact_read_pairs() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let cell = slot();
    let read = |memory: &CMemory, address: &Pointer| {
        let snapshot = intern_c_memory_ref(memory);
        CPointerValue::new(
            Pointer::loaded_value(&snapshot, address),
            CType::Int32Pointer,
        )
        .with_pointee_constant(true)
        .with_pointee_volatile(true)
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            snapshot,
            address.clone(),
        )))
    };
    let value_equal = |left: &CPointerValue, right: &CPointerValue, facts: &PureFactContext| {
        c_values_proven_equal_for_memory_resolution(
            &CValue::Pointer(left.clone()),
            &CValue::Pointer(right.clone()),
            facts,
        )
    };
    let before = CMemory::new().with_block(cell.block.clone(), 32);
    let old = read(&before, &cell);
    let after = before
        .clone()
        .store(cell.offset_by_bytes(8), int32(u32::MAX));
    let current = read(&after, &cell);
    assert_ne!(old.pointer(), current.pointer());
    assert!(value_equal(&old, &current, &context));
    assert!(value_equal(&current, &old, &context));
    let canonical = canonical_loaded_pointer_carrier(&current, &context).unwrap();
    assert_eq!(canonical.c_type(), current.c_type());
    assert!(canonical.pointee_constant());
    assert!(canonical.pointee_volatile());
    assert!(resolve_loaded_pointer_carrier(&current, &context).is_none());

    for address in [cell.clone(), cell.offset_by_bytes(4)] {
        let partial = before.clone().store(address, int32(7));
        assert!(!value_equal(&old, &read(&partial, &cell), &context));
    }
    let changed = before
        .clone()
        .store(cell.clone(), CValue::Pointer(selected("first")));
    assert!(!value_equal(&old, &read(&changed, &cell), &context));
    let havoc = before.with_storage_memory_havoc(
        Variable(986_220),
        &[CMemoryRange::new(cell.clone(), 0u32.into(), 8u32.into())],
        &context,
    );
    let other_origin = read(&havoc, &cell);
    let numeric = context.clone().assume_condition(
        ConditionTerm::pointer_equal(old.pointer().clone(), other_origin.pointer().clone()),
        true,
    );
    assert!(!value_equal(&old, &other_origin, &numeric));
    let legacy = CPointerValue::new(old.pointer().clone(), old.c_type());
    let unresolved = legacy
        .clone()
        .with_designation(PointerDesignation::Unresolved(Variable(986_221)));
    assert!(!value_equal(&old, &legacy, &context));
    assert!(!value_equal(&old, &unresolved, &context));
    let sibling = read(&after, &cell.offset_by_bytes(16));
    let numeric = context.assume_condition(
        ConditionTerm::pointer_equal(old.pointer().clone(), sibling.pointer().clone()),
        true,
    );
    assert!(!value_equal(&old, &sibling, &numeric));
}

#[test]
fn native_prefix_carrier_frames_metadata_and_separated_pointee_store() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(986_230)),
    };
    let before = CMemory::new();
    let snapshot = intern_c_memory_ref(&before);
    let Bitvector32Term::Variable(variable) = crate::kernel::eval::canonical_form_of_load(
        snapshot.clone(),
        cell.clone(),
        LoadKind::Pointer,
    ) else {
        panic!("the full pointer read has an immutable producer name");
    };
    let original = CPointerValue::new(
        Pointer::loaded(cell.block.clone(), Bitvector32Term::Variable(variable), 4),
        CType::Int32Pointer,
    )
    .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
        snapshot,
        cell.clone(),
    )));
    let admitted = before
        .with_native_input_span(
            original.clone(),
            CType::Int32,
            IntegerTerm::constant_i64(1).into(),
        )
        .unwrap();
    let range =
        |base, end, width| CMemoryRange::new_with_element_width(base, 0u32.into(), end, width);
    let composition = Proposition::CResourceComposition(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(range(
                cell.clone(),
                2u32.into(),
                4,
            )))
            .unchecked_with_fact(CResourceFact::own_memory(range(
                original.pointer().clone(),
                1u32.into(),
                4,
            ))),
    );
    let context = PureFactContext::new().assume_proposition(composition.clone());
    let after = admitted.clone().store(original.pointer().clone(), int32(0));
    let read = |memory: &CMemory| {
        let snapshot = intern_c_memory_ref(memory);
        let Bitvector32Term::Variable(variable) = crate::kernel::eval::canonical_form_of_load(
            snapshot.clone(),
            cell.clone(),
            LoadKind::Pointer,
        ) else {
            panic!("a complete pointer read");
        };
        let Some(Bitvector32Term::MemoryLoad(defining, address, LoadKind::Pointer)) =
            crate::kernel::registered_load_term_for_variable(&variable)
        else {
            panic!("the producer retains its full immutable definition");
        };
        CPointerValue::new(
            Pointer::loaded(
                address.block.clone(),
                Bitvector32Term::Variable(variable),
                4,
            ),
            CType::Int32Pointer,
        )
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            defining, *address,
        )))
    };
    assert!(!extended_dag_bridging_active());
    assert!(!explicit_dag_check_active());
    let framed = canonical_loaded_pointer_carrier(&read(&after), &context).unwrap();
    assert_eq!(framed.designation(), original.designation());
    assert!(after.native_input_span(&framed).is_some());
    assert!(!extended_dag_bridging_active());
    assert!(!explicit_dag_check_active());
    let current = read(&after);
    let mut work_samples = Vec::new();
    for unrelated in [16u64, 128, 1024] {
        let mut facts = context.clone();
        for index in 0..unrelated {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(986_300 + index)),
                    100u32.into(),
                ),
                true,
            );
        }
        let _scope = facts.enter_id_scope();
        let (framed, work) = crate::instrumentation::measure_deterministic_work(|| {
            canonical_loaded_pointer_carrier(&current, &facts)
        });
        assert_eq!(framed.unwrap().designation(), original.designation());
        work_samples.push(work);
    }
    assert_eq!(
        work_samples[0], work_samples[2],
        "checking the selected three-hop read cannot visit unrelated order facts: {work_samples:?}"
    );
    // Compositions are retained separately from exact proposition facts;
    // use a context that never admitted this ownership authority.
    let withdrawn = PureFactContext::new();
    let unproved = canonical_loaded_pointer_carrier(&read(&after), &withdrawn);
    assert!(unproved.is_none_or(|value| value.designation() != original.designation()));
    let partial = admitted.store(cell.clone(), int32(7));
    let changed = canonical_loaded_pointer_carrier(&read(&partial), &context);
    assert!(changed.is_none_or(|value| value.designation() != original.designation()));
}

#[test]
fn loaded_pointer_designation_refuses_stale_partial_numeric_and_havoc_origins() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let cell = slot();
    let first = selected("first");
    let second = selected("second");
    assert_eq!(first.pointer(), second.pointer());
    let memory = CMemory::new()
        .with_block(cell.block.clone(), 32)
        .store(cell.clone(), CValue::Pointer(first.clone()));
    let old = loaded(&memory, &cell);
    let overwritten = memory
        .clone()
        .store(cell.clone(), CValue::Pointer(second.clone()));
    let new = loaded(&overwritten, &cell);
    assert!(!equal(&old, &new, &context));
    assert!(!equal(&new, &first, &context));
    assert!(equal(&new, &second, &context));
    for value in [
        CValue::UInt8(Bitvector32Term::Constant(0)),
        CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
    ] {
        let altered = memory.clone().store(cell.clone(), value);
        let read = loaded(&altered, &cell);
        assert!(!equal(&read, &old, &context));
        assert!(!equal(&read, &first, &context));
        assert!(!equal(
            &read,
            &CPointerValue::new(read.pointer().clone(), read.c_type()),
            &context
        ));
    }
    let havoc = memory.with_storage_memory_havoc(
        Variable(986_101),
        &[CMemoryRange::new(cell.clone(), 0u32.into(), 8u32.into())],
        &context,
    );
    assert!(!equal(&loaded(&havoc, &cell), &old, &context));
    assert!(!equal(&loaded(&havoc, &cell), &first, &context));
}

#[test]
fn pointer_designation_transport_uses_storage_alias_evidence_only() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = slot();
    let alias = Pointer::symbolic(Variable(986_102));
    let first = selected("first");
    let second = selected("second");
    let memory = CMemory::new()
        .with_block(cell.block.clone(), 32)
        .store(cell.clone(), CValue::Pointer(first.clone()))
        .store(cell.offset_by_bytes(8), CValue::Pointer(second.clone()));
    let context = PureFactContext::new();
    let unknown = loaded(&memory, &alias);
    {
        let _scope = context.enter_id_scope();
        assert!(!equal(&unknown, &first, &context));
        assert!(!equal(&unknown, &first, &context));
    }
    let cell_equality = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), cell.clone()),
        true,
    );
    let known = context.assume_proposition(cell_equality.clone());
    {
        let _scope = known.enter_id_scope();
        assert!(equal(&unknown, &first, &known));
        assert!(equal(&unknown, &first, &known));
    }
    let withdrawn = known.without_exact_fact(&cell_equality);
    {
        let _scope = withdrawn.enter_id_scope();
        assert!(!equal(&unknown, &first, &withdrawn));
    }
    let read = loaded(&memory, &cell).with_pointer(Pointer::symbolic(Variable(986_103)));
    let sibling = loaded(&memory, &cell.offset_by_bytes(8))
        .with_pointer(Pointer::symbolic(Variable(986_104)));
    let numeric = known.assume_condition(
        ConditionTerm::pointer_equal(read.pointer().clone(), sibling.pointer().clone()),
        true,
    );
    assert!(!equal(&read, &sibling, &numeric));
    assert!(!c_values_proven_equal_for_memory_resolution(
        &CValue::Pointer(read),
        &CValue::Pointer(sibling),
        &numeric,
    ));
}

#[test]
fn loaded_pointer_designation_memo_tracks_late_edges_and_lookup_modes() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new();
    let _scope = context.enter_id_scope();
    let cell = slot();
    let first = selected("first");
    let stored = CMemory::new()
        .with_block(cell.block.clone(), 8)
        .store(cell.clone(), CValue::Pointer(first.clone()));
    let base = intern_c_memory_ref(&stored);
    // This is the same byte-preserving cell-forgetting transition used by
    // production, with its faithful edge recorded after the first query.
    let mut forgotten = stored.clone();
    std::sync::Arc::make_mut(&mut forgotten.cells).remove(&cell);
    forgotten.mark_forgotten_from(&base);
    let read = loaded(&forgotten, &cell);
    let origin = read.designation().cloned();
    let expected = first.designation().cloned();
    with_extended_dag_bridging(|| {
        assert_eq!(
            resolve_loaded_pointer_designation(origin.clone(), &context),
            origin
        );
        let generation = c_memory_derivation_generation();
        record_c_memory_derivation(&mut forgotten, CMemoryDerivation::CellsForgotten { base });
        assert!(c_memory_derivation_generation() > generation);
        assert_eq!(
            resolve_loaded_pointer_designation(origin.clone(), &context),
            expected
        );
    });
    // Ordinary planning cannot reuse the answer that crossed the edge in
    // the extended bridging scope.
    assert_eq!(
        resolve_loaded_pointer_designation(origin.clone(), &context),
        origin
    );
    with_extended_dag_bridging(|| {
        let Some(PointerDesignation::Loaded(identity)) = &origin else {
            panic!("a loaded origin")
        };
        let lookup = CellLookupGuard::enter(identity.memory(), identity.address()).unwrap();
        let nested = resolve_loaded_pointer_designation(origin.clone(), &context);
        drop(lookup);
        assert_eq!(
            nested, origin,
            "a warm answer must not bypass a live lookup"
        );
        assert_eq!(
            resolve_loaded_pointer_designation(origin.clone(), &context),
            expected
        );
        let memo_size = LOADED_POINTER_DESIGNATIONS_MEMO.with(|memo| memo.borrow().len());
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let explicit_scope = loaded_pointer_designation_memo_scope(&context);
        let explicit = resolve_loaded_pointer_designation(origin.clone(), &context);
        let explicit_memo_size = LOADED_POINTER_DESIGNATIONS_MEMO.with(|memo| memo.borrow().len());
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
        assert!(explicit_scope.is_none());
        assert_eq!(explicit, expected);
        assert_eq!(
            explicit_memo_size, memo_size,
            "explicit checking stays unmemoized"
        );
    });
}

#[test]
fn copied_loaded_pointer_designations_resolve_with_linear_total_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let first = selected("first");
    let cell = slot();
    let mut samples = Vec::new();
    for count in [4u32, 16, 64] {
        let context = PureFactContext::new();
        let mut memory = CMemory::new()
            .with_block(cell.block.clone(), count * 8)
            .store(cell.clone(), CValue::Pointer(first.clone()));
        let mut previous = loaded(&memory, &cell);
        let mut reads = vec![previous.clone()];
        for index in 1..count {
            let target = cell.offset_by_bytes(index * 8);
            memory = memory.store(target.clone(), CValue::Pointer(previous));
            previous = loaded(&memory, &target);
            reads.push(previous.clone());
        }
        let _scope = context.enter_id_scope();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            // Each endpoint is queried once. Pair-comparison memoization
            // cannot hide repeated walks of their shared origin chain.
            for read in &reads {
                assert!(equal(read, &first, &context));
            }
        });
        samples.push(work);
    }
    eprintln!("copied designation chain work: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= 5 * pair[0] + 512,
            "copied designation chains repeated their prefixes: {samples:?}"
        );
    }
}

#[test]
fn resource_candidate_lookup_retains_checked_pointer_frames_without_ambient_scan() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = slot();
        let read = |memory: &CMemory| {
            let snapshot = intern_c_memory_ref(memory);
            CPointerValue::new(Pointer::loaded_value(&snapshot, &cell), CType::Int32Pointer)
                .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
                    snapshot,
                    cell.clone(),
                )))
        };
        let fact = |pointer| {
            CResourceFact::own(CResource::Composite {
                name: "indexed-carrier".into(),
                arguments: vec![AlgebraicValue::C(CValue::Pointer(pointer))].into(),
            })
        };
        let before = CMemory::new().with_block(cell.block.clone(), 32);
        let old = read(&before);
        let after = before.clone().store(cell.offset_by_bytes(8), int32(7));
        let current = read(&after);
        let context = PureFactContext::new();
        assert!(c_values_proven_equal_for_memory_resolution(
            &CValue::Pointer(old.clone()),
            &CValue::Pointer(current.clone()),
            &context
        ));
        let held = fact(old.clone());
        let required = fact(current);
        let mut resources = ResourceContext::new().unchecked_with_fact(held.clone());
        for index in 0..size {
            let address = cell.offset_by_bytes(64 + (index as u32) * 8);
            let snapshot = intern_c_memory_ref(&before);
            resources = resources.unchecked_with_fact(fact(
                CPointerValue::new(
                    Pointer::loaded_value(&snapshot, &address),
                    CType::Int32Pointer,
                )
                .with_designation(PointerDesignation::Loaded(
                    PointerLoadIdentity::new(snapshot, address),
                )),
            ));
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .directly_supporting_fact(&required, &context)
                .cloned()
        });
        assert_eq!(found, Some(held.clone()), "size={size}, work={work}");
        assert!(work < 100, "size={size}, work={work}");
        let withdrawn = resources
            .clone()
            .without_exact_representation(&held)
            .unwrap();
        assert!(
            withdrawn
                .directly_supporting_fact(&required, &context)
                .is_none()
        );
        let partial = before.clone().store(cell.offset_by_bytes(4), int32(7));
        let changed = fact(read(&partial));
        assert!(
            resources
                .directly_supporting_fact(&changed, &context)
                .is_none()
        );
        let numeric = context.assume_condition(
            ConditionTerm::pointer_equal(old.pointer().clone(), read(&partial).pointer().clone()),
            true,
        );
        assert!(
            resources
                .directly_supporting_fact(&changed, &numeric)
                .is_none()
        );
    }
}

#[test]
fn resource_read_index_withdraws_original_keys_after_late_frame_edges() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = slot();
    let base = CMemory::new().with_block(cell.block.clone(), 32);
    let base_ref = intern_c_memory_ref(&base);
    let mut forgotten = base.clone();
    forgotten.mark_forgotten_from(&base_ref);
    let after = forgotten.clone().store(cell.offset_by_bytes(8), int32(7));
    let read = |memory: &CMemory| {
        let snapshot = intern_c_memory_ref(memory);
        CPointerValue::new(Pointer::loaded_value(&snapshot, &cell), CType::Int32Pointer)
            .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
                snapshot,
                cell.clone(),
            )))
    };
    let fact = |pointer| {
        CResourceFact::own(CResource::Composite {
            name: "late-index-frame".into(),
            arguments: vec![AlgebraicValue::C(CValue::Pointer(pointer))].into(),
        })
    };
    let held = fact(read(&after));
    let resources = ResourceContext::new().unchecked_with_fact(held.clone());
    record_c_memory_derivation(
        &mut forgotten,
        CMemoryDerivation::CellsForgotten { base: base_ref },
    );
    let withdrawn = resources.without_exact_representation(&held).unwrap();
    assert!(
        withdrawn
            .directly_supporting_fact(&fact(read(&forgotten)), &PureFactContext::new())
            .is_none()
    );
}

#[test]
fn null_pointer_resources_do_not_require_a_referent_designation() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new().with_block(slot().block.clone(), 32);
    let left = loaded(&memory, &slot()).with_pointer(Pointer::symbolic(Variable(986_900)));
    let right = loaded(&memory, &slot().offset_by_bytes(8))
        .with_pointer(Pointer::symbolic(Variable(986_901)));
    let null = CPointerValue::new(Pointer::null(), CType::Int32Pointer);
    let context = PureFactContext::new();
    assert!(!equal(&left, &right, &context));
    let one_null = context.assume_condition(
        crate::kernel::eval::pointer_is_null_condition(left.pointer().clone()),
        true,
    );
    assert!(equal(&left, &null, &one_null));
    assert!(!equal(&left, &right, &one_null));
    let both_null = one_null.assume_condition(
        crate::kernel::eval::pointer_is_null_condition(right.pointer().clone()),
        true,
    );
    assert!(equal(&left, &right, &both_null));
    assert!(c_values_proven_equal_for_memory_resolution(
        &CValue::Pointer(left.clone()),
        &CValue::Pointer(right.clone()),
        &both_null,
    ));
    assert!(resolve_loaded_pointer_carrier(&left, &both_null).is_none());
    assert!(resolve_loaded_pointer_carrier(&right, &both_null).is_none());
    let numeric_only = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone()),
        true,
    );
    assert!(!equal(&left, &right, &numeric_only));
}

#[test]
fn null_designation_matching_ignores_unrelated_pointer_equations() {
    for size in [16u64, 256, 4096] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let left = loaded(&memory, &slot()).with_pointer(Pointer::symbolic(Variable(987_000)));
        let null = CPointerValue::new(Pointer::null(), CType::Int32Pointer);
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(1_100_000 + index * 2)),
                    Pointer::symbolic(Variable(1_100_001 + index * 2)),
                ),
                true,
            );
        }
        context = context.assume_condition(
            crate::kernel::eval::pointer_is_null_condition(left.pointer().clone()),
            true,
        );
        let _scope = context.enter_id_scope();
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| equal(&left, &null, &context));
        assert!(answer);
        assert!(
            work <= 256,
            "{size} unrelated pointer equations caused {work} work"
        );
    }
}
