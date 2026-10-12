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
