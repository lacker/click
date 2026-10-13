use super::*;
use crate::kernel::prelude::*;

fn layout() -> Arc<CAggregateLayout> {
    Arc::new(CAggregateLayout::new(
        8,
        4,
        vec![
            CAggregateField::new("first", 0, CType::Int32),
            CAggregateField::new("second", 4, CType::Int32),
        ],
    ))
}

fn unresolved(identity: u64, address: Pointer) -> CPointerValue {
    CPointerValue::new(address, CType::UInt8Pointer)
        .with_designation(PointerDesignation::Unresolved(Variable(identity)))
}

fn loaded(memory: &CMemory, address: &Pointer) -> CPointerValue {
    let snapshot = intern_c_memory_ref(memory);
    CPointerValue::new(
        Pointer::loaded_value(&snapshot, address),
        CType::UInt8Pointer,
    )
    .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
        snapshot,
        address.clone(),
    )))
}

#[test]
fn native_record_selected_guards_cancel_scaled_root_and_nested_member_offsets() {
    let _session = crate::kernel::VerificationSession::enter();
    for (size, name, offset) in [(4, "refs", 0), (8, "second", 4)] {
        let record = Arc::new(CAggregateLayout::new(
            size,
            4,
            vec![CAggregateField::new(name, offset, CType::Int32)],
        ));
        // Source formal addresses themselves have a native scale. Rebuilding
        // the containing root through +field followed by -field must cancel
        // outside that observed machine value, including a zero-offset field.
        let origin = unresolved(
            989_950 + u64::from(size),
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(989_960)),
                    i64::from(size),
                ),
            },
        )
        .with_type(CType::Int32Pointer);
        let memory = CMemory::new()
            .with_native_record_input(origin.clone(), record.clone())
            .unwrap();
        let selection = CAggregateMemberSelection {
            layout: record,
            path: vec![name.to_string()].into(),
            value_type: CType::Int32,
        };
        assert!(memory.checked_native_record_pointer(&origin).is_some());
        let (selected, guards) = memory
            .guarded_native_record_selection(&origin, &selection, &PureFactContext::new())
            .unwrap();
        assert!(
            guards
                .iter()
                .all(|guard| PureFactContext::new().decide(guard) == Some(true)),
            "{guards:?}"
        );
        assert!(
            memory
                .authenticated_input_selection(&selected, &PureFactContext::new())
                .unwrap()
                .iter()
                .all(|guard| PureFactContext::new().decide(guard) == Some(true))
        );
    }
}

#[test]
fn native_record_input_selects_exact_identity_and_preserves_current_position() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(989_000));
    let pointer = unresolved(989_001, address.clone())
        .with_pointee_constant(true)
        .with_pointee_volatile(true);
    let before = CMemory::new();
    let memory = before
        .clone()
        .with_native_record_input(pointer.clone(), layout())
        .unwrap();
    assert_eq!(memory.blocks, before.blocks);
    assert_eq!(memory.cells, before.cells);
    assert_eq!(memory.heap.initialized, before.heap.initialized);
    let checked = memory.checked_native_record_pointer(&pointer).unwrap();
    assert!(checked.pointee_constant() && checked.pointee_volatile());
    assert_eq!(checked.pointer(), &address);
    assert!(memory.authenticated_pointer_domain_at_base(&checked));
    assert!(
        memory
            .checked_native_record_pointer(&CPointerValue::new(
                address.clone(),
                CType::UInt8Pointer
            ))
            .is_none()
    );
    assert!(
        memory
            .checked_native_record_pointer(&unresolved(989_002, address.clone()))
            .is_none()
    );
    let shifted = pointer.clone().with_pointer(address.offset_by_bytes(8));
    let checked_shifted = memory.checked_native_record_pointer(&shifted).unwrap();
    assert_eq!(checked_shifted.pointer(), &address.offset_by_bytes(8));
    assert!(checked_shifted.same_designation(&checked));
    let selection = CAggregateMemberSelection {
        layout: layout(),
        path: vec!["first".into()].into(),
        value_type: CType::Int32,
    };
    assert!(
        memory
            .checked_member_pointer(&pointer, &selection)
            .is_some()
    );
    assert!(
        memory
            .checked_member_pointer(&shifted, &selection)
            .is_none()
    );
}

#[test]
fn native_record_input_never_overrides_a_known_declaration_or_descriptor() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = CMemory::local_pointer("native-record-scalar");
    let memory = CMemory::new().with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
    let scalar = memory
        .declared_scalar_pointer(&address, CType::Int32)
        .unwrap();
    assert!(
        memory
            .clone()
            .with_native_record_input(scalar.clone(), layout())
            .is_err()
    );
    assert!(
        memory
            .with_native_record_input(unresolved(989_010, address), layout())
            .is_err()
    );
    let input = unresolved(989_011, Pointer::symbolic(Variable(989_012)));
    let memory = CMemory::new()
        .with_native_record_input(input.clone(), layout())
        .unwrap();
    let wrong_layout = Arc::new(CAggregateLayout::new(
        16,
        4,
        vec![CAggregateField::new("first", 0, CType::Int32)],
    ));
    assert!(
        memory
            .with_native_record_input(input, wrong_layout)
            .is_err()
    );
}

#[test]
fn native_record_loaded_input_requires_the_exact_full_pointer_read_pair() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = CMemory::local_pointer("native-record-pointer-cell");
    let memory = CMemory::new().with_block(cell.block.clone(), C_POINTER_BYTE_WIDTH);
    let pointer = loaded(&memory, &cell);
    let before = memory.clone();
    let memory = memory
        .with_native_record_input(pointer.clone(), layout())
        .unwrap();
    assert_eq!(memory.cells, before.cells);
    assert_eq!(memory.heap.initialized, before.heap.initialized);
    assert!(memory.checked_native_record_pointer(&pointer).is_some());
    let forged = pointer
        .clone()
        .with_pointer(Pointer::symbolic(Variable(989_020)));
    assert!(memory.checked_native_record_pointer(&forged).is_none());
    assert!(
        CMemory::new()
            .with_native_record_input(forged, layout())
            .is_err()
    );
    let other = loaded(&before, &cell.offset_by_bytes(8));
    assert!(memory.checked_native_record_pointer(&other).is_none());
    let shifted = pointer
        .clone()
        .with_pointer(pointer.pointer().offset_by_bytes(8));
    assert_eq!(
        memory
            .checked_native_record_pointer(&shifted)
            .unwrap()
            .pointer(),
        shifted.pointer()
    );
    let snapshot = intern_c_memory_ref(&before);
    let cell = cell.offset_by_bytes(16);
    crate::kernel::eval::symbolic_load_value(&before, &cell, CType::Int32).unwrap();
    let narrow = canonical_form_of_load(snapshot.clone(), cell.clone(), LoadKind::Bits32);
    let Bitvector32Term::Variable(variable) = narrow else {
        panic!("registered read")
    };
    let narrow_pointer = CPointerValue::new(Pointer::symbolic(variable), CType::UInt8Pointer)
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            snapshot, cell,
        )));
    assert!(
        CMemory::new()
            .with_native_record_input(narrow_pointer, layout())
            .is_err()
    );
}

#[test]
fn native_record_inputs_retire_known_and_possible_aliases_without_resurrection() {
    let _session = crate::kernel::VerificationSession::enter();
    for known_alias in [false, true] {
        let allocation = Pointer {
            block: PointerBlock::Heap(989_030),
            offset: PointerOffsetTerm::Constant(0),
        };
        let address = Pointer::symbolic(Variable(989_031));
        let pointer = unresolved(989_032, address.clone());
        let memory = CMemory::new()
            .with_heap_allocation_claim(allocation.clone(), 8)
            .unwrap()
            .with_native_record_input(pointer.clone(), layout())
            .unwrap();
        let assumptions = if known_alias {
            PureFactContext::new().assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(address.clone(), allocation.clone()),
                true,
            ))
        } else {
            PureFactContext::new()
        };
        let retired = memory.free_heap_block(&allocation, &assumptions).unwrap();
        assert!(retired.checked_native_record_pointer(&pointer).is_none());
        assert!(retired.heap.native_record_inputs.is_empty());
        assert!(retired.heap.native_record_input_origins.is_empty());
        let layout_only = retired
            .with_object_input_domain(address, &layout())
            .unwrap();
        assert!(
            layout_only
                .checked_native_record_pointer(&pointer)
                .is_none()
        );
    }
}

#[test]
fn native_record_input_substitution_and_whole_delta_collectors_preserve_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let from = Variable(989_040);
    let to = Variable(989_041);
    let identity = Variable(989_042);
    let pointer = unresolved(identity.0, Pointer::symbolic(from));
    let memory = CMemory::new()
        .with_native_record_input(pointer.clone(), layout())
        .unwrap();
    let mapped = substitute_pointer_variable_in_memory(&memory, from, &Pointer::symbolic(to));
    let mapped_pointer = pointer.with_pointer(Pointer::symbolic(to));
    assert!(
        mapped
            .checked_native_record_pointer(&mapped_pointer)
            .is_some()
    );
    assert!(
        mapped
            .checked_native_record_pointer(&unresolved(to.0, Pointer::symbolic(to)))
            .is_none()
    );
    let mut whole = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables_whole(&mapped, &mut whole);
    assert!(whole.contains(&identity) && whole.contains(&to) && !whole.contains(&from));
    let base = intern_c_memory_ref(&memory);
    let after = intern_c_memory_ref(&mapped);
    let mut before_variables = BTreeSet::new();
    collect_shared_memory_bitvector_variables(&base, &mut before_variables);
    let mut delta_variables = BTreeSet::new();
    collect_shared_memory_bitvector_variables(&after, &mut delta_variables);
    assert_eq!(whole, delta_variables);
}

#[test]
fn native_record_input_query_ignores_unrelated_witnesses_and_memory() {
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = unresolved(989_050, Pointer::symbolic(Variable(989_051)));
        let mut memory = CMemory::new()
            .with_native_record_input(pointer.clone(), layout())
            .unwrap();
        for index in 0..count {
            let address = Pointer {
                block: PointerBlock::Heap(990_000 + index),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory
                .with_native_record_input(unresolved(991_000 + index, address), layout())
                .unwrap();
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.checked_native_record_pointer(&pointer)
        });
        assert!(checked.is_some());
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn native_record_input_local_lifetime_end_and_no_write_lineage_are_explicit() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = CMemory::local_pointer("native-record-lifetime");
    let cell = CMemory::local_pointer("native-record-other-cell");
    let pointer = unresolved(989_060, address.clone());
    let before = CMemory::new()
        .with_block(address.block.clone(), 8)
        .with_block(cell.block.clone(), 4);
    let before_read =
        canonical_form_of_load(intern_c_memory_ref(&before), cell.clone(), LoadKind::Bits32);
    let memory = before
        .clone()
        .with_native_record_input(pointer.clone(), layout())
        .unwrap();
    let after_read =
        canonical_form_of_load(intern_c_memory_ref(&memory), cell.clone(), LoadKind::Bits32);
    assert_eq!(
        before_read, after_read,
        "validity must not create a byte-memory write"
    );
    let ended = memory.without_local_block(&address.block);
    assert!(ended.checked_native_record_pointer(&pointer).is_none());
    assert!(ended.heap.native_record_inputs.is_empty());
    assert!(ended.heap.native_record_input_origins.is_empty());
}

#[test]
fn native_input_local_retirement_drops_possible_aliases_but_keeps_fresh_objects() {
    let _session = crate::kernel::VerificationSession::enter();
    let local = CMemory::local_pointer("addressed-native-input-lifetime");
    let may_alias = unresolved(989_100, Pointer::symbolic(Variable(989_101)));
    let fresh = unresolved(
        989_102,
        Pointer {
            block: PointerBlock::Heap(989_103),
            offset: PointerOffsetTerm::Constant(0),
        },
    );
    let scalar_address = Pointer::symbolic(Variable(989_104));
    let scalar = CPointerValue::new(scalar_address.clone(), CType::Int32Pointer).with_designation(
        PointerDesignation::Object {
            root: scalar_address.clone(),
            path: Arc::from([]),
            base: scalar_address,
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::constant_i64(1).into(),
        },
    );
    let prefix =
        unresolved(989_105, Pointer::symbolic(Variable(989_106))).with_type(CType::Int32Pointer);
    let memory = CMemory::new()
        .with_block(local.block.clone(), 8)
        .with_native_record_input(may_alias.clone(), layout())
        .unwrap()
        .with_native_record_input(fresh.clone(), layout())
        .unwrap()
        .with_scalar_input_domain(scalar.clone(), CType::Int32)
        .unwrap()
        .with_native_input_span(
            prefix.clone(),
            CType::Int32,
            IntegerTerm::constant_i64(2).into(),
        )
        .unwrap();
    let retained_object = memory.checked_native_record_pointer(&may_alias).unwrap();
    assert!(memory.authenticated_pointer_domain_at_base(&retained_object));
    let ended = memory.without_local_block(&local.block);
    assert!(ended.checked_native_record_pointer(&may_alias).is_none());
    assert!(!ended.authenticated_pointer_domain_at_base(&retained_object));
    assert!(!ended.has_scalar_object_domain(&scalar, CType::Int32));
    assert!(ended.native_input_span(&prefix).is_none());
    assert!(ended.checked_native_record_pointer(&fresh).is_some());
    assert_eq!(ended.heap.native_record_inputs.len(), 1);
}

#[test]
fn native_typed_prefix_storage_preserves_identity_without_declaring_an_array() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer =
        unresolved(989_110, Pointer::symbolic(Variable(989_111))).with_type(CType::Int32Pointer);
    let before = CMemory::new();
    let count = SharedIntegerTerm::from(IntegerTerm::constant_i64(2));
    let memory = before
        .clone()
        .with_native_input_span(pointer.clone(), CType::Int32, count.clone())
        .unwrap();
    assert_eq!(memory.blocks, before.blocks);
    assert_eq!(memory.cells, before.cells);
    assert_eq!(memory.heap.initialized, before.heap.initialized);
    assert!(memory.heap.object_input_domains.is_empty());
    assert!(memory.checked_native_record_pointer(&pointer).is_none());
    let (origin, element_type, retained_count) = memory.native_input_span(&pointer).unwrap();
    assert_eq!(origin, pointer);
    assert_eq!(element_type, CType::Int32);
    assert_eq!(retained_count, count);
    let raw = CPointerValue::new(pointer.pointer().clone(), CType::Int32Pointer);
    assert!(memory.native_input_span(&raw).is_none());
    assert!(
        memory
            .native_input_span(&unresolved(989_112, pointer.pointer().clone()))
            .is_none()
    );
    let shifted = pointer
        .clone()
        .with_pointer(pointer.pointer().offset_by_bytes(4));
    assert_eq!(memory.native_input_span(&shifted).unwrap().0, pointer);
    let cast = shifted.with_type(CType::UInt8Pointer);
    assert_eq!(memory.native_input_span(&cast).unwrap().1, CType::Int32);
    assert!(
        CMemory::new()
            .with_native_input_span(
                pointer.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(-1).into()
            )
            .is_err()
    );
    assert!(
        CMemory::new()
            .with_native_input_span(
                pointer,
                CType::Int32,
                IntegerTerm::constant_i64(i64::MAX / 4 + 1).into()
            )
            .is_err()
    );
}

#[test]
fn native_typed_prefix_loaded_pair_and_lifetime_remain_exact() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = CMemory::local_pointer("native-prefix-pointer-cell");
    let allocation = Pointer {
        block: PointerBlock::Heap(989_120),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new()
        .with_block(cell.block.clone(), C_POINTER_BYTE_WIDTH)
        .with_heap_allocation_claim(allocation.clone(), 8)
        .unwrap();
    let pointer = loaded(&before, &cell).with_type(CType::Int32Pointer);
    let memory = before
        .clone()
        .with_native_input_span(
            pointer.clone(),
            CType::Int32,
            IntegerTerm::constant_i64(2).into(),
        )
        .unwrap();
    assert!(memory.native_input_span(&pointer).is_some());
    let forged = pointer
        .clone()
        .with_pointer(Pointer::symbolic(Variable(989_121)));
    assert!(memory.native_input_span(&forged).is_none());
    assert!(
        CMemory::new()
            .with_native_input_span(forged, CType::Int32, IntegerTerm::constant_i64(2).into())
            .is_err()
    );
    let wrong_cell = loaded(&before, &cell.offset_by_bytes(8));
    assert!(memory.native_input_span(&wrong_cell).is_none());
    let retired = memory
        .free_heap_block(&allocation, &PureFactContext::new())
        .unwrap();
    assert!(retired.native_input_span(&pointer).is_none());
    assert!(retired.heap.native_record_inputs.is_empty());
}

#[test]
fn native_typed_prefix_count_substitution_and_delta_collection_keep_selected_terms() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(989_130);
    let pointer =
        unresolved(989_131, Pointer::symbolic(Variable(989_132))).with_type(CType::Int32Pointer);
    let count = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        Bitvector32Term::Variable(variable),
    ));
    let memory = CMemory::new()
        .with_native_input_span(pointer.clone(), CType::Int32, count.into())
        .unwrap();
    let before = intern_c_memory_ref(&memory);
    let mut original_variables = BTreeSet::new();
    collect_shared_memory_bitvector_variables(&before, &mut original_variables);
    assert!(original_variables.contains(&variable));
    let mapped = crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
        &memory,
        variable,
        &Bitvector32Term::Constant(3),
    );
    assert!(mapped.native_input_span(&pointer).is_some());
    let mut whole = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables_whole(&mapped, &mut whole);
    assert!(!whole.contains(&variable));
    assert!(whole.contains(&Variable(989_131)) && whole.contains(&Variable(989_132)));
    let mut delta = BTreeSet::new();
    collect_shared_memory_bitvector_variables(&intern_c_memory_ref(&mapped), &mut delta);
    assert_eq!(whole, delta);
}

#[test]
fn native_input_selected_members_keep_distinct_keys_at_the_same_address() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(989_200));
    let first = unresolved(989_201, address.clone());
    let second = unresolved(989_202, address.clone());
    let memory = CMemory::new()
        .with_native_record_input(first.clone(), layout())
        .unwrap()
        .with_native_record_input(second.clone(), layout())
        .unwrap();
    let path = vec!["second".to_owned()];
    let first_member = memory
        .checked_member_pointer_by_path(&first, &path)
        .unwrap();
    let second_member = memory
        .checked_member_pointer_by_path(&second, &path)
        .unwrap();
    assert_eq!(first_member.pointer(), second_member.pointer());
    assert!(!first_member.same_designation(&second_member));
    assert_ne!(
        CValue::Pointer(first_member.clone()),
        CValue::Pointer(second_member)
    );
    assert!(memory.has_scalar_object_domain(&first_member, CType::Int32));
    let first_record = memory.checked_native_record_pointer(&first).unwrap();
    let reused = memory
        .clone()
        .with_native_record_input(first_record.clone(), layout())
        .unwrap();
    assert_eq!(
        reused, memory,
        "reusing an authenticated selection must add no witness or memory event"
    );
    assert!(
        memory
            .clone()
            .with_native_record_input(first_member.clone(), layout())
            .is_err()
    );
    assert!(
        matches!(memory.checked_native_record_pointer(&first).unwrap().designation(), Some(PointerDesignation::InputSelected { input: CNativeInputIdentity::Unresolved(identity), path, .. }) if *identity == Variable(989_201) && path.is_empty())
    );
    assert!(
        memory
            .checked_member_pointer_by_path(&unresolved(989_203, address.clone()), &path)
            .is_none()
    );
    assert!(
        memory
            .checked_member_pointer_by_path(
                &CPointerValue::new(address, CType::UInt8Pointer),
                &path
            )
            .is_none()
    );
    let PointerDesignation::InputSelected {
        input,
        origin,
        path,
        base,
        stride,
        count,
        ..
    } = first_member.designation().unwrap()
    else {
        panic!("selected input")
    };
    let forged = first_member
        .clone()
        .with_designation(PointerDesignation::InputSelected {
            input: input.clone(),
            origin: origin.clone(),
            path: path.clone(),
            base: base.clone(),
            element_type: CType::Float32,
            stride: *stride,
            count: count.clone(),
        });
    assert!(
        memory
            .authenticated_input_selection(&forged, &PureFactContext::new())
            .is_none()
    );
    assert!(
        memory
            .clone()
            .with_native_record_input(forged, layout())
            .is_err()
    );
    let known_scalar = memory.with_declared_scalar_block(origin.block.clone(), 4, CType::Int32);
    assert!(
        known_scalar
            .authenticated_input_selection(&first_member, &PureFactContext::new())
            .is_none()
    );
}

#[test]
fn native_input_selected_record_prefix_retains_symbolic_bounds_and_substitution() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(989_210);
    let bits = Bitvector32Term::Variable(variable);
    let origin = unresolved(989_211, Pointer::symbolic(Variable(989_212)));
    let memory = CMemory::new()
        .with_native_record_prefix(
            origin.clone(),
            layout(),
            IntegerTerm::constant_i64(2).into(),
        )
        .unwrap();
    let indexed = origin
        .clone()
        .with_pointer(
            origin
                .pointer()
                .offset_by_typed_elements(bits.clone(), 8, false, false),
        );
    let selection = CAggregateMemberSelection {
        layout: layout(),
        path: vec!["second".into()].into(),
        value_type: CType::Int32,
    };
    let lower = ConditionTerm::signed_less_equal(0u32.into(), bits.clone());
    let upper = ConditionTerm::signed_less_than(bits, 2u32.into());
    let assumptions = PureFactContext::new()
        .assume_condition(lower.clone(), true)
        .assume_condition(upper.clone(), true);
    let (selected, guards) = memory
        .guarded_native_record_selection(&indexed, &selection, &assumptions)
        .unwrap();
    assert!(
        guards
            .iter()
            .all(|guard| assumptions.decide(guard) == Some(true)),
        "{guards:?}"
    );
    assert!(
        memory
            .checked_member_pointer(&indexed, &selection)
            .is_none()
    );
    assert!(
        guards
            .iter()
            .any(|guard| PureFactContext::new().decide(guard) != Some(true))
    );
    let only_lower = PureFactContext::new().assume_condition(lower, true);
    assert!(
        guards
            .iter()
            .any(|guard| only_lower.decide(guard) != Some(true))
    );
    let CValue::Pointer(mapped) =
        crate::kernel::reasoning::substitute_bitvector_variable_in_c_value(
            &CValue::Pointer(selected),
            variable,
            &1u32.into(),
        )
    else {
        panic!("pointer")
    };
    assert_eq!(mapped.pointer().offset.as_const(), Some(12));
    let mapped_guards = memory
        .authenticated_input_selection(&mapped, &PureFactContext::new())
        .unwrap();
    assert!(
        mapped_guards
            .iter()
            .all(|guard| guard == &ConditionTerm::Constant(true)),
        "{mapped_guards:?}"
    );
    assert!(
        matches!(mapped.designation(), Some(PointerDesignation::InputSelected { input: CNativeInputIdentity::Unresolved(identity), path, .. }) if *identity == Variable(989_211) && matches!(path.first(), Some(PointerDomainSelection::Element(index)) if index.as_ref() == &IntegerTerm::constant_i64(1)))
    );
    let past = origin
        .clone()
        .with_pointer(origin.pointer().offset_by_bytes(16));
    let (_, past_guards) = memory
        .guarded_native_record_selection(&past, &selection, &PureFactContext::new())
        .unwrap();
    assert!(past_guards.contains(&ConditionTerm::Constant(false)));
    let empty = CMemory::new()
        .with_native_record_prefix(
            origin.clone(),
            layout(),
            IntegerTerm::constant_i64(0).into(),
        )
        .unwrap();
    assert!(empty.checked_native_record_pointer(&origin).is_none());
    let (_, empty_guards) = empty
        .guarded_native_record_selection(&origin, &selection, &PureFactContext::new())
        .unwrap();
    assert!(empty_guards.contains(&ConditionTerm::Constant(false)));
    assert!(
        CMemory::new()
            .with_native_record_prefix(
                origin,
                Arc::new(CAggregateLayout::new(0, 1, vec![])),
                IntegerTerm::constant_i64(1).into()
            )
            .is_err()
    );
}

#[test]
fn native_input_selected_loaded_key_survives_substitution_and_complete_reload() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = CMemory::local_pointer("native-selected-original-read");
    let stored_cell = CMemory::local_pointer("native-selected-copy");
    let before = CMemory::new()
        .with_block(cell.block.clone(), C_POINTER_BYTE_WIDTH)
        .with_block(stored_cell.block.clone(), C_POINTER_BYTE_WIDTH);
    let origin = loaded(&before, &cell);
    let variable = Variable(989_220);
    let memory = before
        .with_native_record_prefix(
            origin.clone(),
            layout(),
            IntegerTerm::constant_i64(2).into(),
        )
        .unwrap();
    let indexed = origin
        .clone()
        .with_pointer(origin.pointer().offset_by_typed_elements(
            Bitvector32Term::Variable(variable),
            8,
            false,
            false,
        ));
    let selection = CAggregateMemberSelection {
        layout: layout(),
        path: vec!["first".into()].into(),
        value_type: CType::Int32,
    };
    let (selected, _) = memory
        .guarded_native_record_selection(&indexed, &selection, &PureFactContext::new())
        .unwrap();
    let CValue::Pointer(selected) =
        crate::kernel::reasoning::substitute_bitvector_variable_in_c_value(
            &CValue::Pointer(selected),
            variable,
            &1u32.into(),
        )
    else {
        panic!("pointer")
    };
    let PointerDesignation::Loaded(original_key) = origin.designation().unwrap() else {
        panic!("read pair")
    };
    assert!(
        matches!(selected.designation(), Some(PointerDesignation::InputSelected { input: CNativeInputIdentity::Loaded(key), .. }) if key == original_key)
    );
    assert!(
        memory
            .authenticated_input_selection(&selected, &PureFactContext::new())
            .unwrap()
            .iter()
            .all(|guard| guard == &ConditionTerm::Constant(true))
    );
    let stored = memory
        .clone()
        .store(stored_cell.clone(), CValue::Pointer(selected.clone()));
    let read = loaded(&stored, &stored_cell).with_type(CType::Int32Pointer);
    let resolved = crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(
        &read,
        &PureFactContext::new(),
    )
    .unwrap();
    assert_eq!(resolved, selected);
    assert!(
        stored
            .authenticated_input_selection(&resolved, &PureFactContext::new())
            .is_some()
    );
    let PointerDesignation::InputSelected {
        origin: source,
        path,
        base,
        element_type,
        stride,
        count,
        ..
    } = selected.designation().unwrap()
    else {
        panic!("selected")
    };
    let forged = selected
        .clone()
        .with_designation(PointerDesignation::InputSelected {
            input: CNativeInputIdentity::Loaded(PointerLoadIdentity::new(
                original_key.memory().clone(),
                cell.offset_by_bytes(8),
            )),
            origin: source.clone(),
            path: path.clone(),
            base: base.clone(),
            element_type: *element_type,
            stride: *stride,
            count: count.clone(),
        });
    assert!(
        stored
            .authenticated_input_selection(&forged, &PureFactContext::new())
            .is_none()
    );
}

#[test]
fn native_input_selected_array_decay_keeps_parent_guards_and_actual_extent() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = Arc::new(CAggregateLayout::new(
        20,
        4,
        vec![
            CAggregateField::new("tag", 0, CType::Int32),
            CAggregateField::new("items", 4, CType::Int32Array(4)),
        ],
    ));
    let origin = unresolved(989_230, Pointer::symbolic(Variable(989_231)));
    let index = Bitvector32Term::Variable(Variable(989_232));
    let memory = CMemory::new()
        .with_native_record_prefix(
            origin.clone(),
            layout.clone(),
            IntegerTerm::constant_i64(2).into(),
        )
        .unwrap();
    let indexed = origin
        .clone()
        .with_pointer(
            origin
                .pointer()
                .offset_by_typed_elements(index.clone(), 20, false, false),
        );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, 2u32.into()), true);
    let (member, _) = memory
        .guarded_native_record_selection(
            &indexed,
            &CAggregateMemberSelection {
                layout,
                path: vec!["items".into()].into(),
                value_type: CType::Int32Array(4),
            },
            &assumptions,
        )
        .unwrap();
    let (array, guards) = memory
        .guarded_member_array_pointer(&member, &assumptions)
        .unwrap();
    assert!(
        guards
            .iter()
            .all(|guard| assumptions.decide(guard) == Some(true)),
        "{guards:?}"
    );
    assert!(
        guards
            .iter()
            .any(|guard| PureFactContext::new().decide(guard) != Some(true))
    );
    assert!(memory.checked_member_array_pointer(&member).is_none());
    let PointerDesignation::InputSelected {
        input,
        path,
        element_type,
        stride,
        count,
        ..
    } = array.designation().unwrap()
    else {
        panic!("selected array")
    };
    assert_eq!(input, &CNativeInputIdentity::Unresolved(Variable(989_230)));
    assert!(matches!(
        path.first(),
        Some(PointerDomainSelection::Element(_))
    ));
    assert_eq!(*element_type, CType::Int32);
    assert_eq!(*stride, 4);
    assert_eq!(count.as_ref(), &IntegerTerm::constant_i64(4));
    let shifted = member
        .clone()
        .with_pointer(member.pointer().offset_by_bytes(4));
    let (_, shifted_guards) = memory
        .guarded_member_array_pointer(&shifted, &assumptions)
        .unwrap();
    assert!(
        shifted_guards
            .iter()
            .any(|guard| assumptions.decide(guard) != Some(true))
    );
    let wrong_type = member.with_type(CType::UInt8Pointer);
    let (cast_decay, _) = memory
        .guarded_member_array_pointer(&wrong_type, &assumptions)
        .unwrap();
    assert_eq!(cast_decay.c_type(), CType::Int32Pointer);
}

#[test]
fn native_loaded_prefix_normalization_follows_only_full_stored_read_pairs() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = CMemory::local_pointer("prefix-normalization-source");
    let copy = CMemory::local_pointer("prefix-normalization-copy");
    let before = CMemory::new()
        .with_block(cell.block.clone(), 8)
        .with_block(copy.block.clone(), 8);
    crate::kernel::eval::symbolic_load_value(&before, &cell, CType::Int32Pointer).unwrap();
    let source = intern_c_memory_ref(&before);
    let Bitvector32Term::Variable(variable) =
        canonical_form_of_load(source, cell.clone(), LoadKind::Pointer)
    else {
        panic!("registered source")
    };
    assert_eq!(
        crate::kernel::registered_load_bytes_for_variable(&variable),
        Some(8)
    );
    let Some(Bitvector32Term::MemoryLoad(defining_memory, defining_cell, LoadKind::Pointer)) =
        crate::kernel::registered_load_term_for_variable(&variable)
    else {
        panic!("immutable producer read")
    };
    let origin =
        CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer).with_designation(
            PointerDesignation::Loaded(PointerLoadIdentity::new(defining_memory, *defining_cell)),
        );
    let memory = before
        .clone()
        .with_native_input_span(
            origin.clone(),
            CType::Int32,
            IntegerTerm::constant_i64(2).into(),
        )
        .unwrap();
    let legacy = CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer);
    let copied = memory.clone().store(copy.clone(), CValue::Pointer(legacy));
    let read = loaded(&copied, &copy)
        .with_type(CType::Int32Pointer)
        .with_pointee_constant(true)
        .with_pointee_volatile(true);
    let canonical = crate::kernel::memory_provenance::canonical_loaded_pointer_carrier(
        &read,
        &PureFactContext::new(),
    )
    .unwrap();
    assert!(canonical.same_designation(&origin));
    assert!(canonical.pointee_constant() && canonical.pointee_volatile());
    assert!(copied.native_input_span(&canonical).is_some());
    // A manually selected snapshot is a different key from the variable's
    // defining read. The source's block-only metadata cannot rebrand it.
    let manual = loaded(&before, &cell).with_type(CType::Int32Pointer);
    assert!(!manual.same_designation(&origin));
    let mismatched = before
        .clone()
        .with_native_input_span(manual, CType::Int32, IntegerTerm::constant_i64(2).into())
        .unwrap();
    assert!(mismatched.native_input_span(&canonical).is_none());
    assert!(
        crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(
            &read,
            &PureFactContext::new()
        )
        .is_none()
    );
    for changed in [
        copied.clone().store(copy.clone(), int32(7)),
        copied.clone().store(
            copy.clone(),
            CValue::UInt64(Bitvector32Term::UInt64Constant(7)),
        ),
    ] {
        let read = loaded(&changed, &copy).with_type(CType::Int32Pointer);
        let normalized = crate::kernel::memory_provenance::canonical_loaded_pointer_carrier(
            &read,
            &PureFactContext::new(),
        );
        assert!(
            normalized
                .as_ref()
                .is_none_or(|pointer| changed.native_input_span(pointer).is_none())
        );
    }
    let foreign = CPointerValue::new(Pointer::symbolic(Variable(989_250)), CType::Int32Pointer);
    let context = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(foreign.pointer().clone(), origin.pointer().clone()),
        true,
    );
    let unrelated = memory.store(copy.clone(), CValue::Pointer(foreign));
    assert!(
        crate::kernel::memory_provenance::canonical_loaded_pointer_carrier(
            &loaded(&unrelated, &copy),
            &context
        )
        .is_none()
    );
}

#[test]
fn native_loaded_prefix_normalization_has_linear_selected_history_work() {
    let mut samples = vec![];
    for count in [4, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer::symbolic(Variable(989_260));
        let before = CMemory::new().with_block(cell.block.clone(), (count + 1) * 8);
        let Bitvector32Term::Variable(variable) =
            crate::kernel::eval::canonical_form_of_typed_load(
                intern_c_memory_ref(&before),
                cell.clone(),
                CType::Int32Pointer,
            )
            .expect("complete pointer read")
        else {
            panic!("registered source")
        };
        let Some(Bitvector32Term::MemoryLoad(defining_memory, defining_cell, LoadKind::Pointer)) =
            crate::kernel::registered_load_term_for_variable(&variable)
        else {
            panic!("immutable producer read")
        };
        let origin = CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer)
            .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
                defining_memory,
                *defining_cell,
            )));
        let mut memory = before
            .with_native_input_span(
                origin.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(1024).into(),
            )
            .unwrap();
        let mut previous = origin;
        for index in 1..=count {
            let destination = cell.offset_by_bytes(index * 8);
            memory = memory.store(destination.clone(), CValue::Pointer(previous));
            previous = loaded(&memory, &destination).with_type(CType::Int32Pointer);
        }
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::canonical_loaded_pointer_carrier(
                &previous,
                &PureFactContext::new(),
            )
        });
        assert!(memory.native_input_span(&normalized.unwrap()).is_some());
        samples.push((count, work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 * 5),
        "{samples:?}"
    );
    assert!(samples.last().unwrap().1 < 64 * 64, "{samples:?}");
}
