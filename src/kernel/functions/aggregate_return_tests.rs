//! Copy-return compatibility and checked construction-destination oracles.
//! C++ source admission is tested separately from these shared operations.
use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

fn node_layout() -> CAggregateLayout {
    CAggregateLayout::new(
        16,
        8,
        vec![
            CAggregateField::new("self", 0, CType::Int32Pointer),
            CAggregateField::new("value", 8, CType::Int32),
        ],
    )
}

#[test]
fn aggregate_result_binding_preserves_input_and_existing_declarations() {
    let layout = node_layout();
    let interface = c_function(
        CType::UInt8Array(layout.size_bytes()),
        "retain_source",
        Vec::new(),
        c_return(c_void_value()),
    )
    .with_return_aggregate_layout(layout.clone());
    let address = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(874_071))),
            byte_width: 4,
        },
    };
    let pointer = CMemory::aggregate_input_pointer(address.clone(), &layout, CType::UInt8Pointer);
    let memory = CMemory::new()
        .with_object_input_domain(address.clone(), &layout)
        .unwrap();
    let mut state = CState::new().with_memory(memory.clone());
    set_contract_result(
        &mut state,
        interface.contract_interface(),
        CValue::Pointer(pointer.clone()),
    );
    assert_eq!(state.memory(), &memory);
    assert!(
        state
            .memory()
            .has_aggregate_object_domain(&pointer, &layout)
    );
    assert!(state.memory().blocks.get(&address.block).is_none());

    // A result name cannot replace a conflicting real declaration either.
    let conflicting = memory.with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
    let mut state = CState::new().with_memory(conflicting.clone());
    set_contract_result(
        &mut state,
        interface.contract_interface(),
        CValue::Pointer(pointer.clone()),
    );
    assert_eq!(state.memory(), &conflicting);
    assert!(
        !state
            .memory()
            .has_aggregate_object_domain(&pointer, &layout)
    );

    let local = CMemory::frame_local_pointer(0, "completed_return");
    let declared = CMemory::new().with_declared_aggregate_block(local.block.clone(), &layout);
    let result = declared
        .declared_aggregate_pointer(&local, &layout)
        .unwrap();
    let mut state = CState::new().with_memory(declared.clone());
    set_contract_result(
        &mut state,
        interface.contract_interface(),
        CValue::Pointer(result.clone()),
    );
    assert_eq!(state.memory(), &declared);
    assert!(state.memory().has_aggregate_object_domain(&result, &layout));
}

// Manual kernel IR names the same fields as native member lowering. Raw byte
// offsets deliberately retain the original domain and cannot select a field.
fn checked_field(
    object: CExpression,
    layout: &CAggregateLayout,
    name: &str,
    value_type: CType,
) -> CExpression {
    CExpression::MemberAddress {
        object: Box::new(object),
        selection: Arc::new(CAggregateMemberSelection {
            layout: Arc::new(layout.clone()),
            path: vec![name.to_string()].into(),
            value_type,
        }),
    }
}

fn copy_function() -> CFunction {
    c_function(
        CType::VoidPointer,
        "copy_result",
        vec![c_parameter("source", CType::VoidPointer)],
        c_return(c_variable("source")),
    )
    .with_return_aggregate_layout(node_layout())
}

fn pointer(value: &CValue) -> Pointer {
    let CValue::Pointer(value) = value else {
        panic!("expected an aggregate storage pointer");
    };
    value.pointer().clone()
}

fn allocate_destination(state: &CState, name: &str) -> CState {
    let paths = crate::kernel::eval::execute_c_statement_paths(
        state,
        &c_allocate_aggregate_destination(name, node_layout()),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("checked destination allocation");
    let [path] = paths.as_slice() else {
        panic!("one allocation outcome expected");
    };
    assert!(path.obligations.is_empty());
    let CStatementOutcome::Normal(state) = &path.outcome else {
        panic!("destination allocation failed: {:?}", path.outcome);
    };
    state.as_ref().clone()
}

fn assert_declared_aggregate(memory: &CMemory, pointer: &Pointer, expected: &CAggregateLayout) {
    let block = memory.blocks.get(&pointer.block).expect("declared storage");
    let Some(CDeclaredObject::Aggregate(layout)) = &block.declared_object else {
        panic!("expected aggregate declaration: {block:?}");
    };
    assert_eq!(layout.as_ref(), expected);
    assert_eq!(block.size.as_const(), Some(expected.size_bytes()));
}

#[test]
fn aggregate_record_boundary_parentage_is_explicit_and_checked() {
    let base = CAggregateLayout::new(16, 4, vec![]);
    let nested = base.clone().with_records(vec![
        CAggregateRecord::new("outer", 0, 16, 4, None),
        CAggregateRecord::new("outer.middle", 0, 8, 4, Some(0)),
        CAggregateRecord::new("outer.middle.leaf", 0, 4, 4, Some(1)),
    ]);
    assert_eq!(
        nested
            .records()
            .iter()
            .map(CAggregateRecord::parent)
            .collect::<Vec<_>>(),
        vec![None, Some(0), Some(1)]
    );
    assert!(
        nested
            .records()
            .iter()
            .all(|record| record.offset_bytes() == 0)
    );
    assert_ne!(nested, base);
    for records in [
        vec![CAggregateRecord::new("bad", 12, 8, 4, None)],
        vec![CAggregateRecord::new("bad", 2, 4, 4, None)],
        vec![CAggregateRecord::new("bad", 0, 4, 4, Some(0))],
        vec![
            CAggregateRecord::new("a", 0, 8, 4, None),
            CAggregateRecord::new("b", 8, 8, 4, None),
            CAggregateRecord::new("a.late", 0, 4, 4, Some(0)),
        ],
    ] {
        assert!(std::panic::catch_unwind(|| base.clone().with_records(records)).is_err());
    }
}

fn selection_layouts() -> (CAggregateLayout, CAggregateLayout) {
    let child = CAggregateLayout::new(8, 4, vec![CAggregateField::new("value", 0, CType::Int32)]);
    let parent = CAggregateLayout::new(
        24,
        4,
        vec![
            CAggregateField::new("first.value", 0, CType::Int32),
            CAggregateField::new("second.value", 8, CType::Int32),
            CAggregateField::new("tail", 16, CType::Int32),
        ],
    )
    .with_records(vec![
        CAggregateRecord::new("first", 0, 8, 4, None),
        CAggregateRecord::new("second", 8, 8, 4, None),
    ]);
    (parent, child)
}

#[test]
fn absent_native_record_identity_preserves_legacy_structural_hashes() {
    use std::hash::{Hash, Hasher};
    fn hash(value: &impl Hash) -> u64 {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut state);
        state.finish()
    }
    let (parent, child) = selection_layouts();
    for record in parent.records() {
        assert_eq!(
            hash(record),
            hash(&(
                record.name(),
                record.offset_bytes(),
                record.size_bytes(),
                record.alignment_bytes(),
                record.parent(),
            )),
        );
    }
    for layout in [&parent, &child] {
        assert_eq!(
            hash(layout),
            hash(&(
                layout.size_bytes(),
                layout.alignment_bytes(),
                layout.fields(),
                layout.unions(),
                layout.records(),
            )),
        );
    }
    let identified = child
        .clone()
        .with_declaration_identity(Some(std::sync::Arc::new(
            CppRecordDeclarationIdentity::new("import", "c:@S@Child"),
        )));
    assert_ne!(hash(&child), hash(&identified));
    assert_eq!(hash(&identified), hash(&identified.clone()));
}

#[test]
fn constructor_binding_requires_the_native_record_declaration_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let identity = |import, declaration| {
        Some(std::sync::Arc::new(CppRecordDeclarationIdentity::new(
            import,
            declaration,
        )))
    };
    let (parent, child) = selection_layouts();
    let child = child.with_declaration_identity(identity("locked-import", "c:@S@Child"));
    let parent = parent
        .clone()
        .with_records(
            parent
                .records()
                .iter()
                .cloned()
                .map(|record| {
                    record.with_declaration_identity(child.declaration_identity().cloned())
                })
                .collect(),
        )
        .with_declaration_identity(identity("locked-import", "c:@S@Parent"));
    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_allocate_aggregate_destination("parent", parent),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let CStatementOutcome::Normal(caller) = &paths[0].outcome else {
        panic!("parent allocation");
    };
    let at = caller.locals.slot("parent").unwrap().offset_by_bytes(8);
    let bind = |layout| {
        let function = c_function(
            CType::Void,
            "construct_child",
            vec![c_parameter("destination", CType::Int32Pointer)],
            c_skip(),
        )
        .with_construction_parameter(0, layout);
        let values = [CValue::typed_pointer(at.clone(), CType::Int32Pointer)];
        (
            bind_c_function_arguments(caller, &function, &values).is_some(),
            bind_c_contract_arguments(caller, function.contract_interface(), &values, None)
                .is_some(),
        )
    };
    assert_eq!(bind(child.clone()), (true, true));
    for wrong in [
        identity("locked-import", "c:@S@OtherChild"),
        identity("other-import", "c:@S@Child"),
        None,
    ] {
        let wrong = child.clone().with_declaration_identity(wrong);
        assert_ne!(child, wrong);
        assert_eq!(bind(wrong), (false, false));
    }
    assert!(!caller.memory.has_initialized_bytes_under(
        &at.offset_by_bytes(4),
        4,
        &PureFactContext::new(),
    ));
}

#[test]
fn constructor_binding_requires_complete_or_explicit_child_designation() {
    let _session = crate::kernel::VerificationSession::enter();
    let (parent, child) = selection_layouts();
    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_allocate_aggregate_destination("parent", parent.clone()),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("one parent declaration");
    };
    let CStatementOutcome::Normal(caller) = &path.outcome else {
        panic!("parent allocation");
    };
    let caller = caller.as_ref().clone();
    let at = caller.locals.slot("parent").unwrap().clone();
    let function = c_function(
        CType::Void,
        "construct_child",
        vec![c_parameter("destination", CType::Int32Pointer)],
        c_skip(),
    )
    .with_construction_parameter(0, child.clone());
    for offset in [0, 8, 4, 12, 16, 24] {
        let values = [CValue::typed_pointer(
            at.offset_by_bytes(offset),
            CType::Int32Pointer,
        )];
        assert_eq!(
            bind_c_function_arguments(&caller, &function, &values).is_some(),
            matches!(offset, 0 | 8)
        );
        assert_eq!(
            bind_c_contract_arguments(&caller, function.contract_interface(), &values, None)
                .is_some(),
            matches!(offset, 0 | 8)
        );
    }
    assert!(caller.memory.has_object_layout_at(&at, &parent, false));
    assert!(
        !caller.memory.has_object_layout_at(&at, &child, false),
        "complete result cannot target a member"
    );
    let flat = CAggregateLayout::new(24, 4, parent.fields().to_vec());
    let wrong = caller.clone().with_memory(
        caller
            .memory
            .clone()
            .with_declared_aggregate_block(at.block.clone(), &flat)
            .with_object_input_domain(at.offset_by_bytes(8), &child)
            .unwrap(),
    );
    assert!(
        bind_c_function_arguments(
            &wrong,
            &function,
            &[CValue::typed_pointer(
                at.offset_by_bytes(8),
                CType::Int32Pointer
            )]
        )
        .is_none(),
        "matching input assumption cannot override a missing declared boundary"
    );
    let unsigned =
        CAggregateLayout::new(8, 4, vec![CAggregateField::new("value", 0, CType::UInt32)]);
    assert!(
        !caller
            .memory
            .has_object_layout_at(&at.offset_by_bytes(8), &unsigned, true)
    );
    let raw = CMemory::new().with_uninitialized_block(at.block.clone(), 24);
    assert!(!raw.has_object_layout_at(&at.offset_by_bytes(8), &child, true));
    let selected = CState::new()
        .with_memory(raw)
        .with_aggregate_return_destination(at.offset_by_bytes(8), child.clone());
    assert!(
        !selected
            .memory
            .has_object_layout_at(&at.offset_by_bytes(8), &child, true)
    );
}

#[test]
fn object_input_domains_survive_value_transitions_without_allocating_or_initializing() {
    let _session = crate::kernel::VerificationSession::enter();
    let (parent, child) = selection_layouts();
    let at = Pointer::symbolic(Variable(984_001));
    let raw = CMemory::new().with_uninitialized_object(at.clone(), 24);
    let entry = raw
        .clone()
        .with_object_input_domain(at.clone(), &parent)
        .unwrap();
    assert!(entry.block_size(&at.block).is_none());
    assert!(entry.known_value(&at).is_none());
    assert!(!entry.has_initialized_bytes_at(&at, 24));
    let written = entry.clone().store(at.offset_by_bytes(8), int32(19));
    let range = CMemoryRange::new_with_element_width(at.clone(), 0u32.into(), 24u32.into(), 1);
    let call = written.clone().with_call_memory_havoc(
        Variable(984_002),
        std::slice::from_ref(&range),
        &PureFactContext::new(),
        None,
    );
    let looped = written.clone().with_loop_memory_havoc_preserving_loans(
        Variable(984_003),
        &BTreeSet::new(),
        Some(std::slice::from_ref(&range)),
        None,
    );
    let joined = call
        .clone()
        .with_interface_memory_havoc(Variable(984_004), &BTreeSet::new(), &[&call, &looped])
        .unwrap();
    for memory in [&entry, &written, &call, &looped, &joined] {
        assert!(memory.has_object_layout_at(&at.offset_by_bytes(8), &child, true));
        assert!(
            !memory.has_initialized_bytes_under(
                &at.offset_by_bytes(12),
                4,
                &PureFactContext::new()
            ),
            "child padding stays raw"
        );
    }
    let canonical = crate::kernel::memory_provenance::canonical_c_memory_for_pointer_load(
        &joined,
        &at.offset_by_bytes(8),
    );
    assert!(canonical.has_object_layout_at(&at.offset_by_bytes(8), &child, true));
    let deep = crate::kernel::memory_provenance::canonical_c_memory_deep(&joined);
    assert!(deep.has_object_layout_at(&at.offset_by_bytes(8), &child, true));
    assert_ne!(intern_c_memory_ref(&entry), intern_c_memory_ref(&raw));
    assert!(
        entry
            .clone()
            .with_interface_memory_havoc(Variable(984_005), &BTreeSet::new(), &[&entry, &raw])
            .is_err()
    );
    let conflict = raw.with_object_input_domain(at.clone(), &child).unwrap();
    assert!(
        entry
            .clone()
            .with_interface_memory_havoc(Variable(984_006), &BTreeSet::new(), &[&entry, &conflict])
            .is_err()
    );
    assert!(entry.with_object_input_domain(at, &child).is_err());
}

#[test]
fn object_input_substitution_preserves_exact_domains_and_refuses_collisions() {
    let _session = crate::kernel::VerificationSession::enter();
    let (_, child) = selection_layouts();
    let variable = Variable(984_011);
    let at = Pointer::symbolic(variable);
    let target = CMemory::frame_local_pointer(29, "target");
    let memory = CMemory::new()
        .with_object_input_domain(at.clone(), &child)
        .unwrap();
    let state = CState::new().with_memory(memory.clone());
    let proposition = Proposition::CStatementVerifies {
        state: Box::new(state.clone()),
        statement: Box::new(c_skip()),
        outcome: CStatementOutcome::Normal(Box::new(state)),
    };
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &proposition,
        variable,
        &target,
    );
    let Proposition::CStatementVerifies { state, .. } = mapped else {
        panic!("mapped state");
    };
    assert!(state.memory.has_object_layout_at(&target, &child, true));
    assert!(!state.memory.has_object_layout_at(&at, &child, true));
    let mut variables = BTreeSet::new();
    collect_c_state_bitvector_variables(&CState::new().with_memory(memory.clone()), &mut variables);
    assert!(variables.contains(&variable));
    let conflicting =
        CAggregateLayout::new(8, 4, vec![CAggregateField::new("other", 0, CType::Int32)]);
    let memory = memory
        .with_object_input_domain(target.clone(), &conflicting)
        .unwrap();
    let domains = memory.map_object_input_domains(|pointer| {
        if pointer == &at {
            target.clone()
        } else {
            pointer.clone()
        }
    });
    assert!(!domains.contains_key(&target));
    let equal = CMemory::new()
        .with_object_input_domain(at.clone(), &child)
        .unwrap()
        .with_object_input_domain(target.clone(), &child)
        .unwrap();
    assert_eq!(
        equal
            .map_object_input_domains(|pointer| if pointer == &at {
                target.clone()
            } else {
                pointer.clone()
            })
            .len(),
        1
    );
}

#[test]
fn child_selection_work_ignores_siblings_and_unrelated_object_inputs() {
    let (_, child) = selection_layouts();
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = CAggregateLayout::new(
            count * 8,
            4,
            (0..count)
                .map(|index| {
                    CAggregateField::new(format!("child{index}.value"), index * 8, CType::Int32)
                })
                .collect(),
        )
        .with_records(
            (0..count)
                .map(|index| CAggregateRecord::new(format!("child{index}"), index * 8, 8, 4, None))
                .collect(),
        );
        let at = Pointer::symbolic(Variable(984_021));
        let mut input = CMemory::new()
            .with_object_input_domain(at.clone(), &parent)
            .unwrap();
        for index in 0..count {
            input = input
                .with_object_input_domain(
                    Pointer::symbolic(Variable(985_000 + u64::from(index))),
                    &child,
                )
                .unwrap();
        }
        let declared = CMemory::new().with_declared_aggregate_block(at.block.clone(), &parent);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for memory in [&input, &declared] {
                for offset in [0, (count - 1) * 8] {
                    assert!(memory.has_object_layout_at(&at.offset_by_bytes(offset), &child, true));
                }
            }
        });
        samples.push(work);
        let rebuilt = parent.clone().with_records(vec![]);
        assert!(!rebuilt.selects_layout_at(0, &child));
        assert!(
            parent.selects_layout_at(0, &child),
            "clone keeps immutable index"
        );
        let independent = CAggregateLayout::new(count * 8, 4, parent.fields().to_vec())
            .with_records(parent.records().to_vec());
        assert_eq!(independent, parent);
        use std::hash::{Hash, Hasher};
        let hash = |layout: &CAggregateLayout| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            layout.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(hash(&independent), hash(&parent));
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 8),
        "{samples:?}"
    );
}

#[test]
fn aggregate_declaration_survives_value_changes_without_initializing_padding() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = node_layout().with_records(vec![CAggregateRecord::new("tail", 8, 8, 4, None)]);
    let initial = CState::new().with_population_creation_tracking();
    let paths = execute_c_statement_paths(
        &initial,
        &c_declare_aggregate("node", layout.clone()),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("complete aggregate declaration");
    let [path] = paths.as_slice() else {
        panic!("one declaration outcome");
    };
    let CStatementOutcome::Normal(declared) = &path.outcome else {
        panic!("aggregate declaration failed: {:?}", path.outcome);
    };
    let at = declared.locals.slot("node").unwrap().clone();
    assert_declared_aggregate(&declared.memory, &at, &layout);
    assert_eq!(declared.resources, initial.resources);
    assert!(declared.memory.known_value(&at).is_none());
    assert!(!declared.memory.has_initialized_bytes_at(&at, 16));
    assert!(!declared.memory.requires_explicit_scalar_ownership(&at));

    let written = declared
        .memory
        .clone()
        .store(
            at.clone(),
            CValue::typed_pointer(at.clone(), CType::Int32Pointer),
        )
        .store(at.offset_by_bytes(8), CValue::Int32(37u32.into()));
    let range = CMemoryRange::new_with_element_width(at.clone(), 0u32.into(), 12u32.into(), 1);
    let call_havoc = written.clone().with_call_memory_havoc(
        Variable(874_001),
        std::slice::from_ref(&range),
        &PureFactContext::new(),
        None,
    );
    assert!(call_havoc.matches_call_memory_havoc_result(
        &written,
        std::slice::from_ref(&range),
        &PureFactContext::new(),
        None,
    ));
    let loop_havoc = written.clone().with_loop_memory_havoc_preserving_loans(
        Variable(874_002),
        &BTreeSet::new(),
        Some(std::slice::from_ref(&range)),
        None,
    );
    let joined = call_havoc
        .clone()
        .with_interface_memory_havoc(
            Variable(874_003),
            &BTreeSet::new(),
            &[&call_havoc, &loop_havoc],
        )
        .expect("same declared object across branches");
    for memory in [&written, &call_havoc, &loop_havoc, &joined] {
        assert_declared_aggregate(memory, &at, &layout);
        assert!(memory.has_initialized_bytes_under(&at, 8, &PureFactContext::new()));
        assert!(memory.has_initialized_bytes_under(
            &at.offset_by_bytes(8),
            4,
            &PureFactContext::new(),
        ));
        assert!(!memory.has_initialized_bytes_under(
            &at.offset_by_bytes(12),
            4,
            &PureFactContext::new(),
        ));
    }
    assert!(joined.known_value(&at).is_none());

    let flat = declared
        .memory
        .clone()
        .with_declared_aggregate_block(at.block.clone(), &node_layout());
    assert!(
        declared
            .memory
            .clone()
            .with_interface_memory_havoc(
                Variable(874_006),
                &BTreeSet::new(),
                &[&declared.memory, &flat]
            )
            .is_err(),
        "flattened-equivalent declarations retain incompatible boundaries"
    );

    let incompatible = CAggregateLayout::new(
        16,
        8,
        vec![
            CAggregateField::new("self", 0, CType::Int32Pointer),
            CAggregateField::new("value", 8, CType::UInt32),
        ],
    );
    let other = declared
        .memory
        .clone()
        .with_declared_aggregate_block(at.block.clone(), &incompatible);
    assert_ne!(
        declared.memory, other,
        "same size does not erase the declaration"
    );
    assert!(
        declared
            .memory
            .clone()
            .with_interface_memory_havoc(
                Variable(874_004),
                &BTreeSet::new(),
                &[&declared.memory, &other],
            )
            .is_err()
    );
    let raw = CMemory::new().with_uninitialized_block(at.block.clone(), 16);
    assert!(
        declared
            .memory
            .clone()
            .with_interface_memory_havoc(
                Variable(874_005),
                &BTreeSet::new(),
                &[&declared.memory, &raw],
            )
            .is_err()
    );
    let selected = CState::new()
        .with_memory(raw.with_uninitialized_object(at.clone(), 16))
        .with_aggregate_return_destination(at.clone(), layout);
    assert!(
        selected
            .memory
            .blocks
            .get(&at.block)
            .unwrap()
            .declared_object
            .is_none()
    );
}

#[test]
fn aggregate_copy_allocations_retain_their_complete_declarations() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = node_layout();
    let caller = allocate_destination(&CState::new().with_population_creation_tracking(), "node");
    let at = caller.locals.slot("node").unwrap().clone();
    assert_declared_aggregate(&caller.memory, &at, &layout);
    let memory = caller
        .memory
        .clone()
        .store(
            at.clone(),
            CValue::typed_pointer(at.clone(), CType::Int32Pointer),
        )
        .store(at.offset_by_bytes(8), CValue::Int32(37u32.into()));
    let caller = caller.with_memory(memory);
    let function = c_function(
        CType::Void,
        "consume_copy",
        vec![c_parameter_with_aggregate_layout(
            "copy",
            CType::VoidPointer,
            layout.clone(),
        )],
        c_return(c_void_value()),
    );
    let value = CValue::typed_pointer(at.clone(), CType::VoidPointer);
    let body_entry = bind_c_function_arguments(&caller, &function, std::slice::from_ref(&value))
        .expect("checked body argument allocation");
    let summary_entry = bind_c_contract_arguments(
        &caller,
        function.contract_interface(),
        std::slice::from_ref(&value),
        None,
    )
    .expect("checked summary argument allocation");
    for entry in [&body_entry, &summary_entry] {
        let copy = entry.locals.aggregate_object_pointer("copy").unwrap();
        assert_declared_aggregate(&entry.memory, copy, &layout);
        assert!(
            !entry
                .memory
                .has_initialized_bytes_at(&copy.offset_by_bytes(12), 4)
        );
    }
    let mut result_state = caller.clone();
    let result = complete_aggregate_return(
        &mut result_state,
        &copy_function(),
        value,
        &PureFactContext::new(),
    )
    .expect("checked return allocation");
    assert_declared_aggregate(&result_state.memory, &pointer(&result), &layout);
    assert!(
        !result_state
            .memory
            .has_initialized_bytes_at(&pointer(&result).offset_by_bytes(12), 4)
    );
    let summary_result =
        symbolic_contract_result(copy_function().contract_interface(), Variable(874_006));
    set_function_result(&mut result_state, &copy_function(), summary_result.clone());
    assert_declared_aggregate(&result_state.memory, &pointer(&summary_result), &layout);

    let synthetic = CValue::typed_pointer(Pointer::symbolic(Variable(874_007)), CType::VoidPointer);
    set_function_result(&mut result_state, &copy_function(), synthetic.clone());
    assert!(
        result_state
            .memory
            .blocks
            .get(&pointer(&synthetic).block)
            .unwrap()
            .declared_object
            .is_none()
    );
}

#[test]
fn aggregate_declarations_do_not_expand_unrelated_snapshot_hashing() {
    let mut costs = Vec::new();
    for count in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let at = CMemory::frame_local_pointer(23, "selected");
        let mut memory =
            CMemory::new().with_declared_aggregate_block(at.block.clone(), &node_layout());
        let unrelated_layout = CAggregateLayout::new(
            256,
            4,
            (0..64)
                .map(|index| CAggregateField::new(format!("field{index}"), index * 4, CType::Int32))
                .collect(),
        )
        .with_records(
            (0..64)
                .map(|index| CAggregateRecord::new(format!("record{index}"), index * 4, 4, 4, None))
                .collect(),
        );
        for index in 0..count {
            memory = memory.with_declared_aggregate_block(
                CMemory::frame_local_pointer(23, &format!("unrelated{index}")).block,
                &unrelated_layout,
            );
        }
        let (after, cost) = crate::instrumentation::measure_deterministic_work(|| {
            let written = memory
                .clone()
                .store(at.offset_by_bytes(8), CValue::Int32(37u32.into()));
            crate::kernel::intern_c_memory(written.clone());
            written
        });
        assert!(
            Arc::ptr_eq(&memory.blocks, &after.blocks),
            "a store does not rehash declarations"
        );
        assert_declared_aggregate(&after, &at, &node_layout());
        costs.push(cost);
    }
    assert!(
        costs.iter().all(|cost| *cost <= costs[0].max(1) * 2),
        "{costs:?}"
    );
}

// Unlike legacy constructor declarations, allocation grants write authority
// without manufacturing readable placeholders. The second allocation must
// not reuse the first object's identity when the source name is repeated.
#[test]
fn raw_construction_allocation_owns_storage_without_initializing_values() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = allocate_destination(&CState::new().with_population_creation_tracking(), "node");
    let destination = state.locals.slot("node").unwrap().clone();
    assert!(state.memory.has_block(&destination.block));
    assert!(!state.memory.has_initialized_bytes_at(&destination, 16));
    assert!(state.memory.known_value(&destination).is_none());
    assert!(
        crate::kernel::eval::memory_write_permission_outcome(
            &state,
            &destination,
            16,
            &PureFactContext::new(),
        )
        .is_none()
    );
    assert!(aggregate_copy_reads_uninitialized(
        &state.memory,
        &destination,
        &node_layout()
    ));
    let again = allocate_destination(&state, "node");
    assert_ne!(again.locals.slot("node").unwrap(), &destination);
    assert!(!again.memory.has_block(&destination.block));
    assert!(again.memory.is_ended_local_block(&destination.block));
}

fn destination_procedure(name: &str, body: CStatement) -> CFunction {
    let storage = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("destination"),
        c_int32_literal(0),
        c_int32_literal(4),
    ));
    c_function(
        CType::Void,
        name,
        vec![
            c_parameter("destination", CType::Int32Pointer),
            c_parameter("input", CType::Int32),
        ],
        c_seq(body, c_return(c_void_value())),
    )
    .with_resource_summary(vec![storage.clone()], vec![storage])
}

fn construction_function(name: &str, body: CStatement) -> CFunction {
    let storage = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable(C_CONTRACT_RESULT_NAME),
        c_int32_literal(0),
        c_int32_literal(4),
    ));
    c_function(
        CType::VoidPointer,
        name,
        vec![c_parameter("input", CType::Int32)],
        body,
    )
    .with_construction_return(node_layout())
    .with_resource_summary(vec![storage.clone()], vec![storage])
}

fn node_construction_body() -> CStatement {
    let destination = c_variable(C_CONTRACT_RESULT_NAME);
    let field = checked_field(destination.clone(), &node_layout(), "value", CType::Int32);
    c_seq(
        c_typed_store(
            checked_field(
                destination.clone(),
                &node_layout(),
                "self",
                CType::Int32Pointer,
            ),
            field.clone(),
            CType::Int32Pointer,
        ),
        c_seq(
            c_typed_store(field, c_variable("input"), CType::Int32),
            c_return(destination),
        ),
    )
}

#[test]
fn construction_return_preserves_exact_destination_through_two_factories() {
    let _session = crate::kernel::VerificationSession::enter();
    let inner = construction_function("construct_node", node_construction_body());
    let forward = |name: &str, callee: &str| {
        construction_function(
            name,
            c_seq(
                c_call_assign(C_CONTRACT_RESULT_NAME, callee, vec![c_variable("input")]),
                c_return(c_variable(C_CONTRACT_RESULT_NAME)),
            ),
        )
    };
    let middle = forward("forward_node_result", "construct_node");
    let outer = forward("outer_node_result", "forward_node_result");
    let caller = allocate_destination(&CState::new().with_population_creation_tracking(), "node");
    let destination = caller.locals.slot("node").unwrap().clone();
    let caller = caller.with_aggregate_return_destination(destination.clone(), node_layout());
    let paths = execute_c_function_call_paths(
        &caller,
        &outer,
        &[c_int32_literal(37)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new()
            .with_function(inner)
            .with_function(middle),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("one constructed result");
    };
    let CFunctionOutcome::Return { value, state } = &path.outcome else {
        panic!("construction failed: {:?}", path.outcome);
    };
    assert!(path.obligations.is_empty(), "{:?}", path.obligations);
    assert_eq!(pointer(value), destination);
    let object = state
        .memory
        .declared_aggregate_pointer(&destination, &node_layout())
        .unwrap();
    let field = state
        .memory
        .checked_member_pointer(
            &object,
            &CAggregateMemberSelection {
                layout: Arc::new(node_layout()),
                path: vec!["value".into()].into(),
                value_type: CType::Int32,
            },
        )
        .unwrap();
    assert_eq!(field.pointer(), &destination.offset_by_bytes(8));
    assert_eq!(
        state.memory.known_value(&destination),
        Some(CValue::Pointer(field))
    );
    assert_eq!(
        state.memory.known_value(&destination.offset_by_bytes(8)),
        Some(CValue::Int32(37u32.into()))
    );
    assert_eq!(state.next_local_frame, caller.next_local_frame);
    assert!(state.memory.has_block(&destination.block));
}

// A result address alone grants no storage, layout match, or ownership, and
// returning it is not enough to establish that the object was initialized.
#[test]
fn construction_return_rejects_missing_binding_authority_and_partial_values() {
    let _session = crate::kernel::VerificationSession::enter();
    let raw = allocate_destination(&CState::new().with_population_creation_tracking(), "node");
    let destination = raw.locals.slot("node").unwrap().clone();
    let selected = raw
        .clone()
        .with_aggregate_return_destination(destination.clone(), node_layout());
    let function = construction_function("construct_node", node_construction_body());
    for caller in [
        raw,
        selected
            .clone()
            .with_resource_context(ResourceContext::new()),
        selected.clone().with_aggregate_return_destination(
            destination.clone(),
            CAggregateLayout::new(8, 8, vec![]),
        ),
        selected.clone().with_memory(CMemory::new()),
    ] {
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[c_int32_literal(37)],
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, CFunctionOutcome::RuntimeError(_)))
        );
    }
    let partial = construction_function(
        "partial_node",
        c_seq(
            c_typed_store(
                checked_field(
                    c_variable(C_CONTRACT_RESULT_NAME),
                    &node_layout(),
                    "self",
                    CType::Int32Pointer,
                ),
                checked_field(
                    c_variable(C_CONTRACT_RESULT_NAME),
                    &node_layout(),
                    "value",
                    CType::Int32,
                ),
                CType::Int32Pointer,
            ),
            c_return(c_variable(C_CONTRACT_RESULT_NAME)),
        ),
    );
    let paths = execute_c_function_call_paths(
        &selected,
        &partial,
        &[c_int32_literal(37)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(paths.iter().all(|path| matches!(
        path.outcome,
        CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
    )));
}

#[test]
fn construction_destination_can_alias_an_argument_without_becoming_fresh() {
    let _session = crate::kernel::VerificationSession::enter();
    let result = c_variable(C_CONTRACT_RESULT_NAME);
    let field = checked_field(result.clone(), &node_layout(), "value", CType::Int32);
    let storage = CResourceSpec::owned_memory(CMemorySegment::new(
        result.clone(),
        c_int32_literal(0),
        c_int32_literal(4),
    ));
    for read_before_write in [false, true] {
        let write = if read_before_write {
            c_typed_store(
                field.clone(),
                c_typed_load(c_variable("alias"), CType::Int32),
                CType::Int32,
            )
        } else {
            c_typed_store(c_variable("alias"), c_int32_literal(7), CType::Int32)
        };
        let function = c_function(
            CType::VoidPointer,
            "alias_node",
            vec![c_parameter("alias", CType::Int32Pointer)],
            c_seq(
                write,
                c_seq(
                    c_typed_store(
                        checked_field(result.clone(), &node_layout(), "self", CType::Int32Pointer),
                        field.clone(),
                        CType::Int32Pointer,
                    ),
                    c_return(result.clone()),
                ),
            ),
        )
        .with_construction_return(node_layout())
        .with_resource_summary(vec![storage.clone()], vec![storage.clone()]);
        let raw = allocate_destination(&CState::new().with_population_creation_tracking(), "node");
        let at = raw.locals.slot("node").unwrap().clone();
        let selected = raw.with_aggregate_return_destination(at.clone(), node_layout());
        let paths = execute_c_function_call_paths(
            &selected,
            &function,
            &[c_pointer_value(at.offset_by_bytes(8))],
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one alias case");
        };
        if read_before_write {
            assert!(matches!(
                path.outcome,
                CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
            ));
        } else {
            let CFunctionOutcome::Return { value, state } = &path.outcome else {
                panic!("alias store construction failed: {:?}", path.outcome);
            };
            assert_eq!(pointer(value), at);
            assert_eq!(
                state.memory.known_value(&at.offset_by_bytes(8)),
                Some(int32(7))
            );
        }
    }
}

#[test]
fn construction_destination_binding_work_ignores_unrelated_caller_objects() {
    let mut work_by_size = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut caller =
            allocate_destination(&CState::new().with_population_creation_tracking(), "node");
        let at = caller.locals.slot("node").unwrap().clone();
        caller = caller.with_aggregate_return_destination(at, node_layout());
        for index in 0..count {
            let unrelated = CMemory::frame_local_pointer(10, &format!("unrelated{index}"));
            caller.memory = caller.memory.with_block(unrelated.block.clone(), 4);
            caller.resources = caller
                .resources
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    unrelated,
                    0u32.into(),
                    1u32.into(),
                )));
        }
        let function = construction_function("node", node_construction_body());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            construction_return::bind(
                &caller,
                function.contract_interface(),
                &mut CState::new().with_population_creation_tracking(),
            )
            .unwrap();
        });
        work_by_size.push(work);
    }
    assert!(
        work_by_size
            .iter()
            .all(|work| *work <= work_by_size[0].max(1) * 2),
        "{work_by_size:?}"
    );
}

// Full-expression materialization copies pointer values before the temporary
// expires. Only a pointer into separate caller storage remains dereferenceable.
#[test]
fn construction_temporary_retirement_preserves_copies_and_external_backing() {
    for points_to_self in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let result = c_variable(C_CONTRACT_RESULT_NAME);
        let field = checked_field(result.clone(), &node_layout(), "value", CType::Int32);
        let owner = CResourceSpec::owned_memory(CMemorySegment::new(
            result.clone(),
            c_int32_literal(0),
            c_int32_literal(4),
        ));
        let factory = c_function(
            CType::VoidPointer,
            "materialize_descriptor",
            vec![c_parameter("backing", CType::Int32Pointer)],
            c_seq(
                c_typed_store(
                    checked_field(result.clone(), &node_layout(), "self", CType::Int32Pointer),
                    if points_to_self {
                        field.clone()
                    } else {
                        c_variable("backing")
                    },
                    CType::Int32Pointer,
                ),
                c_seq(
                    c_typed_store(field, c_int32_literal(37), CType::Int32),
                    c_return(result),
                ),
            ),
        )
        .with_construction_return(node_layout())
        .with_resource_summary(vec![owner.clone()], vec![owner]);
        let environment = CExecutionEnvironment::new().with_function(factory);
        let sequence = |statements: Vec<CStatement>| statements.into_iter().reduce(c_seq).unwrap();
        let prefix = sequence(vec![
            c_declare("backing", CType::Int32),
            c_assign("backing", c_int32_literal(23)),
            c_allocate_aggregate_destination("node", node_layout()),
            c_allocate_aggregate_destination("temporary", node_layout()),
            c_call_assign(
                "temporary",
                "materialize_descriptor",
                vec![c_addr_of("backing")],
            ),
            c_copy_aggregate(c_variable("node"), c_variable("temporary"), node_layout()),
        ]);
        let paths = execute_c_statement_paths(
            &CState::new().with_population_creation_tracking(),
            &prefix,
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one materialization path");
        };
        let CStatementOutcome::Normal(state) = &path.outcome else {
            panic!("materialization must finish");
        };
        let temporary = state
            .locals
            .aggregate_object_pointer("temporary")
            .unwrap()
            .clone();
        let node = state
            .locals
            .aggregate_object_pointer("node")
            .unwrap()
            .clone();
        let backing = state.locals.slot("backing").unwrap().clone();
        let copied = state.memory.known_value(&node).unwrap();
        let referent = if points_to_self {
            temporary.offset_by_bytes(8)
        } else {
            backing.clone()
        };
        assert_eq!(pointer(&copied), referent);
        let retirement = c_end_automatic_lifetimes(vec!["temporary".into()]);
        let checked = prove_symbolic_c_execution_paths_with_environment(
            state.as_ref().clone(),
            retirement,
            PureFactContext::new(),
            environment.clone(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
        let [path] = checked.paths() else {
            panic!("one retirement path");
        };
        let after = match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
            Proposition::CStatementExecutes {
                outcome: CStatementOutcome::Normal(after),
                ..
            }
            | Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Normal(after),
                ..
            } => after,
            _ => panic!("checked temporary retirement"),
        };
        assert!(after.locals.aggregate_object_pointer("temporary").is_none());
        assert!(after.memory.is_ended_local_block(&temporary.block));
        assert!(!after.memory.has_block(&temporary.block));
        assert!(after.memory.has_block(&node.block));
        assert!(after.memory.has_block(&backing.block));
        assert_eq!(after.memory.known_value(&node), Some(copied));
        assert_eq!(after.memory.known_value(&backing), Some(int32(23)));
        assert!(
            after
                .resources
                .memory_write_range(&node, 16, &PureFactContext::new())
                .is_some()
        );
        assert!(
            after
                .resources
                .memory_write_range(&temporary, 16, &PureFactContext::new())
                .is_none()
        );
        let read = execute_c_statement_paths(
            after,
            &c_return(c_typed_load(c_pointer_value(referent), CType::Int32)),
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(read.len(), 1);
        if points_to_self {
            assert!(matches!(
                read[0].outcome,
                CStatementOutcome::UndefinedBehavior(_)
            ));
        } else {
            assert!(
                matches!(&read[0].outcome, CStatementOutcome::Return { value, .. } if *value == int32(23))
            );
        }
    }
}

#[test]
fn construction_completion_work_scales_with_value_fields() {
    for parameter in [false, true] {
        let mut samples = Vec::new();
        for count in [8, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            // Leave padding between fields so initialization retains separate
            // runs instead of measuring only one contiguous initialized range.
            let layout = CAggregateLayout::new(
                count * 8,
                8,
                (0..count)
                    .map(|index| {
                        CAggregateField::new(format!("field{index}"), index * 8, CType::Int32)
                    })
                    .collect(),
            );
            let at = Pointer::symbolic(Variable(873_004));
            register_block_alignment(&at.block, 8);
            // Native constructor contracts hold separate field owners; include
            // their growing index, rather than only one whole-object owner.
            let resources = if parameter {
                (0..count).fold(ResourceContext::new(), |resources, index| {
                    resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                        at.offset_by_bytes(index * 8),
                        0u32.into(),
                        1u32.into(),
                    )))
                })
            } else {
                ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                    CMemoryRange::new(at.clone(), 0u32.into(), (count * 2).into()),
                ))
            };
            let caller = CState::new()
                .with_population_creation_tracking()
                .with_memory(
                    CMemory::new()
                        .with_uninitialized_block(at.block.clone(), count * 8)
                        .with_object_input_domain(at.clone(), &layout)
                        .unwrap(),
                )
                .with_resource_context(resources)
                .with_aggregate_return_destination(at.clone(), layout.clone());
            let function = if parameter {
                c_function(
                    CType::Void,
                    "wide_constructor",
                    vec![c_parameter("destination", CType::Int32Pointer)],
                    c_skip(),
                )
                .with_construction_parameter(0, layout)
            } else {
                c_function(CType::VoidPointer, "wide_result", vec![], c_skip())
                    .with_construction_return(layout)
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut state = caller.clone().with_local(
                    "destination",
                    CValue::typed_pointer(at.clone(), CType::Int32Pointer),
                );
                construction_return::bind(&caller, function.contract_interface(), &mut state)
                    .unwrap();
                construction_return::initialize_summary(&mut state, &caller);
                if parameter {
                    assert!(
                        construction_return::complete_parameter(
                            &state,
                            function.contract_interface()
                        )
                        .is_none()
                    );
                } else {
                    construction_return::complete(
                        &state,
                        function.contract_interface(),
                        CValue::typed_pointer(at.clone(), CType::VoidPointer),
                    )
                    .unwrap();
                }
            });
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 6),
            "{samples:?}"
        );
    }
}

#[test]
fn construction_destination_survives_substitution_and_requires_agreement_at_join() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(873_003);
    let state = CState::new()
        .with_population_creation_tracking()
        .with_aggregate_return_destination(Pointer::symbolic(variable), node_layout());
    let mut variables = BTreeSet::new();
    collect_c_state_bitvector_variables(&state, &mut variables);
    assert!(variables.contains(&variable));
    let proposition = Proposition::CStatementVerifies {
        state: Box::new(state.clone()),
        statement: Box::new(c_skip()),
        outcome: CStatementOutcome::Normal(Box::new(state.clone())),
    };
    let at = CMemory::frame_local_pointer(15, "caller");
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &proposition,
        variable,
        &at,
    );
    let Proposition::CStatementVerifies {
        state: mapped,
        outcome: CStatementOutcome::Normal(after),
        ..
    } = mapped
    else {
        panic!("substituted construction transition");
    };
    assert_eq!(mapped.aggregate_destination.as_ref().unwrap().pointer, at);
    assert_eq!(mapped.aggregate_destination, after.aggregate_destination);
    assert!(!state.shares_non_memory_storage_with(&mapped));
    assert!(
        abstract_c_state_for_interface_join_across(&state, &[&state, &mapped], &BTreeMap::new(), 0)
            .is_err()
    );
}

// This tests the existing explicit-destination procedure building block,
// without the legacy placeholder-seeding declaration. It does not pass a
// supplied destination off as a by-value aggregate result.
#[test]
fn supplied_constructor_destination_survives_two_procedure_boundaries() {
    let _session = crate::kernel::VerificationSession::enter();
    let field = c_pointer_offset_bytes(c_variable("destination"), 8);
    let constructor = destination_procedure(
        "initialize_node",
        c_seq(
            c_typed_store(
                c_variable("destination"),
                field.clone(),
                CType::Int32Pointer,
            ),
            c_typed_store(field, c_variable("input"), CType::Int32),
        ),
    );
    let forward = destination_procedure(
        "forward_node",
        c_call(
            "initialize_node",
            vec![c_variable("destination"), c_variable("input")],
        ),
    );
    let outer = destination_procedure(
        "outer_node",
        c_call(
            "forward_node",
            vec![c_variable("destination"), c_variable("input")],
        ),
    );
    let caller = allocate_destination(
        &CState::new().with_population_creation_tracking(),
        "caller_node",
    );
    let destination = caller.locals.slot("caller_node").unwrap().clone();
    assert!(!caller.memory.has_initialized_bytes_at(&destination, 16));
    let paths = execute_c_function_call_paths(
        &caller,
        &outer,
        &[c_pointer_value(destination.clone()), c_int32_literal(37)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new()
            .with_function(constructor)
            .with_function(forward),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("forwarded constructor execution");
    let [path] = paths.as_slice() else {
        panic!("one constructor path expected");
    };
    let CFunctionOutcome::Return { value, state } = &path.outcome else {
        panic!("constructor failed: {:?}", path.outcome);
    };
    assert_eq!(*value, CValue::Void);
    assert!(path.obligations.is_empty(), "{:?}", path.obligations);
    assert_eq!(
        state.memory.known_value(&destination),
        Some(CValue::typed_pointer(
            destination.offset_by_bytes(8),
            CType::Int32Pointer,
        )),
    );
    assert_eq!(
        state.memory.known_value(&destination.offset_by_bytes(8)),
        Some(CValue::Int32(Bitvector32Term::Constant(37))),
    );
    assert_eq!(state.next_local_frame, caller.next_local_frame);
    assert!(state.memory.has_block(&destination.block));
}

// C++ copy-assignment coverage does not exercise the function return
// materializer. A future destination-return path must not silently change
// this existing copy mode to rebase self-pointers or elide its copies.
#[test]
fn aggregate_copy_return_preserves_self_pointer_through_two_materializations() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CMemory::frame_local_pointer(100, "node");
    let self_pointer = CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer);
    let memory = CMemory::new()
        .with_block(source.block.clone(), 16)
        .store(source.clone(), self_pointer.clone())
        .store(
            source.offset_by_bytes(8),
            CValue::Int32(Bitvector32Term::Constant(37)),
        );
    let mut state = CState::new()
        .with_population_creation_tracking()
        .with_memory(memory);
    let function = copy_function();
    let first = complete_aggregate_return(
        &mut state,
        &function,
        CValue::typed_pointer(source.clone(), CType::VoidPointer),
        &PureFactContext::new(),
    )
    .expect("first copy result");
    let second = complete_aggregate_return(
        &mut state,
        &function,
        first.clone(),
        &PureFactContext::new(),
    )
    .expect("second copy result");
    assert_ne!(pointer(&first).block, source.block);
    assert_ne!(pointer(&second).block, pointer(&first).block);
    for result in [&first, &second] {
        let result = pointer(result);
        assert_eq!(
            state.memory.known_value(&result),
            Some(self_pointer.clone())
        );
        assert_ne!(pointer(&self_pointer), result.offset_by_bytes(8));
        assert_eq!(
            state.memory.known_value(&result.offset_by_bytes(8)),
            Some(CValue::Int32(Bitvector32Term::Constant(37))),
        );
    }
}

// Retiring a copied descriptor's callee-local source must distinguish a
// self-pointer from an external backing pointer. Keeping the result alive
// must neither rescue the former allocation nor retire the latter.
#[test]
fn aggregate_copy_return_retirement_preserves_only_independently_live_backing() {
    for points_to_self in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::frame_local_pointer(100, "descriptor");
        let backing = CMemory::frame_local_pointer(101, "caller_backing");
        let caller = CMemory::new().with_block(backing.block.clone(), 4).store(
            backing.clone(),
            CValue::Int32(Bitvector32Term::Constant(23)),
        );
        let referent = if points_to_self {
            source.offset_by_bytes(8)
        } else {
            backing.clone()
        };
        let field = CValue::typed_pointer(referent.clone(), CType::Int32Pointer);
        let memory = caller
            .clone()
            .with_block(source.block.clone(), 16)
            .store(source.clone(), field.clone())
            .store(
                source.offset_by_bytes(8),
                CValue::Int32(Bitvector32Term::Constant(23)),
            );
        let mut state = CState::new()
            .with_population_creation_tracking()
            .with_memory(memory);
        state.locals.set_aggregate_object_at(
            "descriptor".to_string(),
            node_layout(),
            source.clone(),
        );
        let function = copy_function();
        let result = complete_aggregate_return(
            &mut state,
            &function,
            CValue::typed_pointer(source.clone(), CType::VoidPointer),
            &PureFactContext::new(),
        )
        .expect("copy result");
        set_function_result(&mut state, &function, result.clone());
        let memory =
            end_function_body_automatic_lifetimes(&state, &function, &caller, Some(&result))
                .expect("callee retirement");
        assert!(!memory.has_block(&source.block));
        assert!(memory.has_block(&pointer(&result).block));
        assert!(memory.has_block(&backing.block));
        assert_eq!(memory.known_value(&pointer(&result)), Some(field));
        assert_eq!(memory.has_block(&referent.block), !points_to_self);
        assert_eq!(
            memory.known_value(&backing),
            Some(CValue::Int32(Bitvector32Term::Constant(23))),
        );
    }
}

// Modular field-copy results intentionally have fresh identities. The new
// construction mode needs a different binding; changing this helper globally
// would break existing C framing and would conceal destination aliasing.
#[test]
fn aggregate_copy_symbolic_result_has_a_fresh_identity_per_call() {
    let _session = crate::kernel::VerificationSession::enter();
    let function = copy_function();
    let first = symbolic_contract_result(function.contract_interface(), Variable(870_001));
    let second = symbolic_contract_result(function.contract_interface(), Variable(870_002));
    assert!(matches!(pointer(&first).block, PointerBlock::Temporary(_)));
    assert!(matches!(pointer(&second).block, PointerBlock::Temporary(_)));
    assert_ne!(pointer(&first).block, pointer(&second).block);
}

// A by-value result must not erase the caller's read history. Check the
// value judgment and its certificate, then refuse it across an actual write.
#[test]
fn aggregate_copy_result_preserves_unrelated_entry_byte_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = CMemory::local_pointer("input-byte");
    let before = CMemory::new().with_block(input.block.clone(), 1);
    let read = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(input.clone()),
            LoadKind::UInt8,
        )
    };
    let equality = |memory: &CMemory| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(read(memory)), Box::new(read(&before))),
            true,
        )
    };
    let function = copy_function();
    let mut state = CState::new().with_memory(before.clone());
    let result = symbolic_contract_result(function.contract_interface(), Variable(870_003));
    set_function_result(&mut state, &function, result);
    let context = PureFactContext::new();
    let proof = context
        .derive_simp_atomic_proposition(&equality(state.memory()))
        .expect("a returned record leaves the caller's byte unchanged");
    assert!(proof.check(&context));
    assert!(proof.context_premises().is_empty());

    let written = state
        .memory()
        .clone()
        .store(input.clone(), CValue::UInt8(Bitvector32Term::Constant(7)));
    assert!(
        context
            .derive_simp_atomic_proposition(&equality(&written))
            .is_none()
    );
}

// Return completion must reject before allocating a result or copying any
// prefix. The two body-completion paths must not supply separate, drifting
// checks for this precondition.
#[test]
fn aggregate_copy_return_refuses_partial_initialization_without_changing_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CMemory::frame_local_pointer(100, "partial");
    let mut state = CState::new()
        .with_population_creation_tracking()
        .with_memory(CMemory::new().with_block(source.block.clone(), 16).store(
            source.clone(),
            CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer),
        ));
    let before = state.clone();
    assert_eq!(
        complete_aggregate_return(
            &mut state,
            &copy_function(),
            CValue::typed_pointer(source, CType::VoidPointer),
            &PureFactContext::new(),
        ),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    assert_eq!(state, before);
}

// Symbolic proof-entry destinations must not inherit the existing convention
// that unspecified external argument memory is initialized. This is the
// completion check's negative oracle before adding the new result mode.
#[test]
fn symbolic_construction_storage_requires_written_fields_before_copy_return() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_003));
    let mut state = CState::new()
        .with_population_creation_tracking()
        .with_memory(CMemory::new().with_uninitialized_block(source.block.clone(), 16));
    let value = CValue::typed_pointer(source.clone(), CType::VoidPointer);
    assert_eq!(
        complete_aggregate_return(
            &mut state,
            &copy_function(),
            value.clone(),
            &PureFactContext::new()
        ),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    state.set_memory(state.memory.clone().store(
        source.clone(),
        CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer),
    ));
    assert_eq!(
        complete_aggregate_return(
            &mut state,
            &copy_function(),
            value.clone(),
            &PureFactContext::new()
        ),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    state.set_memory(state.memory.clone().store(
        source.offset_by_bytes(8),
        CValue::Int32(Bitvector32Term::Constant(37)),
    ));
    assert!(
        complete_aggregate_return(&mut state, &copy_function(), value, &PureFactContext::new())
            .is_ok()
    );
}

#[test]
fn symbolic_construction_storage_is_unreadable_until_written() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_004));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    for (mode, assumptions) in [
        ("ordinary", PureFactContext::new()),
        (
            "preferred",
            PureFactContext::new().prefer_symbolic_external_loads(),
        ),
        (
            "forced",
            PureFactContext::new().force_symbolic_external_loads(),
        ),
    ] {
        for written in [false, true] {
            let memory = if written {
                raw.clone()
                    .store(source.clone(), CValue::Int32(Bitvector32Term::Constant(37)))
            } else {
                raw.clone()
            };
            let state = CState::new()
                .with_population_creation_tracking()
                .with_memory(memory)
                .with_resource_context(ResourceContext::new().unchecked_with_fact(
                    CResourceFact::own_memory(CMemoryRange::new(
                        source.clone(),
                        0u32.into(),
                        1u32.into(),
                    )),
                ));
            let paths = execute_c_statement_paths(
                &state,
                &c_return(c_typed_load(c_pointer_value(source.clone()), CType::Int32)),
                &assumptions,
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::default(),
            )
            .expect("raw destination read");
            let [path] = paths.as_slice() else {
                panic!("expected one read path");
            };
            if written {
                assert!(matches!(path.outcome, CStatementOutcome::Return { .. }));
            } else {
                assert!(
                    matches!(
                        path.outcome,
                        CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
                    ),
                    "{mode}: {:?}",
                    path.outcome
                );
            }
        }
    }
}

// A supplied destination may alias an ordinary input. That equality must
// neither make unwritten storage readable nor hide a write through the alias.
#[test]
fn symbolic_construction_storage_respects_known_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_005));
    let alias = Pointer::symbolic(Variable(870_006));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(source.clone(), alias.clone()),
        true,
    );
    for forgotten in [false, true] {
        for written in [false, true] {
            for read in [&source, &alias] {
                let mut memory = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
                if written {
                    memory = memory.store(alias.clone(), CValue::Int32(37u32.into()));
                }
                if forgotten {
                    memory = memory.with_loop_memory_havoc_preserving_loans(
                        Variable(870_020),
                        &BTreeSet::new(),
                        None,
                        None,
                    );
                }
                let state = CState::new()
                    .with_population_creation_tracking()
                    .with_memory(memory)
                    .with_resource_context(ResourceContext::new().unchecked_with_fact(
                        CResourceFact::own_memory(CMemoryRange::new(
                            source.clone(),
                            0u32.into(),
                            1u32.into(),
                        )),
                    ));
                let paths = execute_c_statement_paths(
                    &state,
                    &c_return(c_typed_load(c_pointer_value(read.clone()), CType::Int32)),
                    &assumptions,
                    &CExecutionEnvironment::new(),
                    CExecutionSemantics::EXECUTE_BODIES,
                    &mut ExecutionBudget::default(),
                )
                .expect("aliased destination read");
                assert!(!paths.is_empty());
                for path in paths {
                    if written {
                        assert!(
                            matches!(path.outcome, CStatementOutcome::Return { .. }),
                            "{:?}",
                            path.outcome
                        );
                    } else {
                        assert!(
                            matches!(
                                path.outcome,
                                CStatementOutcome::UndefinedBehavior(
                                    CUndefinedBehavior::UninitializedRead
                                )
                            ),
                            "{:?}",
                            path.outcome
                        );
                    }
                }
            }
        }
    }
}

// Resource projection is a logical name, not a constructor store, including
// when the resource uses another spelling that could alias the destination.
#[test]
fn naming_symbolic_construction_storage_does_not_initialize_it() {
    let source = Pointer::symbolic(Variable(870_007));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    for address in [source.clone(), Pointer::symbolic(Variable(870_008))] {
        let named = raw
            .clone()
            .materialize_named_cell(address.clone(), CValue::Int32(37u32.into()));
        assert_eq!(named, raw);
        assert!(!named.has_initialized_bytes_at(&address, 4));
    }
}

// Forgetting values preserves writes; a branch that skipped the write still
// prevents the joined destination from counting as completely initialized.
#[test]
fn symbolic_construction_initialization_survives_havoc_and_intersects_at_join() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_009));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 8);
    let partial = raw
        .clone()
        .store(source.clone(), CValue::Int32(37u32.into()));
    let full = partial
        .clone()
        .store(source.offset_by_bytes(4), CValue::Int32(42u32.into()));
    let forgotten = full.with_loop_memory_havoc_preserving_loans(
        Variable(870_010),
        &BTreeSet::new(),
        None,
        None,
    );
    assert!(forgotten.has_initialized_bytes_at(&source, 8));
    assert!(forgotten.may_read_uninitialized_object(&source, 8));
    assert!(forgotten.known_value(&source).is_none());
    let joined = forgotten
        .clone()
        .with_interface_memory_havoc(Variable(870_011), &BTreeSet::new(), &[&forgotten, &partial])
        .expect("construction initialization join");
    assert!(joined.has_initialized_bytes_at(&source, 4));
    assert!(!joined.has_initialized_bytes_at(&source, 8));
    assert!(joined.may_read_uninitialized_object(&source, 8));
}

// Substitution retains the byte footprint even at a nonzero offset. This
// metadata does not authorize resizing the caller object or subobject construction.
#[test]
fn symbolic_construction_initialization_substitution_preserves_extent() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(870_012);
    let source = Pointer::symbolic(variable);
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    let destination = CMemory::frame_local_pointer(20, "container").offset_by_bytes(8);
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_memory(
        &raw,
        variable,
        &destination,
    );
    assert!(mapped.may_read_uninitialized_object(&destination, 4));
    assert!(!mapped.may_read_uninitialized_object(&destination.offset_by_bytes(4), 4));
    assert!(!mapped.may_read_uninitialized_object(
        &CMemory::frame_local_pointer(20, "container").offset_by_bytes(4),
        4
    ));
    assert!(!mapped.has_initialized_bytes_at(&destination, 4));
}

// Query work is bounded by potentially aliasing tracked objects, not other
// caller allocations. Concrete unrelated raw objects are excluded by the index.
#[test]
fn construction_initialization_lookup_ignores_unrelated_caller_storage() {
    let mut work_by_size = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::frame_local_pointer(21, "construction");
        let mut memory = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
        for index in 0..count {
            memory = memory.with_uninitialized_block(format!("local:unrelated:{index}"), 4);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.may_read_uninitialized_object(&source, 4)
        });
        assert!(result);
        work_by_size.push(work);
    }
    assert!(
        work_by_size
            .iter()
            .all(|work| *work <= work_by_size[0].max(1) * 2),
        "{work_by_size:?}"
    );
}

// Instantiating an object can put a variable only in its byte offset. Both
// whole and incremental collectors must reserve it against fresh witnesses.
#[test]
fn construction_object_offsets_participate_in_fresh_variable_collection() {
    let _session = crate::kernel::VerificationSession::enter();
    let source_variable = Variable(870_013);
    let offset_variable = Variable(870_014);
    let source = Pointer::symbolic(source_variable);
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    let destination = Pointer {
        block: "local:variable-container".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(offset_variable), 4),
    };
    let mapped = crate::kernel::reasoning::substitute_pointer_variable_in_memory(
        &raw,
        source_variable,
        &destination,
    );
    let mut whole = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables_whole(&mapped, &mut whole);
    assert!(whole.contains(&offset_variable));
    assert!(!whole.contains(&source_variable));
    let before = crate::kernel::intern_c_memory(mapped.clone());
    let mut cached = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&before, &mut cached);
    assert_eq!(cached, whole);
    let after = crate::kernel::intern_c_memory(mapped.store(
        CMemory::frame_local_pointer(22, "unrelated"),
        CValue::Int32(37u32.into()),
    ));
    let mut updated = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&after, &mut updated);
    assert_eq!(updated, whole);
}

// Neither compact resource naming nor a claimed havoc edge may manufacture
// initialization or discard the marker that requires it.
#[test]
fn construction_initialization_cannot_be_erased_or_seeded_by_a_proof_shortcut() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_015));
    let raw = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
    assert!(
        raw.clone()
            .with_symbolic_storage_run(
                source.clone(),
                CType::Int32,
                1,
                crate::kernel::intern_c_memory(raw.clone())
            )
            .is_err()
    );
    let assumptions = PureFactContext::new();
    let mut havoc = raw
        .clone()
        .with_call_memory_havoc(Variable(870_016), &[], &assumptions, None);
    assert!(havoc.matches_call_memory_havoc_result(&raw, &[], &assumptions, None));
    Arc::make_mut(&mut havoc.heap).uninitialized_objects.clear();
    assert!(!havoc.matches_call_memory_havoc_result(&raw, &[], &assumptions, None));
}

// An actual write can use an alias whose variable survives only in the byte
// initialization record after havoc. Fresh witnesses must not reuse it.
#[test]
fn forgotten_construction_writes_keep_their_address_variables_reserved() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(870_017));
    let alias_variable = Variable(870_018);
    let alias = Pointer::symbolic(alias_variable);
    let written = CMemory::new()
        .with_uninitialized_block(source.block.clone(), 4)
        .store(alias.clone(), CValue::Int32(37u32.into()));
    let before = crate::kernel::intern_c_memory(written.clone());
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(&before, &mut variables);
    assert!(variables.contains(&alias_variable));
    let forgotten = written.with_loop_memory_havoc_preserving_loans(
        Variable(870_019),
        &BTreeSet::new(),
        None,
        None,
    );
    assert!(forgotten.known_value(&alias).is_none());
    let mut whole = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables_whole(&forgotten, &mut whole);
    let mut cached = BTreeSet::new();
    crate::kernel::reasoning::collect_shared_memory_bitvector_variables(
        &crate::kernel::intern_c_memory(forgotten),
        &mut cached,
    );
    assert!(cached.contains(&alias_variable));
    assert_eq!(whole, cached);
}

// A constructor keeps its native void signature. Completion checks the entry
// destination even when the ordinary pointer parameter has been reassigned.
#[test]
fn construction_parameter_completion_checks_original_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    for complete in [false, true] {
        let field = c_cast(
            c_pointer_offset_bytes(c_variable("destination"), 8),
            CType::Int32Pointer,
        );
        let body = c_seq(
            c_typed_store(
                c_variable("destination"),
                field.clone(),
                CType::Int32Pointer,
            ),
            if complete {
                c_typed_store(field, c_variable("input"), CType::Int32)
            } else {
                c_skip()
            },
        );
        let function = destination_procedure("initialize_node", body)
            .with_construction_parameter(0, node_layout());
        let caller =
            allocate_destination(&CState::new().with_population_creation_tracking(), "node");
        let at = caller.locals.slot("node").unwrap().clone();
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[c_pointer_value(at.clone()), c_int32_literal(37)],
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one constructor path");
        };
        if complete {
            let CFunctionOutcome::Return { state, .. } = &path.outcome else {
                panic!("constructor completion failed");
            };
            assert!(
                state.aggregate_destination.is_none(),
                "callee destination cannot replace caller metadata"
            );
            assert!(!aggregate_copy_reads_uninitialized(
                &state.memory,
                &at,
                &node_layout()
            ));
            assert!(
                !state.memory.has_initialized_bytes_at(&at, 16),
                "padding stays unwritten"
            );
        } else {
            assert!(matches!(
                path.outcome,
                CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(_))
            ));
        }
    }
    // Reassigning the parameter to an unrelated initialized object does not
    // complete the original destination.
    let function = c_function(
        CType::Void,
        "redirect_constructor",
        vec![
            c_parameter("destination", CType::Int32Pointer),
            c_parameter("other", CType::Int32Pointer),
        ],
        c_seq(
            c_assign("destination", c_variable("other")),
            c_return(c_void_value()),
        ),
    )
    .with_construction_parameter(0, node_layout());
    let caller = allocate_destination(
        &allocate_destination(&CState::new().with_population_creation_tracking(), "node"),
        "other",
    );
    let at = caller.locals.slot("node").unwrap().clone();
    let other = caller.locals.slot("other").unwrap().clone();
    let memory = caller.memory.clone().with_initialized_object(&other, 16);
    let caller = caller.with_memory(memory);
    let paths = execute_c_function_call_paths(
        &caller,
        &function,
        &[c_pointer_value(at), c_pointer_value(other)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(paths.iter().all(|path| matches!(
        path.outcome,
        CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(_))
    )));
}

#[test]
fn raw_object_footprint_does_not_resize_or_initialize_parent_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let at = Pointer::symbolic(Variable(873_031));
    let memory = CMemory::new()
        .with_block(at.block.clone(), 32)
        .with_uninitialized_object(at.offset_by_bytes(8), 8);
    assert_eq!(memory.block_size(&at.block), Some(&32u32.into()));
    assert!(memory.may_read_uninitialized_object(&at.offset_by_bytes(8), 8));
    assert!(!memory.may_read_uninitialized_object(&at, 8));
    assert!(!memory.may_read_uninitialized_object(&at.offset_by_bytes(16), 8));
    assert!(!memory.has_initialized_bytes_at(&at.offset_by_bytes(8), 8));
}

// The admitted value-only constructor profile must yield the same observable
// descriptor after zero, one or several explicit trivial result copies.
#[test]
fn value_only_constructor_preserves_descriptor_across_result_copy_chains() {
    let layout = CAggregateLayout::new(
        16,
        8,
        vec![
            CAggregateField::new("data", 0, CType::Int32Pointer),
            CAggregateField::new("extent", 8, CType::UInt64),
        ],
    );
    let destination = c_variable("destination");
    let owner = CResourceSpec::owned_memory(
        CMemorySegment::new(destination.clone(), c_int32_literal(0), c_int32_literal(16))
            .with_element_width(1),
    );
    let constructor = c_function(
        CType::Void,
        "construct_descriptor",
        vec![
            c_parameter("destination", CType::Int32Pointer),
            c_parameter("backing", CType::Int32Pointer),
            c_parameter("extent", CType::UInt64),
        ],
        c_seq(
            c_typed_store(
                checked_field(destination.clone(), &layout, "data", CType::Int32Pointer),
                c_variable("backing"),
                CType::Int32Pointer,
            ),
            c_seq(
                c_typed_store(
                    checked_field(destination, &layout, "extent", CType::UInt64),
                    c_variable("extent"),
                    CType::UInt64,
                ),
                c_return(c_void_value()),
            ),
        ),
    )
    .with_construction_parameter(0, layout.clone())
    .with_resource_summary(vec![owner.clone()], vec![owner]);
    let environment = CExecutionEnvironment::new().with_function(constructor);
    for copies in [0, 1, 3] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut statements = vec![
            c_declare("backing", CType::Int32),
            c_assign("backing", c_int32_literal(23)),
            c_allocate_aggregate_destination("result", layout.clone()),
        ];
        let names = (0..copies)
            .map(|index| format!("temporary_{index}"))
            .collect::<Vec<_>>();
        for name in &names {
            statements.push(c_allocate_aggregate_destination(name, layout.clone()));
        }
        let first = names.first().map_or("result", String::as_str);
        statements.push(c_call(
            "construct_descriptor",
            vec![
                c_cast(c_variable(first), CType::Int32Pointer),
                c_addr_of("backing"),
                c_uint64_literal(37),
            ],
        ));
        for (index, name) in names.iter().enumerate() {
            let target = names.get(index + 1).map_or("result", String::as_str);
            statements.push(c_copy_aggregate(
                c_variable(target),
                c_variable(name),
                layout.clone(),
            ));
        }
        if !names.is_empty() {
            statements.push(c_end_automatic_lifetimes(
                names.iter().rev().cloned().collect(),
            ));
        }
        // Ordinary local storage has implicit authority rather than a range fact.
        // Writing through the saved backing pointer checks that retirement kept it.
        statements.push(c_typed_store(
            c_addr_of("backing"),
            c_int32_literal(24),
            CType::Int32,
        ));
        let statement = statements.into_iter().reduce(c_seq).unwrap();
        let checked = prove_symbolic_c_execution_paths_with_environment(
            CState::new().with_population_creation_tracking(),
            statement,
            PureFactContext::new(),
            environment.clone(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
        let [path] = checked.paths() else {
            panic!("one descriptor construction path");
        };
        let state = match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
            Proposition::CStatementExecutes {
                outcome: CStatementOutcome::Normal(state),
                ..
            }
            | Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Normal(state),
                ..
            } => state,
            _ => panic!("descriptor construction and copies must complete"),
        };
        let result = state.locals.aggregate_object_pointer("result").unwrap();
        let backing = state.locals.slot("backing").unwrap();
        assert_eq!(
            pointer(&state.memory.known_value(result).unwrap()),
            *backing
        );
        assert_eq!(
            state.memory.known_value(&result.offset_by_bytes(8)),
            Some(CValue::UInt64(Bitvector32Term::UInt64Constant(37)))
        );
        assert_eq!(state.memory.known_value(backing), Some(int32(24)));
        assert!(
            state
                .resources
                .memory_write_range(result, 16, &PureFactContext::new())
                .is_some()
        );
        for name in &names {
            assert!(state.locals.aggregate_object_pointer(name).is_none());
        }
    }
}

// A summary can establish initialized storage without naming its pointer field's
// value. Copying that value must use the same typed read as an ordinary load,
// including when the storage holding it ends immediately afterwards.
#[test]
fn copying_unknown_pointer_field_preserves_its_value_after_source_retirement() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut state =
        allocate_destination(&CState::new().with_population_creation_tracking(), "source");
    state = allocate_destination(&state, "target");
    let source = state
        .locals
        .aggregate_object_pointer("source")
        .unwrap()
        .clone();
    let target = state
        .locals
        .aggregate_object_pointer("target")
        .unwrap()
        .clone();
    state.set_memory(state.memory.clone().with_initialized_object(&source, 16));
    let expected = crate::kernel::eval::symbolic_storage_cell_value(
        &state.memory,
        &source,
        CType::Int32Pointer,
        true,
    )
    .unwrap();
    let checked = prove_symbolic_c_execution_paths_with_environment(
        state,
        c_seq(
            c_copy_aggregate(c_variable("target"), c_variable("source"), node_layout()),
            c_end_automatic_lifetimes(vec!["source".into()]),
        ),
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    );
    let [path] = checked.paths() else {
        panic!("one checked copy path");
    };
    let state = match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Normal(state),
            ..
        }
        | Proposition::CStatementVerifies {
            outcome: CStatementOutcome::Normal(state),
            ..
        } => state,
        _ => panic!("initialized unknown pointer copy must complete"),
    };
    assert_eq!(state.memory.known_value(&target), Some(expected));
    assert!(state.locals.aggregate_object_pointer("source").is_none());
    assert!(
        state
            .resources
            .memory_write_range(&target, 16, &PureFactContext::new())
            .is_some()
    );
}
