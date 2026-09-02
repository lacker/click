use super::*;

fn heap_allocation_paths() -> Vec<CStatementExecutionPath> {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    execute_c_statement_paths(
        &state,
        &c_heap_allocate("p", 16),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("fixed-size allocation should execute")
}

fn successful_heap_allocation_state() -> CState {
    let paths = heap_allocation_paths();
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation statement should produce one pending outcome");
    };
    let Some(CValue::Pointer(pointer)) = pending.locals().get("p") else {
        panic!("allocation should assign a pointer");
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(pointer.clone(), Pointer::null()),
        false,
    ));
    resolve_pending_heap_allocations(pending, &assumptions)
}

#[test]
fn heap_allocate_has_null_or_fresh_uninitialized_outcomes() {
    let paths = heap_allocation_paths();
    assert_eq!(paths.len(), 1);
    let success = successful_heap_allocation_state();
    let Some(CValue::Pointer(pointer)) = success.locals().get("p") else {
        panic!("allocation should assign a pointer");
    };
    assert_eq!(
        success.memory().live_heap_block_size(pointer),
        Some(&Bitvector32Term::Constant(16))
    );
    if !skip_without_memory_dag() {
        let derivation = intern_c_memory_ref(success.memory())
            .derivation()
            .expect("successful allocation should record a memory edge");
        assert!(matches!(
            derivation.as_ref(),
            CMemoryDerivation::HeapAllocated { block, bytes, .. }
                if block == &pointer.block && *bytes == Bitvector32Term::Constant(16)
        ));
    }
    assert!(
        success
            .resources()
            .facts()
            .contains(&CResourceFact::own_allocation(pointer.clone(), 16))
    );
    let read = evaluate_c_expression_paths(
        &success,
        &c_load(c_variable("p")),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            ..
        }]
    ));

    let CStatementOutcome::Normal(pending) = &paths[0].outcome else {
        unreachable!();
    };
    let Some(CValue::Pointer(pointer)) = pending.locals().get("p") else {
        unreachable!();
    };
    let null = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer.clone(), Pointer::null()),
            true,
        )),
    );
    assert!(null.resources().facts().is_empty());
    assert!(null.memory().live_heap_block_size(pointer).is_none());
}

#[test]
fn pending_and_failed_heap_allocation_preserve_existing_memory() {
    if skip_without_memory_dag() {
        return;
    }

    let existing = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(Pointer::null()))
        .with_memory(
            CMemory::new()
                .with_block("arg-memory", 4)
                .store(existing.clone(), int32(37)),
        );
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_allocate("p", 16),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("allocation statement should produce a pending result");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation statement should produce one pending outcome");
    };
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("p") else {
        panic!("allocation should assign a symbolic pending pointer");
    };
    let pending_pointer = pending_pointer.clone();
    let pending_memory = pending.memory().clone();

    let pending_derivation = intern_c_memory_ref(&pending_memory)
        .derivation()
        .expect("pending allocation should record a memory edge");
    let CMemoryDerivation::HeapAllocationPending {
        base,
        allocation_base,
        bytes,
    } = pending_derivation.as_ref()
    else {
        panic!("unexpected pending-allocation derivation: {pending_derivation:?}");
    };
    assert_eq!(base.as_ref(), state.memory());
    assert_eq!(allocation_base, &pending_pointer);
    assert_eq!(*bytes, Bitvector32Term::Constant(16));
    assert!(with_extended_dag_bridging(|| c_memory_load_is_unchanged(
        state.memory(),
        &pending_memory,
        &existing,
        &PureFactContext::new(),
    )));

    let failed = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.clone(), Pointer::null()),
            true,
        )),
    );
    assert!(failed.resources().facts().is_empty());
    assert!(
        failed
            .memory()
            .live_heap_block_size(&pending_pointer)
            .is_none()
    );
    assert!(with_extended_dag_bridging(|| c_memory_load_is_unchanged(
        state.memory(),
        failed.memory(),
        &existing,
        &PureFactContext::new(),
    )));
    assert_eq!(failed.memory(), state.memory());

    let succeeded = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.clone(), Pointer::null()),
            false,
        )),
    );
    let derivation = intern_c_memory_ref(succeeded.memory())
        .derivation()
        .expect("successful allocation should record a memory edge");
    let CMemoryDerivation::HeapAllocated { base, block, bytes } = derivation.as_ref() else {
        panic!("unexpected successful-allocation derivation: {derivation:?}");
    };
    assert_eq!(base.as_ref(), &pending_memory);
    assert!(matches!(block, PointerBlock::Heap(_)));
    assert_eq!(*bytes, Bitvector32Term::Constant(16));
    assert!(with_extended_dag_bridging(|| c_memory_load_is_unchanged(
        &pending_memory,
        succeeded.memory(),
        &existing,
        &PureFactContext::new(),
    )));
}

#[test]
fn successful_heap_allocation_is_fresh_from_every_existing_block() {
    let first = successful_heap_allocation_state();
    let Some(CValue::Pointer(first_pointer)) = first.locals().get("p") else {
        panic!("first allocation should assign a pointer");
    };
    let first_pointer = first_pointer.clone();
    assert!(pointers_proven_distinct(
        &first_pointer,
        &Pointer::null(),
        &PureFactContext::new(),
    ));
    assert!(pointers_proven_distinct(
        &first_pointer,
        &CMemory::local_pointer("local"),
        &PureFactContext::new(),
    ));
    assert!(pointers_proven_distinct(
        &first_pointer,
        &Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        &PureFactContext::new(),
    ));

    let state = first.with_local("q", CValue::Pointer(Pointer::null()));
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_allocate("q", 16),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        // Deliberately reset the generator: existing heap identities still
        // have to prevent reuse.
        &mut ExecutionBudget::default(),
    )
    .expect("second allocation should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("second allocation should have one pending outcome");
    };
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("q") else {
        panic!("second allocation should assign a pending pointer");
    };
    let second = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.clone(), Pointer::null()),
            false,
        )),
    );
    let Some(CValue::Pointer(second_pointer)) = second.locals().get("q") else {
        panic!("second allocation should resolve to a pointer");
    };
    assert!(pointers_proven_distinct(
        &first_pointer,
        second_pointer,
        &PureFactContext::new(),
    ));
}

#[test]
fn heap_free_deallocates_the_complete_block_and_rejects_double_free() {
    let success = successful_heap_allocation_state();
    let freed = execute_c_statement_paths(
        &success,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("free should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(freed),
            facts: free_facts,
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("valid free should have one normal path: {freed:?}");
    };
    let Some(CValue::Pointer(pointer)) = freed.locals().get("p") else {
        panic!("freed local should still contain its stale pointer value");
    };
    assert!(freed.memory().is_deallocated_heap_address(pointer));
    assert!(freed.resources().facts().is_empty());
    assert!(matches!(
        free_facts.as_slice(),
        [ExecutionPureFact {
            proposition: Proposition::CHeapAllocationFreed {
                after,
                allocation_base,
                bytes,
                ..
            },
            ..
        }] if after == freed.memory()
            && allocation_base == pointer
            && *bytes == Bitvector32Term::Constant(16)
    ));
    if !skip_without_memory_dag() {
        let derivation = intern_c_memory_ref(freed.memory())
            .derivation()
            .expect("free should record a memory edge");
        assert!(matches!(
            derivation.as_ref(),
            CMemoryDerivation::HeapFreed { allocation_base, bytes, .. }
                if allocation_base == pointer && *bytes == Bitvector32Term::Constant(16)
        ));
    }

    let double = execute_c_statement_paths(
        freed,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("double free should execute to a diagnostic");
    assert!(matches!(
        double.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                CInvalidFree::DoubleFree
            )),
            ..
        }]
    ));
}

#[test]
fn consuming_a_whole_range_drops_snapshot_equivalent_prefix_residues() {
    let owner = Pointer {
        block: "owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held_start = Bitvector32Term::Variable(Variable(90_001));
    let required_start = Bitvector32Term::Variable(Variable(90_002));
    let length = Bitvector32Term::Variable(Variable(90_003));
    let held = CResourceFact::own_memory(CMemoryRange::new(
        owner.clone(),
        held_start.clone(),
        Bitvector32Term::add(held_start.clone(), length.clone()),
    ));
    let required = CResourceFact::own_memory(CMemoryRange::new(
        owner.offset_by_int32_elements(required_start.clone()),
        Bitvector32Term::Constant(0),
        length,
    ));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(held_start, required_start), true);
    let remaining = ResourceContext::new()
        .unchecked_with_fact(held)
        .without_fact(&required, &assumptions)
        .expect("an equivalent whole range should be consumable");
    assert!(remaining.is_empty(), "unexpected residue: {remaining:?}");
}

#[test]
fn scoped_call_borrows_end_before_free() {
    let state = successful_heap_allocation_state();
    let helper = c_function(
        CType::Int32,
        "read_borrow",
        vec![c_parameter("data", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_resource_summary(
        vec![CResourceSpec::ViewMemory(CMemorySegment::new(
            c_variable("data"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        Vec::new(),
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("observed", "read_borrow", vec![c_variable("p")]),
        c_heap_free(c_variable("p")),
    );
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::default(),
    )
    .expect("a read-only call borrow followed by free should execute");

    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after.resources().facts().is_empty()
    ));
}

#[test]
fn standalone_view_cannot_authorize_free() {
    let state = successful_heap_allocation_state();
    let Some(CValue::Pointer(pointer)) = state.locals().get("p") else {
        panic!("successful allocation should expose its pointer")
    };
    let pointer = pointer.clone();
    let complete_access = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    );
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(pointer, 16))
        .unchecked_with_fact(CResourceFact::view_memory(complete_access.clone()));
    let state = state.with_resource_context(resources);
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a standalone view should fail locally at free");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource: CResourceFact::Own(CResource::Memory(missing), _),
            }),
            ..
        }] if missing == &complete_access
    ));
}

#[test]
fn persistent_composite_view_blocks_free_locally() {
    let state = successful_heap_allocation_state();
    let Some(CValue::Pointer(pointer)) = state.locals().get("p") else {
        panic!("successful allocation should expose its pointer")
    };
    let persistent = CResourceFact::view_composite(
        "borrowed_allocation".to_string(),
        vec![CValue::Pointer(pointer.clone())],
    );
    let state = state.clone().with_resource_context(
        state
            .resources()
            .clone()
            .unchecked_with_fact(persistent.clone()),
    );
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a persistent stale view should produce a local diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(
                    CRuntimeError::StaleResourceAfterFree { resource }
                ),
                ..
            }] if resource == &persistent
        ),
        "unexpected free result for {persistent:#?}: {paths:#?}"
    );
}

#[test]
fn separated_persistent_view_survives_free() {
    let state = successful_heap_allocation_state();
    let other = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let view = CResourceFact::view_memory(CMemoryRange::new(
        other,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(view.clone()));
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a view of a distinct allocation should survive free");

    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after.resources().facts() == [view]
    ));
}

#[test]
fn free_of_external_allocation_preserves_unrelated_external_cells() {
    let allocation_base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(908_000)), 4),
    };
    let unrelated = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(908_001)), 4),
    };
    let memory = CMemory::new()
        .store(unrelated.clone(), int32(37))
        .with_heap_allocation_claim(allocation_base.clone(), 16)
        .expect("external allocation claim should be fresh");
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(allocation_base.clone(), 16))
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            allocation_base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        )));
    let state = CState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", CValue::Pointer(allocation_base.clone()));

    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("freeing an imported allocation should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("free should have one normal path: {paths:?}");
    };

    assert_eq!(
        after.memory().load(&unrelated),
        CExpressionOutcome::Value(int32(37))
    );
    assert!(!after.memory().is_deallocated_heap_address(&unrelated));
    assert!(after.memory().is_deallocated_heap_address(&allocation_base));
    assert!(
        after
            .memory()
            .is_deallocated_heap_address(&allocation_base.offset_by_int32_elements(1.into()))
    );
}

#[test]
fn interface_heap_join_retains_potential_live_allocation() {
    let allocation_base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let retained = CState::new().with_memory(
        CMemory::new()
            .with_heap_allocation_claim(allocation_base.clone(), 16)
            .expect("the allocation claim should be fresh"),
    );
    let freed = retained.clone().with_memory(
        retained
            .memory()
            .clone()
            .free_heap_block(&allocation_base)
            .expect("the retained arm should be able to free the allocation"),
    );
    let siblings = [&freed, &retained];
    let freed_join = crate::kernel::abstract_c_state_for_interface_join_across(
        &freed,
        &siblings,
        &BTreeMap::new(),
    )
    .expect("the freed arm should abstract");
    let retained_join = crate::kernel::abstract_c_state_for_interface_join_across(
        &retained,
        &siblings,
        &BTreeMap::new(),
    )
    .expect("the retained arm should abstract");

    assert_eq!(freed_join, retained_join);
    assert_eq!(
        freed_join.memory().live_heap_block_size(&allocation_base),
        Some(&Bitvector32Term::Constant(16))
    );
    assert!(
        !freed_join
            .memory()
            .is_deallocated_heap_address(&allocation_base)
    );
}

#[test]
fn free_requires_allocation_authority_not_just_write_access() {
    let mut success = successful_heap_allocation_state();
    let allocation = success
        .resources
        .facts()
        .iter()
        .find(|fact| fact.allocation().is_some())
        .cloned()
        .expect("successful allocation state includes allocation authority");
    success.resources = success
        .resources
        .clone()
        .without_exact_representation(&allocation)
        .expect("allocation authority has an exact representation");
    let paths = execute_c_statement_paths(
        &success,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("missing-authority free should execute to a diagnostic");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource
            }),
            ..
        }] if resource.allocation().is_some()
    ));
}

#[test]
fn heap_storage_becomes_readable_only_after_a_store() {
    let success = successful_heap_allocation_state();
    let stored = execute_c_statement_paths(
        &success,
        &c_store(c_variable("p"), c_int32_literal(37)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("an owned fresh heap cell should be writable");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(stored),
            ..
        },
    ] = stored.as_slice()
    else {
        panic!("heap store should succeed: {stored:?}");
    };
    let read = evaluate_c_expression_paths(
        stored,
        &c_load(c_variable("p")),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("initialized heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            ..
        }] if value == &int32(37)
    ));
}

#[test]
fn free_null_needs_no_allocation_resources() {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("free(NULL) should execute");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after == &state
    ));
}

#[test]
fn free_preserves_a_separate_recursive_tail_with_the_same_symbolic_block() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(909_000)), 4),
    };
    let tail = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(909_001)), 4),
    };
    let tail_resource =
        CResourceFact::own_composite("allocated_list".to_string(), vec![CValue::Pointer(tail)]);
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(base.clone(), 16))
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        )))
        .unchecked_with_fact(tail_resource.clone());
    let memory = CMemory::new()
        .with_heap_allocation_claim(base.clone(), 16)
        .expect("symbolic allocation claim should be fresh");
    let state = CState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", CValue::Pointer(base));

    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("freeing a separated parent should execute");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after.resources().facts() == [tail_resource]
    ));
}

fn nullable_owner_contract(body: CStatement) -> (CState, CFunction, Vec<CExpression>) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(910_000)), 4),
    };
    let pointer_value = CValue::Pointer(pointer.clone());
    let pointer_expression = SpecExpression::CExpression(c_variable("item"));
    let definition = CCompositeResourceDefinition::new(
        "owned_item",
        vec![c_parameter("item", CType::Int32Pointer)],
        Some(SpecProposition::Comparison {
            left: pointer_expression.clone(),
            operator: CComparisonOperator::NotEqual,
            right: SpecExpression::Value(CValue::Pointer(Pointer::null())),
        }),
        false,
        vec![
            CResourceSpec::Token {
                access: CResourceAccessMode::Own,
                name: "allocation".to_string(),
                arguments: vec![
                    c_variable("item"),
                    CExpression::Value(CValue::Int32(Bitvector32Term::Constant(4))),
                ],
                parameter_types: vec![CType::Int32Pointer, CType::Int32],
            },
            CResourceSpec::OwnMemory(CMemorySegment {
                base: c_variable("item"),
                start: c_int32_literal(0),
                end: c_int32_literal(1),
                guard: None,
            }),
        ],
        Vec::new(),
    );
    let requirement = CResourceSpec::Composite {
        access: CResourceAccessMode::Own,
        name: "owned_item".to_string(),
        arguments: vec![c_variable("item")],
        parameter_types: vec![CType::Int32Pointer],
    };
    let function = c_function(
        CType::Int32,
        "item_destroy",
        vec![c_parameter("item", CType::Int32Pointer)],
        body,
    )
    .with_resource_summary(vec![requirement], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    )
    .with_composite_resource_definitions(vec![definition]);
    let state = CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
        CResourceFact::own_composite("owned_item".to_string(), vec![pointer_value]),
    ));
    (state, function, vec![c_pointer_value(pointer)])
}

#[test]
fn guarded_opaque_call_footprints_skip_only_inactive_segments() {
    let (_, mut function, _) = nullable_owner_contract(c_return(c_int32_literal(0)));
    let active = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("item")),
        operator: CComparisonOperator::NotEqual,
        right: SpecExpression::Value(CValue::Pointer(Pointer::null())),
    };
    function.contract_mutable = vec![
        CMemorySegment::new(c_int32_literal(7), c_int32_literal(0), c_int32_literal(1))
            .with_guard(active),
    ];
    let environment = CExecutionEnvironment::new()
        .with_function(function.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: function.clone(),
        });

    let null = CValue::Pointer(Pointer::null());
    let null_state =
        CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_composite("owned_item".to_string(), vec![null]),
        ));
    let null_paths = execute_c_statement_paths(
        &null_state,
        &c_call_assign("result", "item_destroy", vec![c_int32_literal(0)]),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::default(),
    )
    .expect("an inactive malformed footprint should not be evaluated");
    assert!(matches!(
        null_paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(_),
            ..
        }]
    ));

    let nonnull = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull_state = CState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_composite(
            "owned_item".to_string(),
            vec![CValue::Pointer(nonnull.clone())],
        )),
    );
    let nonnull_paths = execute_c_statement_paths(
        &nonnull_state,
        &c_call_assign("result", "item_destroy", vec![c_pointer_value(nonnull)]),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::default(),
    )
    .expect("an active malformed footprint should produce a local diagnostic");
    assert!(matches!(
        nonnull_paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message)),
            ..
        }] if message.contains("could not evaluate mutable footprint")
    ));
}

#[test]
fn contract_certification_splits_undecided_conditional_resource_guards() {
    let (state, function, arguments) = nullable_owner_contract(c_seq(
        c_heap_free(c_variable("item")),
        c_return(c_int32_literal(0)),
    ));
    let execution = prove_c_function_contract_execution_paths_with_environment(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    assert!(c_verified_function_contract_claims(&function, &execution).is_some());
}

#[test]
fn conditional_resource_certification_checks_the_unsafe_case_too() {
    let (state, function, arguments) = nullable_owner_contract(c_seq(
        c_heap_free(c_variable("item")),
        c_seq(
            c_heap_free(c_variable("item")),
            c_return(c_int32_literal(0)),
        ),
    ));
    let execution = prove_c_function_contract_execution_paths_with_environment(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    let error = c_unverified_function_contract_claims(&function, &execution)
        .expect_err("the nonnull double-free case must invalidate certification");
    assert!(error.contains("DoubleFree"), "unexpected failure: {error}");
}

#[test]
fn interior_free_and_store_after_free_are_rejected() {
    let success = successful_heap_allocation_state();
    let interior = execute_c_statement_paths(
        &success,
        &c_heap_free(c_add(c_variable("p"), c_int32_literal(1))),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("interior free should produce a diagnostic");
    assert!(matches!(
        interior.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                CInvalidFree::InteriorPointer
            )),
            ..
        }]
    ));

    let freed = execute_c_statement_paths(
        &success,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("valid free should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(freed),
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("valid free should succeed: {freed:?}");
    };
    let store = execute_c_statement_paths(
        freed,
        &c_store(c_variable("p"), c_int32_literal(1)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("store-after-free should produce undefined behavior");
    assert!(matches!(
        store.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            ..
        }]
    ));
}

#[test]
fn returning_malloc_result_resolves_null_and_success_outcomes() {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    let statement = c_seq(c_heap_allocate("p", 16), c_return(c_variable("p")));
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("returning a malloc result should split its outcomes");
    assert_eq!(paths.len(), 2);
    assert!(
        paths
            .iter()
            .all(|path| path.facts.iter().all(|fact| !fact.is_public())),
        "the malloc outcome split is internal, not a source-level premise"
    );

    let mut saw_success = false;
    let mut saw_failure = false;
    for path in paths {
        let CStatementOutcome::Return { value, state } = path.outcome else {
            panic!("malloc return should not produce a diagnostic");
        };
        let CValue::Pointer(pointer) = value else {
            panic!("malloc should return a pointer");
        };
        assert!(!state.memory().has_pending_heap_allocation());
        if pointer == Pointer::null() {
            saw_failure = true;
            assert!(state.resources().facts().is_empty());
        } else {
            saw_success = true;
            assert!(matches!(pointer.block, PointerBlock::Heap(_)));
            assert_eq!(
                state.memory().live_heap_block_size(&pointer),
                Some(&Bitvector32Term::Constant(16))
            );
            assert!(
                state
                    .resources()
                    .facts()
                    .contains(&CResourceFact::own_allocation(pointer.clone(), 16))
            );
        }
    }
    assert!(saw_success && saw_failure);
}

#[test]
fn unreturned_unresolved_malloc_result_cannot_cross_a_return() {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    let statement = c_seq(c_heap_allocate("p", 16), c_return(c_int32_literal(0)));
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("unresolved allocation should execute to a diagnostic");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            ..
        }]
    ));
}
