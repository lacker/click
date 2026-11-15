use super::*;
use crate::kernel::loans::LoanLedger;

#[test]
fn free_retires_a_cached_interior_alias() {
    let base = Pointer {
        block: PointerBlock::Heap(945_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(945_001));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), base.offset_by_bytes(8)),
        true,
    ));
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(12))
        .unwrap()
        .with_block(base.block.clone(), 12)
        .store(alias.clone(), int32(7));
    assert_eq!(memory.load(&alias), ExpressionOutcome::Value(int32(7)));
    let freed = memory.free_heap_block(&base, &assumptions).unwrap();
    assert_eq!(
        freed.load(&alias),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
        "an interior alias must not retain a cached value after free"
    );
}

#[test]
fn free_keeps_an_uncertain_block_only_with_ownership_of_the_whole_cell() {
    let base = Pointer::symbolic(Variable(945_010));
    let cell = Pointer::symbolic(Variable(945_011));
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(12))
        .unwrap()
        .store(
            cell.clone(),
            ProgramValue::Int64(MachineTerm::int64_constant(7)),
        );
    let assumptions = PureFactContext::new();
    for owned_bytes in [0u32, 4, 8] {
        let mut ownership = ResourceContext::new();
        if owned_bytes != 0 {
            ownership = ownership.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    cell.clone(),
                    0u32.into(),
                    owned_bytes.into(),
                    1,
                ),
            ));
        }
        let freed = memory
            .clone()
            .free_heap_block_with_owned_frame(&base, &assumptions, &ownership)
            .unwrap();
        assert_eq!(
            freed.load(&cell),
            if owned_bytes == 8 {
                ExpressionOutcome::Value(ProgramValue::Int64(MachineTerm::int64_constant(7)))
            } else {
                ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
            },
            "ownership of {owned_bytes} bytes"
        );
    }
}

#[test]
fn a_free_publishes_its_owned_pointer_frame_as_an_equality() {
    let base = Pointer {
        block: PointerBlock::Heap(950_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let cell = Pointer::symbolic(Variable(950_001));
    let value = Pointer {
        block: PointerBlock::Heap(950_002),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(4))
        .unwrap()
        .store(cell.clone(), ProgramValue::pointer(value));
    let resources = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(base.clone(), 4))
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            base.clone(),
            0u32.into(),
            1u32.into(),
        )))
        .unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(cell.clone(), 0u32.into(), 1u32.into(), 8),
        ));
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", ProgramValue::pointer(base));
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("one free outcome");
    };
    let StatementOutcome::Normal(after) = &path.outcome else {
        panic!("free succeeds: {:?}", path.outcome);
    };
    let ProgramValue::Pointer(before_read) = state
        .memory()
        .symbolic_pointer_version_load(&cell, ProgramType::Int32Pointer)
    else {
        unreachable!()
    };
    let ProgramValue::Pointer(after_read) = after
        .memory()
        .symbolic_pointer_version_load(&cell, ProgramType::Int32Pointer)
    else {
        unreachable!()
    };
    assert_ne!(
        before_read, after_read,
        "fact-supported frames do not choose read names"
    );
    let equality = Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(before_read, after_read),
        true,
    );
    assert!(
        path.facts
            .iter()
            .any(|fact| fact.proposition() == &equality),
        "the step publishes the frame itself"
    );
    let Proposition::ConditionIs(condition, true) = &equality else {
        unreachable!()
    };
    assert!(
        !PureFactContext::new()
            .equality_graph
            .knows_condition(condition, true),
        "the graph needs the step's frame evidence"
    );
    let learned = path
        .facts
        .iter()
        .fold(PureFactContext::new(), |facts, fact| {
            facts.assume_proposition(fact.proposition().clone())
        });
    assert!(learned.equality_graph.knows_condition(condition, true));
    assert!(
        !learned
            .restricted_to_facts(&[], &[])
            .equality_graph
            .knows_condition(condition, true),
        "restricting all facts must withdraw the graph's frame authority"
    );
}

fn active_heap_memory_loan(range: MemoryRange) -> LoanLedger {
    let fact = ResourceFact::own_memory(range);
    let support = ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(&fact)
        .expect("memory backing")
        .0;
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let opening = ledger
        .lend(owner, reader, support, fact)
        .expect("memory loan");
    ledger
        .apply(&opening.transition)
        .expect("memory loan apply")
}

fn assert_heap_loan_write_rejected(outcome: &StatementOutcome) {
    let StatementOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)) = outcome else {
        panic!("expected a loan refusal, got {outcome:?}");
    };
    assert_eq!(
        diagnostic.category(),
        crate::kernel::LoanRefusalCategory::ActiveDependency
    );
    assert_eq!(
        diagnostic.operation(),
        crate::kernel::LoanRefusalOperation::MemoryAccess
    );
    // A lifetime-ending operation names the loan that still protects the
    // allocation, not just the fact that some loan refused.
    assert!(diagnostic.subject().conflicting_resource_fact().is_some());
    assert!(diagnostic.subject().loan_id().is_some());
}

fn heap_allocation_paths() -> Vec<StatementExecutionPath> {
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_local("p", ProgramValue::pointer(Pointer::null()));
    execute_execution_statement_paths(
        &state,
        &program_heap_allocate("p", 16),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("fixed-size allocation should execute")
}

fn successful_heap_allocation_state() -> ExecutionState {
    let paths = heap_allocation_paths();
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation statement should produce one pending outcome");
    };
    let local_native_output_221 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_221.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
        false,
    ));
    resolve_pending_heap_allocations(pending, &assumptions)
}

#[test]
fn checked_object_address_rejects_freed_backing_without_reading_it() {
    let success = successful_heap_allocation_state();
    let paths = execute_execution_statement_paths(
        &success,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let StatementOutcome::Normal(freed) = &paths[0].outcome else {
        panic!("free should complete normally");
    };
    let theorem = prove_program_expression_evaluation(
        *freed.clone(),
        crate::kernel::program_expression::checked_object_address(
            crate::kernel::program_expression::typed_load(
                crate::kernel::program_expression::variable("p"),
                ProgramType::Int32,
            ),
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramExpressionEvaluates {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
            ..
        }
    ));
}

#[test]
fn heap_allocate_has_null_or_fresh_uninitialized_outcomes() {
    let paths = heap_allocation_paths();
    assert_eq!(paths.len(), 1);
    let success = successful_heap_allocation_state();
    let local_native_output_264 = success.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_264.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    assert_eq!(
        success.memory().live_heap_block_extent(pointer),
        Some(&HeapExtent::int32(16))
    );
    let derivation = intern_memory_ref(success.memory())
        .derivation()
        .expect("successful allocation should record a memory edge");
    assert!(matches!(
        derivation.as_ref(),
        MemoryDerivation::HeapAllocated { block, bytes, .. }
            if block == &pointer.block && *bytes == MachineTerm::constant(16)
    ));
    assert!(
        success
            .resources()
            .facts()
            .contains(&ResourceFact::own_allocation(pointer.pointer().clone(), 16))
    );
    let read = evaluate_program_expression_paths(
        &success,
        &crate::kernel::program_expression::load(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            ..
        }]
    ));

    let StatementOutcome::Normal(pending) = &paths[0].outcome else {
        unreachable!();
    };
    let local_native_output_306 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_306.as_deref() else {
        unreachable!();
    };
    let null = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
            true,
        )),
    );
    assert!(null.resources().facts().is_empty());
    assert!(
        null.memory()
            .live_heap_block_extent(pointer.pointer())
            .is_none()
    );
}

#[test]
fn call_havoc_preserves_initialization_of_a_heap_scalar() {
    let allocated = successful_heap_allocation_state();
    let local_native_output_327 = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_327.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let initialized = allocated.clone().with_memory(
        allocated
            .memory()
            .clone()
            .store(pointer.pointer().clone(), int32(7)),
    );
    let range = MemoryRange::new_with_element_width(
        pointer.pointer().clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        4,
    );
    let after_call =
        initialized
            .clone()
            .with_memory(initialized.memory().clone().with_call_memory_havoc(
                Variable(901),
                &[range],
                &PureFactContext::new(),
                None,
            ));
    assert!(after_call.memory().is_uninitialized_heap_address(
        pointer.pointer(),
        4,
        &PureFactContext::new()
    ));
    assert!(
        after_call
            .memory()
            .has_initialized_bytes_at(pointer.pointer(), 4)
    );
    let read = evaluate_program_expression_paths(
        &after_call,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("initialized heap scalar should remain readable after call havoc");
    assert!(matches!(
        read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::Value(_),
            ..
        }]
    ));
}

#[test]
fn naming_an_uninitialized_heap_cell_does_not_initialize_it() {
    let allocated = successful_heap_allocation_state();
    let local_native_output_380 = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_380.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let address = pointer.pointer().clone();
    let memory = allocated.memory().clone();
    let name = canonical_form_of_load(
        intern_memory(memory.clone()),
        address.clone(),
        crate::kernel::LoadKind::Int32,
    );
    let named =
        allocated.with_memory(memory.materialize_named_cell(address, ProgramValue::Int32(name)));
    let read = evaluate_program_expression_paths(
        &named,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            ..
        }]
    ));
}

#[test]
fn naming_an_initialized_heap_cell_preserves_its_initialization() {
    let allocated = successful_heap_allocation_state();
    let local_native_output_410 = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_410.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let address = pointer.pointer().clone();
    let stored = allocated.memory().clone().store(address.clone(), int32(7));
    let range = MemoryRange::new_with_element_width(
        address.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        4,
    );
    let havoc =
        stored.with_call_memory_havoc(Variable(902), &[range], &PureFactContext::new(), None);
    assert!(!havoc.has_known_cell_at(&address));
    let name = canonical_form_of_load(
        intern_memory(havoc.clone()),
        address.clone(),
        crate::kernel::LoadKind::Int32,
    );
    let named = havoc
        .clone()
        .materialize_named_cell(address.clone(), ProgramValue::Int32(name));
    assert!(named.has_known_cell_at(&address));
    assert_eq!(named.heap.initialized, havoc.heap.initialized);
}

#[test]
fn zeroed_heap_allocation_reads_zero_until_a_store() {
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_allocate_sized_with_zeroed(
            "p",
            crate::kernel::program_expression::multiply(
                crate::kernel::program_expression::int32_literal(2),
                crate::kernel::program_expression::int32_literal(4),
            ),
            true,
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("calloc-shaped allocation should execute");
    let StatementOutcome::Normal(pending) = &paths[0].outcome else {
        panic!("allocation should produce a pending outcome");
    };
    let local_native_output_454 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_454.as_deref() else {
        panic!("allocation should assign a pending pointer");
    };
    let success = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.pointer().clone(), Pointer::null()),
            false,
        )),
    );
    let local_native_output_464 = success.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_464.as_deref() else {
        panic!("successful allocation should assign a heap pointer");
    };
    assert!(
        success
            .memory()
            .is_zeroed_heap_address(pointer, 4, &PureFactContext::new())
    );

    let read = evaluate_program_expression_paths(
        &success,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("zeroed element read should execute");
    assert!(matches!(
        read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::Value(ProgramValue::Int32(value)),
            ..
        }] if *value == MachineTerm::constant(0)
    ));

    let stored = execute_execution_statement_paths(
        &success,
        &program_store(
            crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(1),
            ),
            crate::kernel::program_expression::int32_literal(7),
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("store into zeroed allocation should execute");
    let StatementOutcome::Normal(stored) = &stored[0].outcome else {
        panic!("store should have a normal outcome");
    };
    let read_after_store = evaluate_program_expression_paths(
        stored,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("stored element read should execute");
    assert!(matches!(
        read_after_store.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::Value(ProgramValue::Int32(value)),
            ..
        }] if *value == MachineTerm::constant(7)
    ));
}

#[test]
fn realloc_preserves_zeroed_prefix_and_leaves_growth_uninitialized() {
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(Pointer::null()))
        .with_local("q", ProgramValue::pointer(Pointer::null()));
    let calloc_paths = execute_execution_statement_paths(
        &state,
        &program_heap_allocate_sized_with_zeroed(
            "p",
            crate::kernel::program_expression::multiply(
                crate::kernel::program_expression::int32_literal(2),
                crate::kernel::program_expression::int32_literal(4),
            ),
            true,
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("calloc-shaped allocation should execute");
    let StatementOutcome::Normal(calloc_pending) = &calloc_paths[0].outcome else {
        panic!("calloc should produce a pending outcome");
    };
    let local_native_output_538 = calloc_pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(calloc_pointer)) = local_native_output_538.as_deref() else {
        panic!("calloc should assign a pointer");
    };
    let allocated = resolve_pending_heap_allocations(
        calloc_pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            pointer_is_null_condition(calloc_pointer.pointer().clone()),
            false,
        )),
    );
    let local_native_output_548 = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(old_pointer)) = local_native_output_548.as_deref() else {
        panic!("calloc success should assign a heap pointer");
    };

    let realloc_paths = execute_execution_statement_paths(
        &allocated,
        &program_reallocate_then_assign(
            0,
            "q",
            ProgramType::Int32Pointer,
            vec![
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(12),
            ],
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("realloc of zeroed storage should execute");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            ..
        },
    ] = realloc_paths.as_slice()
    else {
        panic!("realloc should produce one pending path: {realloc_paths:?}");
    };
    let local_native_output_569 = pending.locals().get_native("q");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_569.as_deref() else {
        panic!("realloc should assign a pending pointer");
    };
    assert_eq!(
        pending
            .memory()
            .heap
            .pending_reallocations
            .get(pending_pointer)
            .and_then(|pending| pending.zeroed_prefix.as_ref()),
        Some(&MachineTerm::constant(8))
    );
    assert!(
        pending
            .memory()
            .live_heap_block_extent(old_pointer)
            .is_some()
    );

    let success = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            pointer_is_null_condition(pending_pointer.pointer().clone()),
            false,
        )),
    );
    let local_native_output_595 = success.locals().get_native("q");
    let Some(ProgramValue::Pointer(resized)) = local_native_output_595.as_deref() else {
        panic!("successful realloc should assign a heap pointer");
    };
    assert!(
        success
            .memory()
            .is_zeroed_heap_address(resized, 4, &PureFactContext::new())
    );
    assert!(success.memory().is_uninitialized_heap_address(
        &Pointer {
            block: resized.block.clone(),
            offset: PointerOffsetTerm::Constant(8),
        },
        4,
        &PureFactContext::new(),
    ));

    let prefix_read = evaluate_program_expression_paths(
        &success,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("q"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("zeroed realloc prefix read should execute");
    assert!(matches!(
        prefix_read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::Value(ProgramValue::Int32(value)),
            ..
        }] if *value == MachineTerm::constant(0)
    ));

    let tail_read = evaluate_program_expression_paths(
        &success,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("q"),
            crate::kernel::program_expression::int32_literal(2),
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("uninitialized realloc tail read should execute");
    assert!(matches!(
        tail_read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            ..
        }]
    ));
}

#[test]
fn pending_and_failed_heap_allocation_preserve_existing_memory() {
    let existing = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(Pointer::null()))
        .with_memory(
            Memory::new()
                .with_block("arg-memory", 4)
                .store(existing.clone(), int32(37)),
        );
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_allocate("p", 16),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("allocation statement should produce a pending result");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation statement should produce one pending outcome");
    };
    let local_native_output_673 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_673.as_deref() else {
        panic!("allocation should assign a symbolic pending pointer");
    };
    let pending_pointer = pending_pointer.clone();
    let pending_memory = pending.memory().clone();

    let pending_derivation = intern_memory_ref(&pending_memory)
        .derivation()
        .expect("pending allocation should record a memory edge");
    let MemoryDerivation::HeapAllocationPending {
        base,
        allocation_base,
        bytes,
    } = pending_derivation.as_ref()
    else {
        panic!("unexpected pending-allocation derivation: {pending_derivation:?}");
    };
    assert_eq!(base.as_ref(), state.memory());
    assert_eq!(allocation_base, pending_pointer.pointer());
    assert_eq!(*bytes, MachineTerm::constant(16));
    assert!(checked_memory_load_equality(
        state.memory(),
        &pending_memory,
        &existing,
        &PureFactContext::new(),
    ));

    let failed = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.pointer().clone(), Pointer::null()),
            true,
        )),
    );
    assert!(failed.resources().facts().is_empty());
    assert!(
        failed
            .memory()
            .live_heap_block_extent(pending_pointer.pointer())
            .is_none()
    );
    assert!(checked_memory_load_equality(
        state.memory(),
        failed.memory(),
        &existing,
        &PureFactContext::new(),
    ));
    assert_eq!(failed.memory(), state.memory());

    let succeeded = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.pointer().clone(), Pointer::null()),
            false,
        )),
    );
    let derivation = intern_memory_ref(succeeded.memory())
        .derivation()
        .expect("successful allocation should record a memory edge");
    let MemoryDerivation::HeapAllocated { base, block, bytes } = derivation.as_ref() else {
        panic!("unexpected successful-allocation derivation: {derivation:?}");
    };
    assert_eq!(base.as_ref(), &pending_memory);
    assert!(matches!(block, PointerBlock::Heap(_)));
    assert_eq!(*bytes, MachineTerm::constant(16));
    assert!(checked_memory_load_equality(
        &pending_memory,
        succeeded.memory(),
        &existing,
        &PureFactContext::new(),
    ));
}

#[test]
fn successful_heap_allocation_is_fresh_from_every_existing_block() {
    let first = successful_heap_allocation_state();
    let local_native_output_749 = first.locals().get_native("p");
    let Some(ProgramValue::Pointer(first_pointer)) = local_native_output_749.as_deref() else {
        panic!("first allocation should assign a pointer");
    };
    let first_pointer = first_pointer.clone();
    assert!(pointers_proven_distinct_for_memory_resolution(
        &first_pointer,
        &Pointer::null(),
        &PureFactContext::new(),
    ));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &first_pointer,
        &Memory::local_pointer("local"),
        &PureFactContext::new(),
    ));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &first_pointer,
        &Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        &PureFactContext::new(),
    ));

    let state = first.with_local("q", ProgramValue::pointer(Pointer::null()));
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_allocate("q", 16),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        // Deliberately reset the generator: existing heap identities still
        // have to prevent reuse.
        &mut ExecutionBudget::default(),
    )
    .expect("second allocation should execute");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("second allocation should have one pending outcome");
    };
    let local_native_output_792 = pending.locals().get_native("q");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_792.as_deref() else {
        panic!("second allocation should assign a pending pointer");
    };
    let second = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.pointer().clone(), Pointer::null()),
            false,
        )),
    );
    let local_native_output_802 = second.locals().get_native("q");
    let Some(ProgramValue::Pointer(second_pointer)) = local_native_output_802.as_deref() else {
        panic!("second allocation should resolve to a pointer");
    };
    assert!(pointers_proven_distinct_for_memory_resolution(
        &first_pointer,
        second_pointer,
        &PureFactContext::new(),
    ));
}

/// A `free` ends the whole allocation, so the question a cell has to answer
/// is whether the released *extent* reaches it — not whether its address is
/// the allocation's base. Asking `pointers_proven_distinct_for_memory_resolution`
/// about the base answered "this free left it alone" for every element of the
/// block but the first, so a fact about `p[3]` crossed a `free(p)`.
mod a_free_reaches_every_element_of_its_block {
    use super::*;
    use crate::kernel::memory_provenance::with_extended_dag_bridging;
    use crate::kernel::resource_tracker::{
        TrackedResource,
        step_effect::{Evidence, Separation, StepEffect, affects},
    };

    /// The rule's answer about one cell for the `free` that produced
    /// `freed`, inside the one scope that may read these edges at all.
    fn effect_of_the_free(freed: &Memory, cell: &Pointer) -> StepEffect {
        let produced = crate::kernel::intern_memory(freed.clone());
        let derivation = produced.derivation().expect("the free records an edge");
        let no_facts = PureFactContext::new();
        with_extended_dag_bridging(|| {
            affects(
                derivation.as_ref(),
                &produced,
                TrackedResource::Cell {
                    pointer: cell,
                    bytes: 4,
                },
                &Evidence {
                    assumptions: &no_facts,
                    cross_loop_havoc: false,
                },
            )
        })
    }

    fn freed_sixteen_byte_allocation() -> (Memory, Pointer) {
        let state = successful_heap_allocation_state();
        let local_native_output_849 = state.locals().get_native("p");
        let Some(ProgramValue::Pointer(pointer)) = local_native_output_849.as_deref() else {
            panic!("allocation should assign a pointer");
        };
        let base = pointer.pointer().clone();
        let freed = state
            .memory()
            .clone()
            .free_heap_block(&base, &PureFactContext::new())
            .expect("the allocation is live");
        (freed, base)
    }

    /// Every element of the released block, base included.
    #[test]
    fn a_freed_allocation_affects_its_interior_cells() {
        let (freed, base) = freed_sixteen_byte_allocation();
        for offset in [0, 4, 8, 12] {
            let cell = base.offset_by_bytes(offset);
            assert_eq!(
                effect_of_the_free(&freed, &cell),
                StepEffect::Affected,
                "the free was reported separate from the cell at byte {offset}"
            );
        }
    }

    /// The other polarity: a cell in an object the kernel proves is not the
    /// released one is still framed across the free, on the block ladder
    /// that decides it above the extent question.
    #[test]
    fn a_freed_allocation_leaves_another_object_alone() {
        let (freed, _) = freed_sixteen_byte_allocation();
        let elsewhere = Pointer {
            block: PointerBlock::Concrete("global:g".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        assert_eq!(
            effect_of_the_free(&freed, &elsewhere),
            StepEffect::Separate(Separation::Cell(
                crate::kernel::resource_tracker::cell_source::MemoryDagHopJustification::HeapFreeOfDistinctBlock
            ))
        );
    }
}

#[test]
fn heap_free_deallocates_the_complete_block_and_rejects_double_free() {
    let success = successful_heap_allocation_state();
    let freed = execute_execution_statement_paths(
        &success,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("free should execute");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(freed),
            facts: free_facts,
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("valid free should have one normal path: {freed:?}");
    };
    let local_native_output_915 = freed.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_915.as_deref() else {
        panic!("freed local should still contain its stale pointer value");
    };
    assert!(
        freed
            .memory()
            .is_deallocated_heap_address(pointer, &PureFactContext::new())
    );
    assert!(freed.resources().facts().is_empty());
    assert!(matches!(
        free_facts.to_vec().as_slice(),
        [ExecutionPureFact {
            proposition: Proposition::HeapAllocationFreed {
                after,
                allocation_base,
                bytes,
                ..
            },
            ..
        }] if after == freed.memory()
            && allocation_base == pointer.pointer()
            && *bytes == HeapExtent::int32(MachineTerm::constant(16))
    ));
    let derivation = intern_memory_ref(freed.memory())
        .derivation()
        .expect("free should record a memory edge");
    assert!(matches!(
        derivation.as_ref(),
        MemoryDerivation::HeapFreed { allocation_base, bytes, .. }
            if allocation_base == pointer.pointer() && *bytes == MachineTerm::constant(16)
    ));

    let double = execute_execution_statement_paths(
        freed,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("double free should execute to a diagnostic");
    assert!(matches!(
        double.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::RuntimeError(RuntimeError::InvalidFree(
                InvalidFree::DoubleFree
            )),
            ..
        }]
    ));
}

#[test]
fn consuming_a_whole_range_drops_state_equivalent_prefix_residues() {
    let owner = Pointer {
        block: "owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held_start = MachineTerm::Variable(Variable(90_001));
    let required_start = MachineTerm::Variable(Variable(90_002));
    let length = MachineTerm::Variable(Variable(90_003));
    let held = ResourceFact::own_memory(MemoryRange::new(
        owner.clone(),
        held_start.clone(),
        MachineTerm::add(held_start.clone(), length.clone()),
    ));
    let required = ResourceFact::own_memory(MemoryRange::new(
        owner.offset_by_int32_elements(required_start.clone()),
        MachineTerm::constant(0),
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
    // The call views `p[0]`, so the caller has written it.
    let Some(ProgramValue::Pointer(pointer)) = state.locals().get_native("p").as_deref().cloned()
    else {
        panic!("allocation should assign a pointer");
    };
    let memory = state
        .memory()
        .clone()
        .with_initialized_object(pointer.pointer(), 4);
    let state = state
        .with_memory(memory)
        .with_local("observed", ProgramValue::Int32(0u32.into()));
    let helper = program_function(
        ProgramType::Int32,
        "read_borrow",
        vec![program_parameter("data", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("data"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        Vec::new(),
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let statement = program_seq(
        program_call_then_assign(
            1,
            "observed",
            "read_borrow",
            vec![crate::kernel::program_expression::variable("p")],
        ),
        program_heap_free(crate::kernel::program_expression::variable("p")),
    );
    let paths = execute_execution_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::default(),
    )
    .expect("a read-only call borrow followed by free should execute");

    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::Normal(after),
            ..
        }] if after.resources().facts().is_empty()
    ));
}

#[test]
fn standalone_view_cannot_authorize_free() {
    let state = successful_heap_allocation_state();
    let local_native_output_1054 = state.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_1054.as_deref() else {
        panic!("successful allocation should expose its pointer")
    };
    let pointer = pointer.pointer().clone();
    let complete_access = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    );
    let resources = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(pointer, 16))
        .unchecked_with_fact(ResourceFact::view_memory(complete_access.clone()));
    let state = state.with_resource_context(resources);
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("a standalone view should fail locally at free");
    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::RuntimeError(RuntimeError::MissingResource { resource }),
            ..
        }] if matches!(
            &**resource,
            ResourceFact::Own(Resource::Memory(missing), _) if missing == &complete_access
        )
    ));
}

#[test]
fn persistent_composite_view_blocks_free_and_realloc_locally() {
    let state = successful_heap_allocation_state();
    let local_native_output_1090 = state.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_1090.as_deref() else {
        panic!("successful allocation should expose its pointer")
    };
    let persistent = ResourceFact::view_composite(
        "borrowed_allocation".to_string(),
        vec![ProgramValue::pointer(pointer.pointer().clone())],
    );
    let state = state.clone().with_resource_context(
        state
            .resources()
            .clone()
            .unchecked_with_fact(persistent.clone()),
    );
    let state = state.with_local("q", ProgramValue::pointer(Pointer::null()));
    for statement in [
        program_heap_free(crate::kernel::program_expression::variable("p")),
        program_reallocate_then_assign(
            2,
            "q",
            ProgramType::Int32Pointer,
            vec![
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(8),
            ],
        ),
    ] {
        let paths = execute_execution_statement_paths(
            &state,
            &statement,
            &PureFactContext::new(),
            ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
        )
        .expect("a persistent stale view should produce a local diagnostic");
        assert!(
            matches!(
                paths.as_slice(),
                [StatementExecutionPath {
                    outcome: StatementOutcome::RuntimeError(
                        RuntimeError::StaleResourceAfterFree { resource }
                    ),
                    ..
                }] if **resource == persistent
            ),
            "unexpected free result for {persistent:#?}: {paths:#?}"
        );
    }
}

#[test]
fn separated_persistent_view_survives_free() {
    let state = successful_heap_allocation_state();
    let other = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let view = ResourceFact::view_memory(MemoryRange::new(
        other,
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(view.clone()));
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("a view of a distinct allocation should survive free");

    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::Normal(after),
            ..
        }] if after.resources().facts() == [view]
    ));
}

#[test]
fn free_of_external_allocation_forgets_cells_without_separation() {
    let allocation_base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(908_000)), 4),
    };
    let unrelated = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(908_001)), 4),
    };
    let memory = Memory::new()
        .store(unrelated.clone(), int32(37))
        .with_heap_allocation_claim(allocation_base.clone(), HeapExtent::int32(16))
        .expect("external allocation claim should be fresh");
    let resources = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(allocation_base.clone(), 16))
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            allocation_base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(4),
        )));
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", ProgramValue::pointer(allocation_base.clone()));

    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("freeing an imported allocation should execute");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(after),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("free should have one normal path: {paths:?}");
    };

    assert_eq!(
        after.memory().load(&unrelated),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
    );
    assert!(
        !after
            .memory()
            .is_deallocated_heap_address(&unrelated, &PureFactContext::new())
    );
    assert!(
        after
            .memory()
            .is_deallocated_heap_address(&allocation_base, &PureFactContext::new())
    );
    assert!(after.memory().is_deallocated_heap_address(
        &allocation_base.offset_by_int32_elements(1.into()),
        &PureFactContext::new()
    ));
}

#[test]
fn interface_heap_join_retains_potential_live_allocation() {
    let allocation_base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let retained = ExecutionState::new().with_memory(
        Memory::new()
            .with_heap_allocation_claim(allocation_base.clone(), HeapExtent::int32(16))
            .expect("the allocation claim should be fresh"),
    );
    let freed = retained.clone().with_memory(
        retained
            .memory()
            .clone()
            .free_heap_block(&allocation_base, &PureFactContext::new())
            .expect("the retained arm should be able to free the allocation"),
    );
    let siblings = [&freed, &retained];
    let freed_join =
        crate::kernel::abstract_execution_state_for_interface_join_across(&freed, &siblings, 0)
            .expect("the freed arm should abstract");
    let retained_join =
        crate::kernel::abstract_execution_state_for_interface_join_across(&retained, &siblings, 0)
            .expect("the retained arm should abstract");

    assert_eq!(freed_join, retained_join);
    let freed_join = freed_join.state;
    assert_eq!(
        freed_join.memory().live_heap_block_extent(&allocation_base),
        Some(&HeapExtent::int32(16))
    );
    assert!(
        freed_join
            .memory()
            .is_deallocated_heap_address(&allocation_base, &PureFactContext::new()),
        "the freed arm keeps an alias unsafe at the join"
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
    let paths = execute_execution_statement_paths(
        &success,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("missing-authority free should execute to a diagnostic");
    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                resource
            }),
            ..
        }] if resource.allocation().is_some()
    ));
}

#[test]
fn heap_storage_becomes_readable_only_after_a_store() {
    let success = successful_heap_allocation_state();
    let stored = execute_execution_statement_paths(
        &success,
        &program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(37),
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("an owned fresh heap cell should be writable");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(stored),
            ..
        },
    ] = stored.as_slice()
    else {
        panic!("heap store should succeed: {stored:?}");
    };
    let read = evaluate_program_expression_paths(
        stored,
        &crate::kernel::program_expression::load(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("initialized heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            ..
        }] if value == &int32(37)
    ));
}

#[test]
fn active_stable_loan_rejects_overlapping_heap_free_and_realloc() {
    let state = successful_heap_allocation_state();
    let local_native_output_1341 = state.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_1341.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    // The second int32 cell is a strict subrange of the 16-byte allocation.
    let loan = active_heap_memory_loan(MemoryRange::new(
        pointer.pointer().clone(),
        MachineTerm::constant(1),
        MachineTerm::constant(2),
    ));
    let state = state.with_loan_ledger(Some(loan));
    let freed = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("free should return a checked refusal");
    assert_heap_loan_write_rejected(&freed[0].outcome);

    let state = state.with_local("q", ProgramValue::pointer(Pointer::null()));
    let realloc = execute_execution_statement_paths(
        &state,
        &program_reallocate_then_assign(
            3,
            "q",
            ProgramType::Int32Pointer,
            vec![
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(8),
            ],
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("realloc should return a checked refusal");
    assert_heap_loan_write_rejected(&realloc[0].outcome);
}

#[test]
fn realloc_keeps_old_resources_until_result_and_transfers_them_on_success() {
    let state = successful_heap_allocation_state();
    let stored = execute_execution_statement_paths(
        &state,
        &program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(37),
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("the old allocation should be writable");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(stored),
            ..
        },
    ] = stored.as_slice()
    else {
        panic!("heap store should succeed: {stored:?}");
    };
    let state = stored
        .clone()
        .with_local("q", ProgramValue::pointer(Pointer::null()));
    let realloc_paths = execute_execution_statement_paths(
        &state,
        &program_reallocate_then_assign(
            4,
            "q",
            ProgramType::Int32Pointer,
            vec![
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(8),
            ],
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("realloc should leave one pending result");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            ..
        },
    ] = realloc_paths.as_slice()
    else {
        panic!("realloc should produce one pending path: {realloc_paths:?}");
    };
    let local_native_output_1413 = pending.locals().get_native("q");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_1413.as_deref() else {
        panic!("realloc should assign its pending result");
    };
    let local_native_output_1416 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(old_pointer)) = local_native_output_1416.as_deref() else {
        panic!("the old pointer should remain available until realloc resolves");
    };
    assert!(
        pending
            .memory()
            .heap
            .pending_reallocations
            .contains_key(pending_pointer)
    );
    assert!(
        pending
            .memory()
            .live_heap_block_extent(old_pointer)
            .is_some()
    );

    let success_assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        pointer_is_null_condition(pending_pointer.pointer().clone()),
        false,
    ));
    let success = resolve_pending_heap_allocations(pending, &success_assumptions);
    let local_native_output_1438 = success.locals().get_native("q");
    let Some(ProgramValue::Pointer(resized)) = local_native_output_1438.as_deref() else {
        panic!("successful realloc should assign a pointer");
    };
    assert_eq!(
        success.memory().live_heap_block_extent(resized.pointer()),
        Some(&HeapExtent::int32(8))
    );
    assert!(
        success
            .memory()
            .is_deallocated_heap_address(old_pointer.pointer(), &PureFactContext::new())
    );
    assert_eq!(
        success.memory().known_value(resized.pointer()),
        Some(int32(37))
    );
    assert!(
        success
            .resources()
            .facts()
            .contains(&ResourceFact::own_allocation(resized.pointer().clone(), 8,))
    );
    assert!(!success.resources().facts().iter().any(|fact| {
        fact.allocation()
            .is_some_and(|(base, _)| base == old_pointer.pointer())
    }));

    let failure_assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        pointer_is_null_condition(pending_pointer.pointer().clone()),
        true,
    ));
    let failure = resolve_pending_heap_allocations(pending, &failure_assumptions);
    assert_eq!(
        failure.locals().get_native("q").as_deref(),
        Some(&ProgramValue::pointer(Pointer::null()))
    );
    assert!(
        failure
            .memory()
            .live_heap_block_extent(old_pointer)
            .is_some()
    );
    assert!(
        failure
            .resources()
            .facts()
            .contains(&ResourceFact::own_allocation(
                old_pointer.pointer().clone(),
                16,
            ))
    );
}

#[test]
fn free_null_needs_no_allocation_resources() {
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("free(NULL) should execute");
    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::Normal(after),
            ..
        }] if **after == state
    ));
}

#[test]
fn free_preserves_a_separate_recursive_tail_with_the_same_symbolic_block() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(909_000)), 4),
    };
    let tail = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(909_001)), 4),
    };
    let tail_resource = ResourceFact::own_composite(
        "allocated_list".to_string(),
        vec![ProgramValue::pointer(tail)],
    );
    let resources = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(base.clone(), 16))
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(4),
        )))
        .unchecked_with_fact(tail_resource.clone());
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(16))
        .expect("symbolic allocation claim should be fresh");
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", ProgramValue::pointer(base));

    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("freeing a separated parent should execute");
    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::Normal(after),
            ..
        }] if after.resources().facts() == [tail_resource]
    ));
}

fn nullable_owner_contract(
    body: ProgramStatement,
) -> (ExecutionState, ProgramFunction, Vec<ProgramExpression>) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(910_000)), 4),
    };
    let pointer_value = ProgramValue::pointer(pointer.clone());
    let pointer_expression =
        SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("item"));
    let definition = CompositeResourceDefinition::new(
        "owned_item",
        vec![program_parameter("item", ProgramType::Int32Pointer)],
        Some(SpecProposition::Comparison {
            left: pointer_expression.clone(),
            operator: ComparisonOperator::NotEqual,
            right: SpecExpression::Value(ProgramValue::pointer(Pointer::null())),
        }),
        false,
        vec![
            ResourceSpec::token(
                ResourceAccessMode::Own,
                "allocation".to_string(),
                vec![
                    crate::kernel::program_expression::variable("item"),
                    ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(4))),
                ],
                vec![ProgramType::Int32Pointer, ProgramType::Int32],
            ),
            ResourceSpec::owned_memory(MemorySegment {
                base: crate::kernel::program_expression::variable("item"),
                start: crate::kernel::program_expression::int32_literal(0),
                end: crate::kernel::program_expression::int32_literal(1),
                element_width: 4,
                guard: None,
                uninitialized: false,
                value_runs: Default::default(),
            }),
        ],
        Vec::new(),
    );
    let requirement = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "owned_item".to_string(),
        vec![crate::kernel::program_expression::variable("item")],
        vec![ProgramType::Int32Pointer],
    );
    let function = program_function(
        ProgramType::Int32,
        "item_destroy",
        vec![program_parameter("item", ProgramType::Int32Pointer)],
        body,
    )
    .with_resource_summary(vec![requirement], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    )
    .with_composite_resource_definitions(vec![definition]);
    let state =
        ExecutionState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_composite("owned_item".to_string(), vec![pointer_value]),
        ));
    (
        state,
        function,
        vec![crate::kernel::program_expression::pointer_value(pointer)],
    )
}

#[test]
fn guarded_opaque_call_footprints_skip_only_inactive_segments() {
    let (_, mut function, _) = nullable_owner_contract(program_return(
        crate::kernel::program_expression::int32_literal(0),
    ));
    let active = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            "item",
        )),
        operator: ComparisonOperator::NotEqual,
        right: SpecExpression::Value(ProgramValue::pointer(Pointer::null())),
    };
    std::sync::Arc::make_mut(&mut function.contract_interface).contract_mutable = vec![
        MemorySegment::new(
            crate::kernel::program_expression::int32_literal(7),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        )
        .with_guard(active),
    ];
    let environment = ExecutionEnvironment::new()
        .with_function(function.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: function.clone(),
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });

    let null = ProgramValue::pointer(Pointer::null());
    let null_state = ExecutionState::new()
        .with_local("result", ProgramValue::Int32(0u32.into()))
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_composite("owned_item".to_string(), vec![null]),
        ));
    let null_paths = execute_execution_statement_paths(
        &null_state,
        &program_call_then_assign(
            5,
            "result",
            "item_destroy",
            vec![crate::kernel::program_expression::int32_literal(0)],
        ),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::default(),
    )
    .expect("an inactive malformed footprint should not be evaluated");
    assert!(matches!(
        null_paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::Normal(_),
            ..
        }]
    ));

    let nonnull = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull_state = ExecutionState::new()
        .with_local("result", ProgramValue::Int32(0u32.into()))
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_composite(
                "owned_item".to_string(),
                vec![ProgramValue::pointer(nonnull.clone())],
            ),
        ));
    let nonnull_paths = execute_execution_statement_paths(
        &nonnull_state,
        &program_call_then_assign(
            6,
            "result",
            "item_destroy",
            vec![crate::kernel::program_expression::pointer_value(nonnull)],
        ),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::default(),
    )
    .expect("an active malformed footprint should produce a local diagnostic");
    assert!(matches!(
        nonnull_paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
            ..
        }] if message.contains("could not evaluate mutable footprint")
    ));
}

#[test]
fn contract_certification_splits_undecided_conditional_resource_guards() {
    let (state, function, arguments) = nullable_owner_contract(program_seq(
        program_heap_free(crate::kernel::program_expression::variable("item")),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    ));
    let execution = certify_contract_with_kernel_artifacts(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    assert!(program_verified_function_contract_claims(&function, &execution).is_some());
}

#[test]
fn contract_certification_splits_undecided_conditional_produced_resources() {
    let (state, function, arguments) = nullable_owner_contract(program_return(
        crate::kernel::program_expression::int32_literal(0),
    ));
    let guard = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            "item",
        )),
        operator: ComparisonOperator::NotEqual,
        right: SpecExpression::Value(ProgramValue::pointer(Pointer::null())),
    };
    let resource = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "owned_item".to_string(),
        vec![crate::kernel::program_expression::variable("item")],
        vec![ProgramType::Int32Pointer],
    );
    let function =
        function.with_resource_summary(vec![resource.clone()], vec![resource.with_guard(guard)]);
    let execution = certify_contract_with_kernel_artifacts(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    assert!(program_verified_function_contract_claims(&function, &execution).is_some());
}

#[test]
fn conditional_resource_certification_checks_the_unsafe_case_too() {
    let (state, function, arguments) = nullable_owner_contract(program_seq(
        program_heap_free(crate::kernel::program_expression::variable("item")),
        program_seq(
            program_heap_free(crate::kernel::program_expression::variable("item")),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
    ));
    let execution = certify_contract_with_kernel_artifacts(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    let error = program_unverified_function_contract_claims(&function, &execution)
        .expect_err("the nonnull double-free case must invalidate certification");
    assert!(
        error.contains("cannot free an allocation whose lifetime has already ended"),
        "unexpected failure: {error}"
    );
}

#[test]
fn interior_free_and_store_after_free_are_rejected() {
    let success = successful_heap_allocation_state();
    let interior = execute_execution_statement_paths(
        &success,
        &program_heap_free(crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        )),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("interior free should produce a diagnostic");
    assert!(matches!(
        interior.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::RuntimeError(RuntimeError::InvalidFree(
                InvalidFree::InteriorPointer
            )),
            ..
        }]
    ));

    let freed = execute_execution_statement_paths(
        &success,
        &program_heap_free(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("valid free should execute");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(freed),
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("valid free should succeed: {freed:?}");
    };
    let store = execute_execution_statement_paths(
        freed,
        &program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("store-after-free should produce undefined behavior");
    assert!(matches!(
        store.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
            ..
        }]
    ));
}

#[test]
fn returning_malloc_result_resolves_null_and_success_outcomes() {
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
    let statement = program_seq(
        program_heap_allocate("p", 16),
        program_return(crate::kernel::program_expression::variable("p")),
    );
    let paths = execute_execution_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
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
        let StatementOutcome::Return { value, state } = path.outcome else {
            panic!("malloc return should not produce a diagnostic");
        };
        let ProgramValue::Pointer(pointer) = value.clone().into_native() else {
            panic!("malloc should return a pointer");
        };
        assert!(!state.memory().has_pending_heap_allocation());
        if pointer.pointer() == &Pointer::null() {
            saw_failure = true;
            assert!(state.resources().facts().is_empty());
        } else {
            saw_success = true;
            assert!(matches!(pointer.block, PointerBlock::Heap(_)));
            assert_eq!(
                state.memory().live_heap_block_extent(&pointer),
                Some(&HeapExtent::int32(16))
            );
            assert!(
                state
                    .resources()
                    .facts()
                    .contains(&ResourceFact::own_allocation(pointer.pointer().clone(), 16))
            );
        }
    }
    assert!(saw_success && saw_failure);
}

#[test]
fn unreturned_unresolved_malloc_result_cannot_cross_a_return() {
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
    let statement = program_seq(
        program_heap_allocate("p", 16),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let paths = execute_execution_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("unresolved allocation should execute to a diagnostic");
    assert!(matches!(
        paths.as_slice(),
        [StatementExecutionPath {
            outcome: StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome),
            ..
        }]
    ));
}

/// Differently spelled pointer blocks are not separate unless proven so: a
/// contract-returned pointer can equal an allocation base while retaining
/// another block spelling (`ensures result == p`). A free going through the
/// allocation's own spelling must retire the allocation under the aliased
/// spelling too — no cached cell, no zeroed reading, and the load reports the
/// deallocation — while a structurally fresh, proven-distinct allocation
/// loses nothing.
#[test]
fn freeing_through_one_spelling_retires_the_equal_spelling_too() {
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(921_000)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = Pointer {
        block: PointerBlock::Heap(921_001),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fresh = Pointer {
        block: PointerBlock::Heap(921_002),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), base.clone()),
        true,
    ));

    let memory = Memory::new()
        .store(alias.clone(), int32(7))
        .with_block(fresh.block.clone(), 8)
        .store(fresh.clone(), int32(11))
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(4))
        .expect("the allocation claim should be fresh")
        .with_block(base.block.clone(), 4);
    let before = memory;
    assert!(before.is_live_heap_address(&base, &assumptions));
    assert!(before.is_live_heap_address(&alias, &assumptions));
    let freed = before
        .free_heap_block(&base, &assumptions)
        .expect("the live allocation base frees");

    assert!(
        freed.is_deallocated_heap_address(&alias, &assumptions),
        "the load through the equal spelling reads freed memory after the free"
    );
    assert_eq!(
        freed.load(&alias),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
        "no cached cell survives under the aliased spelling"
    );
    assert!(
        !freed.is_zeroed_heap_address(&alias, 4, &assumptions),
        "no zeroed status survives under the aliased spelling"
    );
    assert!(
        freed.is_deallocated_heap_address(&base, &assumptions)
            && freed.load(&base)
                == ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
        "the allocation's own spelling is deallocated and unavailable"
    );
    assert_eq!(
        freed.load(&fresh),
        ExpressionOutcome::Value(int32(11)),
        "a structurally fresh, proven-distinct allocation is unaffected"
    );
}

/// A contract that consumes an allocation without deciding continuity may
/// have freed it. Its former calloc status cannot make a later read concrete,
/// including through an equal pointer spelling.
#[test]
fn contract_retire_forgets_zeroed_reading_and_records_the_change() {
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_allocate_sized_with_zeroed(
            "p",
            crate::kernel::program_expression::int32_literal(4),
            true,
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("calloc-shaped allocation should execute");
    let StatementOutcome::Normal(pending) = &paths[0].outcome else {
        panic!("allocation should produce a pending outcome");
    };
    let local_native_output_1985 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_1985.as_deref() else {
        panic!("allocation should assign a pending pointer");
    };
    let success = resolve_pending_heap_allocations(
        pending,
        &PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.pointer().clone(), Pointer::null()),
            false,
        )),
    );
    let local_native_output_1995 = success.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_1995.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let base = pointer.pointer().clone();
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(922_100)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), base.clone()),
        true,
    ));
    assert!(
        success
            .memory()
            .is_zeroed_heap_address(&alias, 4, &assumptions)
    );
    let retired = success
        .memory()
        .clone()
        .retire_contract_heap_allocation_claim(&base, &MachineTerm::constant(4), &assumptions);
    assert!(
        !retired.is_zeroed_heap_address(&base, 4, &assumptions)
            && !retired.is_zeroed_heap_address(&alias, 4, &assumptions),
        "retiring an allocation must forget its blanket zeroed reading"
    );
    assert!(matches!(
        intern_memory_ref(&retired).derivation().as_deref(),
        Some(MemoryDerivation::ContractAllocationRetired { allocation_base, .. })
            if allocation_base == &base
    ));
    let after_call = success.with_memory(retired);
    let read = evaluate_program_expression_paths(
        &after_call,
        &crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        &assumptions,
        &mut ExecutionBudget::default(),
    )
    .expect("post-retirement load should resolve");
    assert!(
        !matches!(
            read.as_slice(),
            [ExpressionPath {
                outcome: ExpressionOutcome::Value(value),
                ..
            }] if value == &int32(0)
        ),
        "the possible deallocation cannot resolve to a concrete zero"
    );
}

/// A union overlay invalidates a raw cell at a proven-equal address, even
/// when the raw cell uses another pointer spelling.
#[test]
fn store_union_forgets_aliased_raw_cell() {
    let base = Pointer {
        block: PointerBlock::Heap(922_001),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(922_000)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), base.clone()),
        true,
    ));
    let memory = Memory::new().store(alias.clone(), int32(7)).store_union(
        base.clone(),
        ProgramType::Int16,
        crate::kernel::int16(42),
    );
    assert!(memory.has_union_overlay_at(&base));
    assert_eq!(memory.known_value(&alias), None);
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::pointer_equal(alias.clone(), base.clone()),
            true,
        )
    ));

    let memory = Memory::new()
        .store_union(base.clone(), ProgramType::Int16, crate::kernel::int16(42))
        .store_with_context(alias.clone(), int32(7), &assumptions);
    assert_eq!(memory.known_value(&alias), Some(int32(7)));
    assert!(!memory.has_union_overlay_at(&base));
}

#[test]
fn logical_heap_value_does_not_initialize_a_c_read() {
    let state = successful_heap_allocation_state();
    let local_native_output_2087 = state.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2087.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let logical = crate::kernel::eval::evaluate_logical_memory_load_paths(
        state.memory(),
        pointer.pointer().clone(),
        ProgramType::Int32,
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
    );
    let [path] = logical.as_slice() else {
        panic!("one logical read");
    };
    let ExpressionOutcome::Value(ProgramValue::Int32(value)) = &path.outcome else {
        panic!("logical read must have a value");
    };
    assert!(path.obligations.is_empty());
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::equal(value.clone(), MachineTerm::constant(7)),
        true,
    ));
    assert!(!assumptions.proves_memory_read_defined(
        state.memory(),
        pointer.pointer(),
        ProgramType::Int32
    ));
    let reads = evaluate_program_expression_paths(
        &state,
        &crate::kernel::program_expression::load(crate::kernel::program_expression::variable("p")),
        &assumptions,
        &mut ExecutionBudget::default(),
    )
    .expect("C evaluation should report the invalid read");
    assert!(matches!(
        reads.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            ..
        }]
    ));
}

#[test]
fn explicit_read_validity_is_typed_and_does_not_cross_havoc() {
    let state = successful_heap_allocation_state();
    let local_native_output_2133 = state.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2133.as_deref() else {
        panic!("allocated pointer");
    };
    let address = pointer.pointer().clone();
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryReadDefined {
        memory: state.memory().clone(),
        pointer: address.clone(),
        value_type: ProgramType::Int32,
    });
    assert!(assumptions.proves_memory_read_defined(state.memory(), &address, ProgramType::Int32));
    assert!(!assumptions.has_memory_read_defined_evidence(
        state.memory(),
        &address,
        ProgramType::Int64
    ));
    let range = MemoryRange::new(
        address.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let changed = state.memory().clone().with_call_memory_havoc(
        Variable(903),
        &[range],
        &PureFactContext::new(),
        None,
    );
    assert!(!assumptions.has_memory_read_defined_evidence(&changed, &address, ProgramType::Int32));
    let freed = state
        .memory()
        .clone()
        .free_heap_block(&address, &PureFactContext::new())
        .unwrap();
    let stale = Proposition::MemoryReadDefined {
        memory: freed,
        pointer: address,
        value_type: ProgramType::Int32,
    };
    assert!(!crate::kernel::PureFactContext::settles_exactly(
        &assumptions,
        &stale
    ));
}

#[test]
fn read_validity_transports_checked_aliases_without_crossing_writes_or_retirement() {
    let state = successful_heap_allocation_state();
    let local_native_output_2175 = state.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2175.as_deref() else {
        panic!("allocated pointer");
    };
    let address = pointer.pointer().clone();
    let alias = Pointer::symbolic(Variable(940_001));
    let unrelated = Pointer {
        block: PointerBlock::Heap(940_002),
        offset: PointerOffsetTerm::Constant(0),
    };
    let validity = Proposition::MemoryReadDefined {
        memory: state.memory().clone(),
        pointer: address.clone(),
        value_type: ProgramType::Int32,
    };
    let bare = PureFactContext::new().assume_proposition(validity);
    assert!(!bare.has_memory_read_defined_evidence(state.memory(), &alias, ProgramType::Int32));
    let assumptions = bare.assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(alias.clone(), address.clone()),
        true,
    ));
    assert!(assumptions.has_memory_read_defined_evidence(
        state.memory(),
        &alias,
        ProgramType::Int32
    ));
    assert!(!assumptions.has_memory_read_defined_evidence(
        state.memory(),
        &alias,
        ProgramType::Int64
    ));
    assert!(!assumptions.has_memory_read_defined_evidence(
        state.memory(),
        &alias,
        ProgramType::UInt32
    ));
    let changed = state.memory().clone().store(unrelated, int32(5));
    assert!(assumptions.has_memory_read_defined_evidence(&changed, &alias, ProgramType::Int32));
    let range = MemoryRange::new(alias.clone(), 0u32.into(), 1u32.into());
    let havoc =
        changed
            .clone()
            .with_call_memory_havoc(Variable(940_003), &[range], &assumptions, None);
    assert!(!assumptions.has_memory_read_defined_evidence(&havoc, &alias, ProgramType::Int32));
    let freed = changed.free_heap_block(&address, &assumptions).unwrap();
    assert!(!assumptions.has_memory_read_defined_evidence(&freed, &alias, ProgramType::Int32));
}

#[test]
fn read_validity_transports_field_offsets_through_equal_base_pointers() {
    let base = Pointer {
        block: PointerBlock::Heap(943_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(943_001));
    let field = base.offset_by_bytes(4);
    let alias_field = alias.offset_by_bytes(4);
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(8))
        .unwrap();
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::MemoryReadDefined {
            memory: memory.clone(),
            pointer: field.clone(),
            value_type: ProgramType::Int32,
        })
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        ));
    assert!(assumptions.has_memory_read_defined_evidence(
        &memory,
        &alias_field,
        ProgramType::Int32
    ));
    assert!(!assumptions.has_memory_read_defined_evidence(&memory, &alias, ProgramType::Int32));
    assert!(!assumptions.has_memory_read_defined_evidence(
        &memory,
        &alias_field,
        ProgramType::Int64
    ));
    let changed = memory.clone().store(
        Pointer {
            block: PointerBlock::Heap(943_002),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(5),
    );
    assert!(assumptions.has_memory_read_defined_evidence(
        &changed,
        &alias_field,
        ProgramType::Int32
    ));
    let havoc = changed.clone().with_call_memory_havoc(
        Variable(943_003),
        &[MemoryRange::new(
            alias_field.clone(),
            0u32.into(),
            1u32.into(),
        )],
        &assumptions,
        None,
    );
    assert!(!assumptions.has_memory_read_defined_evidence(
        &havoc,
        &alias_field,
        ProgramType::Int32
    ));
    let freed = changed.free_heap_block(&base, &assumptions).unwrap();
    assert!(!assumptions.has_memory_read_defined_evidence(
        &freed,
        &alias_field,
        ProgramType::Int32
    ));
}

#[test]
fn naming_an_uninitialized_local_cell_does_not_initialize_it() {
    let address = Pointer {
        block: "local:uninitialized".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("local:uninitialized", 4);
    let name = canonical_form_of_load(
        intern_memory(memory.clone()),
        address.clone(),
        crate::kernel::LoadKind::Int32,
    );
    let named = memory.materialize_named_cell(address.clone(), ProgramValue::Int32(name));
    let state = ExecutionState::new()
        .with_memory(named)
        .with_local("p", ProgramValue::pointer(address));
    let reads = evaluate_program_expression_paths(
        &state,
        &crate::kernel::program_expression::load(crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        reads.as_slice(),
        [ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            ..
        }]
    ));
}

/// `p[0] = 5; p[1] = 5; p[u] = 7;` under `0 <= u < 2` over fresh heap
/// storage, as the statement executor writes it: the unplaced store forgets
/// both cached elements and, a store never de-initializing, keeps their
/// initialization marks. A read of `p[0]` is then an initialized element on
/// both alias cases; a read of the never-written `p[2]` stays undefined.
#[test]
fn an_unplaced_heap_store_keeps_the_elements_it_may_alias_initialized() {
    let allocated = successful_heap_allocation_state();
    let local_native_output_2298 = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2298.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let base = pointer.pointer().clone();
    let index = MachineTerm::Variable(Variable(925_001));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), MachineTerm::constant(2)),
            true,
        );
    let unplaced = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let store = |memory: Memory, pointer: Pointer, value: u32| {
        memory
            .without_possible_aliasing_cells(&pointer, 4, &assumptions)
            .store_with_context(pointer, int32(value), &assumptions)
    };
    let memory = store(allocated.memory().clone(), base.clone(), 5);
    let memory = store(memory, base.offset_by_bytes(4), 5);
    let memory = store(memory, unplaced, 7);
    assert!(!memory.has_known_cell_at(&base));
    let state = allocated.clone().with_memory(memory);
    let read = |element: u32| {
        evaluate_program_expression_paths(
            &state,
            &crate::kernel::program_expression::index(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(element),
            ),
            &assumptions,
            &mut ExecutionBudget::default(),
        )
        .expect("the read evaluates")
    };
    let first = read(0);
    assert_eq!(first.len(), 2, "the read splits on the alias: {first:?}");
    assert!(
        first
            .iter()
            .all(|path| matches!(path.outcome, ExpressionOutcome::Value(_))),
        "an initialized element whose value is forgotten reads as a value: {first:?}"
    );
    assert!(
        read(2).iter().any(|path| matches!(
            path.outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
        )),
        "a never-written element stays uninitialized"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/heap_tests.rs");
}

#[test]
fn fresh_heap_struct_binding_checks_extent_alignment_and_resolution() {
    let _session = crate::kernel::VerificationSession::enter();
    let class = crate::kernel::effective_type::CAccessClass::Struct(
        crate::kernel::effective_type::CStructClass::opaque("node"),
    );
    for (bytes, alignment, typed) in [(8, 8, true), (16, 8, true), (1, 8, false), (8, 32, false)] {
        for zeroed in [false, true] {
            let state =
                ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
            let paths = execute_execution_statement_paths(
                &state,
                &ProgramStatement::HeapAllocate {
                    target: "p".to_string(),
                    bytes: crate::kernel::program_expression::int32_literal(bytes),
                    zeroed,
                    object_type: Some((class.clone(), 8, alignment)),
                    ends_program_on_failure: false,
                },
                &PureFactContext::new(),
                ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            let [
                StatementExecutionPath {
                    outcome: StatementOutcome::Normal(pending),
                    ..
                },
            ] = paths.as_slice()
            else {
                panic!("one pending allocation expected");
            };
            let local_native_output_2389 = pending.locals().get_native("p");
            let Some(ProgramValue::Pointer(pointer)) = local_native_output_2389.as_deref() else {
                panic!("pointer expected")
            };
            assert_eq!(pointer.object_class(), typed.then(|| class.clone()));
            let null = ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null());
            for succeeds in [false, true] {
                let resolved = resolve_pending_heap_allocations(
                    pending,
                    &PureFactContext::new().assume_condition(null.clone(), !succeeds),
                );
                assert!(resolved.memory.heap.pending_object_classes.is_empty());
                let local_native_output_2400 = resolved.locals().get_native("p");
                let Some(ProgramValue::Pointer(value)) = local_native_output_2400.as_deref() else {
                    panic!("resolved pointer expected")
                };
                if succeeds {
                    assert_eq!(
                        resolved.memory.declared_class(value.pointer()),
                        typed.then(|| class.clone())
                    );
                    assert_eq!(value.object_class(), typed.then(|| class.clone()));
                } else {
                    assert_eq!(value.pointer(), &Pointer::null());
                    assert!(resolved.memory.heap.live_allocations.is_empty());
                }
            }
        }
    }
}

// An allocation whose failure ends the program, as a C++ `new` in a
// `noexcept` function, continues on one path, and that path knows its pointer
// is not null: it resolves to a live block without a null test.
#[test]
fn an_allocation_that_ends_the_program_on_failure_continues_only_on_success() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(Pointer::null()));
    let paths = execute_execution_statement_paths(
        &state,
        &ProgramStatement::HeapAllocate {
            target: "p".to_string(),
            bytes: crate::kernel::program_expression::int32_literal(8),
            zeroed: false,
            object_type: None,
            ends_program_on_failure: true,
        },
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            facts,
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("one allocation path expected");
    };
    let local_native_output_2449 = pending.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2449.as_deref() else {
        panic!("pointer expected")
    };
    let null = ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null());
    let context = crate::kernel::reasoning::assumptions_with_path_context(
        &PureFactContext::new(),
        facts,
        &[],
    );
    assert_eq!(context.decide(&null), Some(false));
    let resolved = resolve_pending_heap_allocations(pending, &context);
    let local_native_output_2460 = resolved.locals().get_native("p");
    let Some(ProgramValue::Pointer(value)) = local_native_output_2460.as_deref() else {
        panic!("resolved pointer expected")
    };
    assert_ne!(value.pointer(), &Pointer::null());
    assert_eq!(resolved.memory.heap.live_allocations.len(), 1);
}

mod free_base_alias_tests;

/// `p = malloc(n * 4)` with a `size_t` count `n`, under `facts`: its paths
/// and, for its one pending outcome, the success state.
fn size_t_heap_allocation(
    facts: &[ConditionTerm],
) -> (Vec<StatementExecutionPath>, Option<ExecutionState>) {
    size_t_heap_allocation_with_zeroed(facts, false)
}

/// `p = malloc(n * 4u64)`, or `p = calloc(n, 4u64)` when `zeroed`, for a
/// `size_t` `n` under `facts`; with its success resolved when it has one
/// normal path.
fn size_t_heap_allocation_with_zeroed(
    facts: &[ConditionTerm],
    zeroed: bool,
) -> (Vec<StatementExecutionPath>, Option<ExecutionState>) {
    let n = MachineTerm::Variable(Variable(1 << 40));
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_local("p", ProgramValue::pointer(Pointer::null()))
        .with_local("n", ProgramValue::UInt64(n));
    let assumptions = facts
        .iter()
        .fold(PureFactContext::new(), |assumptions, fact| {
            assumptions.assume_proposition(Proposition::ConditionIs(fact.clone(), true))
        });
    let paths = execute_execution_statement_paths(
        &state,
        &program_heap_allocate_sized_with_zeroed(
            "p",
            ProgramExpression::Multiply(
                Box::new(crate::kernel::program_expression::variable("n")),
                Box::new(crate::kernel::program_expression::uint64_literal(4)),
            ),
            zeroed,
        ),
        &assumptions,
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("a size_t allocation should execute");
    let success = match paths.as_slice() {
        [
            StatementExecutionPath {
                outcome: StatementOutcome::Normal(pending),
                ..
            },
        ] => {
            let local_native_output_2513 = pending.locals().get_native("p");
            let Some(ProgramValue::Pointer(pointer)) = local_native_output_2513.as_deref() else {
                panic!("allocation should assign a pointer");
            };
            let not_null = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
                false,
            ));
            Some(resolve_pending_heap_allocations(pending, &not_null))
        }
        _ => None,
    };
    (paths, success)
}

/// A bounded `size_t` element count makes a 64-bit block: the exact `uint64`
/// product is its extent, its token holds a `uint64`, and its owned range is
/// wide, counted in elements (`design/heap-extents.md`, stage 2).
#[test]
fn a_bounded_size_t_element_count_makes_a_64_bit_block() {
    let n = MachineTerm::Variable(Variable(1 << 40));
    let (_, success) = size_t_heap_allocation(&[
        ConditionTerm::uint64_greater_than(n.clone(), MachineTerm::uint64_constant(0)),
        ConditionTerm::uint64_less_equal(n.clone(), MachineTerm::uint64_constant(100)),
    ]);
    let success = success.expect("a bounded count allocates");
    let local_native_output_2538 = success.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2538.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    let extent = HeapExtent::new(
        MachineTerm::uint64_multiply(n.clone(), MachineTerm::uint64_constant(4)),
        HeapExtentKind::UInt64,
    );
    assert_eq!(
        success.memory().live_heap_block_extent(pointer.pointer()),
        Some(&extent)
    );
    let facts = success.resources().facts();
    assert!(facts.contains(&ResourceFact::own_heap_allocation(
        pointer.pointer().clone(),
        &extent
    )));
    let range = extent.range(pointer.pointer().clone(), n, 4);
    assert_eq!(range.kind(), RangeIndexKind::UInt64);
    assert!(facts.contains(&ResourceFact::own_memory(range)));
}

/// A `size_t` count with no upper bound is refused, and so is one whose
/// product the facts do not prove exact; neither is narrowed or wrapped.
#[test]
fn an_unbounded_size_t_element_count_is_refused() {
    let n = MachineTerm::Variable(Variable(1 << 40));
    for facts in [
        vec![ConditionTerm::uint64_greater_than(
            n.clone(),
            MachineTerm::uint64_constant(0),
        )],
        vec![
            ConditionTerm::uint64_greater_than(n.clone(), MachineTerm::uint64_constant(0)),
            ConditionTerm::uint64_less_equal(n.clone(), MachineTerm::uint64_constant(1 << 62)),
        ],
    ] {
        let (paths, _) = size_t_heap_allocation(&facts);
        assert!(matches!(
            paths.as_slice(),
            [StatementExecutionPath {
                outcome: StatementOutcome::RuntimeError(RuntimeError::HeapAllocationSize),
                ..
            }]
        ));
    }
}

/// A count the facts fix where `n * 4` wraps is C's wrapped product: a
/// 4-byte block, not `n` elements.
#[test]
fn a_wrapping_size_t_product_is_the_wrapped_block() {
    let n = MachineTerm::Variable(Variable(1 << 40));
    let (_, success) = size_t_heap_allocation(&[ConditionTerm::uint64_equal(
        n,
        MachineTerm::uint64_constant((1 << 62) + 1),
    )]);
    let success = success.expect("the wrapped product allocates");
    let local_native_output_2595 = success.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2595.as_deref() else {
        panic!("allocation should assign a pointer");
    };
    assert_eq!(
        success.memory().live_heap_block_extent(pointer.pointer()),
        Some(&HeapExtent::int32(4))
    );
}

/// `calloc(n, 4)` with a bounded `size_t` count makes a zeroed 64-bit block:
/// the exact `uint64` product is its extent and it reads as zero
/// (`design/heap-extents.md`, stage 4).
#[test]
fn a_bounded_size_t_calloc_count_makes_a_zeroed_64_bit_block() {
    let n = MachineTerm::Variable(Variable(1 << 40));
    let (_, success) = size_t_heap_allocation_with_zeroed(
        &[
            ConditionTerm::uint64_greater_than(n.clone(), MachineTerm::uint64_constant(0)),
            ConditionTerm::uint64_less_equal(n.clone(), MachineTerm::uint64_constant(100)),
        ],
        true,
    );
    let success = success.expect("a bounded calloc count allocates");
    let local_native_output_2618 = success.locals().get_native("p");
    let Some(ProgramValue::Pointer(pointer)) = local_native_output_2618.as_deref() else {
        panic!("calloc should assign a pointer");
    };
    let extent = HeapExtent::new(
        MachineTerm::uint64_multiply(n, MachineTerm::uint64_constant(4)),
        HeapExtentKind::UInt64,
    );
    assert_eq!(
        success.memory().live_heap_block_extent(pointer.pointer()),
        Some(&extent)
    );
    assert!(
        success
            .resources()
            .facts()
            .contains(&ResourceFact::own_heap_allocation(
                pointer.pointer().clone(),
                &extent
            ))
    );
    assert!(
        success
            .memory()
            .is_zeroed_heap_address(pointer.pointer(), 4, &PureFactContext::new())
    );
}

/// calloc never forms its product: a count the facts fix where `n * 4`
/// would wrap is refused, not the wrapped block `malloc` makes, and so is
/// a count with no upper bound.
#[test]
fn a_size_t_calloc_count_whose_product_may_wrap_is_refused() {
    let n = MachineTerm::Variable(Variable(1 << 40));
    for facts in [
        vec![ConditionTerm::uint64_equal(
            n.clone(),
            MachineTerm::uint64_constant((1 << 62) + 1),
        )],
        vec![ConditionTerm::uint64_greater_than(
            n.clone(),
            MachineTerm::uint64_constant(0),
        )],
    ] {
        let (paths, _) = size_t_heap_allocation_with_zeroed(&facts, true);
        assert!(
            matches!(
                paths.as_slice(),
                [StatementExecutionPath {
                    outcome: StatementOutcome::RuntimeError(RuntimeError::HeapAllocationSize),
                    ..
                }]
            ),
            "{paths:?}"
        );
    }
}

/// `realloc(p, m * 4u64)` of a 64-bit block to a bounded `size_t` count:
/// the old token and wide range are consumed, and the new block has the
/// exact 64-bit extent `m * 4u64` and a wide range.
#[test]
fn a_64_bit_block_reallocates_to_a_64_bit_size() {
    let n = MachineTerm::Variable(Variable(1 << 40));
    let m = MachineTerm::Variable(Variable((1 << 40) + 1));
    let facts = [
        ConditionTerm::uint64_greater_than(n.clone(), MachineTerm::uint64_constant(0)),
        ConditionTerm::uint64_less_equal(n.clone(), MachineTerm::uint64_constant(100)),
        ConditionTerm::uint64_greater_than(m.clone(), MachineTerm::uint64_constant(0)),
        ConditionTerm::uint64_less_equal(m.clone(), MachineTerm::uint64_constant(200)),
    ];
    let (_, allocated) = size_t_heap_allocation(&facts);
    let allocated = allocated
        .expect("a bounded count allocates")
        .with_local("q", ProgramValue::pointer(Pointer::null()))
        .with_local("m", ProgramValue::UInt64(m.clone()));
    let local_native_output_2693 = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(old_pointer)) = local_native_output_2693.as_deref() else {
        panic!("malloc should assign a pointer");
    };
    let old_pointer = old_pointer.pointer().clone();
    let assumptions = facts
        .iter()
        .fold(PureFactContext::new(), |assumptions, fact| {
            assumptions.assume_proposition(Proposition::ConditionIs(fact.clone(), true))
        });
    let paths = execute_execution_statement_paths(
        &allocated,
        &program_reallocate_then_assign(
            7,
            "q",
            ProgramType::Int32Pointer,
            vec![
                crate::kernel::program_expression::variable("p"),
                ProgramExpression::Multiply(
                    Box::new(crate::kernel::program_expression::variable("m")),
                    Box::new(crate::kernel::program_expression::uint64_literal(4)),
                ),
            ],
        ),
        &assumptions,
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("a 64-bit realloc should execute");
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("realloc should produce one pending path: {paths:?}");
    };
    let local_native_output_2726 = pending.locals().get_native("q");
    let Some(ProgramValue::Pointer(pending_pointer)) = local_native_output_2726.as_deref() else {
        panic!("realloc should assign a pending pointer");
    };
    let success = resolve_pending_heap_allocations(
        pending,
        &assumptions.assume_proposition(Proposition::ConditionIs(
            pointer_is_null_condition(pending_pointer.pointer().clone()),
            false,
        )),
    );
    let local_native_output_2736 = success.locals().get_native("q");
    let Some(ProgramValue::Pointer(resized)) = local_native_output_2736.as_deref() else {
        panic!("successful realloc should assign a heap pointer");
    };
    let extent = HeapExtent::new(
        MachineTerm::uint64_multiply(m.clone(), MachineTerm::uint64_constant(4)),
        HeapExtentKind::UInt64,
    );
    assert_eq!(
        success.memory().live_heap_block_extent(resized.pointer()),
        Some(&extent)
    );
    assert_eq!(success.memory().live_heap_block_extent(&old_pointer), None);
    let old_extent = HeapExtent::new(
        MachineTerm::uint64_multiply(n.clone(), MachineTerm::uint64_constant(4)),
        HeapExtentKind::UInt64,
    );
    let facts = success.resources().facts();
    assert!(!facts.contains(&ResourceFact::own_heap_allocation(
        old_pointer.clone(),
        &old_extent
    )));
    assert!(!facts.contains(&ResourceFact::own_memory(old_extent.range(
        old_pointer,
        n,
        4
    ))));
    assert!(facts.contains(&ResourceFact::own_heap_allocation(
        resized.pointer().clone(),
        &extent
    )));
    let range = extent.range(resized.pointer().clone(), m, 4);
    assert_eq!(range.kind(), RangeIndexKind::UInt64);
    assert!(facts.contains(&ResourceFact::own_memory(range)));
}

#[test]
fn viewability_alone_cannot_certify_initialization_of_external_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(9_492_101));
    for value_type in [
        ProgramType::UInt8,
        ProgramType::Int32,
        ProgramType::Int32Pointer,
    ] {
        for initialized in [false, true] {
            let mut memory = Memory::new();
            if initialized {
                memory = memory.with_initialized_object(&pointer, value_type.byte_width());
            }
            let assumptions =
                PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: pointer.clone(),
                    bytes: MachineTerm::constant(value_type.byte_width()),
                    wide: false,
                });
            assert_eq!(
                assumptions.proves_memory_read_defined(&memory, &pointer, value_type),
                initialized
            );
        }
    }
}

#[test]
fn typed_read_initialization_accepts_only_complete_cached_byte_coverage() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(9_492_102));
    for count in [0, 1, 2] {
        let memory = Memory::new().with_seeded_cells(
            pointer.clone(),
            4,
            ProgramType::Int32,
            0,
            count,
            crate::kernel::intern_memory(Memory::new()),
        );
        let context = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: MachineTerm::constant(8),
            wide: false,
        });
        assert_eq!(
            context.proves_memory_read_defined(&memory, &pointer, ProgramType::Int32Pointer),
            count == 2
        );
    }
}
