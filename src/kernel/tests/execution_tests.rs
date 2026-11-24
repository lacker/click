use super::*;
use crate::kernel::borrows::BorrowLedger;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{constant_u32, int32_constant};
use std::sync::Arc;

#[test]
// Const construction must initialize once, freeze aliases, and retain declared storage identity.
fn scalar_initialization_freezes_storage_and_preserves_lifetime() {
    let _session = crate::kernel::VerificationSession::enter();
    crate::kernel::set_never_address_taken_locals(BTreeSet::from(["x".into()]));
    let execute = |state: &ExecutionState, statement: &ProgramStatement| {
        execute_execution_statement_paths(
            state,
            statement,
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let declaration = program_declare_initialized(
        "x",
        ProgramType::Int32,
        crate::kernel::program_expression::int32_literal(7),
        false,
        false,
        true,
        false,
    );
    let state = normal_state(&execute(&ExecutionState::new(), &declaration));
    let pointer = state.locals.slot("x").unwrap().clone();
    assert!(state.memory.is_read_only_block(&pointer.base));
    assert!(state.memory.requires_explicit_scalar_ownership(&pointer));
    assert_eq!(state.locals.get_native("x").as_deref(), Some(&int32(7)));
    assert!(matches!(
        execute(
            &state,
            &program_assign("x", crate::kernel::program_expression::int32_literal(9))
        )[0]
        .outcome,
        StatementOutcome::UndefinedBehavior(_)
    ));
    // Even an unqualified forged pointer cannot write the read-only allocation.
    assert!(matches!(
        execute(
            &state,
            &program_typed_store(
                crate::kernel::program_expression::typed_pointer_value(
                    pointer.clone(),
                    ProgramType::Int32Pointer
                ),
                crate::kernel::program_expression::int32_literal(9),
                ProgramType::Int32
            )
        )[0]
        .outcome,
        StatementOutcome::UndefinedBehavior(_)
    ));
    let replaced = normal_state(&execute(&state, &declaration));
    assert_ne!(pointer, *replaced.locals.slot("x").unwrap());
    assert!(matches!(
        execute(
            &replaced,
            &program_return(crate::kernel::program_expression::typed_load(
                crate::kernel::program_expression::typed_pointer_value(
                    pointer,
                    ProgramType::Int32Pointer
                ),
                ProgramType::Int32
            ))
        )[0]
        .outcome,
        StatementOutcome::UndefinedBehavior(_)
    ));
    let unwritten = normal_state(&execute(
        &ExecutionState::new(),
        &program_declare("u", ProgramType::Int32),
    ));
    assert!(!matches!(
        execute(
            &unwritten,
            &program_declare_initialized(
                "x",
                ProgramType::Int32,
                crate::kernel::program_expression::variable("u"),
                false,
                false,
                true,
                false
            )
        )[0]
        .outcome,
        StatementOutcome::Normal(_)
    ));
}

#[test]
fn whole_function_execution_resumes_a_direct_forward_goto_target() {
    let target = ControlTargetId(0);
    let target_statement = program_return(crate::kernel::program_expression::variable("x"));
    let function = program_function(
        ProgramType::Int32,
        "forward",
        vec![program_parameter("x", ProgramType::Int32)],
        program_seq(
            program_goto(target),
            program_seq(
                program_return(crate::kernel::program_expression::int32_literal(99)),
                target_statement.clone(),
            ),
        ),
    )
    .with_control_targets(BTreeMap::from([(
        target,
        ControlTarget {
            statement_index: 2,
            remaining: Arc::new(target_statement),
        },
    )]));
    let theorem = prove_symbolic_program_function_execution(
        ExecutionState::new(),
        function,
        vec![crate::kernel::program_expression::int32_literal(1)],
        PureFactContext::new(),
    )
    .expect("forward goto should resume at its target");
    assert!(
        matches!(
            theorem.proposition(),
            Proposition::ProgramFunctionVerifies {
                outcome: FunctionOutcome::Return {
                    value,
                    ..
                },
                ..
            } if matches!(value.native().as_ref(), ProgramValue::Int32(int32_constant!(1)))
        ),
        "{:?}",
        theorem.proposition()
    );
}

fn active_memory_borrow(range: MemoryRange) -> BorrowLedger {
    let fact = ResourceFact::own_memory(range);
    let support = ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(&fact)
        .expect("memory backing")
        .0;
    let ledger = BorrowLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let opening = ledger
        .lend(owner, reader, support, fact)
        .expect("memory borrow");
    ledger
        .apply(&opening.transition)
        .expect("memory borrow apply")
}

fn normal_state(paths: &[StatementExecutionPath]) -> ExecutionState {
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(state),
            ..
        },
    ] = paths
    else {
        panic!("expected one normal execution path: {paths:?}");
    };
    *state.clone()
}

fn assert_borrow_write_rejected(outcome: &StatementOutcome) {
    let StatementOutcome::RuntimeError(RuntimeError::BorrowRefusal(diagnostic)) = outcome else {
        panic!("expected a borrow refusal, got {outcome:?}");
    };
    assert_eq!(
        diagnostic.category(),
        crate::kernel::BorrowRefusalCategory::ActiveDependency
    );
    assert_eq!(
        diagnostic.operation(),
        crate::kernel::BorrowRefusalOperation::MemoryAccess
    );
    assert!(diagnostic.subject().conflicting_resource_fact().is_some());
}

fn borrow_write_separation(path: &StatementExecutionPath) -> (&Resource, &Resource) {
    assert!(matches!(path.outcome, StatementOutcome::Normal(_)));
    let [obligation] = path.obligations.as_slice() else {
        panic!(
            "expected one scalar write obligation, got {:?}",
            path.obligations
        );
    };
    let Proposition::ResourceSeparate { left, right } = obligation.proposition() else {
        panic!(
            "expected borrow separation, got {:?}",
            obligation.proposition()
        );
    };
    (left, right)
}

#[test]
fn active_stable_borrow_requires_separation_for_local_assignment_and_alias_store() {
    let _session = crate::kernel::VerificationSession::enter();
    let declaration = program_declare("x", ProgramType::Int32);
    let execute = |state: &ExecutionState, statement: &ProgramStatement| {
        execute_execution_statement_paths(
            state,
            statement,
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let state = normal_state(&execute(&ExecutionState::new(), &declaration));
    let state = normal_state(&execute(&state, &program_declare("y", ProgramType::Int32)));
    let pointer = state.locals().slot("x").unwrap().clone();
    let write = program_assign("x", crate::kernel::program_expression::int32_literal(1));
    let store = program_store(
        crate::kernel::program_expression::addr_of("x"),
        crate::kernel::program_expression::int32_literal(1),
    );
    assert!(execute(&state, &write)[0].obligations.is_empty());

    let overlapping = active_memory_borrow(MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let with_active_borrow = state.clone().with_borrow_ledger(Some(overlapping));
    let direct = execute(&with_active_borrow, &write);
    let indirect = execute(&with_active_borrow, &store);
    let (written, protected) = borrow_write_separation(&direct[0]);
    assert_eq!((written, protected), borrow_write_separation(&indirect[0]));
    assert_eq!(
        written,
        &Resource::Memory(MemoryRange::from_pointer_value(
            &Pointer::new(pointer, ProgramType::Int32Pointer),
            0u32.into(),
            1u32.into(),
            4,
        )),
    );
    assert!(!PureFactContext::new().proves_resource_separate(written, protected));
    assert_borrow_write_rejected(&execute(&with_active_borrow, &declaration)[0].outcome);

    let disjoint = active_memory_borrow(MemoryRange::new(
        state.locals().slot("y").unwrap().clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let with_active_borrow = state.with_borrow_ledger(Some(disjoint));
    let unowned = with_active_borrow
        .clone()
        .with_resource_context(ResourceContext::new());
    assert!(matches!(
        execute(&unowned, &write)[0].outcome,
        StatementOutcome::RuntimeError(RuntimeError::MissingResource { .. })
    ));
    let direct = execute(&with_active_borrow, &write);
    let (written, protected) = borrow_write_separation(&direct[0]);
    assert!(PureFactContext::new().proves_resource_separate(written, protected));
    assert_eq!(
        normal_state(&direct).locals().get_native("x").as_deref(),
        Some(&int32(1))
    );
}

#[test]
fn private_pointer_copy_retains_qualifier_ownership_and_borrow_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    crate::kernel::set_never_address_taken_locals(BTreeSet::from(["p".into()]));
    let execute = |state: &ExecutionState, statement: &ProgramStatement| {
        execute_execution_statement_paths(
            state,
            statement,
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let state = normal_state(&execute(
        &ExecutionState::new(),
        &program_declare("p", ProgramType::UInt8Pointer),
    ));
    let value = ProgramValue::typed_pointer(
        Address::symbolic(Variable(93_700)),
        ProgramType::UInt8Pointer,
    );
    let copy = program_assign("p", ProgramExpression::Value(value.clone()));
    assert_eq!(
        normal_state(&execute(&state, &copy))
            .locals()
            .get_native("p")
            .as_deref(),
        Some(&value)
    );
    let unowned = state.clone().with_resource_context(ResourceContext::new());
    assert!(matches!(
        execute(&unowned, &copy)[0].outcome,
        StatementOutcome::RuntimeError(RuntimeError::MissingResource { .. })
    ));
    let protected = MemoryRange::new_with_element_width(
        state.locals().slot("p").unwrap().clone(),
        0u32.into(),
        1u32.into(),
        value.byte_width(),
    );
    let with_active_borrow = state.with_borrow_ledger(Some(active_memory_borrow(protected)));
    assert_borrow_write_rejected(&execute(&with_active_borrow, &copy)[0].outcome);
}

#[test]
fn active_stable_borrow_allows_a_disjoint_local_store() {
    let declared = execute_execution_statement_paths(
        &ExecutionState::new(),
        &ProgramStatement::Declare {
            name: ("a".to_string()).into(),
            program_type: ProgramType::Int32Array(2),
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            initializer: None,
            zero_fill: None,
            declared_class: None,
        },
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("array declaration should execute");
    let state = normal_state(&declared);
    let base = state.locals().slot("a").cloned().expect("array pointer");
    let borrow = active_memory_borrow(MemoryRange::new(
        base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let state = state.with_borrow_ledger(Some(borrow)).with_local(
        "p",
        ProgramValue::typed_pointer(base.offset_by_bytes(4), ProgramType::Int32Pointer),
    );
    let paths = execute_execution_statement_paths(
        &state,
        &program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(3),
        ),
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("disjoint store should execute");
    assert!(
        matches!(&paths[0].outcome, StatementOutcome::Normal(_)),
        "disjoint store outcome: {:?}",
        paths[0].outcome
    );
}

#[test]
fn volatile_parameter_accesses_emit_ordered_facts() {
    let function = program_function(
        ProgramType::Int32,
        "volatile_read",
        vec![program_parameter("value", ProgramType::Int32).with_volatile(true)],
        ProgramStatement::seq(
            std::sync::Arc::new(ProgramStatement::Assign {
                source: Default::default(),
                name: ("value".to_string()).into(),
                expression: crate::kernel::program_expression::int32_literal(8),
                prior_result: None,
            }),
            std::sync::Arc::new(ProgramStatement::Return(
                crate::kernel::program_expression::variable("value"),
            )),
        ),
    );
    let bound = bind_program_function_arguments(&ExecutionState::new(), &function, &[int32(7)])
        .expect("volatile parameter should bind");
    let paths = execute_execution_statement_paths(
        &bound,
        function.body(),
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("volatile parameter body should execute");
    let accesses = paths[0]
        .facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            crate::kernel::Proposition::VolatileAccess(event) => Some(event.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 2);
    assert_eq!(accesses[0].kind, crate::kernel::VolatileAccessKind::Write);
    assert_eq!(accesses[1].kind, crate::kernel::VolatileAccessKind::Read);
    assert_ne!(accesses[0], accesses[1]);

    // A volatile event id is one allocation from the execution's counter like
    // any other. It used to be taken by incrementing the counter's field
    // directly, which skipped the range check: an execution could walk past
    // the ceiling into the ranges the surface's quantifier and binder
    // variables reserve without a word. It refuses there now.
    let span = ExecutionBudget::KERNEL_VARIABLE_CEILING - ExecutionBudget::KERNEL_VARIABLE_BASE;
    let mut exhausted = ExecutionBudget::default().with_next_kernel_variable(span);
    assert_eq!(
        execute_execution_statement_paths(
            &bound,
            function.body(),
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut exhausted,
        ),
        Err(ExecutionLimit::KernelVariables {
            ceiling: ExecutionBudget::KERNEL_VARIABLE_CEILING,
        })
    );
}

/// A memory-havoc marker spells its identity in a block name rather than
/// carrying it in a term, so a scan of a state's terms did not see it and the
/// branch join harvested block names itself -- for `havoc:` only, and only in
/// that one place. The state scan reserves both marker forms now, so every
/// caller that must avoid what a state already mentions sees them.
#[test]
fn a_state_scan_reserves_memory_havoc_marker_identities() {
    let state = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_block("havoc:1000004", 0)
            .with_block("call-havoc:1000009", 0)
            .with_block("local:x", 4),
    );
    let mut reserved = BTreeSet::new();
    crate::kernel::reasoning::collect_execution_state_bitvector_variables(&state, &mut reserved);
    assert!(reserved.contains(&Variable(1_000_004)));
    assert!(reserved.contains(&Variable(1_000_009)));

    // A fresh stream over that state therefore avoids both without the
    // caller naming the marker convention.
    let mut budget = ExecutionBudget::default().with_next_kernel_variable(4);
    let mut variables = KernelVariableGenerator::fresh_for_execution(reserved);
    for _ in 0..8 {
        let identity = variables
            .next_in(&mut budget)
            .expect("the counter is nowhere near its ceiling");
        assert_ne!(identity, Variable(1_000_004));
        assert_ne!(identity, Variable(1_000_009));
    }
}

#[test]
fn scalar_local_updates_share_memory_and_resource_state() {
    let before = ExecutionState::new();
    let after = before.clone().with_local("x", int32(1));
    assert!(before.shares_nonlocal_storage_with(&after));
}

#[test]
fn loop_back_edge_rejects_heap_and_resource_state_changes() {
    let allocation = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let memory = SymbolicMemory::new()
        .with_heap_allocation_claim(allocation.clone(), AllocationSize::int32(16))
        .expect("test allocation claim should be fresh");
    let top = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_allocation(allocation.clone(), 16))
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    allocation,
                    MachineTerm::constant(0),
                    MachineTerm::constant(4),
                ))),
        );
    let freed = execute_execution_statement_paths(
        &top,
        &program_heap_free(ProgramExpression::Value(ProgramValue::pointer(Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        }))),
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("test free should execute");
    let StatementOutcome::Normal(freed) = &freed[0].outcome else {
        panic!("test free should have a normal outcome");
    };
    let error = loop_state_components_match_at_back_edge(&top, freed, &PureFactContext::new(), &[])
        .expect_err("a freed allocation must not cross a loop back edge");
    assert!(error.contains("heap allocation lifetime"));

    let consumed = top.clone().with_resource_context(ResourceContext::new());
    let error =
        loop_state_components_match_at_back_edge(&top, &consumed, &PureFactContext::new(), &[])
            .expect_err("consumed resources must not cross a loop back edge");
    assert!(error.contains("resource ownership"));

    let token = ResourceFact::own_token("can_complete".to_string(), Vec::new());
    let token_top = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(token));
    let token_consumed = ExecutionState::new();
    let error = loop_state_components_match_at_back_edge(
        &token_top,
        &token_consumed,
        &PureFactContext::new(),
        &[],
    )
    .expect_err("an abstract token must not cross a loop back edge");
    assert!(error.contains("resource ownership"));
}

#[test]
fn final_iteration_condition_can_use_the_pre_body_bound() {
    let original = Variable(91_001);
    let original_bits = MachineTerm::Variable(original);
    let state = ExecutionState::new().with_local(
        "i",
        int32(MachineTerm::add(
            original_bits.clone(),
            MachineTerm::constant(1),
        )),
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(original_bits.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(original_bits, MachineTerm::constant(1)),
            true,
        );

    assert!(
        !classify_loop_condition(
            &state,
            &crate::kernel::program_expression::less_than(
                crate::kernel::program_expression::variable("i"),
                crate::kernel::program_expression::int32_literal(1)
            ),
            &assumptions,
        )
        .expect("condition classification should stay within its expression budget")
        .may_continue()
    );
}

#[test]
fn join_state_forgets_changed_scalars_and_memory() {
    let stable_x = int32(MachineTerm::Variable(Variable(7)));
    let pointer = Address {
        base: "heap".into(),
        offset: AddressOffset::Constant(0),
    };
    let state_zero = ExecutionState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(0))
        .with_memory(
            SymbolicMemory::new()
                .with_block("heap", 4)
                .store(pointer.clone(), int32(0)),
        )
        .with_resource_context(own_memory_context(pointer.clone(), 0, 1));
    let state_one = ExecutionState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(1))
        .with_memory(
            SymbolicMemory::new()
                .with_block("heap", 4)
                .store(pointer, int32(1)),
        );
    let stable = BTreeMap::from([("x".into(), stable_x.clone())]);

    let abstract_zero =
        abstract_execution_state_for_join(&state_zero, &stable, 0).expect("join abstraction");
    let abstract_one =
        abstract_execution_state_for_join(&state_one, &stable, 0).expect("join abstraction");

    assert_eq!(abstract_zero, abstract_one);
    // The abstraction issued an identity, and it says so: the joined
    // execution continues above everything the join spent.
    assert!(abstract_zero.next_kernel_variable > 0);
    let abstract_zero = abstract_zero.state;
    assert_eq!(
        abstract_zero.locals().get_native("x").as_deref(),
        Some(&stable_x)
    );
    assert_ne!(
        abstract_zero.locals().get_native("y").as_deref(),
        Some(&int32(0))
    );
    assert!(abstract_zero.resources().is_empty());
}

#[test]
fn join_state_abstracts_changed_pointer_locals() {
    let left = Address {
        base: "left".into(),
        offset: AddressOffset::Constant(0),
    };
    let right = Address {
        base: "right".into(),
        offset: AddressOffset::Constant(0),
    };
    let abstract_left = abstract_execution_state_for_join(
        &ExecutionState::new().with_local("selected", ProgramValue::pointer(left)),
        &BTreeMap::new(),
        0,
    )
    .expect("pointer join abstraction");
    let abstract_right = abstract_execution_state_for_join(
        &ExecutionState::new().with_local("selected", ProgramValue::pointer(right)),
        &BTreeMap::new(),
        0,
    )
    .expect("pointer join abstraction");

    assert_eq!(abstract_left, abstract_right);
    let local_native_output_596 = abstract_left.state.locals().get_native("selected");
    let Some(ProgramValue::Pointer(selected)) = local_native_output_596.as_deref() else {
        panic!("selected should remain a pointer local");
    };
    assert!(selected.has_symbolic_block());
}

#[test]
fn join_state_fresh_variables_do_not_collide_with_symbolic_address_bases() {
    let state = ExecutionState::new().with_local(
        "selected",
        ProgramValue::pointer(Address::symbolic(Variable(1_000_000))),
    );
    let abstract_state = abstract_execution_state_for_join(&state, &BTreeMap::new(), 0)
        .expect("pointer join abstraction");
    // `v1000000` was reserved by the state, so the abstraction issued
    // `v1000001` for the local and `v1000002` for its memory-havoc marker.
    // The counter it returns is above both, and the joined execution
    // continues from there.
    assert_eq!(abstract_state.next_kernel_variable, 3);
    let local_native_output_615 = abstract_state.state.locals().get_native("selected");
    let Some(ProgramValue::Pointer(selected)) = local_native_output_615.as_deref() else {
        panic!("selected should remain a pointer local");
    };

    assert_eq!(selected.base, AddressBase::Symbolic(Variable(1_000_001)));
}

#[test]
fn sibling_join_abstraction_is_deterministic_after_a_nested_join() {
    let nested_source = ExecutionState::new().with_local("y", int32(0));
    let nested = abstract_execution_state_for_join(&nested_source, &BTreeMap::new(), 0)
        .expect("nested join abstraction");
    let sibling = ExecutionState::new().with_local("y", int32(1));
    let states = [&nested.state, &sibling];

    let abstract_nested = abstract_execution_state_for_join_across(
        &nested.state,
        &states,
        &BTreeMap::new(),
        nested.next_kernel_variable,
    )
    .expect("outer nested-arm abstraction");
    let abstract_sibling = abstract_execution_state_for_join_across(
        &sibling,
        &states,
        &BTreeMap::new(),
        nested.next_kernel_variable,
    )
    .expect("outer sibling abstraction");

    assert_eq!(abstract_nested, abstract_sibling);

    let inner_empty =
        abstract_execution_state_for_join(&ExecutionState::new(), &BTreeMap::new(), 0)
            .expect("inner empty-state abstraction");
    let raw_empty = ExecutionState::new();
    let empty_states = [&inner_empty.state, &raw_empty];
    let outer_nested = abstract_execution_state_for_join_across(
        &inner_empty.state,
        &empty_states,
        &BTreeMap::new(),
        inner_empty.next_kernel_variable,
    )
    .expect("outer nested empty-state abstraction");
    let outer_raw = abstract_execution_state_for_join_across(
        &raw_empty,
        &empty_states,
        &BTreeMap::new(),
        inner_empty.next_kernel_variable,
    )
    .expect("outer raw empty-state abstraction");
    assert_eq!(outer_nested, outer_raw);
    assert_ne!(outer_nested.state, inner_empty.state);
}

#[test]
fn symbolic_address_bases_do_not_imply_non_aliasing() {
    let symbolic = Address::symbolic(Variable(21_000));
    let concrete = Address {
        base: "heap".into(),
        offset: AddressOffset::Constant(0),
    };

    assert_eq!(
        PureFactContext::new().decide(&ConditionTerm::address_equal(symbolic, concrete)),
        None
    );
}

#[test]
fn concrete_address_base_names_cannot_create_symbolic_identity() {
    let misleading_name = Address {
        base: "symbolic-pointer:21000".into(),
        offset: AddressOffset::Constant(0),
    };
    let heap = Address {
        base: "heap".into(),
        offset: AddressOffset::Constant(0),
    };

    assert!(!misleading_name.has_symbolic_block());
    assert!(misleading_name.blocks_proven_distinct(&heap));
}

#[test]
fn concrete_max_executes_without_list_encoding() {
    let state = program_max_state(int32(0), int32(1));
    let theorem = prove_execution_statement_execution(state.clone(), program_max_body())
        .expect("max should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(program_max_body()),
            outcome: StatementOutcome::Return {
                value: int32(1).into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn concrete_max_function_call_preserves_caller_locals() {
    let state = ExecutionState::new().with_local("caller", int32(99));
    let function = program_max_function();
    let arguments = vec![
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    ];
    let theorem = prove_symbolic_program_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramFunctionVerifies {
            state: Box::new(state.clone()),
            function: Box::new(function),
            arguments,
            outcome: FunctionOutcome::Return {
                value: int32(1).into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn symbolic_max_function_call_reports_branch_facts() {
    let a = Variable(14);
    let b = Variable(15);
    let a_bits = MachineTerm::Variable(a);
    let b_bits = MachineTerm::Variable(b);
    let condition = program_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = ExecutionState::new();
    let function = program_max_function();
    let arguments = vec![
        ProgramExpression::Value(int32(a_bits.clone())),
        ProgramExpression::Value(int32(b_bits.clone())),
    ];
    let execution = prove_symbolic_program_function_execution_paths(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::condition_is(condition.clone(), true)),
            Box::new(Proposition::ProgramFunctionVerifies {
                state: Box::new(state.clone()),
                function: Box::new(function.clone()),
                arguments: arguments.clone(),
                outcome: FunctionOutcome::Return {
                    value: int32(b_bits).into(),
                    state: Box::new(state.clone()),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition.clone(), false)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::condition_is(condition, false)),
            Box::new(Proposition::ProgramFunctionVerifies {
                state: Box::new(state.clone()),
                function: Box::new(function),
                arguments,
                outcome: FunctionOutcome::Return {
                    value: int32(a_bits).into(),
                    state: Box::new(state),
                },
            }),
        )
    );
}

#[test]
fn execution_derivation_matches_only_equivalent_call_havoc() {
    let assumptions = PureFactContext::new();
    let base = SymbolicMemory::new().with_block("arc", 16);
    let first_range = memory_range(arc_pointer(0), 0, 1);
    let other_range = memory_range(arc_pointer(4), 0, 1);
    let left = FunctionOutcome::Return {
        value: int32(0).into(),
        state: Box::new(
            ExecutionState::new().with_memory(base.clone().with_call_memory_havoc(
                Variable(41),
                std::slice::from_ref(&first_range),
                &assumptions,
                None,
            )),
        ),
    };
    let equivalent = FunctionOutcome::Return {
        value: int32(0).into(),
        state: Box::new(
            ExecutionState::new().with_memory(base.clone().with_call_memory_havoc(
                Variable(42),
                std::slice::from_ref(&first_range),
                &assumptions,
                None,
            )),
        ),
    };
    let different = FunctionOutcome::Return {
        value: int32(0).into(),
        state: Box::new(
            ExecutionState::new().with_memory(base.with_call_memory_havoc(
                Variable(43),
                &[other_range],
                &assumptions,
                None,
            )),
        ),
    };

    assert!(
        program_function_outcomes_program_state_equal_by_derivation(
            &left,
            &[],
            &equivalent,
            &[],
            &assumptions,
        ),
        "fresh marker names should not distinguish the same call havoc"
    );
    assert!(
        !program_function_outcomes_program_state_equal_by_derivation(
            &left,
            &[],
            &different,
            &[],
            &assumptions,
        ),
        "different mutable ranges must not be coupled as one call effect"
    );
}

#[test]
fn function_call_threads_memory_but_discards_callee_locals() {
    let pointer = Address {
        base: "block".into(),
        offset: AddressOffset::Constant(0),
    };
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = ExecutionState::new()
        .with_local("caller", int32(42))
        .with_resource_context(resources.clone());
    let function = program_function(
        ProgramType::Int32,
        "store_and_load",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_seq(
            program_store(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(9),
            ),
            program_return(crate::kernel::program_expression::load(
                crate::kernel::program_expression::variable("p"),
            )),
        ),
    );
    let arguments = vec![crate::kernel::program_expression::pointer_value(
        pointer.clone(),
    )];
    let final_state = ExecutionState::new()
        .with_local("caller", int32(42))
        .with_memory(SymbolicMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_program_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramFunctionVerifies {
            state: Box::new(state),
            function: Box::new(function),
            arguments,
            outcome: FunctionOutcome::Return {
                value: int32(9).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn call_result_then_assignment_uses_function_environment() {
    let increment = program_function(
        ProgramType::Int32,
        "increment",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("x"),
            crate::kernel::program_expression::int32_literal(1),
        )),
    );
    let environment = ExecutionEnvironment::new().with_function((increment).with_inline_body());
    let state = ExecutionState::new().with_local("result", int32(0));
    let statement = program_seq(
        program_call_then_assign(
            1,
            "result",
            "increment",
            vec![crate::kernel::program_expression::int32_literal(41)],
        ),
        program_return(crate::kernel::program_expression::variable("result")),
    );
    let final_state = ExecutionState::new().with_local("result", int32(42));
    let theorem = prove_symbolic_program_execution_with_environment(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    )
    .expect("known function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementVerifies {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(42).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn direct_call_propagates_internal_throw_and_skips_its_suffix() {
    let thrower = program_function(
        ProgramType::Int32,
        "thrower",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome();
    let environment = ExecutionEnvironment::new().with_function((thrower).with_inline_body());
    let state = ExecutionState::new().with_local("result", int32(1));
    let statement = program_seq(
        program_call_then_assign(2, "result", "thrower", Vec::new()),
        program_return(crate::kernel::program_expression::variable("result")),
    );
    let theorem = prove_symbolic_program_execution_with_environment(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    )
    .expect("an internal throw should cross an inline helper call");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Throw {
                value: int32(7).into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn int32_handler_receives_payload_and_thrown_state_across_a_call() {
    let thrower = program_function(
        ProgramType::Int32,
        "thrower",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome();
    let environment = ExecutionEnvironment::new().with_function((thrower).with_inline_body());
    let state = ExecutionState::new().with_local("x", int32(1));
    let statement = program_try_catch_int32(
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(9)),
            program_seq(
                program_call("thrower", Vec::new()),
                program_return(crate::kernel::program_expression::int32_literal(99)),
            ),
        ),
        "caught",
        program_return(crate::kernel::program_expression::variable("caught")),
    );
    let theorem = prove_symbolic_program_execution_with_environment(
        state,
        statement,
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    )
    .expect("the checked handler should execute from the thrown state");
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Return { value, state },
        ..
    } = theorem.proposition()
    else {
        panic!("expected a caught return: {:?}", theorem.proposition());
    };
    assert_eq!(value.native().as_ref(), &int32(7));
    assert_eq!(state.locals.get_native("x").as_deref(), Some(&int32(9)));
    assert_eq!(
        state.locals.get_native("caught").as_deref(),
        Some(&int32(7))
    );
}

#[test]
fn int32_handler_does_not_run_on_normal_or_return_paths() {
    let initial = ExecutionState::new().with_local("x", int32(1));
    let normal = program_seq(
        program_try_catch_int32(
            program_assign("x", crate::kernel::program_expression::int32_literal(9)),
            "caught",
            program_return(crate::kernel::program_expression::int32_literal(99)),
        ),
        program_return(crate::kernel::program_expression::variable("x")),
    );
    let theorem = prove_symbolic_program_execution(initial.clone(), normal, PureFactContext::new())
        .expect("a normal try body should bypass the handler");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Return {
                value,
                ..
            },
            ..
        } if matches!(value.native().as_ref(), ProgramValue::Int32(int32_constant!(9)))
    ));
    let returning = program_try_catch_int32(
        program_return(crate::kernel::program_expression::int32_literal(3)),
        "caught",
        program_return(crate::kernel::program_expression::int32_literal(99)),
    );
    let theorem = prove_symbolic_program_execution(initial, returning, PureFactContext::new())
        .expect("a return from the try body should bypass the handler");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Return {
                value,
                ..
            },
            ..
        } if matches!(value.native().as_ref(), ProgramValue::Int32(int32_constant!(3)))
    ));
}

#[test]
fn throw_from_int32_handler_escapes_instead_of_being_recaught() {
    let statement = program_try_catch_int32(
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
        "caught",
        ProgramStatement::Throw(crate::kernel::program_expression::variable("caught")),
    );
    let theorem =
        prove_symbolic_program_execution(ExecutionState::new(), statement, PureFactContext::new())
            .expect("a handler throw should escape the same handler");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Throw {
                value,
                ..
            },
            ..
        } if matches!(value.native().as_ref(), ProgramValue::Int32(int32_constant!(7)))
    ));
}

#[test]
fn int32_handler_rejects_a_binding_that_would_replace_a_live_local() {
    let statement = program_try_catch_int32(
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
        "live",
        program_return(crate::kernel::program_expression::variable("live")),
    );
    let theorem = prove_symbolic_program_execution(
        ExecutionState::new().with_local("live", int32(11)),
        statement,
        PureFactContext::new(),
    )
    .expect("a colliding catch binding must be rejected, not overwrite the local");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
            ..
        } if message.contains("handler binding `live` is not fresh")
    ));
}

#[test]
fn caught_throw_satisfies_a_nonthrowing_function_signature() {
    let function = program_function(
        ProgramType::Int32,
        "fully_handled",
        Vec::new(),
        program_try_catch_int32(
            ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
            "caught",
            program_return(crate::kernel::program_expression::variable("caught")),
        ),
    );
    let theorem = prove_symbolic_program_function_execution(
        ExecutionState::new(),
        function,
        Vec::new(),
        PureFactContext::new(),
    )
    .expect("a fully caught body should be a nonthrowing function");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramFunctionVerifies {
            outcome: FunctionOutcome::Return {
                value,
                ..
            },
            ..
        } if matches!(value.native().as_ref(), ProgramValue::Int32(int32_constant!(7)))
    ));
}

#[test]
fn conditional_catch_has_a_continuing_call_outcome_and_a_terminal_one() {
    let helper = program_function(
        ProgramType::Int32,
        "helper",
        vec![program_parameter("should_throw", ProgramType::Bool)],
        program_if(
            crate::kernel::program_expression::variable("should_throw"),
            ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
            program_return(crate::kernel::program_expression::int32_literal(5)),
        ),
    )
    .with_int32_exceptional_outcome();
    let caller = program_function(
        ProgramType::Int32,
        "caller",
        vec![
            program_parameter("construct", ProgramType::Bool),
            program_parameter("should_throw", ProgramType::Bool),
        ],
        program_seq(
            program_if(
                crate::kernel::program_expression::variable("construct"),
                program_try_catch_int32(
                    program_call(
                        "helper",
                        vec![crate::kernel::program_expression::variable("should_throw")],
                    ),
                    "caught",
                    program_return(crate::kernel::program_expression::variable("caught")),
                ),
                program_skip(),
            ),
            program_return(crate::kernel::program_expression::int32_literal(5)),
        ),
    );
    let execution = prove_symbolic_program_function_execution_paths_with_environment(
        ExecutionState::new(),
        caller,
        vec![
            ProgramExpression::Value(bool_value(MachineTerm::Variable(Variable(80_001)))),
            ProgramExpression::Value(bool_value(MachineTerm::Variable(Variable(80_002)))),
        ],
        PureFactContext::new(),
        ExecutionEnvironment::new().with_function((helper).with_inline_body()),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    );
    assert!(execution.limit().is_none());
    assert_eq!(execution.paths().len(), 3);
    let mut returned_values = execution
        .paths()
        .iter()
        .map(|path| {
            assert!(path.obligations().is_empty());
            let mut proposition = path.theorem().proposition();
            while let Proposition::Implies(_, body) = proposition {
                proposition = body;
            }
            match proposition {
                Proposition::ProgramFunctionVerifies {
                    outcome: FunctionOutcome::Return { value, .. },
                    ..
                } => {
                    let native = value.native();
                    let ProgramValue::Int32(int32_constant!(bits)) = native.as_ref() else {
                        panic!("constant return");
                    };
                    constant_u32(*bits)
                }
                other => panic!("conditional catch produced a non-return outcome: {other:?}"),
            }
        })
        .collect::<Vec<_>>();
    returned_values.sort_unstable();
    assert_eq!(returned_values, [5, 5, 7]);
}

#[test]
fn internal_throw_is_int32_only_and_requires_a_verified_direct_rule() {
    let throwing = program_function(
        ProgramType::Int32,
        "throwing",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome();
    assert!(!throwing.opaque_contract_supported());
    assert!(throwing.verified_direct_contract_supported());
    // A throwing interface is a named contract too; the throw is part of it.
    assert!(
        FunctionContract::new("Throwing", throwing.clone()).is_some_and(|contract| {
            contract.interface().exceptional_signature() == ExceptionalSignature::Int32
        })
    );

    let declared_without_throw = program_function(
        ProgramType::Int32,
        "declared_without_throw",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_int32_exceptional_outcome();
    assert!(!declared_without_throw.opaque_contract_supported());
    assert!(declared_without_throw.verified_direct_contract_supported());
    assert!(FunctionContract::new("DeclaredWithoutThrow", declared_without_throw).is_some());

    let modular = prove_symbolic_program_execution_with_environment(
        ExecutionState::new(),
        program_call("throwing", Vec::new()),
        PureFactContext::new(),
        ExecutionEnvironment::new().with_function(throwing),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    )
    .expect("a throwing function should produce an explicit modular refusal");
    assert!(
        matches!(
            modular.proposition(),
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::RuntimeError(RuntimeError::MissingVerifiedFunctionRule(name)),
                ..
            } if name == "throwing"
        ),
        "{:?}",
        modular.proposition()
    );

    let theorem = prove_symbolic_program_execution(
        ExecutionState::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::pointer_value(
            Address::null(),
        )),
        PureFactContext::new(),
    )
    .expect("a non-int32 throw should produce a checked type mismatch");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            ..
        }
    ));
}

#[test]
fn function_execution_rejects_an_undeclared_exceptional_outcome() {
    let function = program_function(
        ProgramType::Int32,
        "undeclared_throw",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    );
    let theorem = prove_symbolic_program_function_execution(
        ExecutionState::new(),
        function,
        Vec::new(),
        PureFactContext::new(),
    )
    .expect("an undeclared throw should produce a checked contract error");
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramFunctionVerifies {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
            ..
        } if message == "undeclared_throw produced an exceptional outcome not declared by its signature"
    ));
}

#[test]
fn loop_semantics_explicitly_select_verification_or_verified_rules() {
    let state = ExecutionState::new().with_local("i", int32(0));
    let statement = program_while_with_invariant_checks(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        Vec::new(),
        vec![LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("i"),
                ),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        program_assign(
            "i",
            crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("i"),
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    );
    let assumptions = PureFactContext::new();
    let (certified, loop_rule) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            assumptions.clone(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
    let loop_rule = loop_rule.expect("loop verification should produce a rule");
    assert!(certified.paths().iter().all(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(proposition, Proposition::ProgramStatementVerifies { .. })
    }));

    let missing = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(missing.paths().is_empty());

    let mut ignored_rule = loop_rule.clone();
    ignored_rule.paths.clear();
    let base_environment = ExecutionEnvironment::new();
    let cloned_environment = base_environment.clone();
    assert!(base_environment.shares_all_storage_with(&cloned_environment));
    let loop_environment = cloned_environment.with_verified_loop_rules([ignored_rule]);
    assert!(base_environment.shares_project_storage_with(&loop_environment));
    let verified_directly = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        loop_environment,
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    );
    assert!(!verified_directly.paths().is_empty());

    let reused = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions
            .clone()
            .assume_condition(ConditionTerm::Constant(true), true),
        ExecutionEnvironment::new().with_verified_loop_rules([loop_rule.clone()]),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(reused.paths().len(), certified.paths().len());
    assert!(reused.paths().iter().all(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(proposition, Proposition::ProgramStatementVerifies { .. })
    }));

    let mismatched = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.with_local("unrelated", int32(0)),
        statement,
        assumptions,
        ExecutionEnvironment::new().with_verified_loop_rules([loop_rule]),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(mismatched.paths().is_empty());
}

#[test]
fn statement_checks_share_one_execution_environment_variable_index() {
    let reserved = Variable(1_000_000);
    let indexed_function = program_function(
        ProgramType::Int32,
        "indexed",
        Vec::new(),
        program_return(ProgramExpression::Value(ProgramValue::Int32(
            MachineTerm::Variable(reserved),
        ))),
    );
    let environment = ExecutionEnvironment::new().with_function(indexed_function);
    let cloned_before_initialization = environment.clone();
    assert_eq!(environment.variable_index.build_count(), 0);

    for candidate in [environment.clone(), cloned_before_initialization] {
        let execution = prove_symbolic_execution_statement_verification_paths_with_environment(
            ExecutionState::new(),
            program_skip(),
            PureFactContext::new(),
            candidate,
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
        assert_eq!(execution.paths().len(), 1);
    }

    assert_eq!(
        environment.variable_index.build_count(),
        1,
        "environment clones must share one derived symbolic-variable scan"
    );
    let indexed = execution_environment_variable_index(&environment);
    assert!(indexed.contains(&reserved));
    assert_eq!(environment.variable_index.build_count(), 1);
    let mut budget = ExecutionBudget::new();
    let mut generator = KernelVariableGenerator::fresh_for_execution_with_shared_reservations(
        BTreeSet::from([Variable(1_000_001)]),
        indexed,
    );
    assert_eq!(
        generator.next_in(&mut budget),
        Ok(Variable(1_000_002)),
        "fresh variables must avoid both shared environment and local reservations"
    );

    let changed = environment.with_function(program_function(
        ProgramType::Int32,
        "changed",
        Vec::new(),
        program_return(ProgramExpression::Value(ProgramValue::Int32(
            MachineTerm::Variable(Variable(1_000_001)),
        ))),
    ));
    assert_eq!(changed.variable_index.build_count(), 0);
    let changed_index = execution_environment_variable_index(&changed);
    assert!(changed_index.contains(&reserved));
    assert!(changed_index.contains(&Variable(1_000_001)));
    assert_eq!(changed.variable_index.build_count(), 1);
}

/// An environment that gains a verified loop rule collects that rule's
/// reserved variables alone. A proof's `loop` tactic adds its rule to an
/// environment holding every earlier loop's, and each rule holds its whole
/// path context, so collecting them all again made each loop linear in the
/// loops before it and the proof quadratic.
#[test]
fn adding_a_loop_rule_collects_only_that_rules_variables() {
    let rule = |index: u64| VerifiedLoopRule {
        symbolic_entry_state: ExecutionState::default(),
        loop_statement: program_skip(),
        loop_evidence: None,
        required_assumptions: PureFactContext::new()
            .assume_proposition(guard_operand_fact(1_000_000 + index, true)),
        paths: Vec::new(),
        composite_resource_definitions: Default::default(),
        recursion_anchor: None,
        variable_index: Default::default(),
    };
    let base = ExecutionEnvironment::new();
    execution_environment_variable_index(&base);
    let mut environment = base.clone();
    for index in 0..8 {
        environment = environment.with_verified_loop_rules([rule(index)]);
        let reserved = execution_environment_variable_index(&environment);
        assert!((0..=index).all(|earlier| reserved.contains(&Variable(1_000_000 + earlier))));
    }
    assert!(
        environment
            .variable_index
            .shares_storage_with(&base.variable_index),
        "adding loop rules keeps the index of the environment's other parts"
    );
    assert_eq!(environment.variable_index.build_count(), 1);
    assert!(
        environment
            .verified_loop_rules
            .iter()
            .all(|rule| rule.variable_index.build_count() == 1),
        "each loop rule's variables are collected once, by the first environment that asks"
    );
}

#[test]
fn environment_variable_scans_do_not_multiply_by_statement_count() {
    for size in [8, 32, 128, 512] {
        let mut body = program_return(ProgramExpression::Value(int32(0)));
        for index in (0..size).rev() {
            body = program_seq(
                program_assign(
                    "symbolic",
                    ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(
                        1_000_000 + index,
                    )))),
                ),
                body,
            );
        }
        let environment = ExecutionEnvironment::new().with_function(program_function(
            ProgramType::Int32,
            format!("indexed_{size}"),
            Vec::new(),
            body,
        ));

        for _ in 0..size {
            let execution = prove_symbolic_execution_statement_verification_paths_with_environment(
                ExecutionState::new(),
                program_skip(),
                PureFactContext::new(),
                environment.clone(),
                ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            );
            assert_eq!(execution.paths().len(), 1);
        }
        assert_eq!(
            environment.variable_index.build_count(),
            1,
            "size {size} rebuilt the environment variable index across statement checks"
        );
    }
}

#[test]
fn perpetual_loop_verifies_safety_without_minting_a_concrete_exit() {
    let state = ExecutionState::new();
    let statement = program_while_with_invariant_checks(
        crate::kernel::program_expression::int32_literal(1),
        Vec::new(),
        vec![LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
            Some("perpetual loop entry".to_string()),
            Some("perpetual loop preservation".to_string()),
        )],
        program_skip(),
    );
    let (verification, rule) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
    assert!(rule.is_some());
    assert_eq!(verification.paths().len(), 1);
    let mut proposition = verification.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::VerificationDiverges,
            ..
        }
    ));

    let concrete = prove_symbolic_program_execution_paths(state, statement, PureFactContext::new());
    assert!(concrete.paths().is_empty());
    assert!(concrete.limit().is_some());
}

#[test]
fn loop_head_preserves_sparse_body_field_view_reservations() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = ExecutionBudget::KERNEL_VARIABLE_BASE;
    let mut state = ExecutionState::new().with_local("i", int32(0));
    let view = ResourceInstance::field_view(
        "parent".to_string(),
        std::iter::empty().collect(),
        ResourceFieldSchema::new(vec![(
            "rank".to_string(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap(),
        [crate::kernel::AlgebraicValue::Program(int32(
            MachineTerm::Variable(Variable(base + 1)),
        ))]
        .into_iter()
        .collect(),
    )
    .unwrap();
    state.body_field_view = Some(Arc::new(view));
    let body = program_assign("i", crate::kernel::program_expression::int32_literal(1));
    let head = crate::kernel::api::loop_phase_preservation_contexts(
        &state,
        None,
        &[],
        &[],
        &[],
        &[],
        &body,
        &PureFactContext::new(),
        0,
    )
    .expect("preservation context");

    // The iteration uses the free candidate before the field's identity. The
    // havoc of i must skip over the field and take the next free identity.
    assert_eq!(head[0].iterations(), &IntegerTerm::var(Variable(base)));
    assert_eq!(head[0].next_kernel_variable(), 3);
}

#[test]
fn loop_exit_rule_with_proven_preservation_does_not_reverify_the_body() {
    let state = ExecutionState::new().with_local("i", int32(0));
    let statement = program_while_with_invariant_checks(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        Vec::new(),
        vec![LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("i"),
                ),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        program_assign(
            "i",
            crate::kernel::program_expression::int32_literal(u32::MAX),
        ),
    );
    let assumptions = PureFactContext::new();
    let automatic = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    );
    assert!(
        automatic
            .paths()
            .iter()
            .flat_map(SymbolicExecutionPath::obligations)
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );

    let (after_proof, loop_rule) = prove_symbolic_loop_exit_with_proven_phases(
        state,
        statement,
        assumptions,
        ExecutionEnvironment::new(),
        false,
        true,
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    assert!(loop_rule.is_some());
    assert!(after_proof.paths().iter().all(|path| {
        path.obligations()
            .iter()
            .all(|obligation| obligation.context() != Some("loop preservation"))
    }));
}

#[test]
fn loop_exit_with_unproven_preservation_does_not_produce_rule() {
    let state = ExecutionState::new().with_local("i", int32(u32::MAX));
    let statement = program_while_with_invariant_checks(
        crate::kernel::program_expression::int32_literal(1),
        Vec::new(),
        vec![LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("i"),
                ),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        program_assign(
            "i",
            crate::kernel::program_expression::int32_literal(u32::MAX),
        ),
    );
    let (execution, loop_rule) = prove_symbolic_loop_exit_with_proven_phases(
        state,
        statement,
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        true,
        false,
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );

    assert!(loop_rule.is_none());
    let obligations = execution
        .paths()
        .iter()
        .flat_map(SymbolicExecutionPath::obligations)
        .collect::<Vec<_>>();
    assert!(
        obligations
            .iter()
            .all(|obligation| obligation.context() != Some("loop entry"))
    );
    assert!(
        obligations
            .iter()
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );
}

#[test]
fn unknown_call_assign_is_runtime_error() {
    let state = ExecutionState::new();
    let statement = program_call_then_assign(3, "result", "missing", Vec::new());
    let theorem = prove_symbolic_program_execution_with_environment(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
    )
    .expect("unknown function should produce a single runtime-error path");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementVerifies {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::RuntimeError(RuntimeError::UnknownFunction(
                "missing".to_string(),
            )),
        }
    );
}

/// A guard operand the function has no authority to read leaves the guard
/// undecided. Neither truthiness request may answer with the operands that
/// happened to evaluate: assuming `!(a != 0)` alone at the exit is strictly
/// weaker than assuming `!(a != 0 && p[0] != 0)`, and that gap once proved
/// `result == 0` for a function that can return a nonzero `a`.
#[test]
fn unreadable_guard_operand_leaves_the_condition_undecided() {
    let pointer = Address {
        base: "external".into(),
        offset: AddressOffset::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("a", int32(MachineTerm::Variable(Variable(1))))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
        );
    let condition = crate::kernel::program_expression::and(
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::variable("a"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::load(crate::kernel::program_expression::variable(
                "p",
            )),
            crate::kernel::program_expression::int32_literal(0),
        ),
    );
    let mut budget = ExecutionBudget::for_program_expression(&condition);
    for desired_truthiness in [false, true] {
        let assumptions = crate::kernel::loops::assume_loop_entry_truthiness(
            &state,
            Some(&condition),
            &[],
            &PureFactContext::new(),
            &[],
            &[],
            desired_truthiness,
            &mut budget,
        )
        .expect("the guard should evaluate within its budget");
        assert!(
            assumptions.iter().any(|assumption| matches!(
                assumption.undecided_outcome(),
                Some(StatementOutcome::RuntimeError(
                    RuntimeError::MissingResource { .. }
                ))
            )),
            "the unreadable operand must be reported, not dropped (truthiness {desired_truthiness})"
        );
    }
}

#[test]
fn while_loop_executes_concrete_countdown() {
    let state = ExecutionState::new().with_local("x", int32(3));
    let loop_statement = program_while(
        crate::kernel::program_expression::greater_than(
            crate::kernel::program_expression::variable("x"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        Vec::new(),
        program_assign(
            "x",
            crate::kernel::program_expression::subtract(
                crate::kernel::program_expression::variable("x"),
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    );
    let statement = program_seq(
        loop_statement,
        program_return(crate::kernel::program_expression::variable("x")),
    );
    let final_state = ExecutionState::new().with_local("x", int32(0));
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("concrete countdown loop should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementVerifies {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn loop_budget_exhaustion_is_executor_failure_not_c_runtime_error() {
    let state = ExecutionState::new().with_local("x", int32(0));
    let statement = program_while(
        crate::kernel::program_expression::int32_literal(1),
        Vec::new(),
        program_assign("x", crate::kernel::program_expression::variable("x")),
    );
    let budget = ExecutionBudget::new().with_loop_unrolls(2);
    let execution = prove_symbolic_program_execution_paths_with_budget(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
        budget.clone(),
    );

    assert_eq!(execution.limit(), Some(ExecutionLimit::LoopUnrolls));
    assert_eq!(execution.paths(), &[] as &[SymbolicExecutionPath]);
    assert!(
        prove_symbolic_program_execution_with_budget(
            state,
            statement,
            PureFactContext::new(),
            budget,
        )
        .is_none()
    );
}

#[test]
fn executor_budgets_cap_steps_calls_and_paths() {
    let state = ExecutionState::new();
    let statement = program_return(crate::kernel::program_expression::int32_literal(1));

    assert_eq!(
        prove_symbolic_program_execution_paths_with_budget(
            state.clone(),
            statement.clone(),
            PureFactContext::new(),
            ExecutionBudget::new().with_statement_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::StatementSteps)
    );
    assert_eq!(
        prove_symbolic_program_execution_paths_with_budget(
            state.clone(),
            statement,
            PureFactContext::new(),
            ExecutionBudget::new().with_expression_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::ExpressionSteps)
    );

    let function = program_function(
        ProgramType::Int32,
        "id",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::variable("x")),
    );
    assert_eq!(
        prove_symbolic_program_function_execution_paths_with_budget(
            ExecutionState::new(),
            function,
            vec![crate::kernel::program_expression::int32_literal(1)],
            PureFactContext::new(),
            ExecutionBudget::new().with_function_calls(0),
        )
        .limit(),
        Some(ExecutionLimit::FunctionCalls)
    );

    let straight_line = (0..128).fold(
        program_return(crate::kernel::program_expression::int32_literal(1)),
        |tail, _| program_seq(ProgramStatement::Skip, tail),
    );
    assert_eq!(
        prove_symbolic_program_execution_paths_with_budget(
            state.clone(),
            straight_line,
            PureFactContext::new(),
            ExecutionBudget::new()
                .with_statement_steps(129)
                .with_paths(1),
        )
        .limit(),
        None,
        "a path budget is not a source-length budget; singleton continuations are free"
    );

    let branchy_statement = program_if(
        ProgramExpression::Value(int32(MachineTerm::Variable(Variable(75)))),
        program_return(crate::kernel::program_expression::int32_literal(1)),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    assert_eq!(
        prove_symbolic_program_execution_paths_with_budget(
            state,
            branchy_statement,
            PureFactContext::new(),
            ExecutionBudget::new().with_paths(1),
        )
        .limit(),
        Some(ExecutionLimit::Paths)
    );
}

#[test]
fn whole_function_default_budget_scales_with_selected_source() {
    const ASSIGNMENTS: usize = 3_334;

    let mut statements = (0..ASSIGNMENTS)
        .map(|_| program_assign("x", crate::kernel::program_expression::variable("x")))
        .chain(std::iter::once(program_return(
            crate::kernel::program_expression::variable("x"),
        )))
        .collect::<Vec<_>>();
    while statements.len() > 1 {
        let mut next = Vec::with_capacity(statements.len().div_ceil(2));
        let mut pairs = statements.into_iter();
        while let Some(first) = pairs.next() {
            next.push(match pairs.next() {
                Some(second) => program_seq(first, second),
                None => first,
            });
        }
        statements = next;
    }
    let function = program_function(
        ProgramType::Int32,
        "large_identity",
        vec![program_parameter("x", ProgramType::Int32)],
        statements.pop().expect("nonempty function body"),
    );
    let arguments = vec![crate::kernel::program_expression::int32_literal(1)];

    let fixed_budget_execution =
        prove_symbolic_program_function_verification_paths_with_environment_and_budget(
            ExecutionState::new(),
            function.clone(),
            arguments.clone(),
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            ExecutionBudget::default(),
        );
    assert_eq!(
        fixed_budget_execution.limit(),
        Some(ExecutionLimit::ExpressionSteps),
        "explicit budgets remain exact and still bound evaluator work"
    );

    let source_sized_execution =
        prove_symbolic_program_function_verification_paths_with_environment(
            ExecutionState::new(),
            function,
            arguments,
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
    assert_eq!(
        source_sized_execution.limit(),
        None,
        "selected straight-line source should not exhaust the dynamic reserve"
    );
    assert_eq!(source_sized_execution.paths().len(), 1);
}

#[test]
fn while_invariant_is_proof_obligation() {
    let pointer = Address {
        base: "block".into(),
        offset: AddressOffset::Constant(0),
    };
    let invariant = Proposition::MemoryLoadable {
        memory: SymbolicMemory::new(),
        base: pointer,
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let state = ExecutionState::new().with_local("x", int32(0));
    let statement = program_while(
        crate::kernel::program_expression::greater_than(
            crate::kernel::program_expression::variable("x"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        vec![invariant.clone()],
        program_assign(
            "x",
            crate::kernel::program_expression::subtract(
                crate::kernel::program_expression::variable("x"),
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    );
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("false loop should execute under invariant obligation");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(invariant),
            Box::new(Proposition::ProgramStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement),
                outcome: StatementOutcome::Normal(Box::new(state)),
            }),
        )
    );
}

/// A verified loop rule carries the assumptions it was verified under. When
/// several rules certify the same `while` statement from the same symbolic
/// entry state, those prerequisites are the only thing that tells them apart,
/// so applying a rule has to check them against the facts available at the
/// application site. This is the case no fixture reaches through the surface:
/// a source loop's invariant checks carry its loop index, so two source loops
/// are never the same `ProgramStatement`, and one source loop is planned once per
/// proof path.
#[test]
fn verified_loop_rules_are_selected_by_their_exact_prerequisites() {
    let (statement, base_rule) = prerequisite_loop_rule_fixture();
    let state = ExecutionState::new().with_local("i", int32(0));
    let first_guard = loop_rule_guard(1);
    let second_guard = loop_rule_guard(2);

    let mut first = base_rule.clone();
    first.required_assumptions = PureFactContext::new().assume_condition(first_guard.clone(), true);
    let mut second = base_rule.clone();
    second.required_assumptions =
        PureFactContext::new().assume_condition(second_guard.clone(), true);
    // The second rule's path set is distinguishable, so the applied paths name
    // which rule the kernel selected.
    second.paths.extend(base_rule.paths.iter().cloned());
    let environment =
        ExecutionEnvironment::new().with_verified_loop_rules([first.clone(), second.clone()]);

    let applied_first = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        PureFactContext::new().assume_condition(first_guard.clone(), true),
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(applied_first.paths().len(), first.paths.len());

    // The first rule is rejected here because its prerequisite is not
    // available, so the second rule is the one that applies.
    let applied_second = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        PureFactContext::new().assume_condition(second_guard.clone(), true),
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(applied_second.paths().len(), second.paths.len());
    assert_ne!(first.paths.len(), second.paths.len());

    // Neither prerequisite is available, so no rule applies at all.
    let applied_none = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        PureFactContext::new().assume_condition(loop_rule_guard(3), true),
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(applied_none.paths().is_empty());

    // A prerequisite that the ambient facts refute, rather than merely omit,
    // is also rejected: the check is exact availability, not consistency.
    let applied_refuted = prove_symbolic_execution_statement_verification_paths_with_environment(
        state,
        statement,
        PureFactContext::new()
            .assume_condition(first_guard, false)
            .assume_condition(second_guard, false),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(applied_refuted.paths().is_empty());
}

/// A rule's prerequisite that merely follows from the ambient facts is not
/// available: selecting the rule by proving its assumptions from whatever
/// happens to be in scope is proof planning, so the rule does not apply and
/// its own assumption has to be established where the rule is used.
#[test]
fn verified_loop_rule_prerequisites_are_not_reproved_from_ambient_facts() {
    let (statement, base_rule) = prerequisite_loop_rule_fixture();
    let state = ExecutionState::new().with_local("i", int32(0));
    let bound = MachineTerm::Variable(Variable(900_001));
    let required = ConditionTerm::signed_greater_equal(bound.clone(), MachineTerm::constant(0));
    let stronger = ConditionTerm::signed_greater_equal(bound, MachineTerm::constant(1));
    let mut rule = base_rule;
    rule.required_assumptions = PureFactContext::new().assume_condition(required.clone(), true);
    let environment = ExecutionEnvironment::new().with_verified_loop_rules([rule]);

    let stronger_facts = PureFactContext::new().assume_condition(stronger, true);
    // The retained condition checker still decides the implication; the rule
    // is rejected anyway, because deciding a prerequisite is not the same as
    // the rule's prerequisite being available.
    assert_eq!(stronger_facts.decide(&required), Some(true));
    let applied = prove_symbolic_execution_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        stronger_facts,
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(applied.paths().is_empty());

    let exact = prove_symbolic_execution_statement_verification_paths_with_environment(
        state,
        statement,
        PureFactContext::new().assume_condition(required, true),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(!exact.paths().is_empty());
}

fn loop_rule_guard(value: u32) -> ConditionTerm {
    ConditionTerm::equal(
        MachineTerm::Variable(Variable(900_000)),
        MachineTerm::constant(value),
    )
}

/// One verified `while` rule, built by ordinary loop verification, that the
/// prerequisite regressions above re-issue under different required
/// assumptions.
fn prerequisite_loop_rule_fixture() -> (ProgramStatement, VerifiedLoopRule) {
    let state = ExecutionState::new().with_local("i", int32(0));
    let statement = program_while_with_invariant_checks(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        Vec::new(),
        vec![LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("i"),
                ),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        program_assign(
            "i",
            crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("i"),
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    );
    let (_, rule) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule(
            state,
            statement.clone(),
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
    let rule = rule.expect("loop verification should produce a rule");
    assert!(!rule.paths.is_empty());
    (statement, rule)
}

/// R23's back-edge case. A loop head that holds a stable-view root can only
/// close its back edge at the *same* borrow authority. Two body paths that a
/// term-level comparison would call equal are refused here: one that handed
/// the live share away, and one that built a fresh root over the same support
/// occurrence instead of carrying the head's. The resource context, the
/// support occurrence, the viewed term, and the occurrence bindings are
/// identical in every state below; only ledger identity separates them
/// (laws 4 and 5; docs/internals/stable-views.md).
#[test]
fn loop_back_edge_refuses_a_dropped_share_or_a_regenerated_root() {
    let pointer = Address {
        base: "block".into(),
        offset: AddressOffset::Constant(0),
    };
    let viewed = view_memory_fact(pointer, 0, 1);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];

    let rooted = |ledger: BorrowLedger| {
        let participant = ledger.fresh_participant().expect("a participant");
        let opening = ledger
            .borrowed_contract_input(participant, support, viewed.clone(), None)
            .expect("a checked contract input root");
        let ledger = ledger.apply(&opening.transition).expect("the root applies");
        (ledger, participant, opening)
    };

    let (head_ledger, participant, opening) = rooted(BorrowLedger::new());
    let bindings = crate::kernel::borrows::BorrowBindings::default().with_inserted(
        support,
        crate::kernel::borrows::BorrowBinding {
            borrow: opening.borrow,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: viewed.clone(),
            hold: None,
        },
    );
    let at = |ledger: BorrowLedger, participant| {
        ExecutionState::new()
            .with_resource_context(resources.clone())
            .with_borrow_ledger(Some(ledger))
            .with_borrow_participant(Some(participant))
            .with_borrow_bindings(bindings.clone())
    };
    let head = at(head_ledger.clone(), participant);
    let assumptions = PureFactContext::new();
    let definitions: &[CompositeResourceDefinition] = &[];

    // The head state closes its own back edge.
    assert_eq!(
        crate::kernel::loop_state_components_match_at_back_edge(
            &head,
            &head,
            &assumptions,
            definitions,
        ),
        Ok(())
    );

    // A body path that generated a fresh root over the same resource, in the
    // head's own arena and for the head's own participant. The viewed term
    // and the support occurrence are the ones the head used, and the
    // participant and the occurrence bindings are unchanged, so ledger
    // identity is the only thing left to notice it.
    let regenerated = head_ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a second contract input root over the same support");
    assert_eq!(
        regenerated.description.viewed(),
        opening.description.viewed()
    );
    assert_eq!(
        regenerated.description.support(),
        opening.description.support()
    );
    assert_ne!(regenerated.borrow, opening.borrow);
    let regenerated_state = at(
        head_ledger
            .apply(&regenerated.transition)
            .expect("the regenerated root applies"),
        participant,
    );
    let refusal = crate::kernel::loop_state_components_match_at_back_edge(
        &head,
        &regenerated_state,
        &assumptions,
        definitions,
    )
    .expect_err("a back edge cannot regenerate the head's root");
    assert!(
        refusal.contains("stable-view borrow authority"),
        "{refusal}"
    );

    // A body path that handed the live share to someone else.
    let reader = head_ledger
        .fresh_participant()
        .expect("a second participant");
    let transfer = head_ledger
        .transfer(opening.root_share, participant, reader)
        .expect("the share transfers");
    let dropped = at(
        head_ledger.apply(&transfer).expect("the transfer applies"),
        participant,
    );
    let refusal = crate::kernel::loop_state_components_match_at_back_edge(
        &head,
        &dropped,
        &assumptions,
        definitions,
    )
    .expect_err("a back edge cannot discard the share the head holds");
    assert!(
        refusal.contains("stable-view borrow authority"),
        "{refusal}"
    );
}

#[test]
fn loop_entry_goals_retain_satisfied_duplicate_declarations() {
    let state = ExecutionState::new().with_local("i", int32(0));
    let proposition = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: ComparisonOperator::LessEqual,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("i")),
    };
    let checks = (0..2)
        .map(|index| {
            LoopInvariantCheck::new(
                proposition.clone(),
                Some(format!("invariant {index}")),
                None,
            )
        })
        .collect::<Vec<_>>();
    let assumptions = PureFactContext::new();
    let goals = loop_entry_goals(&state, &checks, &assumptions).unwrap();
    assert_eq!(goals.declarations().len(), 2);
    for (index, declaration) in goals.declarations().iter().enumerate() {
        assert_eq!(declaration.len(), 1);
        assert_eq!(
            declaration[0].context(),
            Some(format!("invariant {index}").as_str())
        );
        assert!(declaration[0].introductions().is_some());
    }
    assert_eq!(
        goals.declarations()[0][0].proposition(),
        goals.declarations()[1][0].proposition()
    );
    assert!(
        matches!(&goals.declarations()[0][0].proposition(), condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { .. }, _))))
    );
    assert!(
        loop_invariant_obligations_at_entry(&state, &checks, &assumptions)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn loop_entry_goals_preserve_guarded_judgments() {
    let state = ExecutionState::new().with_local("i", int32(MachineTerm::Variable(Variable(600))));
    let proposition = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: ComparisonOperator::LessEqual,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("i")),
    };
    let checks = (0..2)
        .map(|index| {
            LoopInvariantCheck::new(
                proposition.clone(),
                Some(format!("invariant {index}")),
                None,
            )
        })
        .collect::<Vec<_>>();
    let assumptions = PureFactContext::new();
    let goals = loop_entry_goals(&state, &checks, &assumptions).unwrap();
    assert_eq!(goals.declarations().len(), 2);
    assert!(goals.declarations().iter().all(|goals| goals.len() == 1));
    let first = &goals.declarations()[0][0];
    let second = &goals.declarations()[1][0];
    assert!(
        matches!(second.proposition(), Proposition::Implies(guard, body)
        if guard.as_ref() == first.proposition() && body.as_ref() == first.proposition())
    );
    let outstanding = loop_invariant_obligations_at_entry(&state, &checks, &assumptions).unwrap();
    assert_eq!(
        goals
            .declarations()
            .iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>(),
        outstanding
    );
}

/// `a != 0` as the kernel spells a short-circuit guard operand's fact.
fn guard_operand_fact(variable: u64, nonzero: bool) -> Proposition {
    Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(variable))),
            right: Box::new(MachineTerm::constant(0)),
        },
        !nonzero,
    )
}

/// The guard paths' disjunction reads in short-circuit order however the
/// kernel enumerated the paths, and drops the conjunct the short-circuit path
/// refutes. `while (a || b)` is entered by `a != 0`, or by `a == 0 && b != 0`;
/// what a proof writes is `a != 0 or b != 0`.
#[test]
fn guard_path_disjunction_reads_in_short_circuit_order() {
    let (a_nonzero, a_zero) = (guard_operand_fact(0, true), guard_operand_fact(0, false));
    let b_nonzero = guard_operand_fact(1, true);
    let expected = Proposition::Or(Box::new(a_nonzero.clone()), Box::new(b_nonzero.clone()));
    let short_circuit_first = vec![
        vec![a_nonzero.clone()],
        vec![a_zero.clone(), b_nonzero.clone()],
    ];
    let short_circuit_last = vec![vec![a_zero, b_nonzero], vec![a_nonzero]];
    for paths in [short_circuit_first, short_circuit_last] {
        assert_eq!(
            crate::kernel::loops::guard_path_disjunction(&paths),
            Some(expected.clone()),
            "the disjunction must not depend on the order the paths were enumerated in"
        );
    }
}

/// A path that states nothing of its own makes the disjunction vacuously
/// true, and a single path is not a disjunction at all. Neither exports
/// anything for a proof to split on.
#[test]
fn guard_path_disjunction_has_nothing_to_export_without_two_stating_paths() {
    let a_nonzero = guard_operand_fact(0, true);
    let b_nonzero = guard_operand_fact(1, true);
    assert_eq!(
        crate::kernel::loops::guard_path_disjunction(&[
            vec![a_nonzero.clone()],
            vec![b_nonzero],
            Vec::new(),
        ]),
        None
    );
    assert_eq!(
        crate::kernel::loops::guard_path_disjunction(std::slice::from_ref(&vec![a_nonzero])),
        None
    );
}

/// A branch join invents identities too, and they come from the execution's
/// one counter. The join used to count from the base of that counter's range
/// with an allocator of its own, and a caller carried the arms' counter
/// across the join unchanged, so the next allocation that does not first
/// consult a reserved set -- a heap identity, a re-bound loop binder's model
/// fields, an arbitrary algebraic binding, an aggregate field -- was handed
/// an identity a live abstracted local was still using. With `malloc` after
/// a `branch`, `have fresh == picked by { close(); }` closed outright
/// (mdtest `branch_join_variable_is_not_a_later_allocation`).
///
/// The join now counts from the arms' counter and reports where it left it,
/// so the continuation cannot start below what the join spent.
#[test]
fn a_post_join_allocation_never_reuses_a_join_abstracted_variable() {
    let then_state = ExecutionState::new()
        .with_local("kept", int32(7))
        .with_local("picked", int32(1));
    let else_state = then_state.clone().with_local("picked", int32(2));
    let siblings = [&then_state, &else_state];

    // The arms have issued nothing of their own, which is the case the old
    // code shared a starting point with.
    let arms_next_kernel_variable = 0;
    let abstraction = abstract_execution_state_for_interface_join_across(
        &then_state,
        &siblings,
        arms_next_kernel_variable,
    )
    .expect("the arms have one deterministic abstraction");
    let local_native_output_2533 = abstraction.state.locals().get_native("picked");
    let Some(ProgramValue::Int32(MachineTerm::Variable(abstracted))) =
        local_native_output_2533.as_deref()
    else {
        panic!("a local the arms disagree on abstracts to one symbolic int32");
    };

    // Keeping the arms' counter is exactly the bug: the first identity a
    // budget built from it hands out is the one the join just issued.
    let mut stale = ExecutionBudget::default().with_next_kernel_variable(arms_next_kernel_variable);
    assert_eq!(
        stale
            .allocate_kernel_variable()
            .expect("the counter is nowhere near its ceiling"),
        *abstracted,
        "the arms' counter must not still point at an identity the join issued"
    );

    // The counter the join reports is above everything it issued, and stays
    // above it however many identities the continuation goes on to spend.
    let mut budget =
        ExecutionBudget::default().with_next_kernel_variable(abstraction.next_kernel_variable);
    for _ in 0..8 {
        let identity = budget
            .allocate_kernel_variable()
            .expect("the counter is nowhere near its ceiling");
        assert_ne!(
            identity, *abstracted,
            "a post-join allocation reused a live join-abstracted identity"
        );
    }
}

/// The counter a joined execution continues with is the kernel's, not a
/// caller's. `ExecutionProofCore::next_kernel_variable` is private and moves
/// only through `advance_kernel_variable_mark`, which refuses a rewind, and
/// `record_interface_branch_join` installs the mark of the abstraction the
/// kernel recomputed itself. The surface used to choose the successor's
/// counter -- the maximum of the two arms', neither of which the join had
/// moved -- and nothing checked it.
#[test]
fn a_join_successor_cannot_continue_from_a_rewound_counter() {
    use crate::kernel::proof::{ExecutionFrontier, ExecutionProofCore};

    let then_state = ExecutionState::new()
        .with_local("kept", int32(7))
        .with_local("picked", int32(1));
    let else_state = then_state.clone().with_local("picked", int32(2));
    let siblings = [&then_state, &else_state];

    let arms_next_kernel_variable = 0;
    let abstraction = abstract_execution_state_for_interface_join_across(
        &then_state,
        &siblings,
        arms_next_kernel_variable,
    )
    .expect("the arms have one deterministic abstraction");
    assert!(
        abstraction.next_kernel_variable > arms_next_kernel_variable,
        "the join spent identities, so its mark is above the arms'"
    );

    let mut successor =
        ExecutionProofCore::at_entry(abstraction.state.clone(), ExecutionFrontier::default());
    successor
        .advance_kernel_variable_mark(abstraction.next_kernel_variable)
        .expect("the join's mark is above the successor's counter");
    assert_eq!(
        successor.kernel_variable_mark(),
        abstraction.next_kernel_variable
    );
    assert_eq!(
        successor.advance_kernel_variable_mark(arms_next_kernel_variable),
        Err("an execution's fresh-variable counter cannot move backwards"),
        "carrying the arms' counter across the join is exactly what is refused"
    );
    assert_eq!(
        successor.kernel_variable_mark(),
        abstraction.next_kernel_variable,
        "a refused rewind leaves the counter where the kernel put it"
    );
}

/// Every kernel allocation counts up from one base, and the ranges above it
/// belong to producers that pick identities by a constant base and a hash:
/// the surface's quantifier variables and the algebraic binders. Those producers cannot avoid an execution that has counted into
/// their range, so the execution refuses at the lowest of them instead --
/// promptly, by name, and without a panic.
#[test]
fn the_execution_identity_counter_refuses_at_the_first_reserved_range() {
    let span = ExecutionBudget::KERNEL_VARIABLE_CEILING - ExecutionBudget::KERNEL_VARIABLE_BASE;
    let mut budget = ExecutionBudget::default().with_next_kernel_variable(span - 1);
    assert_eq!(
        budget.allocate_kernel_variable(),
        Ok(Variable(ExecutionBudget::KERNEL_VARIABLE_CEILING - 1)),
        "the last identity below the ceiling is still the execution's"
    );
    let refusal = Err(ExecutionLimit::KernelVariables {
        ceiling: ExecutionBudget::KERNEL_VARIABLE_CEILING,
    });
    assert_eq!(budget.allocate_kernel_variable(), refusal);

    // A reserved-set stream refuses through the same ceiling rather than
    // wrapping around onto identities it has already issued.
    let mut variables = KernelVariableGenerator::fresh_for_execution(BTreeSet::new());
    assert_eq!(variables.next_in(&mut budget), refusal);

    // The ceiling is below the first range it protects: the surface's
    // quantifier base (`2_000_000`) and algebraic base (`4_000_000`). Spec
    // fold binders have their own origin, so no execution identity is one.
    for name in ["index", "accumulator", "item"] {
        let binder = crate::kernel::spec::spec_fold_bound_variable(&name.into(), 0);
        assert!(
            binder.is_spec_fold_binder() && binder != Variable(binder.0),
            "a spec fold binder must be no identity an execution can issue"
        );
    }
}

/// A loop head invents two unrelated things: an arbitrary value for every
/// local the body modifies, drawn from the execution's fresh-name stream, and
/// an arbitrary model for every resource instance the loop re-binds, drawn
/// from the execution budget. Those are one allocator. When they were two
/// streams over the same range they both started at `v1000000`, so the
/// havocked `i` and the re-bound binder's `c.rank` were literally the same
/// kernel variable and `have c.rank == i by { close(); }` closed with nothing
/// relating them (mdtest `loop_resource_binder_field_is_not_a_local`).
#[test]
fn a_rebound_binder_field_never_reuses_a_havocked_local_variable() {
    use crate::kernel::functions::arbitrary_resource_instance_fields;

    let mut budget = ExecutionBudget::new();
    let mut variables = KernelVariableGenerator::fresh_for_execution(BTreeSet::new());
    let schema = ResourceFieldSchema::new(vec![(
        "rank".to_string(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .expect("one int32 model field");

    let mut issued = BTreeSet::new();
    for _ in 0..4 {
        let local = variables
            .next_in(&mut budget)
            .expect("the execution's counter is nowhere near its ceiling");
        assert!(
            issued.insert(local),
            "the loop-local havoc stream reissued {local:?}"
        );
        let fields = arbitrary_resource_instance_fields(
            &schema,
            crate::kernel::functions::ModelFieldMintSite {
                identity: InstanceId::from_variable(Variable(1)),
                minted_by: &crate::kernel::model_fields::ModelMint::Refinement,
            },
            &mut budget,
        )
        .expect("the execution's counter is nowhere near its ceiling");
        let Some(ResourceFieldValue::Program(ProgramValue::Int32(MachineTerm::Variable(field)))) =
            fields.get(0)
        else {
            panic!("an int32 model field is one symbolic int32: {fields:?}");
        };
        assert_ne!(
            local, *field,
            "a re-bound binder's model field took the same kernel variable as a havocked local"
        );
        assert!(
            issued.insert(*field),
            "a re-bound binder's model field reused {field:?}"
        );
    }
}

/// A loop head's preservation contexts are built by their own evaluation, and
/// that evaluation used to start a fresh `ExecutionBudget` -- restarting the
/// execution's identity counter at the base of its range in the middle of the
/// execution. Everything the head then invented (the havoc of every local the
/// body modifies, the memory-havoc marker, a re-bound binder's model fields,
/// an arbitrary algebraic binding) could carry an identity the enclosing
/// execution had already handed to something live.
///
/// The head now counts from the execution's counter and reports where it left
/// it, so neither the iteration that continues past the loop nor the body
/// proof that runs inside it can start below what the head spent.
#[test]
fn loop_preservation_contexts_allocate_above_the_executions_counter() {
    let loop_entry_state = ExecutionState::new()
        .with_local("i", int32(0))
        .with_local("n", int32(MachineTerm::Variable(Variable(7))));
    let condition = crate::kernel::program_expression::less_than(
        crate::kernel::program_expression::variable("i"),
        crate::kernel::program_expression::variable("n"),
    );
    let body = program_assign(
        "i",
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );

    let head_identities = |spent: u64| -> (BTreeSet<Variable>, u64) {
        let contexts = loop_preservation_contexts(
            &loop_entry_state,
            &condition,
            &[],
            &[],
            &[],
            &[],
            &body,
            &PureFactContext::new(),
            spent,
        )
        .expect("a bare counting loop has a preservation context");
        let [context] = contexts.as_slice() else {
            panic!("a single-guard loop has one preservation context");
        };
        let mut identities = BTreeSet::new();
        crate::kernel::reasoning::collect_execution_state_bitvector_variables(
            context.state(),
            &mut identities,
        );
        // Keep only what an execution can issue: the parameter's own identity
        // is below the range and says nothing about the head's allocations.
        identities.retain(|variable| {
            variable.0 >= ExecutionBudget::KERNEL_VARIABLE_BASE
                && variable.0 < ExecutionBudget::KERNEL_VARIABLE_CEILING
        });
        (identities, context.next_kernel_variable())
    };

    let (fresh_head, fresh_mark) = head_identities(0);
    assert!(
        !fresh_head.is_empty(),
        "the head havocs the local the body modifies"
    );
    assert!(
        fresh_mark > 0,
        "the head reports the identities it spent: {fresh_mark}"
    );

    // An execution that has already issued identities gets a head above them,
    // and a mark above what it inherited.
    let spent = 64;
    let (later_head, later_mark) = head_identities(spent);
    let floor = ExecutionBudget::KERNEL_VARIABLE_BASE + spent;
    for identity in &later_head {
        assert!(
            identity.0 >= floor,
            "a loop head reused {identity:?}, which the execution had already issued"
        );
    }
    assert_eq!(
        later_mark,
        spent + fresh_mark,
        "the head spends the same identities wherever it starts, and reports where it left off"
    );
    assert!(
        fresh_head
            .iter()
            .all(|identity| !later_head.contains(identity)),
        "the two heads must not agree on an identity: the second counts from {spent}"
    );
}

/// A budget is either the start of an execution or a continuation of one.
///
/// `ExecutionBudget` used to hand a fresh-identity counter to whoever wrote
/// nothing at all: `Default` started it at the base of the range, so an
/// evaluation in the middle of an execution restarted it by omission. There is
/// no default outside tests now, and the two constructors cannot issue the
/// same identity.
#[test]
fn a_budget_starts_an_execution_or_continues_one() {
    let mut start = ExecutionBudget::for_new_execution();
    assert_eq!(start.next_kernel_variable(), 0, "a start has spent nothing");
    let first = start.allocate_kernel_variable().expect("an identity");
    assert_eq!(
        first,
        Variable(ExecutionBudget::KERNEL_VARIABLE_BASE),
        "a new execution counts from the base of the range"
    );

    let spent = 64;
    let mut continuation = ExecutionBudget::continuing_from(spent);
    assert_eq!(continuation.next_kernel_variable(), spent);
    let continued = continuation
        .allocate_kernel_variable()
        .expect("an identity above the mark");
    assert_eq!(
        continued,
        Variable(ExecutionBudget::KERNEL_VARIABLE_BASE + spent),
        "a continuation counts from the mark it was given"
    );
    assert_ne!(
        first, continued,
        "a continuation must not re-issue what the execution already spent"
    );
}

/// The mark is execution-relative, and reading it out of one budget and into
/// the next must not lose the base.
///
/// `FunctionContractRefinementContext` carried the counter as a raw absolute
/// field and rebuilt its obligations' budget from that field directly. It now
/// reads the mark through `next_kernel_variable` and rebuilds with
/// `continuing_from`, which is correct exactly while the two agree on the
/// representation. This is that agreement, stated once.
#[test]
fn a_reached_mark_round_trips_into_the_next_budget() {
    let mut first = ExecutionBudget::for_new_execution();
    let issued = (0..5)
        .map(|_| first.allocate_kernel_variable().expect("an identity"))
        .collect::<BTreeSet<_>>();

    let mut next = ExecutionBudget::continuing_from(first.next_kernel_variable());
    for _ in 0..5 {
        let identity = next.allocate_kernel_variable().expect("an identity");
        assert!(
            !issued.contains(&identity),
            "{identity:?} was already issued by the budget this one continues"
        );
        assert!(
            identity.0 >= ExecutionBudget::KERNEL_VARIABLE_BASE + 5,
            "{identity:?} is below the mark the first budget reached"
        );
    }
}

/// A budget beside a live state cannot invent an execution identity at all.
///
/// `ExecutionBudget::beside_live_state` evaluates over a state that belongs
/// to an execution whose mark the caller does not carry, so an
/// identity counted from the base would name a havocked local, a join
/// abstraction or a heap block that state already holds. Nothing those sites
/// invent needs one: a match binder has its own origin, and
/// anything else has to be given the execution's mark. The request is a defect
/// in the caller and refuses as one.
#[test]
fn a_budget_beside_a_live_state_refuses_an_execution_identity() {
    let mut beside = ExecutionBudget::beside_live_state();
    assert_eq!(
        beside.allocate_kernel_variable(),
        Err(ExecutionLimit::ExecutionIdentityBesideLiveState),
        "an execution identity beside a live state is a defect, not a restart"
    );
    assert_eq!(
        beside.allocate_match_binder_variable(),
        Ok(Variable::match_binder(0)),
        "a bound variable is not an execution identity and stays available"
    );
}

/// Spec fold binders have their own origin, so none equals an identity any
/// other producer that can contribute free variables to a fold body mints.
#[test]
fn a_spec_fold_binder_is_no_other_producer_s_identity() {
    let mut allocated = std::collections::BTreeSet::new();
    for name in ["accumulator", "item", "index", "sum", "nested"] {
        for salt in [0, 1] {
            let variable = crate::kernel::spec::spec_fold_bound_variable(&name.into(), salt);
            assert!(
                variable.is_spec_fold_binder(),
                "{name} salt {salt}: {variable:?}"
            );
            assert_ne!(variable, Variable(variable.0), "{name} salt {salt}");
            assert!(!variable.is_match_binder(), "{name} salt {salt}");
            assert!(allocated.insert(variable), "{name} salt {salt} aliases");
        }
    }
}

/// Match binders are bound variables with their own origin, so no binder
/// equals an identity any other producer mints, whatever its number: a binder
/// that equals a free identity is exactly the capture the binder-elimination
/// rewrite cannot see.
#[test]
fn a_match_binder_is_no_other_producer_s_identity() {
    let mut budget = ExecutionBudget::for_new_execution();
    let first = budget
        .allocate_match_binder_variable()
        .expect("a match binder");
    let second = budget
        .allocate_match_binder_variable()
        .expect("a second match binder");
    assert_ne!(
        first, second,
        "two binders of one lowering -- a nested match's included -- are distinct"
    );
    for binder in [first, second] {
        assert!(
            ExecutionBudget::is_match_binder_variable(binder),
            "{binder:?} is not recognized as a binder, so a rewrite would refuse it"
        );
    }
    for binder in [first, second] {
        assert_ne!(
            binder,
            Variable(binder.0),
            "{binder:?} equals the C or execution identity with its number"
        );
        assert!(
            !ExecutionBudget::is_match_binder_variable(Variable(binder.0)),
            "an identity with a binder's number must never pass as a binder"
        );
    }
    assert!(
        !ExecutionBudget::is_match_binder_variable(Variable(ExecutionBudget::KERNEL_VARIABLE_BASE)),
        "the first identity a loop havoc issues must never pass as a binder"
    );
}

/// Variables order by origin first: every ordinary variable, whatever its
/// number, before `Variable::FIRST_NON_ORDINARY`, and every other origin at
/// or after it, so a query for the greatest ordinary variable bounds itself
/// by the sentinel and a producer's variables are one contiguous run.
#[test]
fn variables_order_by_origin_before_number() {
    let others = [
        Variable::FIRST_NON_ORDINARY,
        Variable::match_binder(0),
        Variable::spec_fold_binder(3),
        Variable::witness(0),
        Variable::produced(crate::kernel::Producer::ProofQuantifier, 0),
    ];
    for other in others {
        assert!(Variable(u64::MAX) < other, "{other:?}");
        assert!(Variable::FIRST_NON_ORDINARY <= other, "{other:?}");
        assert!(!other.is_ordinary() || other == Variable::FIRST_NON_ORDINARY);
    }
    assert!(Variable(0).is_ordinary() && !Variable::FIRST_NON_ORDINARY.is_ordinary());
    let set: std::collections::BTreeSet<_> = [
        Variable(7),
        Variable::witness(1),
        Variable(u64::MAX - 1),
        Variable::match_binder(2),
    ]
    .into_iter()
    .collect();
    assert_eq!(
        set.range(..Variable::FIRST_NON_ORDINARY).next_back(),
        Some(&Variable(u64::MAX - 1))
    );
    let witnesses: Vec<_> = set
        .range(Variable::witness(0)..=Variable::witness(u64::MAX))
        .collect();
    assert_eq!(witnesses, [&Variable::witness(1)]);
}

/// A universal introduction's witness is a free identity standing for an
/// arbitrary value, and it has to miss every producer that can appear free
/// beside it — starting with the C identities, which the freshener used to
/// count into from `Variable(0)`. Witnesses have their own origin, so no
/// identity another producer mints is one, whatever its number.
#[test]
fn a_universal_witness_is_no_other_producer_s_identity() {
    for number in [0, 1, ExecutionBudget::KERNEL_VARIABLE_BASE, 1 << 42] {
        assert!(
            !ExecutionBudget::is_universal_witness_variable(Variable(number)),
            "an ordinary identity numbered {number} must never pass as a witness"
        );
        assert!(ExecutionBudget::is_universal_witness_variable(
            Variable::witness(number)
        ));
        assert_ne!(Variable::witness(number), Variable(number));
    }
    assert!(!ExecutionBudget::is_universal_witness_variable(
        Variable::match_binder(0)
    ));
}

/// A loop invariant the entry lowering cannot evaluate names where it
/// stopped, never the kernel's `ExecutionLimit` variant. It used to read
/// `could not lower entry invariants: ResourceFieldInstanceUnavailable`.
#[test]
fn loop_entry_lowering_limit_is_spelled_in_words() {
    let state = ExecutionState::new().with_local("i", int32(0));
    let proposition = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: ComparisonOperator::LessEqual,
        right: SpecExpression::ResourceField {
            projection: ResourceFieldProjection {
                identity: InstanceId::from_variable(Variable(10)).into(),
                children: vec![],
                field_name: None,
                field_index: 0,
                at_entry: false,
            },
            program_type: ProgramType::Int32,
        },
    };
    let checks = vec![LoopInvariantCheck::new(
        proposition,
        Some("invariant 0".to_string()),
        None,
    )];
    let assumptions = PureFactContext::new();
    let refusal = loop_entry_goals(&state, &checks, &assumptions).unwrap_err();
    assert_eq!(
        refusal,
        "could not lower entry invariants: they stopped at a model field of a resource instance this state does not hold"
    );
}

/// The declaration `struct node items[length] = {…}` as the C frontend
/// lowers it when the declaration zero-fills: a 16-byte struct whose
/// element zero stores are an int32 key, a byte tag and a pointer, then
/// the stores of the fields the initializer writes.
fn zero_filled_node_array(
    length: u32,
    written: &[(u32, ProgramValue, ProgramType)],
) -> ProgramStatement {
    let fill = ZeroFill::new(
        16,
        length,
        vec![
            ZeroCell::new(0, ProgramType::Int32, false, int32(0)),
            ZeroCell::new(4, ProgramType::UInt8, false, int32(0)),
            ZeroCell::new(8, ProgramType::Int32Pointer, false, int32(0)),
        ],
    );
    written.iter().fold(
        program_declare_with_zero_fill(
            "items",
            ProgramType::UInt8Array(length * 16),
            false,
            false,
            false,
            false,
            Some(fill),
        ),
        |statement, (offset, value, value_type)| {
            program_seq(
                statement,
                program_typed_store(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable("items"),
                        *offset,
                    ),
                    ProgramExpression::Value(value.clone()),
                    *value_type,
                ),
            )
        },
    )
}

/// `statements` in order as a balanced sequence, so executing a long one
/// does not recurse once per statement.
fn balanced_c_seq(statements: &[ProgramStatement]) -> ProgramStatement {
    match statements {
        [] => ProgramStatement::Skip,
        [statement] => statement.clone(),
        _ => {
            let (first, second) = statements.split_at(statements.len() / 2);
            program_seq(balanced_c_seq(first), balanced_c_seq(second))
        }
    }
}

fn load_items_field(
    state: &ExecutionState,
    offset: u32,
    value_type: ProgramType,
) -> ExpressionOutcome {
    let paths = evaluate_program_expression_paths(
        state,
        &crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::pointer_offset_bytes(
                crate::kernel::program_expression::variable("items"),
                offset,
            ),
            value_type,
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("a field load executes");
    let [path] = paths.as_slice() else {
        panic!("one load path: {paths:?}");
    };
    path.outcome.clone()
}

fn execute_declaration(state: &ExecutionState, statement: &ProgramStatement) -> ExecutionState {
    normal_state(
        &execute_execution_statement_paths(
            state,
            statement,
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
        )
        .expect("the declaration executes"),
    )
}

/// A zero-filled automatic struct array holds exactly the cells of storing
/// every element's zero fields and then the written fields one by one, and
/// an array declared without an initializer holds no cell, so reading one
/// of its elements stays an uninitialized read.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.3s in the parallel gate"]
fn a_zero_filled_automatic_array_holds_exactly_the_per_element_stores() {
    for length in [1u32, 2, 5, 64, 65] {
        let written = [
            (16 * (length - 1), int32(7), ProgramType::Int32),
            (4, uint8(9), ProgramType::UInt8),
        ];
        let filled = execute_declaration(
            &ExecutionState::new(),
            &zero_filled_node_array(length, &written),
        );
        let stores = (0..length)
            .flat_map(|element| {
                [
                    (16 * element, int32(0), ProgramType::Int32),
                    (16 * element + 4, int32(0), ProgramType::UInt8),
                    (16 * element + 8, int32(0), ProgramType::Int32Pointer),
                ]
            })
            .chain(written.iter().cloned())
            .map(|(offset, value, value_type)| {
                program_typed_store(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable("items"),
                        offset,
                    ),
                    ProgramExpression::Value(value),
                    value_type,
                )
            })
            .collect::<Vec<_>>();
        let per_element = program_seq(
            program_declare("items", ProgramType::UInt8Array(length * 16)),
            balanced_c_seq(&stores),
        );
        let stored = execute_declaration(&ExecutionState::new(), &per_element);
        assert_eq!(
            filled.memory().cells.logical(),
            stored.memory().cells.logical(),
            "[{length}] holds the per-element cells"
        );
        assert!(
            filled.memory().cells.representation_len() <= 5,
            "[{length}] is three runs and two written cells"
        );
        let declared = execute_declaration(
            &ExecutionState::new(),
            &program_declare("items", ProgramType::UInt8Array(length * 16)),
        );
        assert_eq!(
            load_items_field(&declared, 16 * (length - 1), ProgramType::Int32),
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            "[{length}] an array declared without an initializer is uninitialized"
        );
    }
}

fn assert_statement_reserves_application_integer_argument(
    invariant: SpecProposition,
    held: Variable,
) {
    let statement = program_while_with_invariant_checks(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        Vec::new(),
        vec![LoopInvariantCheck::new(invariant, None, None)],
        program_assign(
            "i",
            crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("i"),
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    );
    let mut reserved = BTreeSet::new();
    crate::kernel::reasoning::collect_execution_statement_bitvector_variables(
        &statement,
        &mut reserved,
    );
    let mut budget = ExecutionBudget::for_new_execution();
    let mut variables = KernelVariableGenerator::fresh_for_execution(reserved);
    assert_ne!(variables.next_in(&mut budget).unwrap(), held);
}

#[test]
fn statement_reservations_cover_integer_arguments_of_machine_applications() {
    let held = Variable(ExecutionBudget::KERNEL_VARIABLE_BASE);
    let call = SpecExpression::PureFunctionApplication {
        name: "f".into(),
        arguments: vec![SpecPureFunctionArgument::Integer(
            SpecIntegerExpression::Term(IntegerTerm::var(held)),
        )],
        result_type: ProgramType::Int32,
        pointer_result: None,
        result_object_class: None,
    };
    assert_statement_reserves_application_integer_argument(
        SpecProposition::Comparison {
            left: call,
            operator: ComparisonOperator::LessEqual,
            right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "i",
            )),
        },
        held,
    );
}

#[test]
fn statement_reservations_cover_integer_arguments_of_algebraic_applications() {
    let held = Variable(ExecutionBudget::KERNEL_VARIABLE_BASE);
    let ty = AlgebraicType::parameter("T".into());
    let call = SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::PureFunctionApplication {
            name: "g".into(),
            arguments: vec![SpecPureFunctionArgument::Integer(
                SpecIntegerExpression::Term(IntegerTerm::var(held)),
            )],
        },
    };
    assert_statement_reserves_application_integer_argument(
        SpecProposition::AlgebraicComparison {
            left: call,
            equal: true,
            right: SpecAlgebraicExpression {
                algebraic_type: ty,
                node: SpecAlgebraicExpressionNode::Variable(Variable(99)),
            },
        },
        held,
    );
}

/// Deferring a statement's input walk must still reserve all existing names
/// before its first allocation, exactly once. Stores that allocate nothing
/// should never pay for this walk.
#[test]
fn deferred_execution_reservations_skip_unused_scans_and_avoid_collisions() {
    let scans = std::cell::Cell::new(0);
    let collect = || {
        scans.set(scans.get() + 1);
        BTreeSet::from([Variable(1_000_000), Variable(1_000_002)])
    };
    let shared = std::sync::Arc::new(BTreeSet::from([Variable(1_000_001)]));
    drop(
        KernelVariableGenerator::fresh_for_execution_with_deferred_reservations(
            collect,
            shared.clone(),
        ),
    );
    assert_eq!(scans.get(), 0);
    let mut generator =
        KernelVariableGenerator::fresh_for_execution_with_deferred_reservations(collect, shared);
    let mut budget = ExecutionBudget::new();
    assert_eq!(generator.next_in(&mut budget), Ok(Variable(1_000_003)));
    assert_eq!(generator.next_in(&mut budget), Ok(Variable(1_000_004)));
    assert_eq!(scans.get(), 1);
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/execution_tests.rs");
}

#[test]
fn loop_join_reports_the_local_and_both_object_classes() {
    use crate::kernel::effective_type::{CAccessClass, CStructClass};
    let pointer = |class| {
        ProgramValue::Pointer(
            Pointer::new(
                Address::symbolic(Variable(987_001)),
                ProgramType::Int32Pointer,
            )
            .with_object_class(class),
        )
    };
    let node = CAccessClass::Struct(CStructClass::opaque("node"));
    let other = CAccessClass::Struct(CStructClass::opaque("other"));
    let head = ExecutionState::new().with_local("parent", pointer(Some(node.clone())));
    let assumptions = PureFactContext::new();
    for (class, expected) in [
        (Some(other), "struct other"),
        (None, "unknown (no retained object class)"),
    ] {
        let back = ExecutionState::new().with_local("parent", pointer(class));
        let error =
            loop_state_components_match_at_back_edge(&head, &back, &assumptions, &[]).unwrap_err();
        assert!(error.contains("pointer local `parent`: loop-head object class: struct node; back-edge object class: "), "{error}");
        assert!(error.ends_with(expected), "{error}");
    }
    let back = ExecutionState::new().with_local("parent", pointer(Some(node)));
    assert!(loop_state_components_match_at_back_edge(&head, &back, &assumptions, &[]).is_ok());
}

#[test]
fn loop_join_accepts_null_without_restoring_an_object_class() {
    use crate::kernel::effective_type::{CAccessClass, CStructClass};
    let node = CAccessClass::Struct(CStructClass::opaque("node"));
    let head_pointer = Pointer::new(
        Address::symbolic(Variable(987_010)),
        ProgramType::Int32Pointer,
    )
    .with_object_class(Some(node));
    let head = ExecutionState::new().with_local("parent", ProgramValue::Pointer(head_pointer));
    let unknown = Pointer::new(
        Address::symbolic(Variable(987_011)),
        ProgramType::Int32Pointer,
    );
    let null = Pointer::new(Address::null(), ProgramType::Int32Pointer);
    let empty = PureFactContext::new();
    let known_null = empty.clone().assume_condition(
        ConditionTerm::address_equal(unknown.address().clone(), Address::null()),
        true,
    );
    for (pointer, facts) in [(null, &empty), (unknown.clone(), &known_null)] {
        let back = ExecutionState::new().with_local("parent", ProgramValue::Pointer(pointer));
        assert!(loop_state_components_match_at_back_edge(&head, &back, facts, &[]).is_ok());
        assert!(
            matches!(back.locals().get_native("parent").as_deref(), Some(ProgramValue::Pointer(p)) if p.object_class().is_none())
        );
    }
    let back = ExecutionState::new().with_local("parent", ProgramValue::Pointer(unknown.clone()));
    assert!(loop_state_components_match_at_back_edge(&head, &back, &empty, &[]).is_err());
    let nonnull = empty.assume_condition(
        ConditionTerm::address_equal(unknown.address().clone(), Address::null()),
        false,
    );
    assert!(loop_state_components_match_at_back_edge(&head, &back, &nonnull, &[]).is_err());
}

#[test]
fn numeric_descent_is_owed_only_on_a_continuing_loop_edge() {
    use crate::kernel::program_expression::{less_than, subtract, uint32_literal, variable};
    for (next, expect_descent) in [(4, false), (3, true)] {
        let statement = program_while(
            less_than(variable("x"), uint32_literal(4)),
            vec![],
            program_assign("x", uint32_literal(next)),
        )
        .with_loop_ranking_measures(vec![RankingComponent::ProgramExpression(subtract(
            uint32_literal(3),
            variable("x"),
        ))]);
        let execution = prove_symbolic_execution_statement_verification_paths_with_environment(
            ExecutionState::new().with_local("x", uint32(3)),
            statement,
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
        assert!(execution.limit.is_none());
        assert!(!execution.paths.is_empty());
        let owes_descent = execution
            .paths
            .iter()
            .flat_map(|path| &path.obligations)
            .any(|obligation| {
                obligation
                    .context()
                    .is_some_and(|context| context.contains("decreases at the back edge"))
            });
        assert_eq!(owes_descent, expect_descent, "next x = {next}");
    }
}
