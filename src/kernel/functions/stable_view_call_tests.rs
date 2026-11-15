use super::*;
use crate::kernel::loans::LoanRefusal;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn pointer() -> Pointer {
    Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn caller(pointer: &Pointer) -> ExecutionState {
    caller_with_owned_end(pointer, 1, 4)
}

fn caller_with_owned_end(pointer: &Pointer, owned_end: u32, bytes: u32) -> ExecutionState {
    let range = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(owned_end),
    );
    ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), bytes)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(
            ResourceContext::new().unchecked_with_fact(ResourceFact::own(Resource::Memory(range))),
        )
}

fn reader_with_output(name: &str, output_start: u32, output_end: u32) -> ProgramFunction {
    let input = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let output = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(output_start),
        crate::kernel::program_expression::int32_literal(output_end),
    );
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(input)],
        vec![ResourceSpec::viewed_memory(output)],
    )
}

fn reader_for_input(name: &str, input_end: u32) -> ProgramFunction {
    let input = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(input_end),
    );
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(input)], Vec::new())
}

fn reader_with_mutable_range(name: &str, mutable_start: u32, mutable_end: u32) -> ProgramFunction {
    let input = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(input)], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(mutable_start),
            crate::kernel::program_expression::int32_literal(mutable_end),
        )],
        Vec::new(),
        true,
    )
}

fn reader(name: &str, duplicate_view: bool) -> ProgramFunction {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let mut requires = vec![ResourceSpec::viewed_memory(segment.clone())];
    if duplicate_view {
        requires.push(ResourceSpec::viewed_memory(segment));
    }
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(requires, Vec::new())
}

fn composite_reader(name: &str) -> ProgramFunction {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let required = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        "cell".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment)],
        Vec::new(),
    );
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![definition])
}

fn early_reader(name: &str) -> ProgramFunction {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    program_function(
        ProgramType::Void,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        ProgramStatement::If {
            condition: crate::kernel::program_expression::int32_literal(1),
            then_branch: Box::new(program_return(program_void_value())),
            else_branch: Box::new(ProgramStatement::Skip),
        },
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(segment)], Vec::new())
}

/// `resource guarded_item(item) { if item != 0 { owns item[0..1]; } }`
/// consumed by a function whose body reads nothing.
fn conditional_owner(name: &str) -> (ProgramFunction, ExecutionEnvironment) {
    let definition = CompositeResourceDefinition::new(
        "guarded_item",
        vec![program_parameter("item", ProgramType::Int32Pointer)],
        Some(SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "item",
            )),
            operator: ComparisonOperator::NotEqual,
            right: SpecExpression::Value(ProgramValue::pointer(Pointer::null())),
        }),
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("item"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        Vec::new(),
    );
    let function = program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("item", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_resource_summary(
        vec![ResourceSpec::composite(
            ResourceAccessMode::Own,
            "guarded_item".to_string(),
            vec![crate::kernel::program_expression::variable("item")],
            vec![ProgramType::Int32Pointer],
        )],
        Vec::new(),
    )
    .with_composite_resource_definitions(vec![definition]);
    let environment = environment(&function);
    (function, environment)
}

fn environment(function: &ProgramFunction) -> ExecutionEnvironment {
    ExecutionEnvironment::new().with_verified_function_rule(VerifiedFunctionRule {
        pointer_result: None,
        function: function.clone(),
        loop_semantics: LoopSemantics::Verify,
        checked_callees: None,
        applied_tactics: Default::default(),
    })
}

#[test]
fn independent_verification_uses_the_call_transfer_boundary() {
    let pointer = pointer();
    let function = reader_for_input("candidate_verified_reader", 1);
    let state = caller(&pointer);
    let mut budget = ExecutionBudget::new();
    let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
    let paths = execute_program_function_verification_paths(
        &state,
        &function,
        &[crate::kernel::program_expression::pointer_value(pointer)],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut budget,
        &mut variables,
        true,
        false,
    )
    .expect("verification should execute through the transfer boundary");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { .. },
            ..
        }]
    ));
}

#[test]
fn candidate_reader_escrows_owner_until_return() {
    let pointer = pointer();
    let function = reader("candidate_reader", false);
    let caller = caller(&pointer);
    let argument_values = vec![ProgramValue::pointer(pointer.clone())];
    let callee = bind_program_function_arguments(&caller, &function, &argument_values)
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("candidate transfer records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    assert!(
        !transfer.caller_resources_after_requirements.satisfies_fact(
            &ResourceFact::own_memory(MemoryRange::new(
                pointer,
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )),
            &PureFactContext::new()
        )
    );
    assert!(transfer.callee_resources.satisfies_fact(
        &ResourceFact::view_memory(MemoryRange::new(
            Pointer {
                block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_function_entry_preserves_outer_loan_authority() {
    let pointer = pointer();
    let function = program_function(
        ProgramType::Void,
        "candidate_empty_resource_entry",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(program_void_value()),
    );
    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(participant));
    let callee = bind_program_function_arguments(
        &caller_state,
        &function,
        &[ProgramValue::pointer(pointer)],
    )
    .expect("the function argument should bind");

    assert_eq!(callee.loan_ledger(), Some(&ledger));
    assert_eq!(callee.loan_participant(), Some(participant));
    assert!(callee.loan_bindings_are_consistent());
}

#[test]
fn candidate_composite_call_lends_primitive_body_and_recovers_head() {
    let pointer = pointer();
    let head =
        ResourceFact::own_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())]);
    let caller = ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
    let function = composite_reader("candidate_composite_reader");
    let callee = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("composite reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("composite transfer should run")
    .expect("composite transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("composite transfer records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    assert!(plan.ledger.has_active_memory_loans());
    let body_range = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    assert_eq!(
        plan.ledger.permits_memory_access(&body_range),
        Err(LoanRefusal::ActiveDependency)
    );
    assert!(transfer.callee_resources.satisfies_fact(
        &ResourceFact::view_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())],),
        &PureFactContext::new(),
    ));
    let callee_state = callee_state_with_resource_transfer(callee, &transfer);
    let (resources, _, _, _, evidence) = recover_candidate_stable_view_resources(
        &caller,
        &callee_state,
        &transfer,
        ResourceContext::new(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("composite return should recover");
    assert!(resources.satisfies_fact(&head, &PureFactContext::new()));
    assert!(evidence.is_some());
}

/// A composite view lent twice in a row: the first return must leave
/// the caller exactly the recovered head, so the second lend finds one
/// owner and no exposed body piece beside it.
fn composite_reader_with_definition(
    name: &str,
    definition: CompositeResourceDefinition,
) -> ProgramFunction {
    let required = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        "cell".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![definition])
}

fn fact_bearing_cell_definition() -> CompositeResourceDefinition {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment)],
        vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
    )
}

fn plan_composite_lend(function: &ProgramFunction) -> Result<(), RuntimeError> {
    let pointer = pointer();
    let head =
        ResourceFact::own_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())]);
    let caller = ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head));
    let callee =
        bind_program_function_arguments(&caller, function, &[ProgramValue::pointer(pointer)])
            .expect("composite reader arguments should bind");
    prepare_function_resource_transfer(
        &caller,
        &callee,
        function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("composite transfer should run")
    .map(|_| ())
}

/// Recovery restores the exact escrowed head, so a body fact over the
/// body's own cells is re-asserted as folded: such a composite lends.
#[test]
fn candidate_composite_with_body_facts_is_lendable() {
    let function = composite_reader_with_definition(
        "candidate_fact_bearing_reader",
        fact_bearing_cell_definition(),
    );
    plan_composite_lend(&function).expect("a fact over the body's own cells is loan-stable");
}

/// A fact that claims liveness of storage outside the body, or one that
/// reads a population count, is not stabilized by the loan.
#[test]
fn candidate_composite_with_unstable_facts_is_refused() {
    let liveness = composite_reader_with_definition(
        "candidate_liveness_fact_reader",
        fact_bearing_cell_definition().with_liveness_facts(true),
    );
    let error = plan_composite_lend(&liveness).expect_err("a liveness fact is refused");
    assert!(
        matches!(&error, RuntimeError::FunctionContract(message) if message.contains("allocation-liveness")),
        "{error}"
    );
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let counted = composite_reader_with_definition(
        "candidate_counted_fact_reader",
        CompositeResourceDefinition::authority_control(
            "cell",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            vec![ResourceSpec::owned_memory(segment)],
            vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
        ),
    );
    assert!(plan_composite_lend(&counted).is_err());
}

// The owned-interface-to-viewed-implementation adapter (docs/internals/stable-views.md):
// the callee's clause names one composite, the caller owns another whose
// checked frontier covers it.

fn cell_definition(end: u32, facts: Vec<SpecProposition>) -> CompositeResourceDefinition {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(end),
    );
    CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment)],
        facts,
    )
}

fn wide_definition(end: u32) -> CompositeResourceDefinition {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(end),
    );
    CompositeResourceDefinition::new(
        "wide",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment)],
        Vec::new(),
    )
}

/// A reader that views `cell(p)` and knows both definitions.
fn adapter_reader(
    name: &str,
    cell: CompositeResourceDefinition,
    wide: CompositeResourceDefinition,
) -> ProgramFunction {
    let required = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        "cell".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![cell, wide])
}

/// The caller owns `wide(p)` over an eight-byte block and nothing else.
fn adapter_caller(pointer: &Pointer) -> ExecutionState {
    let second = Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::Constant(4),
    };
    ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), 8)
                .store(pointer.clone(), int32(7))
                .store(second, int32(9)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_composite(
                "wide".into(),
                vec![ProgramValue::pointer(pointer.clone())],
            ),
        ))
}

fn plan_adapter_lend(
    function: &ProgramFunction,
) -> (
    ExecutionState,
    Result<FunctionResourceTransfer, RuntimeError>,
) {
    let pointer = pointer();
    let caller = adapter_caller(&pointer);
    let callee = bind_program_function_arguments(
        &caller,
        function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("adapter reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("adapter transfer should run");
    (caller, transfer)
}

/// The caller owns `wide(p)` over `p[0..2]`; the callee views `cell(p)`
/// over `p[0..1]`. The lend escrows the owner the caller actually holds,
/// `views cell(p)` joins that loan's permitted descriptions, and recovery
/// restores `wide(p)` exactly.
#[test]
fn candidate_composite_view_is_backed_by_a_covering_owned_composite() {
    let function = adapter_reader(
        "candidate_adapter_reader",
        cell_definition(1, Vec::new()),
        wide_definition(2),
    );
    let pointer = pointer();
    let (caller, transfer) = plan_adapter_lend(&function);
    let transfer = transfer.expect("a covering owner backs the viewed composite");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("the adapter lend records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    assert!(transfer.callee_resources.satisfies_fact(
        &ResourceFact::view_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())]),
        &PureFactContext::new(),
    ));
    // The whole escrowed frontier is protected, not just the adapted
    // clause's own bytes.
    for end in [1, 2] {
        let range = MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(end),
        );
        assert_eq!(
            plan.ledger.permits_memory_access(&range),
            Err(LoanRefusal::ActiveDependency)
        );
    }
    let callee = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("adapter reader arguments should bind");
    let callee_state = callee_state_with_resource_transfer(callee, &transfer);
    let (resources, _, _, _, _) = recover_candidate_stable_view_resources(
        &caller,
        &callee_state,
        &transfer,
        ResourceContext::new(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("the adapter lend should recover");
    let head = ResourceFact::own_composite("wide".into(), vec![ProgramValue::pointer(pointer)]);
    assert!(resources.satisfies_fact(&head, &PureFactContext::new()));
    assert_eq!(resources.facts(), [head]);
}

/// The owner's body has to cover every piece of the viewed composite's
/// checked frontier. Half of it is not backing.
#[test]
fn candidate_composite_view_over_an_uncovered_owner_is_refused() {
    let function = adapter_reader(
        "candidate_uncovered_adapter_reader",
        cell_definition(2, Vec::new()),
        wide_definition(1),
    );
    let (_, transfer) = plan_adapter_lend(&function);
    let error = transfer.expect_err("an owner that covers half the frontier is not backing");
    let RuntimeError::LoanRefusal(diagnostic) = &error else {
        panic!("{error}");
    };
    assert_eq!(
        diagnostic.category(),
        crate::kernel::loans::LoanRefusalCategory::Missing
    );
    assert_eq!(
        diagnostic.subject().resource_fact(),
        Some(&ResourceFact::view_composite(
            "cell".into(),
            vec![ProgramValue::pointer(pointer())]
        ))
    );
}

/// The viewed composite's facts are what `observe` publishes inside the
/// callee, so the caller has to have established them. A fact the owner's
/// frontier does not give is a refusal, not an assumption.
#[test]
fn candidate_composite_view_with_an_unestablished_fact_is_refused() {
    let unestablished = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
    };
    let function = adapter_reader(
        "candidate_unestablished_fact_adapter_reader",
        cell_definition(1, vec![unestablished]),
        wide_definition(2),
    );
    let (_, transfer) = plan_adapter_lend(&function);
    let error = transfer.expect_err("an unestablished body fact is refused");
    // Assembling the view is a fold, so the refusal names the instance and
    // the body fact it could not establish rather than a missing loan.
    let RuntimeError::UnestablishedAssemblyFact { assembled, .. } = &error else {
        panic!("{error}");
    };
    assert_eq!(
        assembled.as_ref(),
        &ResourceFact::view_composite("cell".into(), vec![ProgramValue::pointer(pointer())])
    );
    // The same adapter with a fact the call already establishes is
    // accepted, so the refusal above is the fact check and not the shape.
    let established = adapter_reader(
        "candidate_established_fact_adapter_reader",
        cell_definition(
            1,
            vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
        ),
        wide_definition(2),
    );
    plan_adapter_lend(&established)
        .1
        .expect("an established body fact backs the adapter");
}

/// With no owned composite to escrow, the planner materializes the viewed
/// composite out of exactly the owned frontier the caller holds, and
/// recovery hands those facts back: the caller's packaging is the same
/// after the call as before it, and the unlent remainder stays writable.
#[test]
fn candidate_composite_view_is_materialized_from_the_caller_frontier() {
    let pointer = pointer();
    let function = composite_reader("candidate_materialized_adapter_reader");
    let caller = caller_with_owned_end(&pointer, 2, 8);
    let callee = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("composite reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("materialized transfer should run")
    .expect("the caller's own frontier backs the viewed composite");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("the materialized lend records a loan plan");
    let lent = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let kept = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(1),
        MachineTerm::constant(2),
    );
    assert_eq!(
        plan.ledger.permits_memory_access(&lent),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(plan.ledger.permits_memory_access(&kept), Ok(()));
    assert!(transfer.callee_resources.satisfies_fact(
        &ResourceFact::view_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())]),
        &PureFactContext::new(),
    ));
    let callee_state = callee_state_with_resource_transfer(callee, &transfer);
    let (resources, _, _, _, _) = recover_candidate_stable_view_resources(
        &caller,
        &callee_state,
        &transfer,
        ResourceContext::new(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("the materialized lend should recover");
    // Recovery hands back the frontier the head was materialized from,
    // never a `cell(p)` head the caller never held. (`return_resources`
    // is empty here, so what is left is exactly the recovered escrow.)
    assert_eq!(
        resources.facts(),
        [ResourceFact::own(Resource::Memory(lent))]
    );
}

/// A callee that views `p[0..1]` and, in the same contract, produces a
/// composite whose body is that same range. Whatever the caller lent, it
/// gets back: composing the produced head beside it would leave the caller
/// owning `p[0..1]` twice, once directly and once inside `zz_box3(p)`.
fn view_and_produce_reader(name: &str) -> ProgramFunction {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let produced = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::Own,
        "zz_box3".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Produce,
        ResourceStateSource::Post,
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "zz_box3",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment.clone())],
        Vec::new(),
    );
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(segment)], vec![produced])
    .with_composite_resource_definitions(vec![definition])
}

#[test]
fn produced_composite_over_a_viewed_owner_is_refused() {
    let pointer = pointer();
    let function = view_and_produce_reader("view_and_produce");
    let environment =
        ExecutionEnvironment::new().with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: function.clone(),
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let paths = execute_program_function_call_paths(
        &caller(&pointer),
        &function,
        &[crate::kernel::program_expression::pointer_value(pointer)],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("the call should execute");
    assert!(
        paths.iter().all(|path| matches!(
            &path.outcome,
            FunctionOutcome::RuntimeError(error) if produced_composite_overlap(error)
        )),
        "{:?}",
        paths.iter().map(|path| &path.outcome).collect::<Vec<_>>()
    );
}

fn produced_composite_overlap(error: &RuntimeError) -> bool {
    matches!(
        error,
        RuntimeError::ProducedCompositeOverlapsHeldResource { .. }
    )
}

#[test]
fn candidate_composite_reader_can_be_called_twice() {
    let pointer = pointer();
    let head =
        ResourceFact::own_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())]);
    let caller = ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
    let function = composite_reader("candidate_composite_reader_twice");
    let first = execute_program_function_call_paths(
        &caller,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("first composite call should execute");
    let [
        FunctionPath {
            outcome: FunctionOutcome::Return {
                state: after_first, ..
            },
            ..
        },
    ] = first.as_slice()
    else {
        panic!("first composite call should return: {first:?}");
    };
    assert_eq!(after_first.resources().facts(), std::slice::from_ref(&head));
    let second = execute_program_function_call_paths(
        after_first,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("second composite call should execute");
    assert!(
        matches!(
            second.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::Return { .. },
                ..
            }]
        ),
        "{second:?}"
    );
}

#[test]
fn candidate_reader_recovers_owner_for_following_write() {
    let pointer = pointer();
    let function = reader("candidate_reader_return", false);
    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant));
    let paths = execute_program_function_call_paths(
        &caller_state,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate call should execute");
    let FunctionOutcome::Return { state, .. } = &paths[0].outcome else {
        panic!("candidate reader should return: {:?}", paths[0].outcome);
    };
    assert_eq!(paths[0].loan_evidence.len(), 1);
    let evidence_items = paths[0].loan_evidence.to_vec();
    let evidence = &evidence_items[0];
    let caller_ledger = caller_state
        .loan_ledger()
        .cloned()
        .expect("candidate execution publishes its caller ledger");
    evidence
        .recheck(
            &caller_ledger,
            caller_state.loan_participant(),
            &evidence.entry.ledger,
            Some(evidence.entry.callee_participant()),
        )
        .expect("retained candidate evidence rechecks");
    assert_eq!(state.loan_ledger(), Some(&evidence.recovered_ledger));
    assert!(state.resources().satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new(
            pointer,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_direct_reader_recovers_owner_for_following_write() {
    let pointer = pointer();
    let function = reader("candidate_direct_reader", false);
    let paths = execute_program_function_paths(
        &caller(&pointer),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate direct call should execute");
    let FunctionOutcome::Return { state, .. } = &paths[0].outcome else {
        panic!(
            "candidate direct reader should return: {:?}",
            paths[0].outcome
        );
    };
    assert!(state.resources().satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new(
            pointer,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_evidence_rejects_definitionally_equal_resources_with_new_identity() {
    let pointer = pointer();
    let function = reader("candidate_identity_guard", false);
    let caller_ledger = LoanLedger::new();
    let caller_participant = caller_ledger
        .fresh_participant()
        .expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(caller_ledger.clone()))
        .with_loan_participant(Some(caller_participant));
    let paths = execute_program_function_call_paths(
        &caller_state,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate call should execute");
    let evidence_items = paths[0].loan_evidence.to_vec();
    let evidence = &evidence_items[0];
    let different_participant = caller_ledger
        .fresh_participant()
        .expect("fresh participant identity");
    assert_eq!(
        evidence
            .recheck(
                &caller_ledger,
                Some(different_participant),
                &evidence.entry.ledger,
                Some(evidence.entry.callee_participant()),
            )
            .expect_err("a different caller participant must be refused"),
        LoanRefusal::WrongHolder
    );
    assert_eq!(
        evidence
            .recheck(
                &LoanLedger::new(),
                Some(caller_participant),
                &evidence.entry.ledger,
                Some(evidence.entry.callee_participant()),
            )
            .expect_err("an unrelated predecessor ledger must be refused"),
        LoanRefusal::StalePredecessor
    );
}

#[test]
fn candidate_nested_body_call_retains_inner_and_outer_evidence() {
    let pointer = pointer();
    let inner = reader("candidate_nested_inner", false);
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let outer = program_function(
        ProgramType::Int32,
        "candidate_nested_outer",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        ProgramStatement::seq(
            Arc::new(program_declare("result", ProgramType::Int32)),
            Arc::new(ProgramStatement::seq(
                Arc::new(program_call_then_assign(
                    0,
                    "result",
                    inner.name(),
                    vec![crate::kernel::program_expression::variable("p")],
                )),
                Arc::new(program_return(crate::kernel::program_expression::variable(
                    "result",
                ))),
            )),
        ),
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(segment)], Vec::new());
    let environment = environment(&outer).with_function(inner);
    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("caller participant");
    let caller_state = caller(&pointer)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant));
    let paths = execute_program_function_call_paths(
        &caller_state,
        &outer,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("nested candidate call should execute");
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].loan_evidence.len(), 2);
    let evidence = paths[0].loan_evidence.to_vec();
    assert_eq!(
        evidence[0].entry.caller_ledger(),
        &evidence[1].entry.ledger,
        "inner evidence starts at the outer callee ledger"
    );
}

/// Implicit local authority backs a checked loan without an owned escrow.
/// A synchronous call closes it before returning to its caller.
#[test]
fn candidate_local_array_view_uses_a_checked_loan_and_recovers() {
    let pointer = pointer();
    let function = reader("candidate_local_reader", false);
    let caller = ExecutionState::new().with_memory(
        Memory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(7)),
    );
    let paths = execute_program_function_call_paths(
        &caller,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate local view call should execute");
    assert_eq!(
        paths[0].loan_evidence.len(),
        1,
        "the local view must have a checked entry and discharge"
    );
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { state, .. },
            ..
        }] if state.loan_ledger().is_none_or(|ledger| !ledger.has_active_memory_loans())
    ));
}

/// The activation-local bounds rule still applies, and it decides the
/// call before the callee reads anything: a local view past the end of
/// its block names storage the block does not have, so the call is
/// refused for the missing resource rather than for a read of whatever
/// lies beyond the block.
#[test]
fn candidate_local_array_view_out_of_bounds_is_refused() {
    let pointer = pointer();
    let function = reader_for_input("candidate_local_wide_reader", 4);
    let caller = ExecutionState::new().with_memory(
        Memory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(7)),
    );
    let paths = execute_program_function_call_paths(
        &caller,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate out-of-bounds local view should execute to a diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::RuntimeError(RuntimeError::MissingResource {
                    resource
                }),
                ..
            }] if resource.is_view()
        ),
        "the bounds rule names the unbacked view, not a later read: {paths:?}"
    );
}

/// A conditional composite whose guard the assumptions decide false has
/// an empty body, so the empty context satisfies it: the planner must
/// discharge `owns guarded_item(null)` definitionally instead of
/// demanding an owned entry the caller was never meant to hold.
#[test]
fn candidate_conditional_composite_with_a_false_guard_needs_no_owned_entry() {
    let (function, environment) = conditional_owner("candidate_guarded_free");
    let paths = execute_program_function_call_paths(
        &ExecutionState::new(),
        &function,
        &[crate::kernel::program_expression::pointer_value(
            Pointer::null(),
        )],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("a false composite guard should execute");
    assert!(
        matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::Return { .. },
                ..
            }]
        ),
        "an empty body is satisfied by the empty context: {paths:?}"
    );
}

/// The same requirement with an undecided guard keeps its entry: only a
/// guard the assumptions decide collapses the body, so a symbolic
/// argument still needs the caller to supply the composite.
#[test]
fn candidate_conditional_composite_with_an_undecided_guard_still_needs_its_entry() {
    let (function, environment) = conditional_owner("candidate_guarded_symbolic_free");
    let symbolic = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(910_101)), 4),
    };
    let paths = execute_program_function_call_paths(
        &ExecutionState::new(),
        &function,
        &[crate::kernel::program_expression::pointer_value(symbolic)],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("an undecided composite guard should execute to a diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::RuntimeError(RuntimeError::MissingResource {
                    resource
                }),
                ..
            }] if matches!(
                resource.resource(),
                Resource::Composite { name, .. } if name == "guarded_item"
            )
        ),
        "an undecided guard is not an empty body: {paths:?}"
    );
}

/// Two clauses naming one token are a single demand for their combined
/// count. The caller holds one unit, so the refusal has to name quantity
/// two: naming one unit would name a fact the caller does hold.
#[test]
fn candidate_repeated_token_requirement_reports_the_demanded_quantity() {
    let requirement = |parameter| {
        ResourceSpec::token(
            ResourceAccessMode::Own,
            "can_complete".to_string(),
            vec![crate::kernel::program_expression::variable(parameter)],
            vec![ProgramType::Int32],
        )
    };
    let function = program_function(
        ProgramType::Int32,
        "candidate_consume_two",
        vec![
            program_parameter("first", ProgramType::Int32),
            program_parameter("second", ProgramType::Int32),
        ],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_resource_summary(
        vec![requirement("first"), requirement("second")],
        Vec::new(),
    );
    let token = ProgramValue::Int32(MachineTerm::constant(5));
    let caller =
        ExecutionState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_token("can_complete".to_string(), vec![token.clone()]),
        ));
    let paths = execute_program_function_call_paths(
        &caller,
        &function,
        &[
            ProgramExpression::Value(token.clone()),
            ProgramExpression::Value(token),
        ],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("a doubled token requirement should execute to a diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::RuntimeError(RuntimeError::MissingResource {
                    resource
                }),
                ..
            }] if resource.owned_quantity_term() == Some(&MachineTerm::constant(2))
        ),
        "the refusal names the whole demand: {paths:?}"
    );
}

#[test]
fn candidate_inline_reader_uses_the_callers_checked_resources() {
    let pointer = pointer();
    let function = reader("candidate_inline_reader", false).with_inline_body();
    let paths = execute_program_function_call_paths(
        &caller(&pointer),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate inline call should execute");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { .. },
            ..
        }]
    ));
}

#[test]
fn candidate_unresolved_return_obligation_refuses_recovery() {
    let pointer = pointer();
    let function = reader("candidate_unresolved_return", false);
    let caller = caller(&pointer);
    let arguments = vec![ProgramValue::pointer(pointer.clone())];
    let callee = bind_program_function_arguments(&caller, &function, &arguments)
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let callee = callee_state_with_resource_transfer(callee, &transfer);
    let unresolved = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    ))
    .with_context("callee postcondition");
    let (outcome, _, _) = function_outcome_from_body_with_resource_transfer(
        &caller,
        &function,
        StatementOutcome::Return {
            value: int32(7).into(),
            state: Box::new(callee),
        },
        vec![unresolved.clone()],
        &PureFactContext::new(),
        &transfer,
        &arguments,
        true,
        &mut ExecutionBudget::new(),
    )
    .expect("candidate return transition should complete");
    assert!(matches!(
        outcome,
        FunctionOutcome::RuntimeError(RuntimeError::PendingCallObligations(pending))
            if pending.as_ref() == [unresolved]
    ));
}

#[test]
fn candidate_rejects_malformed_ledger_participant_pairs() {
    let pointer = pointer();
    let function = reader("candidate_pair_mismatch", false);
    let assumptions = PureFactContext::new();
    let mut budget = ExecutionBudget::new();
    let caller_with_ledger = caller(&pointer).with_loan_ledger(Some(LoanLedger::new()));
    let callee = bind_program_function_arguments(
        &caller_with_ledger,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("reader argument should bind");
    let error = prepare_function_resource_transfer(
        &caller_with_ledger,
        &callee,
        &function,
        &assumptions,
        &mut budget,
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("pair validation should not hit the execution budget")
    .expect_err("ledger-only caller must be refused");
    assert!(matches!(
        error,
        RuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
    ));

    let ledger = LoanLedger::new();
    let participant = ledger.fresh_participant().expect("participant");
    let caller_with_participant = caller(&pointer).with_loan_participant(Some(participant));
    let callee = bind_program_function_arguments(
        &caller_with_participant,
        &function,
        &[ProgramValue::pointer(pointer)],
    )
    .expect("reader argument should bind");
    let error = prepare_function_resource_transfer(
        &caller_with_participant,
        &callee,
        &function,
        &assumptions,
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("pair validation should not hit the execution budget")
    .expect_err("participant-only caller must be refused");
    assert!(matches!(
        error,
        RuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
    ));
}

#[test]
fn candidate_rejects_wrong_callee_participant_on_recovery() {
    let pointer = pointer();
    let function = reader("candidate_wrong_participant", false);
    let caller = caller(&pointer);
    let arguments = vec![ProgramValue::pointer(pointer.clone())];
    let callee = bind_program_function_arguments(&caller, &function, &arguments)
        .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("candidate transfer records a loan plan");
    let wrong_participant = plan.caller_participant();
    let callee = callee_state_with_resource_transfer(callee, &transfer)
        .with_loan_participant(Some(wrong_participant));
    let missing_ledger = callee.clone().with_loan_ledger(None);
    let error = recover_candidate_stable_view_resources(
        &caller,
        &missing_ledger,
        &transfer,
        transfer.caller_resources_after_requirements.clone(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect_err("recovery without a ledger must be refused");
    assert!(matches!(
        error,
        RuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Recovery
    ));
    let error = recover_candidate_stable_view_resources(
        &caller,
        &callee,
        &transfer,
        transfer.caller_resources_after_requirements.clone(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect_err("recovery must refuse the wrong callee participant");
    assert!(matches!(
        error,
        RuntimeError::LoanRefusal(diagnostic)
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::WrongHolder
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Recovery
    ));
}

#[test]
fn candidate_joint_planner_reuses_one_escrow_for_two_aliases() {
    let pointer = pointer();
    let function = reader("candidate_aliases", true);
    let caller = caller(&pointer);
    let callee = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("reader argument should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("candidate transfer records a loan plan");
    assert_eq!(plan.stable_views().len(), 2);
    assert_eq!(
        plan.stable_views()[0].loan,
        plan.stable_views()[1].loan,
        "aliases share one escrow"
    );
}

#[test]
fn candidate_nested_reader_reborrows_and_restores_outer_view_binding() {
    let pointer = pointer();
    let function = reader("candidate_nested_reader", false);
    let caller = caller(&pointer);
    let outer_template = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("outer reader arguments should bind");
    let outer_transfer = prepare_function_resource_transfer(
        &caller,
        &outer_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("outer transfer should run")
    .expect("outer transfer should be accepted");
    let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer);
    let inner_template = bind_program_function_arguments(
        &outer_callee,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("inner reader arguments should bind");
    let inner_transfer = prepare_function_resource_transfer(
        &outer_callee,
        &inner_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("inner transfer should run")
    .expect("inner transfer should be accepted");
    let inner_plan = inner_transfer
        .stable_view_plan
        .as_ref()
        .expect("nested transfer should use the loan plan");
    let outer_plan = outer_transfer
        .stable_view_plan
        .as_ref()
        .expect("outer transfer should use the loan plan");
    assert_ne!(
        inner_plan.stable_views()[0].loan,
        outer_plan.stable_views()[0].loan,
        "nested reader gets a child loan"
    );
    let inner_callee = callee_state_with_resource_transfer(inner_template, &inner_transfer);
    let (resources, ledger, participant, bindings, _) = recover_candidate_stable_view_resources(
        &outer_callee,
        &inner_callee,
        &inner_transfer,
        inner_transfer.caller_resources_after_requirements.clone(),
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .expect("nested reader recovery should run");
    assert_eq!(ledger, outer_callee.loan_ledger().cloned());
    assert_eq!(participant, outer_callee.loan_participant());
    assert_eq!(bindings, outer_callee.loan_view_bindings().clone());
    assert!(resources.satisfies_fact(
        &ResourceFact::view_memory(MemoryRange::new(
            pointer,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_nested_reader_body_call_reborrows_and_recovers_owner() {
    let pointer = pointer();
    let inner = reader("candidate_nested_body_inner", false);
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let outer = program_function(
        ProgramType::Int32,
        "candidate_nested_body_outer",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_seq(
            program_declare("result", ProgramType::Int32),
            program_seq(
                program_call_then_assign(
                    1,
                    "result",
                    inner.name(),
                    vec![crate::kernel::program_expression::variable("p")],
                ),
                program_return(crate::kernel::program_expression::variable("result")),
            ),
        ),
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(segment)], Vec::new());
    let environment = ExecutionEnvironment::new()
        .with_function(inner.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: inner,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });

    let paths = execute_program_function_paths(
        &caller(&pointer),
        &outer,
        &[ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("nested candidate reader should execute through the real body call");
    let FunctionOutcome::Return { value, state } = &paths[0].outcome else {
        panic!(
            "nested candidate reader should return: {:?}",
            paths[0].outcome
        );
    };
    assert_eq!(value.native().as_ref(), &int32(7));
    assert!(state.resources().satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new(
            pointer,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_nested_call_preserves_outer_view_for_wider_output() {
    let pointer = pointer();
    let outer_function = reader_for_input("candidate_outer_view", 2);
    let caller = caller_with_owned_end(&pointer, 2, 8);
    let outer_template = bind_program_function_arguments(
        &caller,
        &outer_function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("outer arguments should bind");
    let outer_transfer = prepare_function_resource_transfer(
        &caller,
        &outer_template,
        &outer_function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("outer transfer should run")
    .expect("outer transfer should be accepted");
    let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer);

    let inner_function = reader_with_output("candidate_outer_output", 0, 2);
    let inner_template = bind_program_function_arguments(
        &outer_callee,
        &inner_function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("inner arguments should bind");
    let inner_transfer = prepare_function_resource_transfer(
        &outer_callee,
        &inner_template,
        &inner_function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("inner transfer should run")
    .expect("inner transfer should be accepted");
    let output = ResourceFact::view_memory(MemoryRange::new(
        pointer,
        MachineTerm::constant(0),
        MachineTerm::constant(2),
    ));
    let (resources, ledger, participant, bindings, _loan_evidence) =
        recover_candidate_stable_view_resources(
            &outer_callee,
            &callee_state_with_resource_transfer(inner_template, &inner_transfer),
            &inner_transfer,
            ResourceContext::new().unchecked_with_fact(output.clone()),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect("outer view should authorize the wider returned view");
    assert!(resources.satisfies_fact(&output, &PureFactContext::new()));
    assert_eq!(ledger, outer_callee.loan_ledger().cloned());
    assert_eq!(participant, outer_callee.loan_participant());
    assert_eq!(bindings, outer_callee.loan_view_bindings().clone());
}

fn assert_unbacked_output_rejected(output_start: u32, output_end: u32, name: &str) {
    let pointer = pointer();
    let function = reader_with_output(name, output_start, output_end);
    let paths = execute_program_function_call_paths(
        &caller_with_owned_end(&pointer, 3, 12),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate output call should execute to a diagnostic path");
    assert!(
        matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::RuntimeError(RuntimeError::UnbackedReturnedView { .. }),
                ..
            }]
        ),
        "unexpected output result: {paths:?}"
    );
}

#[test]
fn candidate_rejects_new_output_view() {
    assert_unbacked_output_rejected(2, 3, "candidate_new_output");
}

#[test]
fn candidate_rejects_wider_output_without_outer_binding() {
    assert_unbacked_output_rejected(0, 2, "candidate_wider_output");
}

/// Build a call whose return context carries `returned` as an extra view
/// beside the caller's retained owner, either as a checked projection of
/// that exact owned occurrence or as a bare equal fact.
fn recover_with_extra_returned_view(
    projected_from_owner: bool,
) -> Result<ResourceContext, RuntimeError> {
    let pointer = pointer();
    let function = reader("candidate_returned_projection", false);
    let caller = caller_with_owned_end(&pointer, 3, 12);
    let callee_template = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("reader argument should bind");
    let mut transfer = prepare_function_resource_transfer(
        &caller,
        &callee_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let owner = ResourceFact::own_memory(MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(1),
        MachineTerm::constant(3),
    ));
    let returned = ResourceFact::view_memory(MemoryRange::new(
        pointer,
        MachineTerm::constant(1),
        MachineTerm::constant(3),
    ));
    // Mirror the output delta recorded by evaluate_contract_return_resources.
    transfer.candidate_output_views.push(returned.clone());
    let base = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (support_occurrence, _) = base
        .unique_owned_occurrence_for_fact(&owner)
        .expect("the retained owner has one occurrence");
    let return_resources = if projected_from_owner {
        base.unchecked_with_supported_facts_from_occurrence_with_memory(
            support_occurrence,
            &owner,
            vec![returned],
            caller.memory(),
        )
    } else {
        base.unchecked_with_fact(returned)
    };
    recover_candidate_stable_view_resources(
        &caller,
        &callee_state_with_resource_transfer(callee_template, &transfer),
        &transfer,
        return_resources,
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .map(|(resources, ..)| resources)
}

#[test]
fn candidate_accepts_a_returned_view_projected_from_a_returned_owner() {
    let resources = recover_with_extra_returned_view(true)
        .expect("a checked projection of the returned owner has provenance");
    let projected = ResourceFact::view_memory(MemoryRange::new(
        pointer(),
        MachineTerm::constant(1),
        MachineTerm::constant(3),
    ));
    assert!(resources.satisfies_fact(&projected, &PureFactContext::new()));
}

#[test]
fn candidate_rejects_a_returned_view_that_only_an_equal_owner_satisfies() {
    let error = recover_with_extra_returned_view(false)
        .expect_err("fact equality against an owner is not provenance");
    assert!(
        matches!(&error, RuntimeError::UnbackedReturnedView { .. }),
        "unexpected refusal: {error}"
    );
}

/// A view of read-only storage is intrinsic read authority rather than a
/// lent capability: `install_borrowed_contract_inputs` gives such a
/// contract input view no borrowed root and `intrinsic_read_views`
/// supplies such a requirement with no ledger transition, both by this
/// block test, so a call that merely carries one across its boundary has
/// provenance for it. Everything else about the two calls below is the
/// same; only the carried block's mutability differs.
fn recover_with_a_carried_view_of_another_block(
    read_only: bool,
) -> Result<ResourceContext, RuntimeError> {
    let pointer = pointer();
    let other = Pointer {
        block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let function = reader("candidate_carried_view", false);
    let owned_caller = caller_with_owned_end(&pointer, 3, 12);
    let caller =
        owned_caller
            .clone()
            .with_memory(owned_caller.memory().clone().with_block_or_read_only(
                other.block.clone(),
                8,
                read_only,
            ));
    let callee_template =
        bind_program_function_arguments(&caller, &function, &[ProgramValue::pointer(pointer)])
            .expect("reader argument should bind");
    let mut transfer = prepare_function_resource_transfer(
        &caller,
        &callee_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("candidate transfer should run")
    .expect("candidate transfer should be accepted");
    let carried = ResourceFact::view_memory(MemoryRange::new(
        other,
        MachineTerm::constant(0),
        MachineTerm::constant(2),
    ));
    // Mirror the output delta recorded by evaluate_contract_return_resources.
    transfer.candidate_output_views.push(carried.clone());
    let return_resources = transfer
        .caller_resources_after_requirements
        .clone()
        .unchecked_with_fact(carried);
    recover_candidate_stable_view_resources(
        &caller,
        &callee_state_with_resource_transfer(callee_template, &transfer),
        &transfer,
        return_resources,
        &PureFactContext::new(),
        &PureFactContext::new(),
        &[],
    )
    .map(|(resources, ..)| resources)
}

#[test]
fn candidate_accepts_a_carried_view_of_read_only_storage() {
    let resources = recover_with_a_carried_view_of_another_block(true)
        .expect("a view of read-only storage is intrinsic read authority");
    let carried = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(2),
    ));
    assert!(resources.satisfies_fact(&carried, &PureFactContext::new()));
}

#[test]
fn candidate_rejects_a_carried_view_of_mutable_storage() {
    let error = recover_with_a_carried_view_of_another_block(false)
        .expect_err("a view of mutable storage the caller never lent has no provenance");
    // The refusal carries the carried view itself, so the surface can
    // name it rather than print a kernel dump of it.
    let carried = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(2),
    ));
    assert!(
        matches!(&error, RuntimeError::UnbackedReturnedView { view } if **view == carried),
        "unexpected refusal: {error}"
    );
}

fn symbolic_bounded_range(start: MachineTerm, end: MachineTerm, element_width: u32) -> MemoryRange {
    MemoryRange::new_with_element_width(
        Pointer {
            block: PointerBlock::Concrete("candidate:separation".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        start,
        end,
        element_width,
    )
}

fn constant_bounded_range(start: i32, end: i32, element_width: u32) -> MemoryRange {
    symbolic_bounded_range(
        MachineTerm::constant(start as u32),
        MachineTerm::constant(end as u32),
        element_width,
    )
}

/// A range that starts below its base meets the ranges it really meets.
/// Zero-extended, `a[-1..2]`'s start scaled to `17179869180`, so every
/// nonnegative range ended at or before it and was called `Disjoint` —
/// which is final, because only a pair this leaves undecided reaches the
/// arithmetic oracle, so it suppressed the refusal an overlapping effect
/// and view owe each other.
#[test]
fn candidate_sees_a_range_that_starts_below_its_base() {
    let assumptions = PureFactContext::new();
    let below = constant_bounded_range(-1, 2, 4);
    for other in [
        constant_bounded_range(0, 1, 4),
        constant_bounded_range(-1, 0, 4),
        constant_bounded_range(1, 2, 4),
        // Differing element widths meet in bytes: `a[-1..2]` covers
        // bytes -4..8 and this covers bytes 0..4.
        constant_bounded_range(0, 4, 1),
    ] {
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&below, &other, &assumptions),
            CandidateMemoryRangeRelation::Overlap
        );
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&other, &below, &assumptions),
            CandidateMemoryRangeRelation::Overlap
        );
    }
}

/// The other polarity: ranges that really do miss each other, on both
/// sides of the base and both wholly below it, stay `Disjoint`.
#[test]
fn candidate_keeps_separate_ranges_below_a_base_separate() {
    let assumptions = PureFactContext::new();
    let below = constant_bounded_range(-4, -1, 4);
    for other in [
        constant_bounded_range(0, 2, 4),
        constant_bounded_range(-1, 0, 4),
        constant_bounded_range(-8, -4, 4),
    ] {
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&below, &other, &assumptions),
            CandidateMemoryRangeRelation::Disjoint
        );
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&other, &below, &assumptions),
            CandidateMemoryRangeRelation::Disjoint
        );
    }
    assert_eq!(
        candidate_memory_ranges_relation_by_bounds(
            &below,
            &constant_bounded_range(-2, 1, 4),
            &assumptions
        ),
        CandidateMemoryRangeRelation::Overlap
    );
}

/// `p[0..n - 1]` and `p[n - 1..n]` are separate for every `n`, and the
/// kernel's own arithmetic decides it. Nothing about the endpoints is
/// concrete, so the bounds comparison alone reports unproved separation.
#[test]
fn candidate_proves_adjacent_symbolic_ranges_separate() {
    let count = MachineTerm::Variable(Variable(910));
    let boundary = MachineTerm::add(count.clone(), MachineTerm::constant(u32::MAX));
    let viewed = symbolic_bounded_range(MachineTerm::constant(0), boundary.clone(), 4);
    let mutable = symbolic_bounded_range(boundary, count, 4);
    assert_eq!(
        candidate_memory_ranges_relation_by_bounds(&mutable, &viewed, &PureFactContext::new()),
        CandidateMemoryRangeRelation::SeparationUnproved
    );
    assert_eq!(
        candidate_memory_ranges_relation(&mutable, &viewed, &PureFactContext::new()),
        CandidateMemoryRangeRelation::Disjoint
    );
}

/// The arithmetic oracle decides separation, it does not assume it: two
/// unrelated symbolic ranges in one block stay unproved, and a proven
/// overlap is never reinterpreted.
#[test]
fn candidate_leaves_unrelated_symbolic_ranges_unproved() {
    let left = symbolic_bounded_range(
        MachineTerm::Variable(Variable(911)),
        MachineTerm::Variable(Variable(912)),
        4,
    );
    let right = symbolic_bounded_range(
        MachineTerm::Variable(Variable(913)),
        MachineTerm::Variable(Variable(914)),
        4,
    );
    assert_eq!(
        candidate_memory_ranges_relation(&left, &right, &PureFactContext::new()),
        CandidateMemoryRangeRelation::SeparationUnproved
    );
    let overlapping = symbolic_bounded_range(MachineTerm::constant(0), MachineTerm::constant(4), 4);
    let inner = symbolic_bounded_range(MachineTerm::constant(1), MachineTerm::constant(2), 4);
    assert_eq!(
        candidate_memory_ranges_relation(&overlapping, &inner, &PureFactContext::new()),
        CandidateMemoryRangeRelation::Overlap
    );
}

fn assert_mutable_view_effect_result(
    mutable_start: u32,
    mutable_end: u32,
    name: &str,
) -> Vec<FunctionPath> {
    let pointer = pointer();
    let function = reader_with_mutable_range(name, mutable_start, mutable_end);
    execute_program_function_call_paths(
        &caller_with_owned_end(&pointer, 2, 8),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate mutable call should execute")
}

#[test]
fn candidate_rejects_mutable_effect_overlapping_view() {
    let paths = assert_mutable_view_effect_result(0, 1, "candidate_overlap_effect");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
            && diagnostic.subject().memory_range().is_some()
    ));
}

/// A mutable effect on the same symbolic base as the lent view, at the
/// same constant offsets, is a proven overlap even though the base
/// offset is unknown: the symbolic view is retained outside the
/// concrete index and compared by offset arithmetic.
#[test]
fn candidate_rejects_symbolic_same_base_overlapping_effect() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let function = reader_with_mutable_range("candidate_symbolic_overlap_effect", 0, 1);
    let paths = execute_program_function_call_paths(
        &caller_with_owned_end(&pointer, 2, 8),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate symbolic overlap should execute to a diagnostic path");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
    ));
}

/// A mutable effect through a second pointer whose relation to the lent
/// view is unknown is neither a proven overlap nor a proven separation;
/// the call is refused as unproved rather than assumed disjoint.
#[test]
fn candidate_rejects_unproved_mutable_effect_separation() {
    let viewed = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let mutated = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(701)),
    };
    let input = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let function = program_function(
        ProgramType::Int32,
        "candidate_unknown_effect",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![ResourceSpec::viewed_memory(input)], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            crate::kernel::program_expression::variable("q"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        )],
        Vec::new(),
        true,
    );
    let paths = execute_program_function_call_paths(
        &caller_with_owned_end(&viewed, 2, 8),
        &function,
        &[
            ProgramExpression::Value(ProgramValue::pointer(viewed)),
            ProgramExpression::Value(ProgramValue::pointer(mutated)),
        ],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate unknown separation should execute to a diagnostic path");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::SeparationUnproved
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::SeparationUnproved
    ));
}

/// A contract that views one parameter and owns another, with the whole
/// write footprint derived from that ownership. Each requirement is
/// served by a different owned occurrence of the caller's partition.
fn viewer_and_writer(name: &str) -> ProgramFunction {
    let viewed = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    // The writer reads only `p`, so `q` may arrive unwritten.
    let owned = MemorySegment::new(
        crate::kernel::program_expression::variable("q"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    )
    .with_uninitialized(true);
    program_function(
        ProgramType::Int32,
        name,
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![
            ResourceSpec::viewed_memory(viewed),
            ResourceSpec::owned_memory(owned),
        ],
        Vec::new(),
    )
    .with_resource_derived_mutable_frame()
}

/// The partition read at a call. The effect is reserved out of one owned
/// occurrence and the view is lent from another, and the two symbolic
/// ranges share a block with an unknown offset relation, so the
/// arithmetic oracle can order neither. A valid resource context is a
/// partition, so distinct owned occurrences are bytewise disjoint by
/// construction and the call is accepted on that provenance alone. This
/// is, in miniature, the shape of a rotation callback that reads its
/// argument's child augmentation.
#[test]
fn candidate_allows_a_mutable_effect_reserved_from_another_owned_occurrence() {
    let viewed = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let mutated = Pointer {
        block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
        offset: PointerOffsetTerm::Variable(Variable(701)),
    };
    let owned_range = |pointer: &Pointer| {
        ResourceFact::own(Resource::Memory(MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )))
    };
    let caller = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_block(viewed.block.clone(), 8)
                .store(viewed.clone(), int32(7)),
        )
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(owned_range(&viewed))
                .unchecked_with_fact(owned_range(&mutated)),
        );
    let function = viewer_and_writer("candidate_separate_occurrence_effect");
    let paths = execute_program_function_call_paths(
        &caller,
        &function,
        &[
            ProgramExpression::Value(ProgramValue::pointer(viewed.clone())),
            ProgramExpression::Value(ProgramValue::pointer(mutated.clone())),
        ],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate separate-occurrence effect call should execute");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { .. },
            ..
        }]
    ));
    let [
        FunctionPath {
            outcome: FunctionOutcome::Return { state: after, .. },
            ..
        },
    ] = paths.as_slice()
    else {
        unreachable!("the return path was checked above")
    };
    let kept = CallKeptRanges::recorded_on(after.memory())
        .expect("the call records its protected caller frame");
    assert!(
        kept.holds_access(&viewed, 4, &PureFactContext::new()),
        "the owner escrowed for the stable view preserves the read cell"
    );
    assert!(
        !kept.holds_access(&mutated, 4, &PureFactContext::new()),
        "ownership lent for mutation does not preserve its previous value"
    );
}

/// The same-occurrence case is not weakened. Here one caller occurrence
/// has to serve both requirements: the exclusive reservation takes the
/// owned bytes out of it first, and the overlapping view it would also
/// have to back is no longer there. Provenance settles nothing, because
/// the effect and the view would be the same partition element, and the
/// call is refused rather than accepted on a support comparison.
#[test]
fn candidate_rejects_a_mutable_effect_overlapping_a_view_from_its_own_occurrence() {
    let pointer = pointer();
    let viewed = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(2),
    );
    let owned = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let function = program_function(
        ProgramType::Int32,
        "candidate_same_occurrence_overlap_effect",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![
            ResourceSpec::viewed_memory(viewed),
            ResourceSpec::owned_memory(owned),
        ],
        Vec::new(),
    )
    .with_resource_derived_mutable_frame();
    let paths = execute_program_function_call_paths(
        &caller_with_owned_end(&pointer, 2, 8),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate same-occurrence overlap should execute to a diagnostic path");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
    ));
}

#[test]
fn candidate_allows_provably_disjoint_mutable_effect() {
    let paths = assert_mutable_view_effect_result(1, 2, "candidate_disjoint_effect");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { .. },
            ..
        }]
    ));
}

/// A composite reader whose contract also declares a mutable footprint.
/// The requirement is `views cell(p)`, which carries no memory range of
/// its own; the bytes it protects are the definition's checked frontier.
fn composite_reader_with_mutable_range(
    name: &str,
    mutable_start: u32,
    mutable_end: u32,
) -> ProgramFunction {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let required = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        "cell".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment)],
        Vec::new(),
    );
    program_function(
        ProgramType::Int32,
        name,
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(vec![required], Vec::new())
    .with_composite_resource_definitions(vec![definition])
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(mutable_start),
            crate::kernel::program_expression::int32_literal(mutable_end),
        )],
        Vec::new(),
        true,
    )
}

fn composite_mutable_effect_paths(
    mutable_start: u32,
    mutable_end: u32,
    name: &str,
) -> Vec<FunctionPath> {
    let pointer = pointer();
    let head =
        ResourceFact::own_composite("cell".into(), vec![ProgramValue::pointer(pointer.clone())]);
    let caller = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), 8)
                .store(pointer.clone(), int32(7)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(head));
    let function = composite_reader_with_mutable_range(name, mutable_start, mutable_end);
    execute_program_function_call_paths(
        &caller,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate composite mutable call should execute")
}

/// F6. The head of a composite view has no memory range, so comparing the
/// declared effects against requirement ranges alone saw nothing here.
/// The checked one-level frontier is what the loan protects, and an
/// effect over one of its pieces is a proven overlap.
#[test]
fn candidate_rejects_mutable_effect_overlapping_a_composite_view_piece() {
    let paths = composite_mutable_effect_paths(0, 1, "candidate_composite_overlap_effect");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
            && diagnostic.subject().memory_range().is_some()
    ));
}

/// The same frontier keeps the supported partition usable: a composite
/// body of `p[0..1]` beside an effect on `p[1..2]` is provably disjoint.
#[test]
fn candidate_allows_a_mutable_effect_disjoint_from_a_composite_view_piece() {
    let paths = composite_mutable_effect_paths(1, 2, "candidate_composite_disjoint_effect");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::Return { .. },
            ..
        }]
    ));
}

/// F6. A local view has no caller-owned occurrence, so effect separation
/// must check its actual bytes rather than treating it as a distinct owner.
#[test]
fn candidate_rejects_mutable_effect_overlapping_a_local_view() {
    let pointer = pointer();
    let function = reader_with_mutable_range("candidate_intrinsic_overlap_effect", 0, 1);
    let caller = ExecutionState::new().with_memory(
        Memory::new()
            .with_block(pointer.block.clone(), 8)
            .store(pointer.clone(), int32(7)),
    );
    let paths = execute_program_function_call_paths(
        &caller,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate intrinsic view effect call should execute");
    assert!(matches!(
        paths.as_slice(),
        [FunctionPath {
            outcome: FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)),
            ..
        }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
            && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
    ));
}

#[test]
fn candidate_nested_reader_rejects_stale_outer_binding() {
    let pointer = pointer();
    let function = reader("candidate_stale_nested_reader", false);
    let caller = caller(&pointer);
    let outer_template = bind_program_function_arguments(
        &caller,
        &function,
        &[ProgramValue::pointer(pointer.clone())],
    )
    .expect("outer reader arguments should bind");
    let outer_transfer = prepare_function_resource_transfer(
        &caller,
        &outer_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("outer transfer should run")
    .expect("outer transfer should be accepted");
    let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer)
        .with_loan_view_bindings(LoanViewBindings::default());
    let inner_template = bind_program_function_arguments(
        &outer_callee,
        &function,
        &[ProgramValue::pointer(pointer)],
    )
    .expect("inner reader arguments should bind");
    let result = prepare_function_resource_transfer(
        &outer_callee,
        &inner_template,
        &function,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("stale binding check should run");
    assert!(matches!(
        result,
        Err(RuntimeError::LoanRefusal(diagnostic))
            if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
    ));
}

#[test]
fn candidate_early_return_closes_call_scope() {
    let pointer = pointer();
    let function = early_reader("candidate_early_reader");
    let paths = execute_program_function_call_paths(
        &caller(&pointer),
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment(&function)),
        &mut ExecutionBudget::new(),
    )
    .expect("candidate early return should execute");
    let FunctionOutcome::Return { state, .. } = &paths[0].outcome else {
        panic!(
            "candidate early reader should return: {:?}",
            paths[0].outcome
        );
    };
    assert!(state.resources().satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new(
            pointer,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )),
        &PureFactContext::new(),
    ));
}

#[test]
fn candidate_wrong_scope_close_is_refused() {
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner participant");
    let reader = ledger.fresh_participant().expect("reader participant");
    let escrow = ResourceFact::own(Resource::Token {
        name: "candidate_scope".to_string(),
        arguments: Vec::new().into(),
    });
    let support = ResourceContext::new()
        .unchecked_with_fact(escrow.clone())
        .unique_owned_occurrence_for_fact(&escrow)
        .expect("token backing")
        .0;
    let opening = ledger
        .lend(owner, reader, support, escrow)
        .expect("loan opening");
    let ledger = ledger.apply(&opening.transition).expect("loan apply");
    let refusal = ledger
        .end(opening.scope, reader)
        .expect_err("a non-owner cannot close the scope");
    assert_eq!(
        refusal
            .diagnostic(crate::kernel::LoanRefusalOperation::Transition)
            .category(),
        crate::kernel::LoanRefusalCategory::WrongHolder
    );
    let wrong_scope = super::super::loans::LoanScopeId::for_test(
        opening.scope.arena_for_test(),
        opening.scope.ordinal_for_test().saturating_add(1),
    );
    let refusal = ledger
        .end(wrong_scope, owner)
        .expect_err("an unknown scope cannot be closed");
    assert_eq!(
        refusal
            .diagnostic(crate::kernel::LoanRefusalOperation::Transition)
            .category(),
        crate::kernel::LoanRefusalCategory::WrongScope
    );
}

/// An empty-bodied token population: the caller holds one representative
/// unit and the declared cardinality lives in the tracked population, so
/// `n of slot(p)` is never one owned entry the reservation can select.
fn token_population_reader(name: &str, population: &str) -> ProgramFunction {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let unit = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::Own,
        population.into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Consume,
        ResourceStateSource::Entry,
    )
    .expect("a unit population term");
    let counted = ResourceSpec::quantified(
        crate::kernel::program_expression::variable("n"),
        unit,
        ResourceTransferRole::Consume,
        ResourceStateSource::Entry,
    )
    .expect("a counted population requirement");
    program_function(
        ProgramType::Int32,
        name,
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("n", ProgramType::Int32),
        ],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(segment), counted],
        Vec::new(),
    )
    .with_composite_resource_definitions(vec![
        CompositeResourceDefinition::new(
            population,
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            Vec::new(),
            Vec::new(),
        )
        .with_authorized(true),
    ])
}

/// A declared quantity must be known nonnegative before any resource
/// route looks at it; that check is unrelated to the planner gap.
fn nonnegative_quantity(quantity: Variable) -> PureFactContext {
    PureFactContext::new().assume_condition(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: Box::new(MachineTerm::Variable(quantity)),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    )
}

fn token_population_unit(population: &str, pointer: &Pointer) -> ResourceFact {
    ResourceFact::own_composite(
        population.into(),
        vec![ProgramValue::pointer(pointer.clone())],
    )
}

/// The planner's exclusive reservation has no "N units out of a
/// population whose count is at least N" step, and a token population
/// protects no memory, so nothing about the loan ledger could supply one.
/// Such a requirement is planned beside a view the same call lends.
#[test]
fn candidate_symbolic_token_population_consume_plans_beside_a_lent_view() {
    let pointer = pointer();
    let function = token_population_reader("candidate_population_reader", "slot");
    let unit = token_population_unit("slot", &pointer);
    let base = caller(&pointer);
    let caller = base
        .clone()
        .with_resource_context(base.resources().clone().unchecked_with_fact(unit.clone()));
    let arguments = vec![
        ProgramValue::pointer(pointer.clone()),
        ProgramValue::Int32(MachineTerm::Variable(Variable(4242))),
    ];
    let assumptions = nonnegative_quantity(Variable(4242));
    let callee = bind_program_function_arguments(&caller, &function, &arguments)
        .expect("population reader arguments should bind");
    let transfer = prepare_function_resource_transfer(
        &caller,
        &callee,
        &function,
        &assumptions,
        &mut ExecutionBudget::new(),
        true,
        ResourceTransitionPurpose::CallSite,
    )
    .expect("population transfer should run")
    .expect("a symbolic population quantity should not refuse the plan");
    let plan = transfer
        .stable_view_plan
        .as_ref()
        .expect("the view clause still records a loan plan");
    assert_eq!(plan.stable_views().len(), 1);
    let viewed = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    assert_eq!(
        plan.ledger.permits_memory_access(&viewed),
        Err(LoanRefusal::ActiveDependency)
    );
    assert!(
        transfer
            .callee_resources
            .satisfies_fact(&ResourceFact::view_memory(viewed), &PureFactContext::new())
    );
}

/// Both execution judgments step a sequence with one driver. A sequence
/// whose first statement leaves abnormally carries that statement's loan
/// evidence out with it under either judgment; the concrete driver once
/// rebuilt the path without it. Here a lending call runs first, so the
/// evidence is what leaves.
#[test]
fn an_abnormal_sequence_exit_keeps_its_loan_evidence_under_both_judgments() {
    let pointer = pointer();
    let function = reader("sequence_exit_reader", false);
    let call = program_call(
        "sequence_exit_reader",
        vec![ProgramExpression::Value(ProgramValue::pointer(
            pointer.clone(),
        ))],
    );
    let exits = [
        ("break", program_break()),
        (
            "return",
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
        (
            "throw",
            ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(1)),
        ),
        (
            "runtime error",
            program_assign(
                "undeclared",
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    ];
    for (name, exit) in exits {
        let statement = program_seq(
            program_seq(call.clone(), exit),
            program_assign(
                "unreached",
                crate::kernel::program_expression::int32_literal(2),
            ),
        );
        let ledger = LoanLedger::new();
        let participant = ledger.fresh_participant().expect("caller participant");
        let state = caller(&pointer)
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(participant));
        let environment = environment(&function).with_function(function.clone());
        let executes = crate::kernel::eval::execute_execution_statement_paths(
            &state,
            &statement,
            &PureFactContext::new(),
            ExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
        )
        .expect("the sequence executes");
        let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
        let verifies = crate::kernel::loops::execute_execution_statement_verification_paths(
            &state,
            &statement,
            &PureFactContext::new(),
            ExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
            &mut variables,
        )
        .expect("the sequence verifies");
        assert_eq!(executes.len(), 1, "{name}: {executes:?}");
        assert!(
            !matches!(executes[0].outcome, StatementOutcome::Normal(_)),
            "{name}: the sequence leaves abnormally"
        );
        assert_eq!(
            executes[0].loan_evidence.len(),
            1,
            "{name}: the concrete path keeps the call's evidence"
        );
        assert!(
            verifies
                .iter()
                .any(|path| path.outcome == executes[0].outcome
                    && path.loan_evidence.len() == executes[0].loan_evidence.len()),
            "{name}: the concrete path is a verification path carrying its evidence"
        );
    }
}

#[test]
fn refused_composite_assembly_retains_the_failed_source_clause() {
    let always = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
    };
    let missing = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
    };
    let definition = cell_definition(1, vec![always.clone(), always, missing])
        .with_fact_source_indices(vec![0, 0, 1])
        .with_fact_source_spellings(vec!["0 == 0".into(), "*p == 0".into()]);
    let function = adapter_reader(
        "source_clause_adapter_reader",
        definition,
        wide_definition(2),
    );
    let (_, transfer) = plan_adapter_lend(&function);
    let RuntimeError::UnestablishedAssemblyFact {
        fact,
        source: Some(source),
        ..
    } = transfer.unwrap_err()
    else {
        panic!("the failed body fact must retain its source");
    };
    assert_eq!(
        *fact,
        Proposition::ConditionIs(ConditionTerm::Constant(false), true)
    );
    assert_eq!(source.spelling, "*p == 0");
    assert_eq!(
        source.bindings,
        vec![("p".into(), ProgramValue::pointer(pointer()))]
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/stable_view_call_tests.rs");
}

#[test]
fn local_storage_classification_does_not_restore_partial_or_aliased_authority() {
    for case in [
        "implicit",
        "other_local",
        "partial",
        "view",
        "aliased_partial",
        "aliased_whole",
        "owner_with_alias_fact",
        "unknown_pointer",
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let local = pointer();
        let other = if matches!(
            case,
            "aliased_partial" | "aliased_whole" | "unknown_pointer"
        ) {
            Pointer::symbolic(Variable(941_001))
        } else if case == "other_local" {
            Pointer {
                block: "local:other".into(),
                offset: PointerOffsetTerm::Constant(0),
            }
        } else {
            local.clone()
        };
        let mut facts = PureFactContext::new();
        if matches!(
            case,
            "aliased_partial" | "aliased_whole" | "owner_with_alias_fact"
        ) {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(local.clone(), Pointer::symbolic(Variable(941_001))),
                true,
            );
        }
        let mut resources = ResourceContext::new_with_equalities(&facts);
        if case != "implicit" {
            let range = MemoryRange::new(
                other,
                0u32.into(),
                if matches!(case, "aliased_whole" | "owner_with_alias_fact") {
                    4u32.into()
                } else {
                    1u32.into()
                },
            );
            resources = resources.unchecked_with_fact(if case == "view" {
                ResourceFact::view_memory(range)
            } else {
                ResourceFact::own_memory(range)
            });
        }
        resources.synchronize_memory_equalities(&facts);
        let state = ExecutionState::new()
            .with_memory(
                Memory::new()
                    .with_block(local.block.clone(), 16)
                    .store(local.clone(), int32(7)),
            )
            .with_resource_context(resources);
        let function = reader_for_input("classify_local_storage_authority", 4);
        let paths = execute_program_function_call_paths(
            &state,
            &function,
            &[crate::kernel::program_expression::pointer_value(local)],
            &facts,
            ExecutionContext::execute_bodies(&environment(&function)),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert_eq!(
            matches!(
                paths.as_slice(),
                [FunctionPath {
                    outcome: FunctionOutcome::Return { .. },
                    ..
                }]
            ),
            matches!(case, "implicit" | "other_local" | "owner_with_alias_fact"),
            "{case}: {paths:?}"
        );
    }
}

#[test]
fn local_storage_absence_summary_tracks_persistent_resource_edits() {
    let facts = PureFactContext::new();
    let local = pointer();
    let unknown = ResourceFact::own_memory(MemoryRange::new(
        Pointer::symbolic(Variable(941_002)),
        0u32.into(),
        1u32.into(),
    ));
    let unrelated = ResourceFact::own_memory(MemoryRange::new(
        Pointer {
            block: "local:other".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0u32.into(),
        1u32.into(),
    ));
    let clean = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(unrelated);
    assert!(clean.has_no_explicit_memory_for_local_storage(&local.block, &facts));
    let branch = clean.clone().unchecked_with_fact(unknown.clone());
    assert!(!branch.has_no_explicit_memory_for_local_storage(&local.block, &facts));
    let consumed = branch
        .clone()
        .without_fact_incrementally(&unknown, &facts)
        .unwrap();
    assert!(consumed.has_no_explicit_memory_for_local_storage(&local.block, &facts));
    assert!(clean.has_no_explicit_memory_for_local_storage(&local.block, &facts));
    assert!(!branch.has_no_explicit_memory_for_local_storage(&local.block, &facts));
}
