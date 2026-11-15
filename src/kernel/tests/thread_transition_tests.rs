use super::*;
use crate::kernel::threads::{
    JoinRuntimeAssumption, PendingThreadCreate, ThreadContext, ThreadHandle,
};
use crate::kernel::{VerifiedFunctionTerminationRule, program_verified_function_termination_rules};

fn pointer(index: usize) -> Pointer {
    Pointer {
        block: format!("thread-task-{index}").into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn range(index: usize, start: u32, end: u32) -> MemoryRange {
    MemoryRange::new(pointer(index), start.into(), end.into())
}

fn parent(size: usize) -> ExecutionState {
    let mut memory = Memory::new();
    let mut resources = ResourceContext::new();
    for index in 0..size {
        memory = memory
            .with_block(pointer(index).block, 8)
            .store(pointer(index), int32(0));
        resources = resources.unchecked_with_fact(ResourceFact::own_memory(range(index, 0, 2)));
    }
    ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(memory)
        .with_resource_context(resources)
}

fn byte_parent() -> ExecutionState {
    ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_block(pointer(0).block, 4)
                .store(pointer(0), crate::kernel::uint8(0)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer(0),
                0.into(),
                4.into(),
                1,
            )),
        ))
}

fn worker() -> (VerifiedFunctionRule, VerifiedFunctionTerminationRule) {
    let owned = ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    ));
    let viewed = ResourceSpec::viewed_memory(MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(1),
        crate::kernel::program_expression::int32_literal(2),
    ));
    let function = program_function(
        ProgramType::Int32,
        "thread_worker",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_seq(
            program_store(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(77),
            ),
            program_return(crate::kernel::program_expression::int32_literal(7)),
        ),
    )
    .with_resource_summary(vec![owned.clone(), viewed], vec![owned])
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("p"),
                )),
                value_type: ProgramType::Int32,
            },
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(77)),
        }],
        vec![],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
            FunctionContractClaim::ensure_resource(1, 0),
        ],
        true,
    )
    .with_resource_derived_mutable_frame();
    certify_worker(function)
}

fn certify_worker(
    function: ProgramFunction,
) -> (VerifiedFunctionRule, VerifiedFunctionTerminationRule) {
    let argument = if matches!(
        function.parameters()[0].program_type(),
        ProgramType::UInt8Pointer | ProgramType::VoidPointer
    ) {
        ProgramExpression::Value(ProgramValue::typed_pointer(
            pointer(0),
            function.parameters()[0].program_type(),
        ))
    } else {
        crate::kernel::program_expression::pointer_value(pointer(0))
    };
    let certification_parent = if matches!(
        function.parameters()[0].program_type(),
        ProgramType::UInt8Pointer | ProgramType::VoidPointer
    ) {
        byte_parent()
    } else {
        parent(1)
    };
    let execution = certify_contract_with_kernel_artifacts(
        certification_parent,
        function.clone(),
        vec![argument],
        vec![],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let claims =
        program_verified_function_contract_claims(&function, &execution).unwrap_or_else(|| {
            panic!(
                "worker body and returned ownership certify: {:?}; diagnostic: {:?}",
                program_unverified_function_contract_claims(&function, &execution),
                execution.reuse_diagnostic(),
            )
        });
    let rule =
        program_verified_function_rule(function.clone(), &claims).expect("checked worker rule");
    let verdicts = program_verified_function_termination_rules(
        std::slice::from_ref(&rule),
        &[],
        &Default::default(),
        &[],
        &[(function.name().to_string(), 0)].into_iter().collect(),
        &Default::default(),
        &Default::default(),
        &Default::default(),
    )
    .unwrap();
    assert!(verdicts.refusals.is_empty(), "{:?}", verdicts.refusals);
    (
        rule,
        verdicts.rules.into_iter().next().expect("worker returns"),
    )
}

#[test]
fn modeled_pthread_calls_cannot_fall_back_to_ordinary_function_rules() {
    let environment = ExecutionEnvironment::new()
        .with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ))
        .with_function(program_function(
            ProgramType::Int32,
            "pthread_create",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ));
    for statement in [
        program_call_then_assign(0, "result", "pthread_create", vec![]),
        program_call("pthread_create", vec![]),
    ] {
        let paths = execute_execution_statement_paths(
            &ExecutionState::new(),
            &statement,
            &PureFactContext::new(),
            ExecutionContext::execute_bodies(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            &paths[0].outcome,
            StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message))
                if message.contains("assigned four-argument call")
        ));
    }
}

fn spawn(
    context: &ThreadContext,
    index: usize,
    worker: &VerifiedFunctionRule,
    termination: &VerifiedFunctionTerminationRule,
    budget: &mut ExecutionBudget,
) -> (ThreadContext, ThreadHandle) {
    let (next, handle, _) = context
        .spawn(
            worker,
            Some(termination),
            ProgramValue::pointer(pointer(index)),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            budget,
        )
        .unwrap()
        .unwrap();
    (next, handle)
}

#[test]
fn completion_right_survives_an_unrelated_c_statement_in_path_state() {
    let (worker, termination) = worker();
    let original = ThreadContext::new(parent(2)).unwrap();
    let (spawned, handle) = spawn(
        &original,
        0,
        &worker,
        &termination,
        &mut ExecutionBudget::new(),
    );
    let paths = execute_execution_statement_paths(
        spawned.parent(),
        &program_declare("unrelated", ProgramType::Int32),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let StatementOutcome::Normal(after) = &paths[0].outcome else {
        panic!("unrelated declaration should execute normally");
    };
    let carried = ThreadContext::new(*after.clone()).unwrap();
    let returned = execute_execution_statement_paths(
        carried.parent(),
        &program_return(crate::kernel::program_expression::int32_literal(0)),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &returned[0].outcome,
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message))
            if message.contains("live pthread completion right")
    ));
    let (joined, _) = carried
        .join(
            handle,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(
        joined
            .join(
                handle,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .is_err()
    );
    assert!(
        spawned
            .join(
                handle,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new()
            )
            .is_ok()
    );
    let returned = execute_execution_statement_paths(
        joined.parent(),
        &program_return(crate::kernel::program_expression::int32_literal(0)),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &returned[0].outcome,
        StatementOutcome::Return { .. }
    ));
}

#[test]
fn modeled_pthread_join_call_consumes_only_the_named_completion() {
    let (worker, termination) = worker();
    let original = ThreadContext::new(parent(2)).unwrap();
    let (first, first_handle) = spawn(
        &original,
        0,
        &worker,
        &termination,
        &mut ExecutionBudget::new(),
    );
    let (second, second_handle) = spawn(
        &first,
        1,
        &worker,
        &termination,
        &mut ExecutionBudget::new(),
    );
    let environment = ExecutionEnvironment::new().with_modeled_pthread_binding(Some(
        crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
    ));
    let join = |handle: ThreadHandle| {
        program_call_then_assign(
            1,
            "status",
            "pthread_join",
            vec![
                ProgramExpression::Value(handle.program_value()),
                crate::kernel::program_expression::pointer_value(Pointer::null()),
            ],
        )
    };
    let state = second
        .parent()
        .clone()
        .with_local("status", int32(9))
        .with_local("copied_handle", first_handle.program_value());
    let guessed = execute_execution_statement_paths(
        &state,
        &program_call(
            "pthread_join",
            vec![
                crate::kernel::program_expression::uint64_literal(1),
                crate::kernel::program_expression::pointer_value(Pointer::null()),
            ],
        ),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &guessed[0].outcome,
        StatementOutcome::RuntimeError(_)
    ));
    let paths = execute_execution_statement_paths(
        &state,
        &program_call_then_assign(
            2,
            "status",
            "pthread_join",
            vec![
                crate::kernel::program_expression::variable("copied_handle"),
                crate::kernel::program_expression::pointer_value(Pointer::null()),
            ],
        ),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let StatementOutcome::Normal(after_first) = &paths[0].outcome else {
        panic!("modeled C join should consume the first child");
    };
    assert_eq!(
        after_first.locals.get_native("status").as_deref(),
        Some(&int32(0))
    );
    let (checked, _) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            state.clone(),
            program_call_then_assign(3,
                "status",
                "pthread_join",
                vec![
                    crate::kernel::program_expression::variable("copied_handle"),
                    crate::kernel::program_expression::pointer_value(Pointer::null()),
                ],
            ),
            PureFactContext::new(),
            environment.clone(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        );
    assert_eq!(checked.paths().len(), 1);
    let mut conclusion = checked.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(matches!(
        conclusion,
        Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Normal(_),
            ..
        }
    ));
    let duplicate = execute_execution_statement_paths(
        after_first,
        &join(first_handle),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &duplicate[0].outcome,
        StatementOutcome::RuntimeError(_)
    ));
    let remaining = execute_execution_statement_paths(
        after_first,
        &join(second_handle),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(&remaining[0].outcome, StatementOutcome::Normal(_)));
}

#[test]
fn modeled_pthread_create_status_selects_the_checked_c_outcome() {
    let owned = ResourceSpec::owned_memory(
        MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(4),
        )
        .with_element_width(1),
    );
    let function = program_function(
        ProgramType::VoidPointer,
        "byte_worker",
        vec![program_parameter("p", ProgramType::VoidPointer)],
        program_seq(
            program_store(
                crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable("p"),
                    ProgramType::UInt8Pointer,
                ),
                crate::kernel::program_expression::uint8_literal(77),
            ),
            program_return(ProgramExpression::Value(ProgramValue::typed_pointer(
                Pointer::null(),
                ProgramType::VoidPointer,
            ))),
        ),
    )
    .with_resource_summary(vec![owned.clone()], vec![owned])
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_resource(1, 0),
        ],
        true,
    )
    .with_resource_derived_mutable_frame();
    let (worker, termination) = certify_worker(function.clone());
    let environment = ExecutionEnvironment::new()
        .with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ))
        .with_function(function)
        .with_verified_function_rule(worker)
        .with_verified_function_termination_rules([termination]);
    let mut state = byte_parent().with_resource_context(
        byte_parent()
            .resources()
            .clone()
            .unchecked_with_fact(ResourceFact::own_memory(range(1, 0, 1))),
    );
    state.set_memory(
        state
            .memory()
            .clone()
            .with_block(pointer(1).block, 4)
            .store(pointer(1), int32(0)),
    );
    for declaration in [
        program_declare("thread", ProgramType::UInt64),
        program_declare("rc", ProgramType::Int32),
    ] {
        let paths = execute_execution_statement_paths(
            &state,
            &declaration,
            &PureFactContext::new(),
            ExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let StatementOutcome::Normal(next) = &paths[0].outcome else {
            panic!("local declaration failed: {:?}", paths[0].outcome);
        };
        state = *next.clone();
    }
    let initialized = execute_execution_statement_paths(
        &state,
        &program_assign(
            "thread",
            crate::kernel::program_expression::uint64_literal(999),
        ),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let StatementOutcome::Normal(initialized) = &initialized[0].outcome else {
        panic!("prior handle value should initialize");
    };
    state = *initialized.clone();
    let create = program_call_then_assign(
        4,
        "rc",
        "pthread_create",
        vec![
            crate::kernel::program_expression::addr_of("thread"),
            crate::kernel::program_expression::pointer_value(Pointer::null()),
            crate::kernel::program_expression::function_address("byte_worker"),
            ProgramExpression::Value(ProgramValue::typed_pointer(
                pointer(0),
                ProgramType::VoidPointer,
            )),
        ],
    );
    let paths = execute_execution_statement_paths(
        &state,
        &create,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let StatementOutcome::Normal(pending) = &paths[0].outcome else {
        panic!(
            "create should return a pending status: {:?}",
            paths[0].outcome
        );
    };
    assert!(pending.pending_thread_create.is_some());
    assert!(pending.locals.is_uninitialized_object("thread"));
    let external_store = |index, value, value_type, pointer_type| ProgramStatement::TypedStore {
        access_class: None,
        pointer: ProgramExpression::Value(ProgramValue::typed_pointer(
            pointer(index),
            pointer_type,
        )),
        value: ProgramExpression::Value(value),
        value_type,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    for hostile in [
        external_store(
            0,
            crate::kernel::uint8(5),
            ProgramType::UInt8,
            ProgramType::UInt8Pointer,
        ),
        ProgramStatement::TypedStore {
            access_class: None,
            pointer: crate::kernel::program_expression::addr_of("thread"),
            value: crate::kernel::program_expression::uint64_literal(123),
            value_type: ProgramType::UInt64,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        },
    ] {
        let paths = execute_execution_statement_paths(
            pending,
            &hostile,
            &PureFactContext::new(),
            ExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert!(!matches!(paths[0].outcome, StatementOutcome::Normal(_)));
    }
    let stored = execute_execution_statement_paths(
        pending,
        &external_store(1, int32(7), ProgramType::Int32, ProgramType::Int32Pointer),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let StatementOutcome::Normal(mut delayed) = stored[0].outcome.clone() else {
        panic!("disjoint store failed: {:?}", stored[0].outcome);
    };
    assert!(delayed.pending_thread_create.is_some());
    for statement in [
        program_declare("saved", ProgramType::Int32),
        program_assign("saved", crate::kernel::program_expression::variable("rc")),
        program_declare("unrelated", ProgramType::Int32),
        program_assign(
            "unrelated",
            crate::kernel::program_expression::int32_literal(7),
        ),
    ] {
        let paths = execute_execution_statement_paths(
            &delayed,
            &statement,
            &PureFactContext::new(),
            ExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let StatementOutcome::Normal(next) = &paths[0].outcome else {
            panic!("delayed local step failed: {:?}", paths[0].outcome);
        };
        delayed = next.clone();
    }
    let status_branch = program_if(
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::variable("saved"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        program_skip(),
        program_skip(),
    );
    let branches = execute_execution_statement_paths(
        &delayed,
        &status_branch,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(branches.len(), 2, "{branches:?}");
    // The verification judgment steps the branch with the same driver, so
    // it passes the same pending-create gate and resolves the create at the
    // branch, rather than reading the state with the create still pending.
    let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
    let verified = crate::kernel::loops::execute_execution_statement_verification_paths(
        &delayed,
        &status_branch,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
        &mut variables,
    )
    .unwrap();
    assert_eq!(
        verified
            .iter()
            .map(|path| &path.outcome)
            .collect::<Vec<_>>(),
        branches
            .iter()
            .map(|path| &path.outcome)
            .collect::<Vec<_>>(),
        "both judgments step the status branch alike"
    );
    // A branch that reads memory while the create is pending is refused at
    // the gate under both judgments. Verification once stepped a branch with
    // its own driver, which evaluated the condition before any gate.
    let memory_branch = program_if(
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::load(ProgramExpression::Value(
                ProgramValue::pointer(pointer(1)),
            )),
            crate::kernel::program_expression::int32_literal(0),
        ),
        program_skip(),
        program_skip(),
    );
    let refused = |paths: &[StatementExecutionPath]| {
        paths.len() == 1 && matches!(paths[0].outcome, StatementOutcome::RuntimeError(_))
    };
    let executes = execute_execution_statement_paths(
        &delayed,
        &memory_branch,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(refused(&executes), "{executes:?}");
    let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
    let verifies = crate::kernel::loops::execute_execution_statement_verification_paths(
        &delayed,
        &memory_branch,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
        &mut variables,
    )
    .unwrap();
    assert!(refused(&verifies), "{verifies:?}");
    let mut success = None;
    let mut failure = None;
    for branch in branches {
        let StatementOutcome::Normal(state) = branch.outcome else {
            panic!("status branch did not resolve: {:?}", branch.outcome);
        };
        assert!(state.pending_thread_create.is_none());
        assert_eq!(
            state.locals.get_native("unrelated").as_deref(),
            Some(&int32(7))
        );
        assert_eq!(
            state.memory().load(state.locals.slot("unrelated").unwrap()),
            ExpressionOutcome::Value(int32(7)),
            "a permitted local assignment must remain in C memory after either status"
        );
        assert_eq!(
            state.memory().load(&pointer(1)),
            ExpressionOutcome::Value(int32(7))
        );
        if state
            .thread_ledger
            .as_ref()
            .is_some_and(|ledger| ledger.has_live_rights())
        {
            success = Some(state);
        } else {
            failure = Some(state);
        }
    }
    let success = success.expect("zero status should create a child");
    let failure = failure.expect("nonzero status should retain the parent");
    assert!(failure.locals.is_uninitialized_object("thread"));
    assert!(success.locals.get_native("thread").as_deref().is_some());
    let premature_read = execute_execution_statement_paths(
        &failure,
        &program_assign("rc", crate::kernel::program_expression::variable("thread")),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(!matches!(
        premature_read[0].outcome,
        StatementOutcome::Normal(_)
    ));
    assert_eq!(failure.resources(), state.resources());
    assert_eq!(
        failure.memory().load(&pointer(0)),
        state.memory().load(&pointer(0))
    );
    assert_ne!(success.resources(), state.resources());
    assert_ne!(
        success.memory().load(&pointer(0)),
        state.memory().load(&pointer(0))
    );
    let join = program_call_then_assign(
        5,
        "rc",
        "pthread_join",
        vec![
            crate::kernel::program_expression::variable("thread"),
            crate::kernel::program_expression::pointer_value(Pointer::null()),
        ],
    );
    let joined = execute_execution_statement_paths(
        &success,
        &join,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(joined[0].outcome, StatementOutcome::Normal(_)));
    let StatementOutcome::Normal(after_join) = &joined[0].outcome else {
        unreachable!()
    };
    // The two caller scalar allocation owners survive alongside the recovered
    // thread argument and byte owners; no worker token or loan escapes join.
    assert_eq!(after_join.resources().facts().len(), 4);
    for fact in [
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            Memory::local_pointer("thread"),
            0.into(),
            8.into(),
            1,
        )),
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            Memory::local_pointer("rc"),
            0.into(),
            4.into(),
            1,
        )),
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            pointer(0),
            0.into(),
            4.into(),
            1,
        )),
        ResourceFact::own_memory(range(1, 0, 1)),
    ] {
        assert!(
            after_join
                .resources()
                .satisfies_fact(&fact, &PureFactContext::new())
        );
    }
    let refused = execute_execution_statement_paths(
        &failure,
        &join,
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(
        !matches!(refused[0].outcome, StatementOutcome::Normal(_)),
        "failed creation must not grant a join: {:?}",
        refused[0].outcome
    );
}

#[test]
fn modeled_pthread_create_refuses_a_wrong_worker_abi() {
    let (worker, termination) = worker();
    let environment = ExecutionEnvironment::new()
        .with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ))
        .with_function(worker.function.clone())
        .with_verified_function_rule(worker)
        .with_verified_function_termination_rules([termination]);
    let mut state = parent(1);
    for declaration in [
        program_declare("thread", ProgramType::UInt64),
        program_declare("rc", ProgramType::Int32),
    ] {
        let paths = execute_execution_statement_paths(
            &state,
            &declaration,
            &PureFactContext::new(),
            ExecutionContext::apply_verified_rules(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let StatementOutcome::Normal(next) = &paths[0].outcome else {
            panic!("local declaration should succeed");
        };
        state = *next.clone();
    }
    let paths = execute_execution_statement_paths(
        &state,
        &program_call_then_assign(
            6,
            "rc",
            "pthread_create",
            vec![
                crate::kernel::program_expression::addr_of("thread"),
                crate::kernel::program_expression::pointer_value(Pointer::null()),
                crate::kernel::program_expression::function_address("thread_worker"),
                crate::kernel::program_expression::pointer_value(pointer(0)),
            ],
        ),
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message))
            if message.contains("void *(*)(void *)")
    ));
}

#[test]
fn thread_join_preserves_other_child_loans_in_both_orders() {
    let (worker, termination) = worker();
    let assumptions = PureFactContext::new();
    for reverse in [false, true] {
        let original = ThreadContext::new(parent(2)).unwrap();
        let mut budget = ExecutionBudget::new();
        let (first, a) = spawn(&original, 0, &worker, &termination, &mut budget);
        let (both, b) = spawn(&first, 1, &worker, &termination, &mut budget);
        let before_join = both.parent().memory().clone();
        let (first_handle, first_index, last_handle, last_index) =
            if reverse { (b, 1, a, 0) } else { (a, 0, b, 1) };
        let (joined, _) = both
            .join(
                first_handle,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &assumptions,
            )
            .unwrap();
        assert_eq!(
            joined.parent().memory(),
            &before_join,
            "join must not rewind memory"
        );
        assert!(joined.parent().resources().satisfies_fact(
            &ResourceFact::own_memory(range(first_index, 0, 2)),
            &assumptions,
        ));
        assert!(!joined.parent().resources().satisfies_fact(
            &ResourceFact::own_memory(range(last_index, 0, 1)),
            &assumptions,
        ));
        assert!(
            joined
                .parent()
                .loan_ledger()
                .unwrap()
                .memory_access_refusal(
                    &range(last_index, 1, 2),
                    &assumptions,
                    crate::kernel::LoanRefusalOperation::MemoryAccess,
                )
                .is_some(),
            "the other child's stable job view must remain protected"
        );
        assert!(
            joined
                .join(
                    first_handle,
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &assumptions
                )
                .is_err()
        );
        let (finished, _) = joined
            .join(
                last_handle,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &assumptions,
            )
            .unwrap();
        for index in 0..2 {
            assert!(
                finished
                    .parent()
                    .resources()
                    .satisfies_fact(&ResourceFact::own_memory(range(index, 0, 2)), &assumptions,)
            );
            assert!(
                finished
                    .parent()
                    .loan_ledger()
                    .unwrap()
                    .memory_access_refusal(
                        &range(index, 1, 2),
                        &assumptions,
                        crate::kernel::LoanRefusalOperation::MemoryAccess,
                    )
                    .is_none()
            );
        }
    }
}

#[test]
fn thread_failed_creation_and_rejected_spawn_preserve_parent() {
    let (worker, termination) = worker();
    let original = ThreadContext::new(parent(2)).unwrap();
    let mut budget = ExecutionBudget::new();
    let prepared = original
        .prepare_create(
            &worker,
            Some(&termination),
            ProgramValue::pointer(pointer(0)),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            &mut budget,
        )
        .unwrap()
        .unwrap();
    assert_eq!(prepared.failure().parent(), original.parent());
    let (first, handle) = spawn(&original, 0, &worker, &termination, &mut budget);
    let failed = first
        .prepare_create(
            &worker,
            Some(&termination),
            ProgramValue::pointer(pointer(1)),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            &mut budget,
        )
        .unwrap()
        .unwrap()
        .failure();
    assert_eq!(failed.parent(), first.parent());
    // The task is already transferred: a second writer cannot receive it.
    assert!(
        failed
            .prepare_create(
                &worker,
                Some(&termination),
                ProgramValue::pointer(pointer(0)),
                &PureFactContext::new(),
                &ExecutionEnvironment::new(),
                &mut budget,
            )
            .unwrap()
            .is_err()
    );
    let (joined, _) = failed
        .join(
            handle,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(joined.parent().resources().satisfies_fact(
        &ResourceFact::own_memory(range(1, 0, 2)),
        &PureFactContext::new(),
    ));
    assert!(
        original
            .join(
                handle,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new()
            )
            .is_err()
    );
    assert!(
        ThreadContext::new(parent(2))
            .unwrap()
            .join(
                handle,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new()
            )
            .is_err()
    );
}

#[test]
fn thread_spawn_requires_exact_termination_evidence() {
    let (worker, termination) = worker();
    let parent = ThreadContext::new(parent(1)).unwrap();
    let mut wrong = termination.clone();
    wrong.function = program_function(
        ProgramType::Void,
        "thread_worker",
        vec![],
        program_return(program_void_value()),
    );
    for evidence in [None, Some(&wrong)] {
        assert!(
            parent
                .spawn(
                    &worker,
                    evidence,
                    ProgramValue::pointer(pointer(0)),
                    &PureFactContext::new(),
                    &ExecutionEnvironment::new(),
                    &mut ExecutionBudget::new(),
                )
                .unwrap()
                .is_err()
        );
    }
}

#[test]
fn thread_empty_or_ambiguous_worker_frontier_is_a_refusal() {
    use crate::kernel::functions::{suspend_verified_worker, unique_worker_completion};
    assert!(unique_worker_completion(true, vec![]).is_err());
    let (worker, _) = worker();
    let parent = ThreadContext::new(parent(1)).unwrap();
    let completion = suspend_verified_worker(
        parent.parent(),
        &worker,
        ProgramValue::pointer(pointer(0)),
        &PureFactContext::new(),
        &ExecutionEnvironment::new(),
        &mut ExecutionBudget::new(),
    )
    .unwrap()
    .unwrap();
    assert!(unique_worker_completion(true, vec![completion.clone(), completion.clone()]).is_err());
    assert!(unique_worker_completion(false, vec![completion]).is_err());
    assert!(
        parent
            .prepare_create(
                &worker,
                None,
                ProgramValue::pointer(pointer(0)),
                &PureFactContext::new(),
                &ExecutionEnvironment::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
            .is_err(),
        "failure cannot hide an invalid worker task"
    );
}

#[test]
fn thread_guarantees_are_withheld_until_join() {
    let (worker, termination) = worker();
    let original = ThreadContext::new(parent(1)).unwrap();
    let (spawned, handle, effect) = original
        .spawn(
            &worker,
            Some(&termination),
            ProgramValue::pointer(pointer(0)),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
        .unwrap();
    assert!(matches!(
        effect.proposition,
        Proposition::MemoryEffectSummary { .. }
    ));
    assert!(!spawned.parent().resources().satisfies_fact(
        &ResourceFact::own_memory(range(0, 0, 1)),
        &PureFactContext::new(),
    ));
    let (_, facts) = spawned
        .join(
            handle,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    let postcondition = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                intern_memory_ref(spawned.parent().memory()),
                Box::new(pointer(0)),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::constant(77),
        ),
        true,
    );
    assert!(
        crate::kernel::search::ProofSearch::proves(
            &(facts
                .iter()
                .fold(PureFactContext::new(), |assumptions, fact| {
                    assumptions.assume_proposition(fact.proposition.clone())
                })),
            &postcondition
        ),
        "join must publish the worker's exact state postcondition"
    );
}

#[test]
fn thread_reborrowed_view_stays_pinned_until_child_joins() {
    let function = program_function(
        ProgramType::Int32,
        "thread_reader",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function.clone());
    let view = ResourceFact::view_memory(range(0, 0, 1));
    let state =
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(view.clone()));
    let state = execution_state_with_borrowed_contract_inputs(
        state,
        &function,
        &[crate::kernel::program_expression::pointer_value(pointer(0))],
        &PureFactContext::new(),
    )
    .unwrap();
    let occurrence = state.resources().occurrences_for_fact(&view)[0];
    let binding = state.loan_view_bindings().get(&occurrence).unwrap().clone();
    let participant = state.loan_participant().unwrap();
    let parent = ThreadContext::new(state).unwrap();
    let mut budget = ExecutionBudget::new();
    for reverse in [false, true] {
        let (first, a) = spawn(&parent, 0, &reader, &termination, &mut budget);
        let (second, b) = spawn(&first, 0, &reader, &termination, &mut budget);
        assert!(
            second
                .parent()
                .loan_ledger()
                .unwrap()
                .validate_view_binding(binding.clone(), participant)
                .is_err(),
            "the original whole share is split while children are live"
        );
        assert!(second.parent().loan_bindings_are_consistent());
        assert!(
            !second
                .parent()
                .thread_ledger
                .as_ref()
                .unwrap()
                .witnesses_loan_recovery(
                    parent.parent().loan_ledger().unwrap(),
                    second.parent().loan_ledger().unwrap(),
                    participant,
                )
        );
        let (joined, _) = second
            .join(
                if reverse { b } else { a },
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .unwrap();
        assert!(joined.parent().loan_bindings_are_consistent());
        let (finished, _) = joined
            .join(
                if reverse { a } else { b },
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .unwrap();
        assert_eq!(
            finished.parent().loan_view_bindings().get(&occurrence),
            Some(&binding),
            "the exact root share must be reconstructed after both joins"
        );
        assert!(finished.parent().loan_bindings_are_consistent());
        assert!(
            finished
                .parent()
                .thread_ledger
                .as_ref()
                .unwrap()
                .witnesses_loan_recovery(
                    parent.parent().loan_ledger().unwrap(),
                    finished.parent().loan_ledger().unwrap(),
                    participant,
                )
        );
    }
}

#[test]
fn two_workers_share_one_implicit_local_root_until_both_join() {
    let function = program_function(
        ProgramType::Int32,
        "thread_reader",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function);
    let local = Pointer {
        block: "local:shared-reader".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let view = ResourceFact::view_memory(MemoryRange::new(local.clone(), 0.into(), 1.into()));
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_block(local.block.clone(), 4)
                .store(local.clone(), int32(7)),
        );
    let original = ThreadContext::new(state).unwrap();
    for reverse in [false, true] {
        let mut budget = ExecutionBudget::new();
        let (first, a, _) = original
            .spawn(
                &reader,
                Some(&termination),
                ProgramValue::pointer(local.clone()),
                &PureFactContext::new(),
                &ExecutionEnvironment::new(),
                &mut budget,
            )
            .unwrap()
            .unwrap();
        let first_binding = first
            .parent()
            .thread_ledger
            .as_ref()
            .unwrap()
            .local_view_binding(&view)
            .unwrap()
            .clone();
        let (second, b, _) = first
            .spawn(
                &reader,
                Some(&termination),
                ProgramValue::pointer(local.clone()),
                &PureFactContext::new(),
                &ExecutionEnvironment::new(),
                &mut budget,
            )
            .unwrap()
            .unwrap();
        let second_binding = second
            .parent()
            .thread_ledger
            .as_ref()
            .unwrap()
            .local_view_binding(&view)
            .unwrap();
        assert_eq!(first_binding.loan, second_binding.loan);
        assert_eq!(first_binding.scope, second_binding.scope);
        assert_ne!(first_binding.share, second_binding.share);
        assert!(second.parent().resources().facts().is_empty());
        let (once, _) = second
            .join(
                if reverse { b } else { a },
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .unwrap();
        assert!(
            once.parent()
                .thread_ledger
                .as_ref()
                .unwrap()
                .local_view_binding(&view)
                .is_some()
        );
        assert!(
            once.parent()
                .loan_ledger()
                .unwrap()
                .permits_memory_access(view.memory_range().unwrap())
                .is_err()
        );
        let (finished, _) = once
            .join(
                if reverse { a } else { b },
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .unwrap();
        assert!(
            finished
                .parent()
                .thread_ledger
                .as_ref()
                .unwrap()
                .local_view_binding(&view)
                .is_none()
        );
        assert!(
            !finished
                .parent()
                .loan_ledger()
                .unwrap()
                .has_active_memory_loans()
        );
        assert!(finished.parent().resources().facts().is_empty());
    }
}

#[test]
fn two_workers_recover_one_escrowed_owner_only_after_both_join() {
    let function = program_function(
        ProgramType::Int32,
        "thread_reader",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function);
    let owned = ResourceFact::own_memory(range(0, 0, 1));
    let viewed = ResourceFact::view_memory(range(0, 0, 1));
    let state =
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(owned.clone()));
    let original = ThreadContext::new(state).unwrap();
    let failed = original
        .prepare_create(
            &reader,
            Some(&termination),
            ProgramValue::pointer(pointer(0)),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
        .unwrap()
        .failure();
    assert_eq!(failed.parent().resources(), original.parent().resources());
    assert_eq!(
        failed.parent().loan_ledger(),
        original.parent().loan_ledger()
    );
    assert!(
        !failed
            .parent()
            .thread_ledger
            .as_ref()
            .unwrap()
            .has_live_rights()
    );
    for reverse in [false, true] {
        let mut budget = ExecutionBudget::new();
        let (first, a) = spawn(&original, 0, &reader, &termination, &mut budget);
        assert!(
            !first
                .parent()
                .resources()
                .satisfies_fact(&owned, &PureFactContext::new())
        );
        assert_eq!(
            first
                .parent()
                .resources()
                .view_occurrences_for_fact(&viewed, &PureFactContext::new())
                .len(),
            1
        );
        let (second, b) = spawn(&first, 0, &reader, &termination, &mut budget);
        let (once, _) = second
            .join(
                if reverse { b } else { a },
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .unwrap();
        assert!(
            !once
                .parent()
                .resources()
                .satisfies_fact(&owned, &PureFactContext::new())
        );
        assert!(
            once.parent()
                .loan_ledger()
                .unwrap()
                .permits_memory_access(&range(0, 0, 1))
                .is_err()
        );
        let (finished, _) = once
            .join(
                if reverse { a } else { b },
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .unwrap();
        assert!(
            finished
                .parent()
                .resources()
                .satisfies_fact(&owned, &PureFactContext::new())
        );
        assert!(
            finished
                .parent()
                .resources()
                .view_occurrences_for_fact(&viewed, &PureFactContext::new())
                .is_empty()
        );
        assert!(
            !finished
                .parent()
                .loan_ledger()
                .unwrap()
                .has_active_memory_loans()
        );
        assert!(finished.parent().loan_bindings_are_consistent());
    }
}

#[test]
fn shared_reader_completion_right_is_consumed_once_on_its_own_path() {
    let function = program_function(
        ProgramType::Int32,
        "thread_reader",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function.clone());
    let view = ResourceFact::view_memory(range(0, 0, 1));
    let state = execution_state_with_borrowed_contract_inputs(
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(view)),
        &function,
        &[crate::kernel::program_expression::pointer_value(pointer(0))],
        &PureFactContext::new(),
    )
    .unwrap();
    let original = ThreadContext::new(state).unwrap();
    let mut budget = ExecutionBudget::new();
    let (first, a) = spawn(&original, 0, &reader, &termination, &mut budget);
    let (second, b) = spawn(&first, 0, &reader, &termination, &mut budget);
    let (after_a, _) = second
        .join(
            a,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(
        after_a
            .join(
                a,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .err(),
        Some("no live completion right for this handle")
    );
    assert_eq!(
        first
            .join(
                b,
                JoinRuntimeAssumption::ValidJoinSucceeds,
                &PureFactContext::new(),
            )
            .err(),
        Some("no live completion right for this handle"),
        "a handle from a later path cannot recover a sibling here"
    );
    assert!(
        after_a
            .parent()
            .loan_ledger()
            .unwrap()
            .has_active_memory_loans()
    );
    let (finished, _) = after_a
        .join(
            b,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(finished.parent().loan_bindings_are_consistent());
}

#[test]
fn thread_parent_c_access_requires_join_and_implicit_storage_transfers_refuse() {
    let (worker, termination) = worker();
    let original = ThreadContext::new(parent(1)).unwrap();
    let (spawned, handle) = spawn(
        &original,
        0,
        &worker,
        &termination,
        &mut ExecutionBudget::new(),
    );
    let (joined, _) = spawned
        .join(
            handle,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    for body in [
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
        program_seq(
            program_store(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(9),
            ),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
    ] {
        let accessor = program_function(
            ProgramType::Int32,
            "parent_access",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            body,
        );
        for (state, accessible) in [(spawned.parent(), false), (joined.parent(), true)] {
            let theorem = prove_symbolic_program_function_execution_with_environment(
                state.clone(),
                accessor.clone(),
                vec![crate::kernel::program_expression::pointer_value(pointer(0))],
                PureFactContext::new(),
                ExecutionEnvironment::new(),
                ExecutionSemantics::EXECUTE_BODIES,
            )
            .unwrap();
            let Proposition::ProgramFunctionExecutes { outcome, .. } = theorem.proposition() else {
                panic!("function outcome");
            };
            if accessible {
                assert!(matches!(outcome, FunctionOutcome::Return { .. }));
            } else {
                assert!(
                    matches!(
                        outcome,
                        FunctionOutcome::RuntimeError(RuntimeError::MissingResource { .. })
                    ),
                    "parent access must be refused before join"
                );
            }
        }
    }
    for block in [
        "local:thread-output",
        "global:thread-output",
        "static:thread-output",
    ] {
        let local = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = ExecutionState::new()
            .with_population_creation_tracking()
            .with_memory(Memory::new().with_block(local.block.clone(), 8))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new(local.clone(), 0.into(), 2.into())),
            ));
        let context = ThreadContext::new(state).unwrap();
        assert!(
            context
                .spawn(
                    &worker,
                    Some(&termination),
                    ProgramValue::pointer(local),
                    &PureFactContext::new(),
                    &ExecutionEnvironment::new(),
                    &mut ExecutionBudget::new(),
                )
                .unwrap()
                .is_err()
        );
    }
}

#[test]
fn thread_local_view_blocks_writes_and_all_scope_exits_until_join() {
    let reader = program_function(
        ProgramType::Int32,
        "local_job_reader",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(reader);
    let mut declaration = crate::kernel::eval::execute_execution_statement_paths(
        &ExecutionState::new().with_population_creation_tracking(),
        &program_declare("job", ProgramType::Int32Array(2)),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let StatementOutcome::Normal(declared) = declaration.remove(0).outcome else {
        panic!("local declaration");
    };
    let local = declared.locals().slot("job").unwrap().clone();
    let declared = declared
        .clone()
        .with_memory(declared.memory().clone().store(local.clone(), int32(7)));
    let declared_resources = declared.resources().facts().to_vec();
    let original = ThreadContext::new(declared).unwrap();
    let (active, handle, _) = original
        .spawn(
            &reader,
            Some(&termination),
            ProgramValue::pointer(local.clone()),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
        .unwrap();
    // The frame owns the array's bytes from its declaration. The view loan
    // escrows the lent element's backing and adds no ownership: the parent
    // keeps exactly the rest of the array.
    let [ResourceFact::Own(Resource::Memory(declared_range), _)] = declared_resources.as_slice()
    else {
        panic!("a local array's declaration owns its bytes");
    };
    // The parent keeps a view of the lent element and owns only the rest.
    let owned = active
        .parent()
        .resources()
        .facts()
        .iter()
        .filter_map(|fact| match fact {
            ResourceFact::Own(Resource::Memory(range), _) => Some(range),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [kept] = owned.as_slice() else {
        panic!("lending a local must not invent explicit ownership");
    };
    assert_eq!(kept.base().block, declared_range.base().block);
    assert_eq!(
        (kept.constant_start(), kept.constant_end()),
        (Some(4), Some(8)),
        "the parent keeps exactly the array's unlent bytes"
    );
    assert!(
        active
            .parent()
            .loan_ledger()
            .unwrap()
            .has_active_memory_loans()
    );
    let names = vec!["job".to_string()];
    assert!(crate::kernel::eval::end_scope_automatic_lifetimes(active.parent(), &names).is_err());
    let state = active.parent();
    for outcome in [
        StatementOutcome::Normal(Box::new(state.clone())),
        StatementOutcome::Break(Box::new(state.clone())),
        StatementOutcome::Continue(Box::new(state.clone())),
        StatementOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state.clone()),
        },
        StatementOutcome::Throw {
            value: int32(0).into(),
            state: Box::new(state.clone()),
        },
        StatementOutcome::Jump {
            target: crate::kernel::ControlTargetId(1),
            state: Box::new(state.clone()),
        },
    ] {
        let paths = crate::kernel::eval::paths_after_scope_exit(
            vec![StatementExecutionPath {
                call_parameters: None,
                outcome,
                facts: vec![].into(),
                obligations: vec![],
                loop_invariant_correspondence: Default::default(),
                call_result: None,
                loan_evidence: crate::kernel::empty_checked_loan_evidence_sequence(),
            }],
            &names,
        );
        assert!(matches!(
            paths[0].outcome,
            StatementOutcome::RuntimeError(RuntimeError::LoanRefusal(_))
        ));
    }
    let writer = program_function(
        ProgramType::Void,
        "alias_write",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(7),
        ),
    );
    let theorem = prove_symbolic_program_function_execution_with_environment(
        active.parent().clone(),
        writer.clone(),
        vec![crate::kernel::program_expression::pointer_value(
            local.clone(),
        )],
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
    )
    .unwrap();
    let Proposition::Implies(requirement, _) = theorem.proposition() else {
        panic!("even a same-value alias write must require loan separation");
    };
    let Proposition::ResourceSeparate { left, right } = requirement.as_ref() else {
        panic!("expected the explicit loan separation premise");
    };
    assert!(!PureFactContext::new().proves_resource_separate(left, right));
    let (joined, _) = active
        .join(
            handle,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    // The join ends the loan: the parent again owns all of the array's bytes,
    // in the pieces the loan left, and holds nothing else.
    let mut owned = joined
        .parent()
        .resources()
        .facts()
        .iter()
        .map(|fact| match fact {
            ResourceFact::Own(Resource::Memory(range), _) => {
                assert_eq!(range.base().block, declared_range.base().block);
                let width = range.element_width();
                (
                    range.constant_start().unwrap() * width,
                    range.constant_end().unwrap() * width,
                )
            }
            other => panic!("joining must not leave {other:?}"),
        })
        .collect::<Vec<_>>();
    owned.sort();
    let mut cursor = 0;
    for (start, end) in owned {
        assert_eq!(start, cursor, "the parent's bytes are contiguous");
        cursor = end;
    }
    assert_eq!(cursor, 8, "the parent owns the whole array again");
    assert!(
        !joined
            .parent()
            .loan_ledger()
            .unwrap()
            .has_active_memory_loans()
    );
    let theorem = prove_symbolic_program_function_execution_with_environment(
        joined.parent().clone(),
        writer,
        vec![crate::kernel::program_expression::pointer_value(
            local.clone(),
        )],
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::ProgramFunctionExecutes {
            outcome: FunctionOutcome::Return { .. },
            ..
        }
    ));
    let ended =
        crate::kernel::eval::end_scope_automatic_lifetimes(joined.parent(), &names).unwrap();
    assert!(ended.memory().is_ended_local_address(&local));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/thread_transition_tests.rs");
}
