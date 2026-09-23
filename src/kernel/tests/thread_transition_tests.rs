use super::*;
use crate::kernel::threads::{
    JoinRuntimeAssumption, PendingThreadCreate, ThreadContext, ThreadHandle,
};
use crate::kernel::{CVerifiedFunctionTerminationRule, c_verified_function_termination_rules};
use crate::surface::planning::proposition_search::PropositionSearch;

fn pointer(index: usize) -> Pointer {
    Pointer {
        block: format!("thread-task-{index}").into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn range(index: usize, start: u32, end: u32) -> CMemoryRange {
    CMemoryRange::new(pointer(index), start.into(), end.into())
}

fn parent(size: usize) -> CState {
    let mut memory = CMemory::new();
    let mut resources = ResourceContext::new();
    for index in 0..size {
        memory = memory
            .with_block(pointer(index).block, 8)
            .store(pointer(index), int32(0));
        resources = resources.unchecked_with_fact(CResourceFact::own_memory(range(index, 0, 2)));
    }
    CState::new()
        .with_memory(memory)
        .with_resource_context(resources)
}

fn byte_parent() -> CState {
    CState::new()
        .with_memory(
            CMemory::new()
                .with_block(pointer(0).block, 4)
                .store(pointer(0), CValue::UInt8(0.into())),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                pointer(0),
                0.into(),
                4.into(),
                1,
            )),
        ))
}

fn worker() -> (CVerifiedFunctionRule, CVerifiedFunctionTerminationRule) {
    let owned = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(1),
    ));
    let viewed = CResourceSpec::viewed_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(1),
        c_int32_literal(2),
    ));
    let function = c_function(
        CType::Int32,
        "thread_worker",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(77)),
            c_return(c_int32_literal(7)),
        ),
    )
    .with_resource_summary(vec![owned.clone(), viewed], vec![owned])
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(SpecExpression::CExpression(c_variable("p"))),
                value_type: CType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(77)),
        }],
        vec![],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
            CFunctionContractClaim::ensure_resource(1, 0),
        ],
        true,
    )
    .with_resource_derived_mutable_frame();
    certify_worker(function)
}

fn certify_worker(
    function: CFunction,
) -> (CVerifiedFunctionRule, CVerifiedFunctionTerminationRule) {
    let argument = if matches!(
        function.parameters()[0].c_type(),
        CType::UInt8Pointer | CType::VoidPointer
    ) {
        CExpression::Value(CValue::typed_pointer(
            pointer(0),
            function.parameters()[0].c_type(),
        ))
    } else {
        c_pointer_value(pointer(0))
    };
    let certification_parent = if matches!(
        function.parameters()[0].c_type(),
        CType::UInt8Pointer | CType::VoidPointer
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
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let claims = c_verified_function_contract_claims(&function, &execution).unwrap_or_else(|| {
        panic!(
            "worker body and returned ownership certify: {:?}; diagnostic: {:?}",
            c_unverified_function_contract_claims(&function, &execution),
            execution.reuse_diagnostic(),
        )
    });
    let rule = c_verified_function_rule(function.clone(), &claims).expect("checked worker rule");
    let verdicts = c_verified_function_termination_rules(
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
    let environment = CExecutionEnvironment::new()
        .with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ))
        .with_function(c_function(
            CType::Int32,
            "pthread_create",
            vec![],
            c_return(c_int32_literal(0)),
        ));
    for statement in [
        c_call_assign("result", "pthread_create", vec![]),
        c_call("pthread_create", vec![]),
    ] {
        let paths = execute_c_statement_paths(
            &CState::new(),
            &statement,
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            &paths[0].outcome,
            CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message))
                if message.contains("assigned four-argument call")
        ));
    }
}

fn spawn(
    context: &ThreadContext,
    index: usize,
    worker: &CVerifiedFunctionRule,
    termination: &CVerifiedFunctionTerminationRule,
    budget: &mut ExecutionBudget,
) -> (ThreadContext, ThreadHandle) {
    let (next, handle, _) = context
        .spawn(
            worker,
            Some(termination),
            CValue::pointer(pointer(index)),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
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
    let paths = execute_c_statement_paths(
        spawned.parent(),
        &c_declare("unrelated", CType::Int32),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let CStatementOutcome::Normal(after) = &paths[0].outcome else {
        panic!("unrelated declaration should execute normally");
    };
    let carried = ThreadContext::new(after.clone()).unwrap();
    let returned = execute_c_statement_paths(
        carried.parent(),
        &c_return(c_int32_literal(0)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &returned[0].outcome,
        CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message))
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
    let returned = execute_c_statement_paths(
        joined.parent(),
        &c_return(c_int32_literal(0)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &returned[0].outcome,
        CStatementOutcome::Return { .. }
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
    let environment = CExecutionEnvironment::new().with_modeled_pthread_binding(Some(
        crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
    ));
    let join = |handle: ThreadHandle| {
        c_call_assign(
            "status",
            "pthread_join",
            vec![
                CExpression::Value(handle.c_value()),
                c_pointer_value(Pointer::null()),
            ],
        )
    };
    let state = second
        .parent()
        .clone()
        .with_local("status", int32(9))
        .with_local("copied_handle", first_handle.c_value());
    let guessed = execute_c_statement_paths(
        &state,
        &c_call(
            "pthread_join",
            vec![c_uint64_literal(1), c_pointer_value(Pointer::null())],
        ),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &guessed[0].outcome,
        CStatementOutcome::RuntimeError(_)
    ));
    let paths = execute_c_statement_paths(
        &state,
        &c_call_assign(
            "status",
            "pthread_join",
            vec![
                c_variable("copied_handle"),
                c_pointer_value(Pointer::null()),
            ],
        ),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let CStatementOutcome::Normal(after_first) = &paths[0].outcome else {
        panic!("modeled C join should consume the first child");
    };
    assert_eq!(after_first.locals.get("status"), Some(&int32(0)));
    let (checked, _) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            state.clone(),
            c_call_assign(
                "status",
                "pthread_join",
                vec![
                    c_variable("copied_handle"),
                    c_pointer_value(Pointer::null()),
                ],
            ),
            PureFactContext::new(),
            environment.clone(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        );
    assert_eq!(checked.paths().len(), 1);
    let mut conclusion = checked.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(matches!(
        conclusion,
        Proposition::CStatementVerifies {
            outcome: CStatementOutcome::Normal(_),
            ..
        }
    ));
    let duplicate = execute_c_statement_paths(
        after_first,
        &join(first_handle),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &duplicate[0].outcome,
        CStatementOutcome::RuntimeError(_)
    ));
    let remaining = execute_c_statement_paths(
        after_first,
        &join(second_handle),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &remaining[0].outcome,
        CStatementOutcome::Normal(_)
    ));
}

#[test]
fn modeled_pthread_create_status_selects_the_checked_c_outcome() {
    let owned = CResourceSpec::owned_memory(
        CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(4))
            .with_element_width(1),
    );
    let function = c_function(
        CType::VoidPointer,
        "byte_worker",
        vec![c_parameter("p", CType::VoidPointer)],
        c_seq(
            c_store(
                c_cast(c_variable("p"), CType::UInt8Pointer),
                c_uint8_literal(77),
            ),
            c_return(CExpression::Value(CValue::typed_pointer(
                Pointer::null(),
                CType::VoidPointer,
            ))),
        ),
    )
    .with_resource_summary(vec![owned.clone()], vec![owned])
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_resource(1, 0),
        ],
        true,
    )
    .with_resource_derived_mutable_frame();
    let (worker, termination) = certify_worker(function.clone());
    let environment = CExecutionEnvironment::new()
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
            .unchecked_with_fact(CResourceFact::own_memory(range(1, 0, 1))),
    );
    state.set_memory(
        state
            .memory()
            .clone()
            .with_block(pointer(1).block, 4)
            .store(pointer(1), int32(0)),
    );
    for declaration in [
        c_declare("thread", CType::UInt64),
        c_declare("rc", CType::Int32),
    ] {
        let paths = execute_c_statement_paths(
            &state,
            &declaration,
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let CStatementOutcome::Normal(next) = &paths[0].outcome else {
            panic!("local declaration failed: {:?}", paths[0].outcome);
        };
        state = next.clone();
    }
    let initialized = execute_c_statement_paths(
        &state,
        &c_assign("thread", c_uint64_literal(999)),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let CStatementOutcome::Normal(initialized) = &initialized[0].outcome else {
        panic!("prior handle value should initialize");
    };
    state = initialized.clone();
    let create = c_call_assign(
        "rc",
        "pthread_create",
        vec![
            c_addr_of("thread"),
            c_pointer_value(Pointer::null()),
            c_function_address("byte_worker"),
            CExpression::Value(CValue::typed_pointer(pointer(0), CType::VoidPointer)),
        ],
    );
    let paths = execute_c_statement_paths(
        &state,
        &create,
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let CStatementOutcome::Normal(pending) = &paths[0].outcome else {
        panic!(
            "create should return a pending status: {:?}",
            paths[0].outcome
        );
    };
    assert!(pending.pending_thread_create.is_some());
    assert!(pending.locals.is_uninitialized_object("thread"));
    let external_store = |index, value, value_type, pointer_type| CStatement::TypedStore {
        pointer: CExpression::Value(CValue::typed_pointer(pointer(index), pointer_type)),
        value: CExpression::Value(value),
        value_type,
        volatile: false,
        pointee_constant: false,
    };
    for hostile in [
        external_store(
            0,
            CValue::UInt8(5.into()),
            CType::UInt8,
            CType::UInt8Pointer,
        ),
        CStatement::TypedStore {
            pointer: c_addr_of("thread"),
            value: c_uint64_literal(123),
            value_type: CType::UInt64,
            volatile: false,
            pointee_constant: false,
        },
    ] {
        let paths = execute_c_statement_paths(
            pending,
            &hostile,
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert!(!matches!(paths[0].outcome, CStatementOutcome::Normal(_)));
    }
    let stored = execute_c_statement_paths(
        pending,
        &external_store(1, int32(7), CType::Int32, CType::Int32Pointer),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let CStatementOutcome::Normal(mut delayed) = stored[0].outcome.clone() else {
        panic!("disjoint store failed: {:?}", stored[0].outcome);
    };
    assert!(delayed.pending_thread_create.is_some());
    for statement in [
        c_declare("saved", CType::Int32),
        c_assign("saved", c_variable("rc")),
        c_declare("unrelated", CType::Int32),
        c_assign("unrelated", c_int32_literal(7)),
    ] {
        let paths = execute_c_statement_paths(
            &delayed,
            &statement,
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let CStatementOutcome::Normal(next) = &paths[0].outcome else {
            panic!("delayed local step failed: {:?}", paths[0].outcome);
        };
        delayed = next.clone();
    }
    let branches = execute_c_statement_paths(
        &delayed,
        &c_if(
            c_not_equal(c_variable("saved"), c_int32_literal(0)),
            c_skip(),
            c_skip(),
        ),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(branches.len(), 2, "{branches:?}");
    let mut success = None;
    let mut failure = None;
    for branch in branches {
        let CStatementOutcome::Normal(state) = branch.outcome else {
            panic!("status branch did not resolve: {:?}", branch.outcome);
        };
        assert!(state.pending_thread_create.is_none());
        assert_eq!(state.locals.get("unrelated"), Some(&int32(7)));
        assert_eq!(
            state.memory().load(state.locals.slot("unrelated").unwrap()),
            CExpressionOutcome::Value(int32(7)),
            "a permitted local assignment must remain in C memory after either status"
        );
        assert_eq!(
            state.memory().load(&pointer(1)),
            CExpressionOutcome::Value(int32(7))
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
    assert!(success.locals.get("thread").is_some());
    let premature_read = execute_c_statement_paths(
        &failure,
        &c_assign("rc", c_variable("thread")),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(!matches!(
        premature_read[0].outcome,
        CStatementOutcome::Normal(_)
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
    let join = c_call_assign(
        "rc",
        "pthread_join",
        vec![c_variable("thread"), c_pointer_value(Pointer::null())],
    );
    let joined = execute_c_statement_paths(
        &success,
        &join,
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(joined[0].outcome, CStatementOutcome::Normal(_)));
    let CStatementOutcome::Normal(after_join) = &joined[0].outcome else {
        unreachable!()
    };
    assert_eq!(after_join.resources().facts().len(), 2);
    for fact in [
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            pointer(0),
            0.into(),
            4.into(),
            1,
        )),
        CResourceFact::own_memory(range(1, 0, 1)),
    ] {
        assert!(
            after_join
                .resources()
                .satisfies_fact(&fact, &PureFactContext::new())
        );
    }
    let refused = execute_c_statement_paths(
        &failure,
        &join,
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(
        !matches!(refused[0].outcome, CStatementOutcome::Normal(_)),
        "failed creation must not grant a join: {:?}",
        refused[0].outcome
    );
}

#[test]
fn modeled_pthread_create_refuses_a_wrong_worker_abi() {
    let (worker, termination) = worker();
    let environment = CExecutionEnvironment::new()
        .with_modeled_pthread_binding(Some(
            crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin(),
        ))
        .with_function(worker.function.clone())
        .with_verified_function_rule(worker)
        .with_verified_function_termination_rules([termination]);
    let mut state = parent(1);
    for declaration in [
        c_declare("thread", CType::UInt64),
        c_declare("rc", CType::Int32),
    ] {
        let paths = execute_c_statement_paths(
            &state,
            &declaration,
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let CStatementOutcome::Normal(next) = &paths[0].outcome else {
            panic!("local declaration should succeed");
        };
        state = next.clone();
    }
    let paths = execute_c_statement_paths(
        &state,
        &c_call_assign(
            "rc",
            "pthread_create",
            vec![
                c_addr_of("thread"),
                c_pointer_value(Pointer::null()),
                c_function_address("thread_worker"),
                c_pointer_value(pointer(0)),
            ],
        ),
        &PureFactContext::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message))
            if message.contains("void *(*)(void *)")
    ));
}

#[test]
fn pending_status_resolution_scales_with_explicit_intervening_work() {
    let status = Bitvector32Term::Variable(Variable(890_000));
    let zero = ConditionTerm::Bitvector32Equal(
        Box::new(status.clone()),
        Box::new(Bitvector32Term::Constant(0)),
    );
    let success_assumptions =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(zero.clone(), true));
    let failure_assumptions =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(zero, false));
    let base = parent(1);
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut pending = PendingThreadCreate::new(
            status.clone(),
            Pointer::null(),
            CValue::UInt64(0.into()),
            &base,
            &base,
        );
        let mut visible = base.clone();
        for index in 0..size {
            let value = int32(index as u32);
            visible.set_memory(visible.memory().clone().store(pointer(0), value.clone()));
            pending = pending.with_delta(crate::kernel::threads::PendingThreadMemoryDelta::Store {
                pointer: pointer(0),
                value,
            });
        }
        let failed = pending.resolve(&visible, &failure_assumptions).unwrap();
        assert_eq!(failed.memory(), visible.memory());
        let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
            pending.resolve(&visible, &success_assumptions).unwrap()
        });
        assert_eq!(
            resolved.memory().load(&pointer(0)),
            CExpressionOutcome::Value(int32((size - 1) as u32))
        );
        assert!(work >= size);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "pending resolution grew faster than explicit work: {samples:?}"
        );
    }
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
            &CResourceFact::own_memory(range(first_index, 0, 2)),
            &assumptions,
        ));
        assert!(!joined.parent().resources().satisfies_fact(
            &CResourceFact::own_memory(range(last_index, 0, 1)),
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
                    .satisfies_fact(&CResourceFact::own_memory(range(index, 0, 2)), &assumptions,)
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
            CValue::pointer(pointer(0)),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
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
            CValue::pointer(pointer(1)),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
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
                CValue::pointer(pointer(0)),
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
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
        &CResourceFact::own_memory(range(1, 0, 2)),
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
    wrong.function = c_function(
        CType::Void,
        "thread_worker",
        vec![],
        c_return(c_void_value()),
    );
    for evidence in [None, Some(&wrong)] {
        assert!(
            parent
                .spawn(
                    &worker,
                    evidence,
                    CValue::pointer(pointer(0)),
                    &PureFactContext::new(),
                    &CExecutionEnvironment::new(),
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
        CValue::pointer(pointer(0)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
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
                CValue::pointer(pointer(0)),
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
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
            CValue::pointer(pointer(0)),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
        .unwrap();
    assert!(matches!(
        effect.proposition,
        Proposition::CMemoryEffectSummary { .. }
    ));
    assert!(!spawned.parent().resources().satisfies_fact(
        &CResourceFact::own_memory(range(0, 0, 1)),
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
            Bitvector32Term::MemoryLoad(
                intern_c_memory_ref(spawned.parent().memory()),
                Box::new(pointer(0)),
            ),
            Bitvector32Term::Constant(77),
        ),
        true,
    );
    assert!(
        facts
            .iter()
            .fold(PureFactContext::new(), |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition.clone())
            })
            .proves(&postcondition),
        "join must publish the worker's exact snapshot postcondition"
    );
}

#[test]
fn thread_recovery_work_depends_on_one_child_not_the_outstanding_registry() {
    let (worker, termination) = worker();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut context = ThreadContext::new(parent(size)).unwrap();
        let mut budget = ExecutionBudget::new();
        let mut handles = Vec::new();
        for index in 0..size {
            let (next, handle) = spawn(&context, index, &worker, &termination, &mut budget);
            context = next;
            handles.push(handle);
        }
        let ((next, _), work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .join(
                    handles[0],
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &assumptions,
                )
                .unwrap()
        });
        assert!(work > 0);
        samples.push((size, work));
        // The last child's loan must survive even the oldest child's join.
        assert!(
            next.parent()
                .loan_ledger()
                .unwrap()
                .memory_access_refusal(
                    &range(size - 1, 1, 2),
                    &assumptions,
                    crate::kernel::LoanRefusalOperation::MemoryAccess,
                )
                .is_some()
        );
    }
    assert!(
        samples.last().unwrap().1 <= samples[0].1 * 2,
        "joining one child must not scan the ambient ledger/frame: {samples:?}"
    );
}

#[test]
fn thread_reborrowed_view_stays_pinned_until_child_joins() {
    let function = c_function(
        CType::Int32,
        "thread_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function.clone());
    let view = CResourceFact::view_memory(range(0, 0, 1));
    let state =
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(view.clone()));
    let state = c_state_with_borrowed_contract_inputs(
        state,
        &function,
        &[c_pointer_value(pointer(0))],
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
    let function = c_function(
        CType::Int32,
        "thread_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function);
    let local = Pointer {
        block: "local:shared-reader".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let view = CResourceFact::view_memory(CMemoryRange::new(local.clone(), 0.into(), 1.into()));
    let state = CState::new().with_memory(
        CMemory::new()
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
                CValue::pointer(local.clone()),
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
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
                CValue::pointer(local.clone()),
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
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
    let function = c_function(
        CType::Int32,
        "thread_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function);
    let owned = CResourceFact::own_memory(range(0, 0, 1));
    let viewed = CResourceFact::view_memory(range(0, 0, 1));
    let state =
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(owned.clone()));
    let original = ThreadContext::new(state).unwrap();
    let failed = original
        .prepare_create(
            &reader,
            Some(&termination),
            CValue::pointer(pointer(0)),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
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
fn joining_one_of_many_shared_readers_touches_only_its_share_branch() {
    let function = c_function(
        CType::Int32,
        "thread_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function.clone());
    let view = CResourceFact::view_memory(range(0, 0, 1));
    let state = c_state_with_borrowed_contract_inputs(
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(view.clone())),
        &function,
        &[c_pointer_value(pointer(0))],
        &PureFactContext::new(),
    )
    .unwrap();
    let occurrence = state.resources().occurrences_for_fact(&view)[0];
    let root_binding = state.loan_view_bindings().get(&occurrence).unwrap().clone();
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut context = ThreadContext::new(state.clone()).unwrap();
        let mut handles = Vec::new();
        let mut budget = ExecutionBudget::new();
        for _ in 0..size {
            let (next, handle) = spawn(&context, 0, &reader, &termination, &mut budget);
            context = next;
            handles.push(handle);
        }
        let ((next, _), work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .join(
                    handles[0],
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &PureFactContext::new(),
                )
                .unwrap()
        });
        samples.push((size, work));
        context = next;
        for handle in handles.into_iter().skip(1) {
            context = context
                .join(
                    handle,
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &PureFactContext::new(),
                )
                .unwrap()
                .0;
        }
        assert_eq!(
            context.parent().loan_view_bindings().get(&occurrence),
            Some(&root_binding)
        );
    }
    assert!(
        samples.last().unwrap().1 <= samples[0].1 * 3,
        "joining a fixed shared reader scanned unrelated children: {samples:?}"
    );
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
        c_return(c_load(c_variable("p"))),
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_int32_literal(0)),
        ),
    ] {
        let accessor = c_function(
            CType::Int32,
            "parent_access",
            vec![c_parameter("p", CType::Int32Pointer)],
            body,
        );
        for (state, accessible) in [(spawned.parent(), false), (joined.parent(), true)] {
            let theorem = prove_symbolic_c_function_execution_with_environment(
                state.clone(),
                accessor.clone(),
                vec![c_pointer_value(pointer(0))],
                PureFactContext::new(),
                CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
            )
            .unwrap();
            let Proposition::CFunctionExecutes { outcome, .. } = theorem.proposition() else {
                panic!("function outcome");
            };
            if accessible {
                assert!(matches!(outcome, CFunctionOutcome::Return { .. }));
            } else {
                assert!(
                    matches!(
                        outcome,
                        CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
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
        let state = CState::new()
            .with_memory(CMemory::new().with_block(local.block.clone(), 8))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_memory(CMemoryRange::new(local.clone(), 0.into(), 2.into())),
            ));
        let context = ThreadContext::new(state).unwrap();
        assert!(
            context
                .spawn(
                    &worker,
                    Some(&termination),
                    CValue::pointer(local),
                    &PureFactContext::new(),
                    &CExecutionEnvironment::new(),
                    &mut ExecutionBudget::new(),
                )
                .unwrap()
                .is_err()
        );
    }
}

#[test]
fn thread_local_view_blocks_writes_and_all_scope_exits_until_join() {
    let reader = c_function(
        CType::Int32,
        "local_job_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(reader);
    let mut declaration = crate::kernel::eval::execute_c_statement_paths(
        &CState::new(),
        &c_declare("job", CType::Int32Array(2)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let CStatementOutcome::Normal(declared) = declaration.remove(0).outcome else {
        panic!("local declaration");
    };
    let local = declared.locals().slot("job").unwrap().clone();
    let declared = declared
        .clone()
        .with_memory(declared.memory().clone().store(local.clone(), int32(7)));
    let original = ThreadContext::new(declared).unwrap();
    let (active, handle, _) = original
        .spawn(
            &reader,
            Some(&termination),
            CValue::pointer(local.clone()),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
        .unwrap();
    assert!(
        active.parent().resources().is_empty(),
        "lending a local must not invent explicit ownership"
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
        CStatementOutcome::Normal(state.clone()),
        CStatementOutcome::Break(state.clone()),
        CStatementOutcome::Continue(state.clone()),
        CStatementOutcome::Return {
            value: int32(0),
            state: state.clone(),
        },
        CStatementOutcome::Throw {
            value: int32(0),
            state: state.clone(),
        },
        CStatementOutcome::Jump {
            target: crate::kernel::CControlTargetId(1),
            state: state.clone(),
        },
    ] {
        let paths = crate::kernel::eval::paths_after_scope_exit(
            vec![CStatementExecutionPath {
                outcome,
                facts: vec![],
                obligations: vec![],
                loop_invariant_correspondence: Default::default(),
                loan_evidence: crate::kernel::empty_checked_loan_evidence_sequence(),
            }],
            &names,
        );
        assert!(matches!(
            paths[0].outcome,
            CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_))
        ));
    }
    let writer = c_function(
        CType::Void,
        "alias_write",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_store(c_variable("p"), c_int32_literal(7)),
    );
    let theorem = prove_symbolic_c_function_execution_with_environment(
        active.parent().clone(),
        writer.clone(),
        vec![c_pointer_value(local.clone())],
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .unwrap();
    assert!(
        matches!(
            theorem.proposition(),
            Proposition::CFunctionExecutes {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(_)),
                ..
            }
        ),
        "even a same-value write through an alias conflicts with the local loan"
    );
    let (joined, _) = active
        .join(
            handle,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(joined.parent().resources().is_empty());
    assert!(
        !joined
            .parent()
            .loan_ledger()
            .unwrap()
            .has_active_memory_loans()
    );
    let theorem = prove_symbolic_c_function_execution_with_environment(
        joined.parent().clone(),
        writer,
        vec![c_pointer_value(local.clone())],
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CFunctionExecutes {
            outcome: CFunctionOutcome::Return { .. },
            ..
        }
    ));
    let ended =
        crate::kernel::eval::end_scope_automatic_lifetimes(joined.parent(), &names).unwrap();
    assert!(ended.memory().is_ended_local_address(&local));
}
