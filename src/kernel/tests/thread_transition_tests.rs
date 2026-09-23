use super::*;
use crate::kernel::threads::{JoinRuntimeAssumption, ThreadContext, ThreadHandle};
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
    let execution = certify_contract_with_kernel_artifacts(
        parent(1),
        function.clone(),
        vec![c_pointer_value(pointer(0))],
        vec![],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let claims = c_verified_function_contract_claims(&function, &execution)
        .expect("worker body and returned ownership certify");
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
                if message.contains("no checked C transition")
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
    let original_bindings = state.loan_view_bindings().clone();
    let parent = ThreadContext::new(state).unwrap();
    let mut budget = ExecutionBudget::new();
    let (first, a) = spawn(&parent, 0, &reader, &termination, &mut budget);
    assert!(
        first
            .parent()
            .resources()
            .loan_dependency(occurrence)
            .is_some(),
        "first spawn must preserve the parent's view binding"
    );
    assert!(
        first
            .parent()
            .loan_ledger()
            .unwrap()
            .validate_view_binding(binding.clone(), participant)
            .is_err()
    );
    // The initial slice has no explicit share-splitting protocol: a pinned
    // parent view cannot be reborrowed by a second concurrent reader.
    assert!(
        first
            .spawn(
                &reader,
                Some(&termination),
                CValue::pointer(pointer(0)),
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
                &mut budget,
            )
            .unwrap()
            .is_err()
    );
    let (joined, _) = first
        .join(
            a,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(
        joined
            .parent()
            .loan_ledger()
            .unwrap()
            .validate_view_binding(binding.clone(), participant)
            .is_ok()
    );
    assert_eq!(joined.parent().loan_view_bindings(), &original_bindings);
    let (second, b) = spawn(&joined, 0, &reader, &termination, &mut budget);
    let (finished, _) = second
        .join(
            b,
            JoinRuntimeAssumption::ValidJoinSucceeds,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(
        finished
            .parent()
            .loan_ledger()
            .unwrap()
            .validate_view_binding(binding.clone(), participant)
            .is_ok()
    );
    assert_eq!(finished.parent().loan_view_bindings(), &original_bindings);
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
