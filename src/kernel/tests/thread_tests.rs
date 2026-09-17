//! Focused kernel tests for the checked `pthread_create` / `pthread_join`
//! transitions in `super::super::threads`.
//!
//! Every test drives the real dispatch in `execute_c_function_call_paths`, so
//! what is pinned here is the transition a C call actually takes, not a
//! model of it.

use super::*;
use crate::kernel::primitives::{CExternalFunctionRule, ExternalCallSemantics};
use crate::kernel::threads::JOINABLE_RESOURCE_NAME;

const CELL_BLOCK: &str = "thread-worker-cell";
const HANDLE_BLOCK: &str = "thread-handle-cell";
/// What the worker writes into the cell it was given, so its guarantee is a
/// real fact and not a tautology.
const WORKER_MARK: u32 = 7;

fn block_base(block: &str) -> Pointer {
    Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}

/// One owned int32 cell, the authority the worker takes and returns.
fn owned_int32_cell(pointer: &Pointer) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ))
}

/// The eight-byte `pthread_t` cell the created handle is written to.
fn owned_handle_cell(pointer: &Pointer) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        8,
    ))
}

/// `void *preserve_cell(void *arg)`: requires and returns ownership of the
/// single int32 cell reached through `(int32 *)arg`, writes `WORKER_MARK`
/// into it, and guarantees that value on return.
fn preserve_cell_function() -> CFunction {
    let cell = || c_cast(c_variable("arg"), CType::Int32Pointer);
    let segment = CMemorySegment::new(cell(), c_int32_literal(0), c_int32_literal(1));
    let input = CResourceSpec::memory(
        segment.clone(),
        CResourceAccessMode::Own,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    );
    let output = CResourceSpec::memory(
        segment,
        CResourceAccessMode::Own,
        CResourceTransferRole::Produce,
        CResourceSnapshot::Post,
    );
    let marked = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::CExpression(cell())),
            value_type: CType::Int32,
        },
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(WORKER_MARK))),
    };
    c_function(
        CType::VoidPointer,
        "preserve_cell",
        vec![c_parameter("arg", CType::VoidPointer)],
        c_seq(
            c_typed_store(cell(), c_int32_literal(WORKER_MARK), CType::Int32),
            c_return(c_variable("arg")),
        ),
    )
    .with_resource_summary(vec![input], vec![output])
    .with_contract(
        Vec::new(),
        vec![marked],
        vec![CMemorySegment::new(
            cell(),
            c_int32_literal(0),
            c_int32_literal(1),
        )],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::effect(0),
            CFunctionContractClaim::ensure_resource(0, 0),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    )
}

fn certified_worker(state: &CState, function: CFunction, cell: &Pointer) -> CVerifiedFunctionRule {
    let argument = CExpression::Value(CValue::typed_pointer(cell.clone(), CType::VoidPointer));
    let execution = certify_contract_with_kernel_artifacts(
        state.clone(),
        function.clone(),
        vec![argument],
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let claims = c_verified_function_contract_claims(&function, &execution)
        .expect("the worker body and its returned authority must certify");
    c_verified_function_rule(function, &claims).expect("the worker rule must be fully certified")
}

/// `int pthread_create(pthread_t *, const struct __click_pthread_attr *,
/// void *(*)(void *), void *)`, declaration only: the kernel selects the
/// transition from the registered semantics, never from a body.
fn pthread_create_declaration() -> CFunction {
    c_function(
        CType::Int32,
        "pthread_create",
        vec![
            c_parameter("thread", CType::UInt64Pointer),
            // The opaque `pthread_attr_t *` is modeled as an object pointer;
            // the transition inspects only its nullness.
            c_parameter("attr", CType::VoidPointer),
            c_parameter(
                "start_routine",
                CType::FunctionPointer(CType::function_pointer_signature(
                    CType::VoidPointer,
                    &[CType::VoidPointer],
                )),
            ),
            c_parameter("arg", CType::VoidPointer),
        ],
        c_skip(),
    )
}

/// `int pthread_join(pthread_t, void **)`, declaration only.
fn pthread_join_declaration() -> CFunction {
    c_function(
        CType::Int32,
        "pthread_join",
        vec![
            c_parameter("thread", CType::UInt64),
            c_parameter("retval", CType::VoidPointerPointer),
        ],
        c_skip(),
    )
}

fn thread_environment(worker: CVerifiedFunctionRule) -> CExecutionEnvironment {
    // A C `pthread_create(...)` statement resolves the name through
    // `get_function` before the call executor consults the external rule, so
    // the declarations are registered both ways.
    CExecutionEnvironment::new()
        .with_verified_function_rule(worker)
        .with_function(pthread_create_declaration())
        .with_function(pthread_join_declaration())
        .with_external_function_rule(CExternalFunctionRule {
            function: pthread_create_declaration(),
            semantics: ExternalCallSemantics::ThreadCreate,
        })
        .with_external_function_rule(CExternalFunctionRule {
            function: pthread_join_declaration(),
            semantics: ExternalCallSemantics::ThreadJoin,
        })
}

/// The parent's world: an owned int32 cell it is about to hand to a worker,
/// plus the owned `pthread_t` cell the handle is written into.
struct Fixture {
    cell: Pointer,
    handle_slot: Pointer,
    cell_fact: CResourceFact,
    state: CState,
    environment: CExecutionEnvironment,
}

fn fixture() -> Fixture {
    let cell = block_base(CELL_BLOCK);
    let handle_slot = block_base(HANDLE_BLOCK);
    let cell_fact = owned_int32_cell(&cell);
    let memory = CMemory::new()
        .with_block(cell.block.clone(), 4)
        .with_block(handle_slot.block.clone(), 8)
        .store(cell.clone(), CValue::Int32(Bitvector32Term::Constant(11)));
    let worker_state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(ResourceContext::new().unchecked_with_fact(cell_fact.clone()));
    let worker = certified_worker(&worker_state, preserve_cell_function(), &cell);
    let state = CState::new().with_memory(memory).with_resource_context(
        ResourceContext::new()
            .unchecked_with_facts([cell_fact.clone(), owned_handle_cell(&handle_slot)]),
    );
    Fixture {
        cell,
        handle_slot,
        cell_fact,
        state,
        environment: thread_environment(worker),
    }
}

impl Fixture {
    fn create_arguments(&self) -> Vec<CExpression> {
        vec![
            CExpression::Value(CValue::typed_pointer(
                self.handle_slot.clone(),
                CType::UInt64Pointer,
            )),
            CExpression::Value(CValue::pointer(Pointer::null())),
            c_function_address("preserve_cell"),
            CExpression::Value(CValue::typed_pointer(self.cell.clone(), CType::VoidPointer)),
        ]
    }

    fn create(&self) -> Vec<CFunctionPath> {
        self.create_from(&self.state, self.create_arguments())
    }

    fn create_from(&self, state: &CState, arguments: Vec<CExpression>) -> Vec<CFunctionPath> {
        execute_c_function_call_paths(
            state,
            &pthread_create_declaration(),
            &arguments,
            &PureFactContext::new(),
            &self.environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .expect("thread creation should not exhaust the budget")
    }

    fn join_from(&self, state: &CState, arguments: Vec<CExpression>) -> Vec<CFunctionPath> {
        execute_c_function_call_paths(
            state,
            &pthread_join_declaration(),
            &arguments,
            &PureFactContext::new(),
            &self.environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .expect("thread join should not exhaust the budget")
    }

    fn join(&self, state: &CState, handle: CValue) -> Vec<CFunctionPath> {
        self.join_from(
            state,
            vec![
                CExpression::Value(handle),
                CExpression::Value(CValue::pointer(Pointer::null())),
            ],
        )
    }
}

fn returned(path: &CFunctionPath) -> (&CValue, &CState) {
    match &path.outcome {
        CFunctionOutcome::Return { value, state } => (value, state),
        other => panic!("expected a return, got {other:?}"),
    }
}

fn contract_refusal(path: &CFunctionPath) -> &str {
    match &path.outcome {
        CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)) => message,
        other => panic!("expected a contract refusal, got {other:?}"),
    }
}

/// Splits create's two paths into (success, failure) by their result fact.
fn create_paths(paths: &[CFunctionPath]) -> (&CFunctionPath, &CFunctionPath) {
    assert_eq!(
        paths.len(),
        2,
        "creation has exactly two outcomes: {paths:?}"
    );
    // Creation's two paths are told apart by the polarity of the fact it
    // publishes about its own `int` result.
    let zero = |path: &CFunctionPath| {
        let CFunctionOutcome::Return {
            value: CValue::Int32(Bitvector32Term::Variable(result)),
            ..
        } = &path.outcome
        else {
            panic!("creation returns a symbolic `int`: {path:?}");
        };
        path.facts
            .iter()
            .find_map(|fact| match fact.proposition() {
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), is_zero)
                    if **left == Bitvector32Term::Variable(*result)
                        && **right == Bitvector32Term::Constant(0) =>
                {
                    Some(*is_zero)
                }
                _ => None,
            })
            .expect("each creation path states whether its result is zero")
    };
    let (first, second) = (&paths[0], &paths[1]);
    assert!(zero(first) && !zero(second), "{paths:?}");
    (first, second)
}

/// Whether these facts carry the worker's postcondition, which reads
/// `load((int32 *)arg) == WORKER_MARK` once the load is named.
fn states_the_worker_guarantee(facts: &[ExecutionPureFact]) -> bool {
    facts.iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, right), true)
                if **right == Bitvector32Term::Constant(WORKER_MARK)
        )
    })
}

fn joinable_tokens(state: &CState) -> Vec<&CResourceFact> {
    state
        .resources()
        .facts()
        .iter()
        .filter(|fact| {
            fact.is_own()
                && matches!(fact.resource(), CResource::Token { name, .. }
                    if name == JOINABLE_RESOURCE_NAME)
        })
        .collect()
}

fn handle_in_token(token: &CResourceFact) -> CValue {
    let CResource::Token { arguments, .. } = token.resource() else {
        panic!("a joinable right is a token");
    };
    let Some(AlgebraicValue::C(handle)) = arguments.first() else {
        panic!("a joinable right names its handle first");
    };
    handle.clone()
}

/// The success state, its handle value, and the failure state.
fn created(fixture: &Fixture) -> (CState, CValue, CState) {
    let paths = fixture.create();
    let (success, failure) = create_paths(&paths);
    let (_, success_state) = returned(success);
    let (_, failure_state) = returned(failure);
    let tokens = joinable_tokens(success_state);
    assert_eq!(tokens.len(), 1);
    let handle = handle_in_token(tokens[0]);
    (success_state.clone(), handle, failure_state.clone())
}

#[test]
fn creation_forks_into_a_transferring_success_and_an_inert_failure() {
    let fixture = fixture();
    let paths = fixture.create();
    let (success, failure) = create_paths(&paths);
    let assumptions = PureFactContext::new();

    let (success_value, success_state) = returned(success);
    assert!(matches!(success_value, CValue::Int32(_)));
    // The worker's authority left the parent.
    assert!(
        !success_state
            .resources()
            .satisfies_fact(&fixture.cell_fact, &assumptions)
    );
    // Exactly one completion right, naming the handle written to `*thread`.
    let tokens = joinable_tokens(success_state);
    assert_eq!(tokens.len(), 1);
    let handle = handle_in_token(tokens[0]);
    assert!(matches!(handle, CValue::UInt64(_)));
    assert_eq!(
        success_state.memory().load(&fixture.handle_slot),
        CExpressionOutcome::Value(handle)
    );
    assert_eq!(success_state.pending_joins.len(), 1);
    // The worker's guarantee is withheld with its frame; only its memory
    // effect and the result fact are published at the spawn.
    assert!(
        !states_the_worker_guarantee(&success.facts),
        "the worker's postcondition must not leak to the spawn point: {:?}",
        success.facts
    );
    assert!(
        success.facts.iter().any(|fact| matches!(
            fact.proposition(),
            Proposition::CMemoryEffectSummary { .. } | Proposition::CMemoryMutatesOnly { .. }
        )),
        "the worker's memory effect is published at the spawn: {:?}",
        success.facts
    );

    // Failure transferred nothing and minted nothing.
    let (_, failure_state) = returned(failure);
    assert_eq!(failure_state.resources(), fixture.state.resources());
    assert!(joinable_tokens(failure_state).is_empty());
    assert!(failure_state.pending_joins.is_empty());
}

#[test]
fn join_consumes_the_right_and_installs_the_workers_frame_and_guarantee() {
    let fixture = fixture();
    let (success_state, handle, _) = created(&fixture);
    let paths = fixture.join(&success_state, handle);
    assert_eq!(paths.len(), 1, "{paths:?}");
    let (value, joined) = returned(&paths[0]);
    assert_eq!(*value, CValue::Int32(Bitvector32Term::Constant(0)));
    assert!(joinable_tokens(joined).is_empty());
    assert!(joined.pending_joins.is_empty());
    assert!(
        joined
            .resources()
            .satisfies_fact(&fixture.cell_fact, &PureFactContext::new())
    );
    // The worker's guarantee reaches the parent only here.
    assert!(
        states_the_worker_guarantee(&paths[0].facts),
        "join installs the worker's postcondition: {:?}",
        paths[0].facts
    );
}

/// A second join on one handle is refused -- the soundness property. It is
/// refused by the *pending-record* check, not by the completion-right check,
/// because a successful join removes the record and the token together: a
/// re-join is therefore indistinguishable from a forged handle, and the
/// "already consumed or never held" wording is currently unreachable from
/// this transition. If join learns to keep a consumed record so it can say
/// "already consumed", this assertion is the one to update.
#[test]
fn a_second_join_on_one_handle_is_refused() {
    let fixture = fixture();
    let (success_state, handle, _) = created(&fixture);
    let joined = {
        let paths = fixture.join(&success_state, handle.clone());
        returned(&paths[0]).1.clone()
    };
    let paths = fixture.join(&joined, handle);
    assert_eq!(paths.len(), 1, "{paths:?}");
    let refusal = contract_refusal(&paths[0]);
    assert!(
        refusal.contains("already consumed by an earlier join"),
        "{refusal}"
    );
}

#[test]
fn a_handle_the_parent_never_created_carries_no_authority() {
    let fixture = fixture();
    let (success_state, _, _) = created(&fixture);
    let forged = CValue::UInt64(Bitvector32Term::Variable(Variable(987_654)));
    let paths = fixture.join(&success_state, forged);
    assert_eq!(paths.len(), 1, "{paths:?}");
    let refusal = contract_refusal(&paths[0]);
    assert!(refusal.contains("carry no authority"), "{refusal}");
}

#[test]
fn join_on_the_creation_failure_path_is_refused() {
    let fixture = fixture();
    let (_, handle, failure_state) = created(&fixture);
    let paths = fixture.join(&failure_state, handle);
    assert_eq!(paths.len(), 1, "{paths:?}");
    let refusal = contract_refusal(&paths[0]);
    assert!(refusal.contains("carry no authority"), "{refusal}");
}

#[test]
fn join_refuses_a_non_null_result_slot() {
    let fixture = fixture();
    let (success_state, handle, _) = created(&fixture);
    let paths = fixture.join_from(
        &success_state,
        vec![
            CExpression::Value(handle),
            CExpression::Value(CValue::typed_pointer(
                fixture.handle_slot.clone(),
                CType::VoidPointerPointer,
            )),
        ],
    );
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(contract_refusal(&paths[0]).contains("null `void **`"));
}

#[test]
fn creation_refuses_non_null_attributes() {
    let fixture = fixture();
    let mut arguments = fixture.create_arguments();
    arguments[1] = CExpression::Value(CValue::typed_pointer(
        fixture.cell.clone(),
        CType::VoidPointer,
    ));
    let paths = fixture.create_from(&fixture.state, arguments);
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(contract_refusal(&paths[0]).contains("thread attributes are not supported"));
}

#[test]
fn creation_refuses_a_start_routine_that_is_not_a_function() {
    let fixture = fixture();
    let mut arguments = fixture.create_arguments();
    arguments[2] = CExpression::Value(CValue::typed_pointer(
        fixture.cell.clone(),
        CType::VoidPointer,
    ));
    let paths = fixture.create_from(&fixture.state, arguments);
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(contract_refusal(&paths[0]).contains("address of a verified C function"));
}

#[test]
fn creation_refuses_a_worker_requirement_the_parent_does_not_hold() {
    let fixture = fixture();
    let without_cell = fixture.state.clone().with_resource_context(
        ResourceContext::new().unchecked_with_fact(owned_handle_cell(&fixture.handle_slot)),
    );
    let paths = fixture.create_from(&without_cell, fixture.create_arguments());
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(
        matches!(
            paths[0].outcome,
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
        ),
        "a parent without the worker's authority cannot create: {:?}",
        paths[0].outcome
    );
}

#[test]
fn creation_carries_the_ordinary_store_obligation_for_the_handle_cell() {
    let fixture = fixture();
    let without_slot = fixture.state.clone().with_resource_context(
        ResourceContext::new().unchecked_with_fact(fixture.cell_fact.clone()),
    );
    let paths = fixture.create_from(&without_slot, fixture.create_arguments());
    assert_eq!(paths.len(), 2, "{paths:?}");
    for path in &paths {
        assert!(
            path.obligations.iter().any(|obligation| matches!(
                obligation.proposition(),
                Proposition::CMemoryCanStore { .. }
            )),
            "writing the handle into a cell the memory cannot take concretely leaves the ordinary store obligation: {:?}",
            path.obligations
        );
    }
}

#[test]
fn the_parent_cannot_touch_the_transferred_cell_until_it_joins() {
    let fixture = fixture();
    let (success_state, handle, _) = created(&fixture);
    let store = c_typed_store(
        c_typed_pointer_value(fixture.cell.clone(), CType::Int32Pointer),
        c_int32_literal(5),
        CType::Int32,
    );
    let before = execute_c_statement_paths(
        &success_state,
        &store,
        &PureFactContext::new(),
        &fixture.environment,
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("the store executes");
    assert_eq!(before.len(), 1, "{before:?}");
    assert!(
        matches!(
            before[0].outcome,
            CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
        ),
        "a store into a transferred cell is refused for lack of ownership: {before:?}"
    );

    let joined = {
        let paths = fixture.join(&success_state, handle);
        returned(&paths[0]).1.clone()
    };
    let after = execute_c_statement_paths(
        &joined,
        &store,
        &PureFactContext::new(),
        &fixture.environment,
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("the store executes");
    assert!(
        after
            .iter()
            .any(|path| matches!(path.outcome, CStatementOutcome::Normal(_))),
        "after join the parent owns the cell again: {after:?}"
    );
}

#[test]
fn the_same_task_cannot_be_created_twice_without_joining() {
    let fixture = fixture();
    let (success_state, _, _) = created(&fixture);
    let paths = fixture.create_from(&success_state, fixture.create_arguments());
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(
        matches!(
            paths[0].outcome,
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
        ),
        "the worker's authority was already transferred: {:?}",
        paths[0].outcome
    );
}

/// Everything the create/join pair mints from the execution budget is a
/// function of the inputs: the handle variable, the memory, the resource
/// context, and the suspension keys.
///
/// Whole-`CState` equality deliberately cannot be asserted here. A worker
/// that borrows a view installs a `LoanLedger`, whose identity is a globally
/// minted counter compared nominally, never structurally -- see
/// `state_identity_tests::divergent_ledger_successors_make_state_identities_differ`.
/// Two independent runs therefore carry different ledger identities by
/// design, so this pins the budget-determined content instead.
#[test]
fn create_and_join_mint_the_same_content_from_equal_budgets() {
    let run = || {
        let fixture = fixture();
        let (success_state, handle, _) = created(&fixture);
        let paths = fixture.join(&success_state, handle.clone());
        let (value, joined) = returned(&paths[0]);
        (success_state, handle, value.clone(), joined.clone())
    };
    let (first_created, first_handle, first_value, first_joined) = run();
    let (second_created, second_handle, second_value, second_joined) = run();

    assert_eq!(first_handle, second_handle);
    assert_eq!(first_value, second_value);
    for (first, second) in [
        (&first_created, &second_created),
        (&first_joined, &second_joined),
    ] {
        assert_eq!(first.memory(), second.memory());
        assert_eq!(first.resources(), second.resources());
        assert_eq!(
            first.pending_joins.keys().collect::<Vec<_>>(),
            second.pending_joins.keys().collect::<Vec<_>>()
        );
    }
}

/// Documents the current exit behavior for a path that still owns a
/// `joinable` right. The intended behavior is a refusal: an unjoined thread
/// is a leaked right, exactly like an unfreed allocation. If this test starts
/// failing because the exit check learned to refuse the token, delete it and
/// keep the refusing assertion in its place.
#[test]
fn a_returned_path_still_owning_a_joinable_right_is_refused_at_exit() {
    let fixture = fixture();
    let (success_state, _, _) = created(&fixture);
    let value = CValue::Int32(Bitvector32Term::Constant(0));
    let leaky = c_function(
        CType::Int32,
        "creates_without_joining",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    let refusal = unreturned_allocation_at_function_exit(
        &success_state,
        &value,
        &leaky,
        &[],
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("the exit check should not exhaust the budget")
    .expect_err("a path that still owns a `joinable` right must be refused at exit");
    assert!(
        matches!(&refusal, CRuntimeError::FunctionContract(message) if message.contains("must be joined")),
        "{refusal:?}"
    );
}

/// A whole C function that creates a thread, gives the worker's cell away,
/// and returns without joining. Its contract promises back only the handle
/// cell, so the only thing left over at exit is the `joinable` right.
fn leaky_creator(fixture: &Fixture) -> (CFunction, Vec<CExpression>) {
    let slot = || c_variable("slot");
    let cell = || c_cast(c_variable("cell"), CType::Int32Pointer);
    let handle_segment = || {
        CMemorySegment::new(slot(), c_int32_literal(0), c_int32_literal(1)).with_element_width(8)
    };
    let leaky = c_function(
        CType::Int32,
        "creates_without_joining",
        vec![
            c_parameter("slot", CType::UInt64Pointer),
            c_parameter("cell", CType::VoidPointer),
        ],
        c_seq(
            c_call(
                "pthread_create",
                vec![
                    slot(),
                    CExpression::Value(CValue::pointer(Pointer::null())),
                    c_function_address("preserve_cell"),
                    c_variable("cell"),
                ],
            ),
            c_return(c_int32_literal(0)),
        ),
    )
    .with_resource_summary(
        vec![
            CResourceSpec::memory(
                handle_segment(),
                CResourceAccessMode::Own,
                CResourceTransferRole::Borrow,
                CResourceSnapshot::Entry,
            ),
            CResourceSpec::memory(
                CMemorySegment::new(cell(), c_int32_literal(0), c_int32_literal(1)),
                CResourceAccessMode::Own,
                CResourceTransferRole::Consume,
                CResourceSnapshot::Entry,
            ),
        ],
        // Only the handle cell comes back; the worker's cell is given away.
        vec![CResourceSpec::memory(
            handle_segment(),
            CResourceAccessMode::Own,
            CResourceTransferRole::Produce,
            CResourceSnapshot::Post,
        )],
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_resource(0, 0),
        ],
        true,
    );
    let arguments = vec![
        CExpression::Value(CValue::typed_pointer(
            fixture.handle_slot.clone(),
            CType::UInt64Pointer,
        )),
        CExpression::Value(CValue::typed_pointer(
            fixture.cell.clone(),
            CType::VoidPointer,
        )),
    ];
    (leaky, arguments)
}

/// The exit question asked end to end. Certifying the leaky creator today
/// succeeds: the return-resource check compares only the contract's declared
/// resources, and the allocation check looks only at `allocation` tokens, so
/// neither sees the unjoined thread. Flip this to a refusal when the leak is
/// closed.
#[test]
fn a_whole_function_that_creates_and_never_joins_is_refused() {
    let fixture = fixture();
    let (leaky, arguments) = leaky_creator(&fixture);
    let execution = certify_contract_with_kernel_artifacts(
        fixture.state.clone(),
        leaky.clone(),
        arguments,
        Vec::new(),
        fixture.environment.clone(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert!(
        c_verified_function_contract_claims(&leaky, &execution).is_none(),
        "a function that leaves a `joinable` right behind must not certify"
    );
}

/// `CState::pending_joins` is rebuilt from the *caller's* state whenever a
/// function outcome is assembled, so the suspension record does not cross a
/// function return even though the `joinable` right it backs does. The right
/// that escapes here is therefore permanently unjoinable: a later
/// `pthread_join` on its handle takes the "carry no authority" refusal. This
/// pins today's behavior; the intended behavior is that a right and its
/// record travel together, or that the right cannot escape at all.
#[test]
fn a_joinable_right_never_crosses_a_function_return() {
    let fixture = fixture();
    let (leaky, arguments) = leaky_creator(&fixture);
    let checked = prove_checked_c_function_execution_with_environment(
        fixture.state.clone(),
        leaky,
        arguments,
        PureFactContext::new(),
        fixture.environment.clone(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(checked.paths().len(), 2, "creation's two paths");
    let mut refused = 0;
    let mut returned = 0;
    for path in checked.paths() {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        let Proposition::CFunctionVerifies { outcome, .. } = proposition else {
            panic!("unexpected theorem shape: {proposition:?}");
        };
        match outcome {
            CFunctionOutcome::Return { state, .. } => {
                returned += 1;
                assert!(joinable_tokens(state).is_empty());
                assert!(state.pending_joins.is_empty());
            }
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)) => {
                refused += 1;
                assert!(message.contains("must be joined"), "{message}");
            }
            other => panic!("unexpected outcome: {other:?}"),
        }
    }
    assert_eq!(
        (refused, returned),
        (1, 1),
        "the successful creation is refused at return; the failed one returns"
    );
}
