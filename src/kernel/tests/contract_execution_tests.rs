// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::kernel::LoanRefusalCategory;
use crate::surface::planning::proposition_search::PropositionSearch;

fn borrowed_input_view_function(name: &str) -> CFunction {
    c_function(CType::Void, name, vec![], c_return(c_void_value())).with_resource_summary(
        vec![CResourceSpec::token(
            CResourceAccessMode::View,
            "borrowed_input".into(),
            vec![],
            vec![],
        )],
        vec![],
    )
}

#[test]
fn borrowed_contract_input_roots_only_the_exact_principal_view() {
    let viewed = CResourceFact::view_token("borrowed_input".into(), vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let occurrence = resources.occurrences_for_fact(&viewed)[0];
    let state = CState::new().with_resource_context(resources);
    let rooted = c_state_with_borrowed_contract_inputs(
        state,
        &borrowed_input_view_function("read_borrowed_input"),
        &[],
        &PureFactContext::new(),
    )
    .expect("a checked principal input view receives external shared authority");

    assert!(rooted.loan_ledger().is_some());
    assert!(rooted.loan_participant().is_some());
    assert_eq!(
        rooted
            .loan_view_bindings()
            .get(&occurrence)
            .map(|binding| &binding.viewed),
        Some(&viewed)
    );
    assert!(rooted.loan_bindings_are_consistent());
}

/// Every proof unit of one function shares one installed root: a second
/// install on the same entry state returns the same ledger identity, while a
/// changed entry state gets a fresh one.
#[test]
fn borrowed_contract_input_roots_are_shared_across_proof_units_of_one_function() {
    let viewed = CResourceFact::view_token("borrowed_input".into(), vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let state = CState::new().with_resource_context(resources);
    let function = borrowed_input_view_function("shared_root_reader");
    let first = c_state_with_borrowed_contract_inputs(
        state.clone(),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect("first install");
    let second = c_state_with_borrowed_contract_inputs(
        state.clone(),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect("second install on the same entry state");
    assert_eq!(first.loan_ledger(), second.loan_ledger());
    assert_eq!(first.loan_participant(), second.loan_participant());
    assert_eq!(first, second);

    let other_resources = ResourceContext::new().unchecked_with_facts([
        viewed.clone(),
        CResourceFact::own_token("extra".into(), vec![]),
    ]);
    let changed = c_state_with_borrowed_contract_inputs(
        CState::new().with_resource_context(other_resources),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect("install on a changed entry state");
    assert_ne!(first.loan_ledger(), changed.loan_ledger());
}

/// An owned clause that provably overlaps a viewed clause of the same
/// contract is a partition no caller can supply; the root installer refuses
/// it instead of proving a vacuous body under it.
#[test]
fn borrowed_contract_input_refuses_an_owned_clause_inside_a_viewed_range() {
    let pointer = crate::kernel::Pointer {
        block: "buffer".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let viewed = CResourceFact::view_memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    let owned = CResourceFact::own_memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
    ));
    let state = CState::new()
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 8))
        .with_resource_context(
            ResourceContext::new().unchecked_with_facts([viewed.clone(), owned.clone()]),
        );
    let function = c_function(
        CType::Int32,
        "overlapping_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![
            CResourceSpec::viewed_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(2),
            )),
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(1),
                c_int32_literal(2),
            )),
        ],
        vec![],
    );
    let refusal = c_state_with_borrowed_contract_inputs(
        state,
        &function,
        &[CExpression::Value(CValue::pointer(pointer))],
        &PureFactContext::new(),
    )
    .expect_err("an owned clause inside the viewed range is refused at entry");
    assert_eq!(refusal.category(), LoanRefusalCategory::ProvenOverlap);
}

#[test]
fn borrowed_contract_input_rejects_derived_or_ambiguous_views() {
    let viewed = CResourceFact::view_token("borrowed_input".into(), vec![]);
    let owner = CResourceFact::own_token("owner".into(), vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let owner_occurrence = resources.owned_occurrences_for_fact(&owner)[0];
    let derived = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        owner_occurrence,
        &owner,
        [viewed.clone()],
        &CMemory::new(),
    );
    let function = borrowed_input_view_function("reject_derived_input");
    let refusal = c_state_with_borrowed_contract_inputs(
        CState::new().with_resource_context(derived),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect_err("a projection derived from owned authority is not an external root");
    assert_eq!(refusal.category(), LoanRefusalCategory::Missing);

    let duplicate = ResourceContext::new().unchecked_with_facts([viewed.clone(), viewed]);
    let refusal = c_state_with_borrowed_contract_inputs(
        CState::new().with_resource_context(duplicate),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect_err("equal principal occurrences are ambiguous authority anchors");
    assert_eq!(refusal.category(), LoanRefusalCategory::Missing);
}

/// The aggregate-copy path is the same shape at a wider width: the copy's
/// target is owned, its source is readable, and the lent range inside the
/// target refuses the whole-struct write at the ledger (R01 aggregate case;
/// docs/internals/stable-views.md).
#[test]
fn owner_authorized_aggregate_copy_into_a_lent_range_is_refused() {
    let target = Pointer {
        block: "target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source = Pointer {
        block: "source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned_target = own_memory_fact(target.clone(), 0, 2);
    let owned_source = own_memory_fact(source.clone(), 0, 2);
    let viewed = view_memory_fact(target.clone(), 1, 2);
    let resources =
        ResourceContext::new().unchecked_with_facts([owned_target, owned_source, viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().expect("a fresh participant");
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a checked contract input root");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("the input root applies");
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = CState::new()
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let layout = CAggregateLayout::new(
        8,
        4,
        vec![
            CAggregateField::new("a", 0, CType::Int32),
            CAggregateField::new("b", 4, CType::Int32),
        ],
    );
    let function = c_function(
        CType::Void,
        "copy_struct_over_lent_field",
        vec![
            c_parameter("s", CType::Int32Pointer),
            c_parameter("t", CType::Int32Pointer),
        ],
        c_copy_aggregate(c_variable("s"), c_variable("t"), layout),
    );
    let arguments = vec![c_pointer_value(target.clone()), c_pointer_value(source)];
    let theorem = prove_symbolic_c_function_execution_with_environment(
        state,
        function,
        arguments,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("an owner-authorized aggregate copy over a lent field has a checked outcome");
    let Proposition::CFunctionExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected a function execution proposition");
    };
    let CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)) = outcome else {
        panic!("expected a loan refusal, got {outcome:?}");
    };
    assert_eq!(diagnostic.category(), LoanRefusalCategory::ActiveDependency);
    assert_eq!(
        diagnostic.operation(),
        crate::kernel::LoanRefusalOperation::MemoryAccess
    );
    assert_eq!(
        diagnostic.subject().conflicting_resource_fact(),
        Some(&view_memory_fact(target, 1, 2))
    );
}

/// The loan barrier exists for exactly one shape: a write the ordinary
/// owned-authority check already accepted, landing inside a concretely lent
/// range. An unowned write never reaches it, because the missing-ownership
/// check now runs first.
#[test]
fn owner_authorized_write_into_a_lent_range_is_refused() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned = own_memory_fact(pointer.clone(), 0, 2);
    let viewed = view_memory_fact(pointer.clone(), 0, 1);
    let resources = ResourceContext::new().unchecked_with_facts([owned, viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().expect("a fresh participant");
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a checked contract input root");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("the input root applies");
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = CState::new()
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let function = c_function(
        CType::Void,
        "write_owned_lent_cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_store(c_variable("p"), c_int32_literal(9)),
    );
    let pointer_for_assertions = pointer.clone();
    let arguments = vec![c_pointer_value(pointer)];
    let theorem = prove_symbolic_c_function_execution_with_environment(
        state,
        function,
        arguments,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("an owner-authorized write into a lent range has a checked outcome");
    let Proposition::CFunctionExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected a function execution proposition");
    };
    let CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)) = outcome else {
        panic!("expected a loan refusal, got {outcome:?}");
    };
    // The D13 shape: which loan, where it came from, what it protects, and
    // what the write attempted.
    assert_eq!(diagnostic.category(), LoanRefusalCategory::ActiveDependency);
    assert_eq!(
        diagnostic.operation(),
        crate::kernel::LoanRefusalOperation::MemoryAccess
    );
    let subject = diagnostic.subject();
    assert_eq!(
        subject.conflicting_resource_fact(),
        Some(&view_memory_fact(pointer_for_assertions.clone(), 0, 1))
    );
    assert_eq!(
        subject.memory_range().map(CMemoryRange::base),
        Some(&pointer_for_assertions)
    );
    assert_eq!(
        subject.origin(),
        Some(crate::kernel::LoanOriginKind::ContractInputView)
    );
    assert!(subject.loan_id().is_some());
}

/// D2 law 2 is an access restriction, not an equality check: a store of the
/// value the lent cell already holds is refused exactly like a store of a
/// different one. The cell is pre-populated with the stored value, so the
/// only difference from
/// `owner_authorized_write_into_a_lent_range_is_refused` is that the write
/// would change nothing (R01's same-value negative; docs/internals/stable-views.md).
#[test]
fn owner_authorized_same_value_store_into_a_lent_range_is_refused() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned = own_memory_fact(pointer.clone(), 0, 2);
    let viewed = view_memory_fact(pointer.clone(), 0, 1);
    let resources = ResourceContext::new().unchecked_with_facts([owned, viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().expect("a fresh participant");
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a checked contract input root");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("the input root applies");
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    // The cell already holds 9; the body stores 9 into it.
    let populated = CMemory::new()
        .with_block(pointer.block.clone(), 8)
        .store(pointer.clone(), int32(9));
    let state = CState::new()
        .with_memory(populated.clone())
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let function = c_function(
        CType::Void,
        "store_the_same_value_into_a_lent_cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_store(c_variable("p"), c_int32_literal(9)),
    );
    let pointer_for_assertions = pointer.clone();
    let arguments = vec![c_pointer_value(pointer)];
    let theorem = prove_symbolic_c_function_execution_with_environment(
        state,
        function,
        arguments,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("a same-value store into a lent range has a checked outcome");
    let Proposition::CFunctionExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected a function execution proposition");
    };
    let CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)) = outcome else {
        panic!("expected a loan refusal, got {outcome:?}");
    };
    assert_eq!(diagnostic.category(), LoanRefusalCategory::ActiveDependency);
    assert_eq!(
        diagnostic.operation(),
        crate::kernel::LoanRefusalOperation::MemoryAccess
    );
    let subject = diagnostic.subject();
    assert_eq!(
        subject.conflicting_resource_fact(),
        Some(&view_memory_fact(pointer_for_assertions, 0, 1))
    );
    assert_eq!(
        subject.origin(),
        Some(crate::kernel::LoanOriginKind::ContractInputView)
    );
}

#[test]
fn certified_program_entry_claims_do_not_authorize_ordinary_calls() {
    let function = c_function(CType::Int32, "main", vec![], c_return(c_int32_literal(0)))
        .with_program_entry()
        .with_contract(
            vec![],
            vec![],
            vec![],
            vec![CFunctionContractClaim::body_safety()],
            true,
        );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        vec![],
        vec![],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let claims = c_verified_function_contract_claims(&function, &execution).unwrap();
    assert!(!claims.is_empty());
    assert!(c_verified_function_rule(function, &claims).is_none());
}

fn pool_resource_spec(name: &str) -> CResourceSpec {
    CResourceSpec::composite(
        CResourceAccessMode::Own,
        name.to_string(),
        vec![c_variable("pool"), c_variable("object")],
        vec![CType::Int32, CType::Int32],
    )
}

fn pool_transition_function(from: &str, to: &str) -> CFunction {
    let parameters = vec![
        c_parameter("pool", CType::Int32),
        c_parameter("object", CType::Int32),
    ];
    let definition_parameters = parameters.clone();
    c_function(
        CType::Void,
        format!("{from}_to_{to}"),
        parameters,
        c_return(CExpression::Value(CValue::Void)),
    )
    .with_resource_summary(vec![pool_resource_spec(from)], vec![pool_resource_spec(to)])
    .with_composite_resource_definitions(vec![
        CCompositeResourceDefinition::new(
            from,
            definition_parameters.clone(),
            None,
            false,
            Vec::new(),
            Vec::new(),
        ),
        CCompositeResourceDefinition::new(
            to,
            definition_parameters,
            None,
            false,
            Vec::new(),
            Vec::new(),
        ),
    ])
}

fn apply_pool_transition(state: &CState, function: &CFunction, pool: u32, object: u32) -> CState {
    let arguments = vec![c_int32_literal(pool), c_int32_literal(object)];
    let outcome = CFunctionOutcome::Return {
        value: CValue::Void,
        state: state.clone(),
    };
    let (outcome, obligations) = apply_c_function_contract_resource_transition(
        state,
        function,
        &arguments,
        outcome,
        &PureFactContext::new(),
    )
    .expect("the checked resource transition should check");
    assert!(obligations.is_empty());
    let CFunctionOutcome::Return { state, .. } = outcome else {
        panic!("resource transition did not return");
    };
    state
}

fn pool_count(state: &CState, pool: u32) -> Bitvector32Term {
    state
        .counted_population_sum(
            "pool_object",
            &[Some(int32(pool).into()), None],
            &PureFactContext::new(),
        )
        .expect("the pool's entries total a count")
}

#[test]
fn observed_resource_family_counts_cross_checked_contracts() {
    let checkout = pool_transition_function("available", "pool_object");
    let return_object = pool_transition_function("pool_object", "available");
    let mut state = CState::new()
        .with_observed_population_family("pool_object")
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own_composite(
                    "available".to_string(),
                    vec![int32(1), int32(10)],
                ))
                .unchecked_with_fact(CResourceFact::own_composite(
                    "available".to_string(),
                    vec![int32(1), int32(11)],
                ))
                .unchecked_with_fact(CResourceFact::own_composite(
                    "available".to_string(),
                    vec![int32(2), int32(20)],
                )),
        );

    assert_eq!(pool_count(&state, 1), Bitvector32Term::Constant(0));
    assert_eq!(pool_count(&state, 2), Bitvector32Term::Constant(0));

    state = apply_pool_transition(&state, &checkout, 1, 10);
    assert_eq!(pool_count(&state, 1), Bitvector32Term::Constant(1));
    assert_eq!(pool_count(&state, 2), Bitvector32Term::Constant(0));

    state = apply_pool_transition(&state, &checkout, 1, 11);
    assert_eq!(pool_count(&state, 1), Bitvector32Term::Constant(2));
    assert_eq!(pool_count(&state, 2), Bitvector32Term::Constant(0));

    state = apply_pool_transition(&state, &checkout, 2, 20);
    assert_eq!(pool_count(&state, 1), Bitvector32Term::Constant(2));
    assert_eq!(pool_count(&state, 2), Bitvector32Term::Constant(1));

    state = apply_pool_transition(&state, &return_object, 1, 10);
    assert_eq!(pool_count(&state, 1), Bitvector32Term::Constant(1));
    assert_eq!(pool_count(&state, 2), Bitvector32Term::Constant(1));

    state = apply_pool_transition(&state, &return_object, 1, 11);
    assert_eq!(pool_count(&state, 1), Bitvector32Term::Constant(0));
    assert_eq!(pool_count(&state, 2), Bitvector32Term::Constant(1));
    assert!(state.observes_population_family("pool_object"));
}

#[test]
fn local_declaration_allocates_stack_object_for_address_of() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new();
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(5)),
            c_return(c_load(c_addr_of("x"))),
        ),
    );
    let final_state = CState::new().with_local("x", int32(5)).with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, int32(5)),
    );
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("local declaration/address-of should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn addressable_parameter_gets_a_fresh_callee_stack_slot() {
    let function = c_function(
        CType::Int32,
        "addressable_parameter",
        vec![c_parameter("n", CType::Int32)],
        c_seq(
            c_declare("p", CType::Int32Pointer),
            c_seq(c_assign("p", c_addr_of("n")), c_return(c_variable("n"))),
        ),
    );
    let caller_state = c_function_entry_state(&CState::new(), &function, &[c_int32_literal(3)])
        .expect("parameter entry state");
    let caller_slot = caller_state
        .locals()
        .slot("n")
        .expect("parameter slot")
        .clone();
    assert!(caller_slot.block.starts_with("local:frame:0:"));
    assert_eq!(
        caller_state.memory().cells.get(&caller_slot),
        Some(&int32(3))
    );

    let nested_state = c_function_entry_state(&caller_state, &function, &[c_int32_literal(4)])
        .expect("nested parameter entry state");
    let nested_slot = nested_state
        .locals()
        .slot("n")
        .expect("nested parameter slot")
        .clone();
    assert_ne!(caller_slot, nested_slot);
    assert_eq!(
        nested_state.memory().cells.get(&caller_slot),
        Some(&int32(3))
    );
    assert_eq!(
        nested_state.memory().cells.get(&nested_slot),
        Some(&int32(4))
    );
}

#[test]
fn symbolic_execution_stops_without_needed_overflow_fact() {
    let left = Variable(20);
    let right = Variable(21);
    let state = CState::new()
        .with_local("left", int32(Bitvector32Term::Variable(left)))
        .with_local("right", int32(Bitvector32Term::Variable(right)));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));

    assert!(prove_symbolic_c_execution(state, statement, PureFactContext::new()).is_none());
}

#[test]
fn symbolic_execution_reports_branch_facts() {
    let a = Variable(24);
    let b = Variable(25);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(int32(a_bits), int32(b_bits));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), c_max_body(), PureFactContext::new());

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
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Variable(b)),
                    state: state.clone(),
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
            Box::new(Proposition::ConditionIs(condition, false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Variable(a)),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_execution_reports_overflow_facts() {
    let left = Variable(26);
    let right = Variable(27);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(overflow.clone(), false)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(overflow.clone(), false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(left_bits),
                        Box::new(right_bits)
                    )),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(overflow.clone(), true)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(overflow, true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            }),
        )
    );
}

#[test]
fn symbolic_execution_uses_no_overflow_fact() {
    let left = Variable(22);
    let right = Variable(23);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let no_overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let assumptions = PureFactContext::new().assume_condition(no_overflow.clone(), false);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
        .expect("no-overflow fact should let symbolic add execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(no_overflow, false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(left_bits),
                        Box::new(right_bits)
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_add_uses_exact_intervals_to_rule_out_overflow() {
    let left = Variable(24);
    let right = Variable(25);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(left_bits, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(right_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(right_bits.clone(), Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(right_bits, Bitvector32Term::Constant(1)),
            false,
        );

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(left)),
                Box::new(Bitvector32Term::Variable(right)),
            ),
            Bitvector32Term::Constant(2),
        ),
        true,
    )));

    prove_symbolic_c_execution(state, statement, assumptions)
        .expect("exact reconstructed intervals should rule out signed addition overflow");
}

#[test]
fn symbolic_increment_uses_int_max_bound_to_rule_out_overflow() {
    let x = Variable(65);
    let x_bits = Bitvector32Term::Variable(x);
    let state = CState::new().with_local("x", int32(x_bits.clone()));
    let statement = c_return(c_add(c_variable("x"), c_int32_literal(1)));
    let x_lt_int_max =
        ConditionTerm::signed_less_than(x_bits.clone(), Bitvector32Term::Constant(i32::MAX as u32));
    let assumptions = PureFactContext::new().assume_condition(x_lt_int_max.clone(), true);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
        .expect("x < INT_MAX should prove x + 1 does not overflow");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(x_lt_int_max, true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(x_bits),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_increment_uses_any_strict_upper_bound_to_rule_out_overflow() {
    let x_bits = Bitvector32Term::Variable(Variable(651));
    let upper_bits = Bitvector32Term::Variable(Variable(652));
    let assumption = ConditionTerm::signed_less_than(x_bits.clone(), upper_bits);
    let assumptions = PureFactContext::new().assume_condition(assumption, true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            x_bits,
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
}

#[test]
fn signed_addition_uses_both_operand_intervals_to_rule_out_overflow() {
    let left = Bitvector32Term::Variable(Variable(653));
    let right = Bitvector32Term::Variable(Variable(654));
    let million = Bitvector32Term::Constant(1_000_000);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), left.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(left.clone(), million.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), right.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(right.clone(), million),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(left, right)),
        Some(false)
    );
}

#[test]
fn signed_addition_uses_negative_operand_intervals_to_rule_out_overflow() {
    let left = Bitvector32Term::Variable(Variable(655));
    let right = Bitvector32Term::Variable(Variable(656));
    let negative_million = Bitvector32Term::Constant((-1_000_000i32) as u32);
    let zero = Bitvector32Term::Constant(0);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(negative_million.clone(), left.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(left.clone(), zero.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(negative_million, right.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(right.clone(), zero), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(left, right)),
        Some(false)
    );
}

#[test]
fn signed_addition_ranges_nested_additions_only_when_each_level_is_safe() {
    let left = Bitvector32Term::Variable(Variable(657));
    let middle = Bitvector32Term::Variable(Variable(658));
    let right = Bitvector32Term::Variable(Variable(659));
    let upper = Bitvector32Term::Constant(700_000_000);
    let mut assumptions = PureFactContext::new();
    for term in [&left, &middle, &right] {
        assumptions = assumptions
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), term.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(term.clone(), upper.clone()),
                true,
            );
    }
    let partial = Bitvector32Term::add(left, middle);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(partial.clone(), right)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            partial,
            Bitvector32Term::Constant(800_000_000),
        )),
        None
    );
}

#[test]
fn signed_addition_matches_interval_facts_across_unchanged_snapshots() {
    let cell = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(660)), 4),
    };
    let before = CMemory::new();
    let after = before.clone().with_block("local:temporary", 4);
    let before_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before),
        Box::new(cell.clone()),
    );
    let after_load =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(cell));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), before_load.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(before_load, Bitvector32Term::Constant(1_000_000)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            after_load.clone(),
            after_load,
        )),
        Some(false)
    );
}

#[test]
fn pointer_store_through_local_address_updates_named_lvalue() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_store(c_addr_of("x"), c_int32_literal(5)),
            c_return(c_variable("x")),
        ),
    );
    let final_state = CState::new().with_local("x", int32(5)).with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, int32(5)),
    );
    let theorem =
        prove_symbolic_c_execution(CState::new(), statement.clone(), PureFactContext::new())
            .expect("pointer store through local address should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: CState::new(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn memory_load_store_are_native_theorems() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = int32(7);
    let theorem =
        prove_memory_load_after_store_same(CMemory::new(), pointer.clone(), value.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: CMemory::new().store(pointer.clone(), value.clone()),
            pointer,
            outcome: CExpressionOutcome::Value(value),
        }
    );
}

#[test]
fn store_preserves_distinct_memory_cell_frame() {
    let stored_pointer = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let loaded_pointer = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
    let theorem = prove_memory_load_after_store_other(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
    )
    .expect("store to distinct pointer should preserve loaded cell");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: CExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn missing_memory_load_is_native_undefined_behavior() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let theorem = prove_memory_load(CMemory::new(), pointer.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: CMemory::new(),
            pointer,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
        }
    );
}

#[test]
fn contract_certification_checks_every_spec_lowering_path() {
    let base = Pointer {
        block: "local:contract-path-probe".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Variable(Variable(900_001)),
    };
    let memory = CMemory::new()
        .with_block(base.block.clone(), 8)
        .store(base, int32(0));
    let state = CState::new().with_memory(memory);
    let q = SpecExpression::CExpression(c_variable("q"));
    let function = c_function(
        CType::Int32,
        "contract_path_probe",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::MemoryLoadable {
            memory: SpecMemory::Current,
            base: q.clone(),
            start: SpecExpression::Value(int32(0)),
            end: SpecExpression::Value(int32(1)),
            element_width: 4,
        }],
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(q),
                value_type: CType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        state,
        function.clone(),
        vec![c_pointer_value(queried)],
        vec![],
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let unverified = c_unverified_function_contract_claims(&function, &execution)
        .expect("the complete frontier should remain checkable");

    assert_eq!(unverified, vec![CFunctionContractClaimKey::Ensure(0)]);
}

#[test]
fn function_execution_theorem_retains_non_assumable_verification_conditions() {
    let verification_condition = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let theorem = Theorem::new(wrap_proof_facts(
        conclusion,
        &PureFactContext::new(),
        &[],
        &[ProofObligation::verification_condition(
            verification_condition.clone(),
        )],
    ));

    assert!(matches!(
        theorem.proposition(),
        Proposition::Implies(condition, _)
            if condition.as_ref() == &verification_condition
    ));
}

#[test]
fn symbolic_path_can_only_certify_its_exact_function_specification() {
    let function = c_function(
        CType::Int32,
        "exact_path",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    let execution = prove_symbolic_c_function_execution_paths(
        CState::new(),
        function.clone(),
        Vec::new(),
        PureFactContext::new(),
    );
    let false_specification = c_function_specification(
        CState::new(),
        Vec::new(),
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );

    assert!(
        prove_c_function_satisfies_specification_from_symbolic_path(
            function,
            false_specification,
            &execution.paths()[0],
        )
        .is_none()
    );
}

#[test]
fn verified_function_rule_applies_contract_without_executing_body() {
    let helper = c_function(
        CType::Int32,
        "opaque_helper",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(99)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let statement = c_seq(
        c_call_assign("result", "opaque_helper", vec![c_int32_literal(5)]),
        c_return(c_variable("result")),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement.clone(),
        PureFactContext::new(),
        environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution
        .paths()
        .first()
        .expect("opaque call should produce one path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Return { value, .. },
        ..
    } = proposition
    else {
        panic!("opaque call should produce an abstract return branch")
    };
    assert!(*value != int32(99));
    let propositions = path
        .facts()
        .iter()
        .map(|fact| fact.proposition().clone())
        .collect::<Vec<_>>();
    assert!(
        path.facts().iter().any(ExecutionPureFact::is_certified),
        "verified-call ensures should be marked as kernel-certified facts"
    );
    let assumptions = assumptions_with_propositions(&PureFactContext::new(), &propositions);
    let CValue::Int32(result) = value else {
        panic!("opaque helper should return int32")
    };
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(result.clone()),
            Box::new(Bitvector32Term::Constant(5)),
        ),
        true,
    )));

    let body_execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        PureFactContext::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
    );
    let mut proposition = body_execution.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Return { value, .. },
            ..
        } if *value == int32(99)
    ));
}

#[test]
fn verified_function_rule_coerces_null_constants_in_contract_views() {
    let p_is_null = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("p")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let returns_one = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("result")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(1)),
    };
    let helper = c_function(
        CType::Int32,
        "pointer_is_null",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_int32_literal(1)),
    )
    .with_contract(
        vec![p_is_null],
        vec![returns_one],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call_assign("result", "pointer_is_null", vec![c_int32_literal(0)]),
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque null call path");

    assert!(
        path.obligations().is_empty(),
        "typed null precondition should be discharged: {:#?}",
        path.obligations()
    );
    assert!(path.facts().iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(_, right),
                true
            ) if right.as_const() == Some(1)
        )
    }));
}

#[test]
fn verified_function_rule_does_not_publish_one_spec_alias_path() {
    let stored = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = Pointer {
        block: stored.block.clone(),
        offset: PointerOffsetTerm::Variable(Variable(900_002)),
    };
    let q = SpecExpression::CExpression(c_variable("q"));
    let reflexive_load = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(q.clone()),
            value_type: CType::Int32,
        },
        operator: CComparisonOperator::Equal,
        right: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(q),
            value_type: CType::Int32,
        },
    };
    let helper = c_function(
        CType::Int32,
        "opaque_alias_probe",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![reflexive_load],
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new().with_memory(CMemory::new().with_block("heap", 8).store(stored, int32(0))),
        c_call_assign(
            "result",
            "opaque_alias_probe",
            vec![c_pointer_value(queried)],
        ),
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque call path");

    assert!(
        path.obligations().is_empty(),
        "unexpected obligations: {:#?}",
        path.obligations()
    );
    assert!(!path.facts().iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
        )
    }));
}

#[test]
fn opaque_pointer_result_can_alias_its_argument() {
    let argument = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let helper = c_function(
        CType::Int32Pointer,
        "opaque_identity_pointer",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_variable("p")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("p")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call_assign(
            "result",
            "opaque_identity_pointer",
            vec![c_pointer_value(argument.clone())],
        ),
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque call path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Normal(state),
        ..
    } = proposition
    else {
        panic!("opaque pointer call should return normally")
    };
    let Some(CValue::Pointer(result)) = state.locals().get("result") else {
        panic!("call result should be a pointer")
    };

    assert!(result.has_symbolic_block());
    assert!(!result.blocks_proven_distinct(&argument));
    let assumptions = assumptions_with_propositions(
        &PureFactContext::new(),
        &path
            .facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::pointer_equal(result.pointer().clone(), argument),
        true,
    )));
}

#[test]
fn verified_immutable_calls_allocate_distinct_results() {
    let helper = c_function(
        CType::Int32,
        "opaque_identity",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let statement = c_seq(
        c_call_assign("first", "opaque_identity", vec![c_int32_literal(5)]),
        c_seq(
            c_call_assign("second", "opaque_identity", vec![c_int32_literal(7)]),
            c_return(c_variable("second")),
        ),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("calls should execute");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Return { value, state },
        ..
    } = proposition
    else {
        panic!("calls should return normally")
    };

    let first = state.locals().get("first").expect("first result");
    let second = state.locals().get("second").expect("second result");
    assert_ne!(first, second);
    assert_eq!(value, second);
}

#[test]
fn separate_statement_verification_calls_preserve_fresh_identity_progress() {
    let helper = c_function(
        CType::Int32,
        "opaque_identity",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let mut budget = ExecutionBudget::default();

    let (first_execution, _) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            CState::new(),
            c_call_assign("first", "opaque_identity", vec![c_int32_literal(5)]),
            PureFactContext::new(),
            environment.clone(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let first_next = budget.next_kernel_variable();
    let first_path = first_execution.paths().first().expect("first call path");
    let mut first_proposition = first_path.theorem().proposition();
    while let Proposition::Implies(_, body) = first_proposition {
        first_proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Normal(first_state),
        ..
    } = first_proposition
    else {
        panic!("first call should return normally")
    };
    let first_value = first_state.locals().get("first").expect("first result");

    let (second_execution, _) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            first_state.clone(),
            c_call_assign("second", "opaque_identity", vec![c_int32_literal(7)]),
            PureFactContext::new(),
            environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let second_path = second_execution.paths().first().expect("second call path");
    let mut second_proposition = second_path.theorem().proposition();
    while let Proposition::Implies(_, body) = second_proposition {
        second_proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Normal(second_state),
        ..
    } = second_proposition
    else {
        panic!("second call should return normally")
    };
    let second_value = second_state.locals().get("second").expect("second result");

    assert!(first_next > 0);
    assert!(budget.next_kernel_variable() > first_next);
    assert_ne!(first_value, second_value);
}

#[test]
fn verified_function_rule_requires_every_contract_claim_certificate() {
    let function = c_function(
        CType::Int32,
        "two_claims",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
        ],
        Vec::new(),
        vec![
            CFunctionContractClaim::ensure_proposition(0, 0),
            CFunctionContractClaim::ensure_proposition(1, 1),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    let impostor = c_function(
        CType::Int32,
        "two_claims",
        Vec::new(),
        c_return(c_int32_literal(1)),
    );
    let impostor_execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        impostor,
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Ensure(0),
            &impostor_execution,
        )
        .is_none()
    );

    let first = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::Ensure(0),
        &execution,
    )
    .expect("first claim should certify");

    assert!(c_verified_function_rule(function.clone(), std::slice::from_ref(&first)).is_none());

    let second = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::Ensure(1),
        &execution,
    )
    .expect("second claim should certify");
    assert!(c_verified_function_rule(function, &[first, second]).is_some());
}

#[test]
fn verified_function_rule_rejects_unclaimed_contract_obligations() {
    let function = c_function(
        CType::Int32,
        "unclaimed_ensure",
        Vec::new(),
        c_return(c_int32_literal(1)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(
        c_unverified_function_contract_claims(&function, &execution)
            .expect("the complete frontier should remain diagnostic"),
        vec![CFunctionContractClaimKey::Ensure(0)]
    );
    let body_safety = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::BodySafety,
        &execution,
    )
    .expect("the body-safety claim itself should still certify");
    assert!(c_verified_function_rule(function, &[body_safety]).is_none());
}

#[test]
fn declared_exceptional_path_certifies_its_payload_postcondition() {
    let normal_false = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    };
    let exceptional_payload = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable(C_EXCEPTIONAL_RESULT_NAME)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    };
    let function = c_function(
        CType::Int32,
        "certified_throw",
        Vec::new(),
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![exceptional_payload])
    .with_contract(
        Vec::new(),
        vec![normal_false],
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
            CFunctionContractClaim::exceptional_ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    let throw_outcome = CFunctionOutcome::Throw {
        value: int32(7),
        state: CState::new(),
    };
    let goals = c_function_exceptional_ensure_goals(
        &function,
        0,
        &CState::new(),
        &[],
        &throw_outcome,
        &PureFactContext::new(),
    )
    .expect("the exceptional payload should lower at the throw boundary");
    assert_eq!(goals.len(), 1);
    assert!(
        matches!(
            &goals[0].0,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        ),
        "unexpected exceptional goal: {:?}",
        goals[0].0
    );

    assert_eq!(
        c_unverified_function_contract_claims(&function, &execution)
            .expect("a declared exceptional path is a safe certification path"),
        Vec::<CFunctionContractClaimKey>::new(),
    );
    let proofs = c_verified_function_contract_claims(&function, &execution)
        .expect("the payload postcondition should certify");
    assert_eq!(proofs.len(), 3);
    assert!(c_verified_function_rule(function, &proofs).is_some());
}

#[test]
fn verified_exceptional_rule_produces_isolated_outcome_paths() {
    let normal_ensure = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("result")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(5)),
    };
    let exceptional_ensure = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable(C_EXCEPTIONAL_RESULT_NAME)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    };
    let function = c_function(
        CType::Int32,
        "modular_maybe_throw",
        vec![c_parameter("flag", CType::Int32)],
        c_if(
            c_equal(c_variable("flag"), c_int32_literal(0)),
            c_return(c_int32_literal(5)),
            CStatement::Throw(c_int32_literal(7)),
        ),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![exceptional_ensure])
    .with_contract(
        Vec::new(),
        vec![normal_ensure],
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
            CFunctionContractClaim::exceptional_ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(700_001)),
        ))],
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let proofs = c_verified_function_contract_claims(&function, &execution)
        .expect("both outcome families should certify");
    let rule = c_verified_function_rule(function.clone(), &proofs)
        .expect("a certified exceptional direct rule should form");
    let environment = CExecutionEnvironment::new()
        .with_function(function)
        .with_verified_function_rule(rule);
    let call_statement = c_call_assign(
        "call_result",
        "modular_maybe_throw",
        vec![c_int32_literal(0)],
    );
    let call_state = CState::new().with_local("after", int32(0));
    let call_root = crate::kernel::proof::ProofFacts::from_ordered(&[]);
    let call_split = crate::kernel::proof::CheckedCallOutcomeSplit::check(
        call_state.clone(),
        call_statement.clone(),
        &call_root,
        &environment,
        0,
        0,
    )
    .expect("the direct call must have exactly two checked outcome successors");
    let call_paths = prove_symbolic_c_execution_paths_with_environment(
        call_state.clone(),
        call_statement.clone(),
        PureFactContext::new(),
        environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let mut normal = None;
    let mut exceptional = None;
    for path in call_paths.paths() {
        match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
            Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Normal(_),
                ..
            } => normal = Some(path),
            Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Throw { .. },
                ..
            } => exceptional = Some(path),
            other => panic!("unexpected call successor: {other:?}"),
        }
    }
    let normal = normal.expect("normal successor");
    let exceptional = exceptional.expect("exceptional successor");
    assert!(call_split.validates(
        &call_state,
        &call_statement,
        &call_root,
        normal.theorem(),
        exceptional.theorem(),
    ));
    assert!(!call_split.validates(
        &call_state,
        &call_statement,
        &call_root,
        normal.theorem(),
        normal.theorem(),
    ));
    assert!(!call_split.validates(
        &call_state,
        &c_return(c_variable("call_result")),
        &call_root,
        normal.theorem(),
        exceptional.theorem(),
    ));
    let caller = c_function(CType::Int32, "caller", Vec::new(), call_statement.clone())
        .with_int32_exceptional_outcome();
    let mut parent = crate::kernel::proof::ExecutionProofCore::at_entry(
        call_state.clone(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    parent.frontier.position = crate::kernel::proof::FrontierPosition::StatementEntry {
        remaining: std::sync::Arc::new(call_statement.clone()),
    };
    let no_loans = crate::kernel::loans::empty_checked_loan_evidence_sequence();
    let branch = call_split
        .record_branches(
            &parent,
            &caller,
            &[],
            &call_state,
            &call_statement,
            &call_root,
            crate::kernel::proof::CallOutcomeArmEvidence {
                theorem: normal.theorem(),
                context: &PureFactContext::new(),
                execution_facts: &normal.execution_facts(),
                obligations: normal.obligations(),
                loan_evidence: &no_loans,
            },
            crate::kernel::proof::CallOutcomeArmEvidence {
                theorem: exceptional.theorem(),
                context: &PureFactContext::new(),
                execution_facts: &exceptional.execution_facts(),
                obligations: exceptional.obligations(),
                loan_evidence: &no_loans,
            },
        )
        .expect("each named outcome must advance its own checked proof trace");
    assert!(!branch.returned.evidence_completed);
    assert!(branch.threw.evidence_completed);
    assert!(
        branch
            .returned
            .evidence_state
            .as_ref()
            .unwrap()
            .locals()
            .contains_name("call_result")
    );
    assert!(
        !branch
            .threw
            .evidence_state
            .as_ref()
            .unwrap()
            .locals()
            .contains_name("call_result")
    );
    assert_eq!(branch.returned.execution_evidence.len(), 1);
    assert_eq!(branch.threw.execution_evidence.len(), 1);
    assert!(
        call_split
            .record_branches(
                &parent,
                &caller,
                &[],
                &call_state,
                &call_statement,
                &call_root,
                crate::kernel::proof::CallOutcomeArmEvidence {
                    theorem: exceptional.theorem(),
                    context: &PureFactContext::new(),
                    execution_facts: &exceptional.execution_facts(),
                    obligations: exceptional.obligations(),
                    loan_evidence: &no_loans,
                },
                crate::kernel::proof::CallOutcomeArmEvidence {
                    theorem: normal.theorem(),
                    context: &PureFactContext::new(),
                    execution_facts: &normal.execution_facts(),
                    obligations: normal.obligations(),
                    loan_evidence: &no_loans,
                },
            )
            .is_err()
    );
    let statement = c_seq(
        call_statement,
        c_seq(
            c_assign("after", c_int32_literal(1)),
            c_return(c_variable("call_result")),
        ),
    );
    let modular = prove_symbolic_c_execution_paths_with_environment(
        call_state,
        statement,
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );

    assert_eq!(modular.paths().len(), 2);
    let mut saw_return = false;
    let mut saw_throw = false;
    for path in modular.paths() {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        let assumptions = assumptions_with_propositions(
            &PureFactContext::new(),
            &path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>(),
        );
        match proposition {
            Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Return { value, state },
                ..
            } => {
                saw_return = true;
                assert_eq!(state.locals().get("after"), Some(&int32(1)));
                let CValue::Int32(value) = value else {
                    panic!("normal result should be int32")
                };
                assert!(assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(value.clone()),
                        Box::new(Bitvector32Term::Constant(5)),
                    ),
                    true,
                )));
                assert!(!assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(value.clone()),
                        Box::new(Bitvector32Term::Constant(7)),
                    ),
                    true,
                )));
            }
            Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Throw { value, state },
                ..
            } => {
                saw_throw = true;
                assert_eq!(state.locals().get("after"), Some(&int32(0)));
                assert!(state.locals().get("call_result").is_none());
                let CValue::Int32(value) = value else {
                    panic!("exceptional payload should be int32")
                };
                assert!(assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(value.clone()),
                        Box::new(Bitvector32Term::Constant(7)),
                    ),
                    true,
                )));
                assert!(!assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(value.clone()),
                        Box::new(Bitvector32Term::Constant(5)),
                    ),
                    true,
                )));
            }
            other => panic!("unexpected modular outcome: {other:?}"),
        }
    }
    assert!(saw_return && saw_throw);
}

#[test]
fn verified_exceptional_call_enters_int32_handler_with_only_exceptional_claims() {
    let function = c_function(
        CType::Int32,
        "throwing_helper",
        Vec::new(),
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable(C_EXCEPTIONAL_RESULT_NAME)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    }])
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(99)),
        }],
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
            CFunctionContractClaim::exceptional_ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let proofs = c_verified_function_contract_claims(&function, &execution)
        .expect("the helper's exceptional claim should certify");
    let rule = c_verified_function_rule(function.clone(), &proofs)
        .expect("the fully checked helper should form a direct rule");
    let statement = c_try_catch_int32(
        c_seq(
            c_call("throwing_helper", Vec::new()),
            c_return(c_int32_literal(99)),
        ),
        "caught",
        c_return(c_variable("caught")),
    );
    let paths = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        PureFactContext::new(),
        CExecutionEnvironment::new()
            .with_function(function)
            .with_verified_function_rule(rule),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(paths.paths().len(), 2);
    let mut saw_normal = false;
    let mut saw_caught = false;
    for path in paths.paths() {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        let Proposition::CStatementVerifies {
            outcome: CStatementOutcome::Return { value, state },
            ..
        } = proposition
        else {
            panic!("both modular outcomes should return: {proposition:?}");
        };
        if state.locals().get("caught").is_none() {
            saw_normal = true;
            assert_eq!(value, &int32(99));
            continue;
        }
        saw_caught = true;
        assert_eq!(state.locals().get("caught"), Some(value));
        let CValue::Int32(value) = value else {
            panic!("caught payload should be int32");
        };
        let assumptions = assumptions_with_propositions(
            &PureFactContext::new(),
            &path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>(),
        );
        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(7)),
            ),
            true,
        )));
        assert!(!assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(99)),
            ),
            true,
        )));
    }
    assert!(saw_normal && saw_caught);
}

#[test]
fn declared_exceptional_channel_does_not_vanish_without_an_exceptional_ensure() {
    let function = c_function(
        CType::Int32,
        "unconstrained_exceptional_channel",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_int32_exceptional_outcome()
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let certification = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let proofs = c_verified_function_contract_claims(&function, &certification)
        .expect("the declared channel needs no invented exceptional guarantee");
    let rule = c_verified_function_rule(function.clone(), &proofs)
        .expect("the body-certified direct rule should form");
    let modular = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call("unconstrained_exceptional_channel", Vec::new()),
        PureFactContext::new(),
        CExecutionEnvironment::new()
            .with_function(function)
            .with_verified_function_rule(rule),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );

    assert_eq!(modular.paths().len(), 2);
    assert!(modular.paths().iter().any(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(
            proposition,
            Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Throw { .. },
                ..
            }
        )
    }));
}

#[test]
fn exceptional_direct_rule_boundary_excludes_mutable_effects() {
    let function = c_function(
        CType::Int32,
        "effectful_throw",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        )],
        vec![CFunctionContractClaim::effect(0)],
        true,
    );

    assert!(!function.verified_direct_contract_supported());
    assert!(CFunctionContract::new("EffectfulThrow", function).is_none());
}

#[test]
fn exceptional_postconditions_apply_only_to_throw_outcomes() {
    let exceptional_false = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    };
    let function = c_function(
        CType::Int32,
        "ordinary_return_with_exceptional_family",
        Vec::new(),
        c_return(c_int32_literal(4)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![exceptional_false])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::exceptional_ensure_proposition(0, 0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(
        c_unverified_function_contract_claims(&function, &execution)
            .expect("the complete return path should remain checkable"),
        Vec::<CFunctionContractClaimKey>::new(),
    );
}

#[test]
fn false_or_missing_exceptional_postconditions_do_not_certify() {
    let wrong_payload = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable(C_EXCEPTIONAL_RESULT_NAME)),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(8)),
    };
    let with_false_claim = c_function(
        CType::Int32,
        "wrong_exceptional_payload",
        Vec::new(),
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![wrong_payload.clone()])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::exceptional_ensure_proposition(0, 0)],
        true,
    );
    let false_execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        with_false_claim.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(
        c_unverified_function_contract_claims(&with_false_claim, &false_execution)
            .expect("the false exceptional claim should be diagnosed"),
        vec![CFunctionContractClaimKey::ExceptionalEnsure(0)],
    );

    let without_claim = c_function(
        CType::Int32,
        "missing_exceptional_claim",
        Vec::new(),
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![wrong_payload])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let missing_execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        without_claim.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(
        c_unverified_function_contract_claims(&without_claim, &missing_execution)
            .expect("the omitted exceptional claim should be diagnosed"),
        vec![CFunctionContractClaimKey::ExceptionalEnsure(0)],
    );
    let body_safety = c_verified_function_contract_claim(
        &without_claim,
        CFunctionContractClaimKey::BodySafety,
        &missing_execution,
    )
    .expect("the safe body remains independently certified");
    assert!(c_verified_function_rule(without_claim, &[body_safety]).is_none());
}

#[test]
fn exceptional_direct_rule_boundary_excludes_resource_transitions() {
    let function = c_function(
        CType::Int32,
        "resourceful_throw",
        Vec::new(),
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_resource_summary(
        vec![CResourceSpec::token(
            CResourceAccessMode::View,
            "borrowed".into(),
            vec![],
            vec![],
        )],
        Vec::new(),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );

    assert!(!function.verified_direct_contract_supported());
    assert!(CFunctionContract::new("ResourcefulThrow", function).is_none());
}

#[test]
fn exceptional_postconditions_observe_the_throw_state() {
    let pointer = Pointer {
        block: "exceptional-output".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p = SpecExpression::CExpression(c_variable("p"));
    let loadable = SpecProposition::MemoryLoadable {
        memory: SpecMemory::Current,
        base: p.clone(),
        start: SpecExpression::Value(int32(0)),
        end: SpecExpression::Value(int32(1)),
        element_width: 4,
    };
    let claims_ten = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(p),
            value_type: CType::Int32,
        },
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(10)),
    };
    let function = c_function(
        CType::Int32,
        "wrong_exceptional_state",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::Throw(c_int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![claims_ten])
    .with_contract(
        vec![loadable],
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::exceptional_ensure_proposition(0, 0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new().with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(9)),
        ),
        function.clone(),
        vec![c_pointer_value(pointer)],
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(
        c_unverified_function_contract_claims(&function, &execution)
            .expect("the exceptional exit state should be available to claims"),
        vec![CFunctionContractClaimKey::ExceptionalEnsure(0)],
    );
}

#[test]
fn contract_certification_does_not_accept_injected_opaque_predicate_facts() {
    let predicate = SpecProposition::Predicate {
        name: "positive".to_string(),
        arguments: vec![SpecPredicateArgument::Value(SpecExpression::CExpression(
            c_variable("result"),
        ))],
    };
    let positive_body = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("result")),
        operator: CComparisonOperator::GreaterEqual,
        right: SpecExpression::Value(int32(1)),
    };
    let function = c_function(
        CType::Int32,
        "injected_predicate",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![positive_body.clone()],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    )
    .with_predicate_unfoldings(vec![CPredicateUnfolding::new(predicate, positive_body)]);
    let injected = Proposition::ForAll {
        var: Variable(991_001),
        sort: Sort::CInt32,
        body: Box::new(Proposition::Predicate {
            name: "positive".to_string(),
            arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(Variable(
                991_001,
            )))],
        }),
    };
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        vec![injected],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none(),
        "caller-supplied quantified predicate facts must not certify a false ensure"
    );
}

#[test]
fn contract_effect_claim_rejects_an_undecidable_guard() {
    let base = Pointer {
        block: PointerBlock::Concrete("heap:guarded-effect".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let flag = Variable(991_002);
    let function = c_function(
        CType::Int32,
        "undecidable_guarded_effect",
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("flag", CType::Int32),
        ],
        c_seq(
            c_store(
                c_index(c_variable("p"), c_int32_literal(0)),
                c_int32_literal(1),
            ),
            c_return(c_int32_literal(1)),
        ),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![
            CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1))
                .with_guard(SpecProposition::Comparison {
                    left: SpecExpression::CExpression(c_variable("flag")),
                    operator: CComparisonOperator::NotEqual,
                    right: SpecExpression::Value(int32(0)),
                }),
        ],
        vec![CFunctionContractClaim::effect(0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new().with_memory(CMemory::new().with_block(base.block.clone(), 4)),
        function.clone(),
        vec![
            c_pointer_value(base),
            CExpression::Value(CValue::Int32(Bitvector32Term::Variable(flag))),
        ],
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Effect(0),
            &execution,
        )
        .is_none(),
        "a guarded frame must be case-split or proven true before certification"
    );
}

#[test]
fn contract_effect_claim_rejects_interior_entry_live_heap_pointer_as_fresh() {
    let allocation_base = Pointer {
        block: PointerBlock::Heap(991_003),
        offset: PointerOffsetTerm::Constant(0),
    };
    let interior = Pointer {
        block: allocation_base.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let function = c_function(
        CType::Int32,
        "interior_entry_live_effect",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(
                c_pointer_offset_bytes(c_variable("p"), 8),
                c_int32_literal(1),
            ),
            c_return(c_int32_literal(0)),
        ),
    )
    .with_resource_summary(
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            c_pointer_offset_bytes(c_variable("p"), 8),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        Vec::new(),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        )],
        vec![CFunctionContractClaim::effect(0)],
        true,
    );
    let caller_state = CState::new()
        .with_memory(
            CMemory::new()
                .with_heap_allocation_claim(allocation_base.clone(), Bitvector32Term::Constant(16))
                .expect("the entry allocation should be live"),
        )
        .with_resource_context(own_memory_context(interior, 0, 1));
    let execution = certify_contract_with_kernel_artifacts(
        caller_state,
        function.clone(),
        vec![c_pointer_value(allocation_base)],
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Effect(0),
            &execution,
        )
        .is_none(),
        "an interior pointer into an entry-live block must not bypass the mutable frame"
    );
}

#[test]
fn contract_certification_reuses_a_matching_kernel_checked_execution() {
    let function = c_function(
        CType::Int32,
        "checked_once",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::Value(int32(0)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let state = CState::new();
    let environment = CExecutionEnvironment::new();
    let semantics = CExecutionSemantics::EXECUTE_BODIES;
    let mode = CFunctionContractExecutionMode::VerifyLoops;
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let checked = prove_checked_c_function_execution_with_environment(
        state.clone(),
        function.clone(),
        Vec::new(),
        PureFactContext::new(),
        environment.clone(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );

    let execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function.clone(),
        Vec::new(),
        Vec::new(),
        environment,
        semantics,
        mode,
        &[checked],
    );

    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "matching checked authority should avoid a second function-body execution"
    );
    assert!(c_verified_function_contract_claims(&function, &execution).is_some());

    let extra_assumption = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(919_000)),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let unchecked_boundary = prove_checked_c_function_execution_with_environment(
        CState::new(),
        function.clone(),
        Vec::new(),
        extra_assumption,
        CExecutionEnvironment::new(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );
    let fallback = prove_c_function_contract_execution_paths_with_checked_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        semantics,
        mode,
        &[unchecked_boundary],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "an artifact with an unproved entry assumption must not be reused, and certification must not execute the body instead"
    );
    assert_eq!(fallback.path_count(), 0);
    assert!(
        fallback
            .reuse_diagnostic()
            .is_some_and(|detail| detail.contains("a condition fact")),
        "{:?}",
        fallback.reuse_diagnostic()
    );
    assert!(c_verified_function_contract_claims(&function, &fallback).is_none());
}

#[test]
fn checked_view_certificate_initializes_a_pristine_loan_authority() {
    let base = Pointer {
        block: PointerBlock::Concrete("checked:initial-view".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let function = c_function(
        CType::Int32,
        "checked_initial_view",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        Vec::new(),
    )
    .with_contract(Vec::new(), Vec::new(), Vec::new(), Vec::new(), true);
    let state = CState::new()
        .with_memory(
            CMemory::new()
                .with_block(base.block.clone(), 4)
                .store(base.clone(), int32(7)),
        )
        .with_resource_context(own_memory_context(base.clone(), 0, 1));
    let environment = CExecutionEnvironment::new();
    let arguments = vec![c_pointer_value(base)];
    let checked = prove_checked_c_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
        environment.clone(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(checked.paths().len(), 1);
    let execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function,
        arguments,
        Vec::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
        &[checked],
    );
    assert_eq!(execution.path_count(), 1);
}

#[test]
fn contract_certification_reuses_complementary_checked_entry_partitions() {
    let input = Bitvector32Term::Variable(Variable(919_100));
    let branch = ConditionTerm::signed_less_than(input.clone(), Bitvector32Term::Constant(0));
    let function = c_function(
        CType::Int32,
        "checked_partition",
        vec![c_parameter("x", CType::Int32)],
        c_if(
            c_less_than(c_variable("x"), c_int32_literal(0)),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(2)),
        ),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::NotEqual,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let state = CState::new();
    let arguments = vec![CExpression::Value(int32(input))];
    let environment = CExecutionEnvironment::new();
    let semantics = CExecutionSemantics::EXECUTE_BODIES;
    let mode = CFunctionContractExecutionMode::VerifyLoops;
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let checked_true = prove_checked_c_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new().assume_condition(branch.clone(), true),
        environment.clone(),
        semantics,
        mode,
    );
    let checked_false = prove_checked_c_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new().assume_condition(branch, false),
        environment.clone(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        2
    );

    let execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Vec::new(),
        environment.clone(),
        semantics,
        mode,
        &[checked_true.clone(), checked_false],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "two complete opposite entry cases should compose without executing the body again"
    );
    assert_eq!(execution.path_count(), 2);
    assert!(c_verified_function_contract_claims(&function, &execution).is_some());

    let fallback = prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        environment,
        semantics,
        mode,
        &[checked_true],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "one side of an entry partition is not a complete contract frontier, and certification must not execute the body instead"
    );
    assert_eq!(fallback.path_count(), 0);
    assert!(fallback.reuse_diagnostic().is_some());
    assert!(c_verified_function_contract_claims(&function, &fallback).is_none());
}

#[test]
fn contract_certification_reuses_definitionally_equal_entry_resources() {
    let unit = CResourceFact::own_token("entry_unit".to_string(), vec![int32(7)]);
    let proof_resources = ResourceContext::new()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit.clone());
    let contract_resources = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit], &PureFactContext::new())
        .expect("the contract representation should normalize the two units");
    assert_ne!(proof_resources, contract_resources);
    assert!(resource_contexts_definitionally_equal_with_definitions(
        &[],
        &CMemory::new(),
        &proof_resources,
        &CMemory::new(),
        &contract_resources,
        &PureFactContext::new(),
    ));

    let function = c_function(
        CType::Int32,
        "checked_resource_entry",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let proof_state = CState::new().with_resource_context(proof_resources.clone());
    let contract_state = CState::new().with_resource_context(contract_resources.clone());
    let environment = CExecutionEnvironment::new();
    let semantics = CExecutionSemantics::EXECUTE_BODIES;
    let mode = CFunctionContractExecutionMode::VerifyLoops;
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let checked = prove_checked_c_function_execution_with_environment(
        proof_state,
        function.clone(),
        Vec::new(),
        PureFactContext::new(),
        environment.clone(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );

    let execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        contract_state,
        function.clone(),
        Vec::new(),
        Vec::new(),
        environment,
        semantics,
        mode,
        &[checked],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "definitionally equal ghost entry resources should not rerun the C body"
    );
    assert!(c_verified_function_contract_claims(&function, &execution).is_some());

    let recursive_function = function.clone().with_composite_resource_definitions(vec![
        CCompositeResourceDefinition::new(
            "recursive_entry",
            Vec::new(),
            None,
            true,
            Vec::new(),
            Vec::new(),
        ),
    ]);
    let recursive_checked = prove_checked_c_function_execution_with_environment(
        CState::new().with_resource_context(proof_resources),
        recursive_function.clone(),
        Vec::new(),
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );
    let recursive_execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        CState::new().with_resource_context(contract_resources),
        recursive_function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        semantics,
        mode,
        &[recursive_checked],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "recursive resource representations are not rebased without a kernel-issued entry origin, and certification must not execute the body instead"
    );
    assert_eq!(recursive_execution.path_count(), 0);
    assert!(
        recursive_execution
            .reuse_diagnostic()
            .is_some_and(|detail| detail.contains("different entry state")),
        "{:?}",
        recursive_execution.reuse_diagnostic()
    );
    assert!(
        c_verified_function_contract_claims(&recursive_function, &recursive_execution).is_none()
    );
}

#[test]
fn contract_claim_rejects_same_source_function_with_a_different_contract() {
    let body = c_return(c_int32_literal(0));
    let uncontracted = c_function(CType::Int32, "contract_identity", Vec::new(), body.clone());
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        uncontracted,
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let stronger = c_function(CType::Int32, "contract_identity", Vec::new(), body).with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );

    assert!(
        c_verified_function_contract_claim(
            &stronger,
            CFunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none()
    );
}

#[test]
fn body_safety_claim_rejects_an_unproved_execution_condition() {
    let function = c_function(
        CType::Int32,
        "unsafe_body",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let state = CState::new();
    let obligation = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    ));
    let proposition = Proposition::CFunctionExecutes {
        state: state.clone(),
        function: function.clone(),
        arguments: Vec::new(),
        outcome: CFunctionOutcome::Return {
            value: int32(0),
            state,
        },
    };
    let path = SymbolicCExecutionPath {
        completion_origin: None,
        assumptions: PureFactContext::new(),
        facts: Vec::new(),
        effect_facts: Vec::new(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &PureFactContext::new(),
            &[],
            &[obligation],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let execution = CFunctionContractExecution {
        cases: vec![vec![CContractPathSet {
            paths: vec![path],
            checked_resource_claims: vec![Vec::new()],
            checked_resource_transitions: vec![false],
            deferred_contract_exits: vec![false],
            deferred_contract_exit_errors: vec![None],
            checked_returned_resources: vec![ResourceContext::new()],
            completion_origin_state: None,
        }]],
        reuse_diagnostic: None,
        reuse_unauthorized_premise: None,
        checked_call_events: Default::default(),
        loop_semantics: CLoopSemantics::Verify,
    };

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::BodySafety,
            &execution,
        )
        .is_none()
    );
}

/// A claim is judged over each path set of a case in turn: a set whose
/// paths fail it does not decide the claim while another set certifies it,
/// every case needs a certifying set, and a case with no set certifies
/// nothing.
#[test]
fn contract_claims_are_judged_over_each_path_set_of_a_case() {
    let function = c_function(
        CType::Int32,
        "alternatives",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let state = CState::new();
    let proposition = Proposition::CFunctionExecutes {
        state: state.clone(),
        function: function.clone(),
        arguments: Vec::new(),
        outcome: CFunctionOutcome::Return {
            value: int32(0),
            state,
        },
    };
    let unproved = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Variable(Variable(91_200)),
            Bitvector32Term::Constant(8),
        ),
        true,
    ));
    let failing = SymbolicCExecutionPath {
        completion_origin: None,
        assumptions: PureFactContext::new(),
        facts: Vec::new(),
        effect_facts: Vec::new(),
        obligations: vec![unproved.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition.clone(),
            &PureFactContext::new(),
            &[],
            &[unproved],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let clean = SymbolicCExecutionPath {
        completion_origin: None,
        assumptions: PureFactContext::new(),
        facts: Vec::new(),
        effect_facts: Vec::new(),
        obligations: Vec::new(),
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &PureFactContext::new(),
            &[],
            &[],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let set = |path: &SymbolicCExecutionPath| CContractPathSet {
        paths: vec![path.clone()],
        checked_resource_claims: vec![Vec::new()],
        checked_resource_transitions: vec![false],
        deferred_contract_exits: vec![false],
        deferred_contract_exit_errors: vec![None],
        checked_returned_resources: vec![ResourceContext::new()],
        completion_origin_state: None,
    };
    let certified = |cases: Vec<Vec<CContractPathSet>>| {
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::BodySafety,
            &CFunctionContractExecution {
                cases,
                reuse_diagnostic: None,
                reuse_unauthorized_premise: None,
                checked_call_events: Default::default(),
                loop_semantics: CLoopSemantics::Verify,
            },
        )
        .is_some()
    };
    assert!(
        certified(vec![vec![set(&failing), set(&clean)]]),
        "a later path set certifies the claim the first fails"
    );
    assert!(certified(vec![vec![set(&clean), set(&failing)]]));
    assert!(!certified(vec![vec![set(&failing)]]));
    assert!(
        !certified(vec![vec![set(&clean)], vec![set(&failing)]]),
        "every case needs a certifying path set"
    );
    assert!(
        !certified(vec![vec![set(&clean)], Vec::new()]),
        "a case with no path set certifies nothing"
    );
}

#[test]
fn body_safety_claim_uses_path_facts_for_verification_conditions() {
    let function = c_function(
        CType::Int32,
        "guarded_body",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let state = CState::new();
    let guard = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Variable(Variable(91_000)),
            Bitvector32Term::Constant(8),
        ),
        true,
    );
    let fact = ExecutionPureFact::new(guard.clone());
    let obligation = ProofObligation::verification_condition(guard);
    let proposition = Proposition::CFunctionExecutes {
        state: state.clone(),
        function: function.clone(),
        arguments: Vec::new(),
        outcome: CFunctionOutcome::Return {
            value: int32(0),
            state,
        },
    };
    let path = SymbolicCExecutionPath {
        completion_origin: None,
        assumptions: PureFactContext::new(),
        facts: vec![fact.clone()],
        effect_facts: Vec::new(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &PureFactContext::new(),
            &[fact],
            &[obligation],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let execution = CFunctionContractExecution {
        cases: vec![vec![CContractPathSet {
            paths: vec![path],
            checked_resource_claims: vec![Vec::new()],
            checked_resource_transitions: vec![false],
            deferred_contract_exits: vec![false],
            deferred_contract_exit_errors: vec![None],
            checked_returned_resources: vec![ResourceContext::new()],
            completion_origin_state: None,
        }]],
        reuse_diagnostic: None,
        reuse_unauthorized_premise: None,
        checked_call_events: Default::default(),
        loop_semantics: CLoopSemantics::Verify,
    };

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::BodySafety,
            &execution,
        )
        .is_some(),
        "a path guard established by symbolic execution must discharge a guarded safety condition"
    );
}

#[test]
fn effect_endpoint_comparison_ignores_function_local_cells() {
    let local = Pointer {
        block: "local:temporary".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new().with_block("local:temporary", 4);
    let after = before.clone().store(local, int32(7));

    assert!(crate::kernel::api::c_effect_memories_definitionally_equal(
        &before,
        &after,
        &PureFactContext::new(),
    ));

    let external = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let changed_external = after.store(external, int32(9));
    assert!(!crate::kernel::api::c_effect_memories_definitionally_equal(
        &before,
        &changed_external,
        &PureFactContext::new(),
    ));
}

#[test]
fn effect_endpoint_allows_resource_allocation_bookkeeping() {
    let allocation = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(64),
    };
    let before = CMemory::new();
    let after = before
        .clone()
        .with_heap_allocation_claim(allocation, Bitvector32Term::Constant(16))
        .expect("a fresh symbolic allocation claim should be registerable");

    assert!(
        crate::kernel::api::c_effect_memory_advances_over_internal_heap_state(
            &before,
            &after,
            &before,
            &PureFactContext::new(),
        )
    );
}

#[test]
fn bool_range_fact_requires_a_structurally_normalized_bool() {
    let variable = Bitvector32Term::Variable(Variable(1));
    let normalized = bool_value(variable.clone());
    let CValue::Bool(term) = &normalized else {
        panic!("bool_value builds a `_Bool` value");
    };
    let equals = |constant| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(term.clone()),
                Box::new(Bitvector32Term::Constant(constant)),
            ),
            true,
        )
    };
    assert_eq!(
        c_bool_range_fact(&normalized),
        Some(Proposition::Or(Box::new(equals(0)), Box::new(equals(1))))
    );
    // A bare term, an arm outside `{0, 1}`, a constant, and a non-`_Bool`
    // value state nothing the term's shape does not prove.
    assert_eq!(c_bool_range_fact(&CValue::Bool(variable.clone())), None);
    assert_eq!(
        c_bool_range_fact(&CValue::Bool(Bitvector32Term::if_then_else(
            ConditionTerm::Variable(Variable(2)),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        ))),
        None
    );
    assert_eq!(c_bool_range_fact(&bool_value(5)), None);
    assert_eq!(c_bool_range_fact(&int32(variable)), None);
}

#[test]
fn contract_claim_rejects_caller_supplied_false_entry_fact() {
    let function = c_function(
        CType::Int32,
        "false_postcondition",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        CState::new(),
        function.clone(),
        Vec::new(),
        vec![Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none()
    );
}

#[test]
fn decision_memo_distinguishes_equal_shaped_fact_sets_by_content() {
    // The decide memo is keyed by fact-set content identity. Two fact sets
    // that answer the same condition differently must never share a memo
    // entry, no matter how the objects are allocated or reused, and asking
    // one right after the other (in both orders) must not leak either
    // answer to the other.
    let x = Bitvector32Term::Variable(Variable(1));
    let below = ConditionTerm::signed_less_than(x.clone(), Bitvector32Term::Constant(10));
    let assumes_true = PureFactContext::new().assume_condition(below.clone(), true);
    let assumes_false = PureFactContext::new().assume_condition(below.clone(), false);

    for _ in 0..2 {
        assert_eq!(assumes_true.decide(&below), Some(true));
        assert_eq!(assumes_false.decide(&below), Some(false));
        assert_eq!(assumes_true.decide(&below), Some(true));
    }
}

#[test]
fn assumptions_clones_share_facts_and_cache_keys_are_content_stable() {
    let condition = ConditionTerm::signed_less_than(
        Bitvector32Term::Variable(Variable(9)),
        Bitvector32Term::Constant(10),
    );
    let first = PureFactContext::new().assume_condition(condition.clone(), true);
    let clone = first.clone();
    let idempotent = clone.clone().assume_condition(condition.clone(), true);
    let rebuilt = PureFactContext::new().assume_condition(condition.clone(), true);
    let changed = PureFactContext::new().assume_condition(condition, false);

    assert!(first.shares_fact_storage_with(&clone));
    assert!(clone.shares_fact_storage_with(&idempotent));
    assert_eq!(first.memo_fingerprint(), rebuilt.memo_fingerprint());
    assert_ne!(first.memo_fingerprint(), changed.memo_fingerprint());
}

/// `int32 early() { if (0 < 1) { return 0; } return 1; }` with one retained
/// trace: a single statement theorem for the `if` whose outcome is
/// `outcome`. The condition is never evaluated by the proof object, so the
/// theorem's shape is what these tests exercise.
fn early_return_inputs(
    outcome: CStatementOutcome,
) -> (
    CFunctionExecutionCandidates,
    CFunction,
    crate::kernel::proof::PersistentSequence<crate::kernel::proof::CheckedExecutionEvent>,
) {
    let branch = c_if(
        c_less_than(c_int32_literal(0), c_int32_literal(1)),
        c_return(c_int32_literal(0)),
        CStatement::Skip,
    );
    let function = c_function(
        CType::Int32,
        "early",
        Vec::new(),
        c_seq(branch.clone(), c_return(c_int32_literal(1))),
    );
    let caller_state = CState::new();
    let entry_state = c_function_entry_state(&caller_state, &function, &[])
        .expect("a parameterless function binds its entry state");
    let (function_outcome, obligations) = c_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        outcome.clone(),
        Vec::new(),
        &PureFactContext::new(),
    );
    let candidates = c_function_execution_candidates_from_outcomes(
        caller_state,
        function.clone(),
        Vec::new(),
        vec![(function_outcome, Vec::new(), obligations)],
    );
    let theorem = Theorem::new(Proposition::CStatementVerifies {
        state: entry_state,
        statement: branch,
        outcome,
    });
    let mut trace = crate::kernel::proof::PersistentSequence::default();
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Statement(
        theorem,
    ));
    (candidates, function, trace)
}

/// Records a trace's events on a fresh proof object one by one, as a
/// driver would (a theorem with the context event that follows it, the
/// candidate path's facts as each step's execution facts), and completes
/// it. The first record call the proof object refuses, or completion's
/// refusal, is the error.
fn complete_early_return(
    candidates: &CFunctionExecutionCandidates,
    function: &CFunction,
    trace: crate::kernel::proof::PersistentSequence<crate::kernel::proof::CheckedExecutionEvent>,
) -> Result<CCheckedFunctionExecution, &'static str> {
    use crate::kernel::proof::CheckedExecutionEvent;
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    let events = trace.to_vec();
    let execution_facts = candidates.paths()[0].facts();
    let mut index = 0;
    while index < events.len() {
        let context = match events.get(index + 1) {
            Some(CheckedExecutionEvent::Context(context)) => context.clone(),
            _ => PureFactContext::new(),
        };
        match &events[index] {
            CheckedExecutionEvent::Statement(theorem) => core
                .record_statement_transition(
                    function,
                    &[],
                    theorem.clone(),
                    context,
                    execution_facts,
                    &[],
                )
                .map_err(|refusal| refusal.reason)?,
            CheckedExecutionEvent::Condition(theorem) => core
                .record_condition_transition(function, &[], theorem.clone(), context, &[], &[])
                .map_err(|refusal| refusal.reason)?,
            CheckedExecutionEvent::Context(_) => {}
            _ => return Err("the test records only theorems"),
        }
        index += 1;
    }
    core.checked_function_execution(
        candidates,
        function,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    )
}

#[test]
fn completion_accepts_a_return_that_leaves_source_behind_it() {
    let entry_state = c_function_entry_state(
        &CState::new(),
        &c_function(CType::Int32, "early", Vec::new(), CStatement::Skip),
        &[],
    )
    .expect("entry state");
    let returning = CStatementOutcome::Return {
        value: int32(0),
        state: entry_state,
    };
    let (candidates, function, trace) = early_return_inputs(returning);
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let completed = complete_early_return(&candidates, &function, trace)
        .expect("a returning `if` completes although `return 1` follows it in the source");
    assert_eq!(completed.paths().len(), 1);
    let mut conclusion = completed.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(
        matches!(
            conclusion,
            Proposition::CFunctionVerifies { outcome, .. } if outcome == candidates.paths()[0].outcome()
        ),
        "the path theorem concludes the candidate's outcome: {conclusion:?}"
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "completion composes retained theorems; it never executes the body"
    );
}

#[test]
fn completion_refuses_a_trace_that_stops_before_the_path_ends() {
    let entry_state = c_function_entry_state(
        &CState::new(),
        &c_function(CType::Int32, "early", Vec::new(), CStatement::Skip),
        &[],
    )
    .expect("entry state");
    // A `Normal` outcome for the `if` leaves `return 1` unexecuted: no
    // retained theorem covers it, so the path has no completed outcome.
    let (candidates, function, trace) =
        early_return_inputs(CStatementOutcome::Normal(entry_state.clone()));
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("a trace does not reach a return")
    );

    // A trace that continues past its returning statement is refused too.
    let returning = CStatementOutcome::Return {
        value: int32(0),
        state: entry_state.clone(),
    };
    let (candidates, function, mut trace) = early_return_inputs(returning);
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Statement(
        Theorem::new(Proposition::CStatementVerifies {
            state: entry_state.clone(),
            statement: c_return(c_int32_literal(1)),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state: entry_state,
            },
        }),
    ));
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence was recorded after the trace completed")
    );
}

/// `int32 early() { if (0 < 1) { return 0; } return 1; }` whose one retained
/// statement theorem has `premises` and whose candidate path retains `facts`.
fn early_return_inputs_with_facts(
    premises: Vec<Proposition>,
    facts: Vec<Proposition>,
) -> (
    CFunctionExecutionCandidates,
    CFunction,
    crate::kernel::proof::PersistentSequence<crate::kernel::proof::CheckedExecutionEvent>,
) {
    let branch = c_if(
        c_less_than(c_int32_literal(0), c_int32_literal(1)),
        c_return(c_int32_literal(0)),
        CStatement::Skip,
    );
    let function = c_function(
        CType::Int32,
        "early",
        Vec::new(),
        c_seq(branch.clone(), c_return(c_int32_literal(1))),
    );
    let caller_state = CState::new();
    let entry_state = c_function_entry_state(&caller_state, &function, &[])
        .expect("a parameterless function binds its entry state");
    let outcome = CStatementOutcome::Return {
        value: int32(0),
        state: entry_state.clone(),
    };
    let (function_outcome, obligations) = c_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        outcome.clone(),
        Vec::new(),
        &PureFactContext::new(),
    );
    let candidates = c_function_execution_candidates_from_outcomes(
        caller_state,
        function.clone(),
        Vec::new(),
        vec![(
            function_outcome,
            facts.into_iter().map(ExecutionPureFact::new).collect(),
            obligations,
        )],
    );
    let conclusion = Proposition::CStatementVerifies {
        state: entry_state,
        statement: branch,
        outcome,
    };
    let theorem = Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    );
    let mut trace = crate::kernel::proof::PersistentSequence::default();
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Statement(
        theorem,
    ));
    (candidates, function, trace)
}

#[test]
fn recording_finds_a_theorem_premise_inside_a_retained_conjunction() {
    let counter = Bitvector32Term::Variable(Variable(1_000_000));
    let bound = Bitvector32Term::Variable(Variable(0));
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(counter.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let bounded = Proposition::ConditionIs(ConditionTerm::signed_less_equal(counter, bound), true);
    // A loop step retains the lowered invariant as one conjunction; the
    // statement theorem lists each conjunct it executed under.
    let invariant = Proposition::And(Box::new(nonnegative.clone()), Box::new(bounded.clone()));
    let (candidates, function, trace) = early_return_inputs_with_facts(
        vec![nonnegative.clone(), bounded.clone()],
        vec![invariant.clone()],
    );
    complete_early_return(&candidates, &function, trace)
        .expect("each conjunct of a retained conjunction is a retained premise");

    // A disjunction retains neither side, and a premise mentioning a
    // different variable is not retained by a conjunction that does not
    // contain it.
    let disjunction = Proposition::Or(Box::new(nonnegative.clone()), Box::new(bounded.clone()));
    let (candidates, function, trace) =
        early_return_inputs_with_facts(vec![nonnegative.clone()], vec![disjunction]);
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence assumes a premise the proof did not retain")
    );
    let other = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(Variable(1_000_001)),
            Bitvector32Term::Constant(3),
        ),
        true,
    );
    let (candidates, function, trace) =
        early_return_inputs_with_facts(vec![other], vec![invariant]);
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence assumes a premise the proof did not retain")
    );
}

/// `int32 skipping() { ; return 1; }`: a body whose first statement is the
/// `Skip` an empty `if` arm leaves behind, with the given retained trace.
fn skip_inputs(
    events: Vec<crate::kernel::proof::CheckedExecutionEvent>,
) -> (
    CFunctionExecutionCandidates,
    CFunction,
    crate::kernel::proof::PersistentSequence<crate::kernel::proof::CheckedExecutionEvent>,
) {
    let function = c_function(
        CType::Int32,
        "skipping",
        Vec::new(),
        c_seq(CStatement::Skip, c_return(c_int32_literal(1))),
    );
    let caller_state = CState::new();
    let outcome = CStatementOutcome::Return {
        value: int32(1),
        state: caller_state.clone(),
    };
    let (function_outcome, obligations) = c_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        outcome,
        Vec::new(),
        &PureFactContext::new(),
    );
    let candidates = c_function_execution_candidates_from_outcomes(
        caller_state,
        function.clone(),
        Vec::new(),
        vec![(function_outcome, Vec::new(), obligations)],
    );
    let mut trace = crate::kernel::proof::PersistentSequence::default();
    for event in events {
        trace.push(event);
    }
    (candidates, function, trace)
}

fn skip_theorem(state: CState) -> crate::kernel::proof::CheckedExecutionEvent {
    crate::kernel::proof::CheckedExecutionEvent::Statement(Theorem::new(
        Proposition::CStatementVerifies {
            state: state.clone(),
            statement: CStatement::Skip,
            outcome: CStatementOutcome::Normal(state),
        },
    ))
}

fn return_one_theorem(state: CState) -> crate::kernel::proof::CheckedExecutionEvent {
    crate::kernel::proof::CheckedExecutionEvent::Statement(Theorem::new(
        Proposition::CStatementVerifies {
            state: state.clone(),
            statement: c_return(c_int32_literal(1)),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        },
    ))
}

#[test]
fn recording_passes_over_skip_on_either_side() {
    let entry = CState::new();
    // The driver stepped through the `Skip`: it consumes the source's `Skip`.
    let (candidates, function, trace) = skip_inputs(vec![
        skip_theorem(entry.clone()),
        return_one_theorem(entry.clone()),
    ]);
    complete_early_return(&candidates, &function, trace)
        .expect("a `Skip` theorem consumes the `Skip` at the head of the source");
    // The driver completed the empty arm in place: the source's `Skip` is
    // passed over before the real statement is matched.
    let (candidates, function, trace) = skip_inputs(vec![return_one_theorem(entry.clone())]);
    complete_early_return(&candidates, &function, trace)
        .expect("a `Skip` left in the source is passed over");
    // An extra `Skip` theorem touches nothing.
    let (candidates, function, trace) = skip_inputs(vec![
        skip_theorem(entry.clone()),
        skip_theorem(entry.clone()),
        return_one_theorem(entry.clone()),
    ]);
    complete_early_return(&candidates, &function, trace)
        .expect("a second `Skip` theorem is a no-op");
    // A `Skip` theorem must still start from the reached state. (The first
    // event names the trace's entry state, so the mismatch is placed second.)
    let elsewhere = CState::new().with_local("x", int32(1));
    let (candidates, function, trace) = skip_inputs(vec![
        skip_theorem(entry.clone()),
        skip_theorem(elsewhere),
        return_one_theorem(entry),
    ]);
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence does not start from the running state")
    );
}

#[test]
fn completion_accepts_a_case_arm_recorded_after_the_return() {
    // A post-execution case split records its arm after the path's
    // returning statement. Both arms must be present across the traces.
    let entry_state = c_function_entry_state(
        &CState::new(),
        &c_function(CType::Int32, "early", Vec::new(), CStatement::Skip),
        &[],
    )
    .expect("entry state");
    let returning = CStatementOutcome::Return {
        value: int32(0),
        state: entry_state,
    };
    let (candidates, function, trace) = early_return_inputs(returning);
    let root = crate::kernel::proof::ProofFacts::default();
    let then_fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(1_000_050)),
            Bitvector32Term::Constant(5),
        ),
        true,
    );
    let else_fact = Proposition::Not(Box::new(then_fact.clone()));
    let partition = crate::kernel::proof::CheckedProofCasePartition::check(
        &root,
        then_fact.clone(),
        else_fact.clone(),
    )
    .expect("complementary case facts");
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    let outcomes = trace
        .to_vec()
        .into_iter()
        .filter_map(|event| match event {
            crate::kernel::proof::CheckedExecutionEvent::Statement(theorem) => Some(theorem),
            _ => None,
        })
        .map(|theorem| (theorem, &[][..], &[][..]))
        .collect::<Vec<_>>();
    core.record_statement_outcomes(&function, &[], &outcomes, PureFactContext::new())
        .expect("the returning branch theorem advances the entry frontier");
    core.fork_outcome_evidence(&[crate::kernel::proof::OutcomeEvidenceFork::Split {
        partition,
        arm_facts: [root.with_fact(then_fact), root.with_fact(else_fact)],
    }])
    .expect("the single trace forks into both arms");
    let traces = core.execution_evidence.to_vec();
    assert_eq!(traces.len(), 2);
    let candidate = candidates.paths()[0].clone();
    let copy = || {
        (
            candidate.outcome().clone(),
            candidate.facts().to_vec(),
            candidate.obligations().to_vec(),
        )
    };
    let forked = c_function_execution_candidates_from_outcomes(
        candidates.state().clone(),
        function.clone(),
        Vec::new(),
        vec![copy(), copy()],
    );
    core.checked_function_execution(
        &forked,
        &function,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    )
    .expect("both forked paths complete with their case arms");
    // One arm alone is not exhaustive.
    let one_arm = c_function_execution_candidates_from_outcomes(
        candidates.state().clone(),
        function.clone(),
        Vec::new(),
        vec![copy()],
    );
    let mut one_trace = core.clone();
    one_trace.execution_evidence = vec![traces[0].clone()].into();
    assert_eq!(
        one_trace
            .checked_function_execution(
                &one_arm,
                &function,
                PureFactContext::new(),
                CExecutionEnvironment::new(),
                CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                CFunctionContractExecutionMode::VerifyLoops,
            )
            .err(),
        Some("a proof-case partition is not exhausted by the retained traces")
    );
}

#[test]
fn contract_exit_rule_is_the_plain_outcome_without_resources() {
    let function = c_function(
        CType::Int32,
        "plain",
        Vec::new(),
        c_return(c_int32_literal(3)),
    );
    let caller_state = CState::new();
    let entry_state = c_function_entry_state(&caller_state, &function, &[]).expect("entry");
    let returning = CStatementOutcome::Return {
        value: int32(3),
        state: entry_state,
    };
    let (plain, _) = c_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        returning.clone(),
        Vec::new(),
        &PureFactContext::new(),
    );
    let (exit_outcome, _, _) = crate::kernel::functions::contract_exit_outcome(
        &caller_state,
        &function,
        &[],
        returning,
        Vec::new(),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
        crate::kernel::functions::ResourceTransitionPurpose::FunctionBoundary,
    )
    .expect("no execution limit")
    .expect("no runtime error");
    assert_eq!(exit_outcome, plain);
}

#[test]
fn recording_takes_a_premise_from_the_retained_context() {
    // A `have` mid-execution puts `x < 5` in the context a later statement
    // executes under. The statement theorem lists it as a premise; it is
    // neither an entry assumption nor a path fact, so only the retained
    // context can vouch for it.
    let bound = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Variable(Variable(1_000_070)),
            Bitvector32Term::Constant(5),
        ),
        true,
    );
    let (candidates, function, mut trace) =
        early_return_inputs_with_facts(vec![bound.clone()], Vec::new());
    assert_eq!(
        complete_early_return(&candidates, &function, trace.clone()).err(),
        Some("evidence assumes a premise the proof did not retain")
    );
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        PureFactContext::new().assume_proposition(bound),
    ));
    complete_early_return(&candidates, &function, trace)
        .expect("the retained context vouches for the theorem's premise");
    // A context that does not hold the premise vouches for nothing.
    let other = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Variable(Variable(1_000_071)),
            Bitvector32Term::Constant(5),
        ),
        true,
    );
    let (candidates, function, mut trace) = early_return_inputs_with_facts(vec![other], Vec::new());
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(
                Bitvector32Term::Variable(Variable(1_000_072)),
                Bitvector32Term::Constant(5),
            ),
            true,
        )),
    ));
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence assumes a premise the proof did not retain")
    );
}

#[test]
fn recording_covers_a_loadability_premise_from_the_retained_context() {
    // A callee's `loadable(p[i..i + 1])` at the caller's current memory is
    // covered by the caller's `loadable(p[0..n])` under `0 <= i < n`.
    let p = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: 4,
        },
    };
    let i = Bitvector32Term::Variable(Variable(1));
    let n = Bitvector32Term::Variable(Variable(2));
    let current = CMemory::new().with_block("local:value", 4);
    let requirement = Proposition::CMemoryLoadable {
        memory: current,
        base: p.offset_by_int32_elements(i.clone()),
        bytes: Bitvector32Term::Constant(4),
    };
    let caller = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: p.clone(),
        bytes: Bitvector32Term::Multiply(
            Box::new(n.clone()),
            Box::new(Bitvector32Term::Constant(4)),
        ),
    };
    let context = PureFactContext::new()
        .assume_proposition(caller)
        .assume_condition(
            ConditionTerm::signed_greater_equal(i.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i, n.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), n.clone()),
            true,
        )
        // The caller's range is read at element granularity, so `n` has to be
        // an element count that fits a `u32` byte extent once scaled by four —
        // `i32::MAX` elements of four bytes do not.
        .assume_condition(
            ConditionTerm::signed_less_equal(
                n,
                Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        );
    let (candidates, function, mut trace) =
        early_return_inputs_with_facts(vec![requirement.clone()], Vec::new());
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        context.clone(),
    ));
    complete_early_return(&candidates, &function, trace)
        .expect("the caller's wider viewable range covers the callee's requirement");

    // A requirement outside the covered range is refused.
    let outside = Proposition::CMemoryLoadable {
        memory: CMemory::new().with_block("local:value", 4),
        base: p.offset_by_int32_elements(Bitvector32Term::Variable(Variable(2))),
        bytes: Bitvector32Term::Constant(4),
    };
    let (candidates, function, mut trace) =
        early_return_inputs_with_facts(vec![outside], Vec::new());
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        context,
    ));
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence assumes a premise the proof did not retain")
    );
}

#[test]
fn recording_complete_sequence_requires_exact_remaining_source() {
    let body = c_seq(c_return(c_int32_literal(0)), c_return(c_int32_literal(1)));
    let function = c_function(CType::Int32, "sequence", Vec::new(), body.clone());
    let entry = c_function_entry_state(&CState::new(), &function, &[]).expect("entry");
    for (statement, accepted) in [
        (body, true),
        (
            c_seq(c_return(c_int32_literal(0)), c_return(c_int32_literal(2))),
            false,
        ),
        (c_seq(CStatement::Skip, c_return(c_int32_literal(1))), false),
    ] {
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            CState::new(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        let evidence = Theorem::new(Proposition::CStatementVerifies {
            state: entry.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: entry.clone(),
            },
        });
        let recorded = core.record_statement_transition(
            &function,
            &[],
            evidence,
            PureFactContext::new(),
            &[],
            &[],
        );
        assert_eq!(recorded.is_ok(), accepted);
        if accepted {
            assert!(core.evidence_source.is_none());
        }
    }
}

#[test]
fn recording_statement_evidence_checks_it_advances_the_frontier() {
    // The record call itself applies the judgment the end-of-proof walk
    // applies: the theorem proves the frontier's next source statement
    // from the running state, under premises the proof retains.
    let branch = c_if(
        c_less_than(c_int32_literal(0), c_int32_literal(1)),
        c_return(c_int32_literal(0)),
        CStatement::Skip,
    );
    let function = c_function(
        CType::Int32,
        "early",
        Vec::new(),
        c_seq(branch.clone(), c_return(c_int32_literal(1))),
    );
    let entry_state = c_function_entry_state(&CState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let verifies = |state: CState, statement: CStatement| Proposition::CStatementVerifies {
        state: state.clone(),
        statement,
        outcome: CStatementOutcome::Return {
            value: int32(0),
            state,
        },
    };
    let record = |theorem: Theorem, context: PureFactContext| {
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            CState::new(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        core.record_statement_transition(&function, &[], theorem, context, &[], &[])
    };
    record(
        Theorem::new(verifies(entry_state.clone(), branch.clone())),
        PureFactContext::new(),
    )
    .expect("the body's first statement from the entry state advances the entry frontier");
    let refusal = record(
        Theorem::new(verifies(entry_state.clone(), c_return(c_int32_literal(1)))),
        PureFactContext::new(),
    )
    .expect_err("a later statement is not the frontier's next");
    assert_eq!(
        refusal.reason,
        "statement evidence does not prove the frontier's next source statement"
    );
    assert_eq!(refusal.expected.as_ref(), Some(&branch));
    assert_eq!(refusal.proved, Some(c_return(c_int32_literal(1))));
    let elsewhere = entry_state.clone().with_local("x", int32(1));
    assert_eq!(
        record(
            Theorem::new(verifies(elsewhere, branch.clone())),
            PureFactContext::new(),
        )
        .map_err(|refusal| refusal.reason),
        Err("evidence does not start from the running state")
    );
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(Variable(1_000_001)),
            Bitvector32Term::Constant(3),
        ),
        true,
    );
    let conditional = Theorem::new(Proposition::Implies(
        Box::new(premise.clone()),
        Box::new(verifies(entry_state, branch)),
    ));
    let refusal = record(conditional.clone(), PureFactContext::new())
        .expect_err("an unretained premise is refused");
    assert_eq!(
        refusal.reason,
        "evidence assumes a premise the proof did not retain"
    );
    assert_eq!(refusal.premise.as_ref(), Some(&premise));
    record(
        conditional,
        PureFactContext::new().assume_proposition(premise),
    )
    .expect("a premise the recorded context retains is accepted");
}

#[test]
fn recording_condition_evidence_checks_it_decides_the_frontier() {
    // The condition record call applies the same judgment for the theorem
    // that selects an `if` arm or a loop iteration: it decides the
    // frontier's next `if` or `while` condition, from the running state,
    // under premises the proof retains.
    let condition = c_less_than(c_int32_literal(0), c_int32_literal(1));
    let branch = c_if(
        condition.clone(),
        c_return(c_int32_literal(0)),
        CStatement::Skip,
    );
    let function = c_function(
        CType::Int32,
        "early",
        Vec::new(),
        c_seq(branch, c_return(c_int32_literal(1))),
    );
    let entry_state = c_function_entry_state(&CState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let evaluates =
        |state: CState, condition: crate::kernel::CExpression| Proposition::CConditionEvaluates {
            state,
            condition,
            outcome: crate::kernel::CConditionOutcome::Value(true),
        };
    let record = |theorem: Theorem, context: PureFactContext, path_facts: &[Proposition]| {
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            CState::new(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        core.record_condition_transition(&function, &[], theorem, context, path_facts, &[])
            .map_err(|refusal| refusal.reason)
    };
    record(
        Theorem::new(evaluates(entry_state.clone(), condition.clone())),
        PureFactContext::new(),
        &[],
    )
    .expect("the body's `if` condition from the entry state decides the entry frontier");
    assert_eq!(
        record(
            Theorem::new(evaluates(
                entry_state.clone(),
                c_less_than(c_int32_literal(1), c_int32_literal(0)),
            )),
            PureFactContext::new(),
            &[],
        ),
        Err("condition evidence does not decide the frontier's next source condition")
    );
    let elsewhere = entry_state.clone().with_local("x", int32(1));
    assert_eq!(
        record(
            Theorem::new(evaluates(elsewhere, condition.clone())),
            PureFactContext::new(),
            &[],
        ),
        Err("evidence does not start from the running state")
    );
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(Variable(1_000_001)),
            Bitvector32Term::Constant(3),
        ),
        true,
    );
    let conditional = Theorem::new(Proposition::Implies(
        Box::new(premise.clone()),
        Box::new(evaluates(entry_state, condition)),
    ));
    assert_eq!(
        record(conditional.clone(), PureFactContext::new(), &[]),
        Err("evidence assumes a premise the proof did not retain")
    );
    record(
        conditional.clone(),
        PureFactContext::new().assume_proposition(premise.clone()),
        &[],
    )
    .expect("a premise the recorded context retains is accepted");
    // The decision's own path fact is a premise the selected path assumes.
    record(conditional, PureFactContext::new(), &[premise])
        .expect("a premise that is the path's own fact is accepted");
    // A statement that is not an `if` or `while` cannot be decided.
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    let returning = c_function(
        CType::Int32,
        "returning",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    assert_eq!(
        core.record_condition_transition(
            &returning,
            &[],
            Theorem::new(Proposition::CConditionEvaluates {
                state: c_function_entry_state(&CState::new(), &returning, &[]).expect("entry"),
                condition: c_less_than(c_int32_literal(0), c_int32_literal(1)),
                outcome: crate::kernel::CConditionOutcome::Value(true),
            }),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("condition evidence does not decide the frontier's next `if` or `while`")
    );
}

#[test]
fn recorded_evidence_reaches_the_theorem_outcome_not_the_driver_state() {
    // The proof object validates its chain from the theorems alone: the
    // next theorem must start from the state the recorded evidence
    // reached, whatever the driver's own copy of the state says.
    let condition = c_less_than(c_int32_literal(0), c_int32_literal(1));
    let branch = c_if(condition.clone(), CStatement::Skip, CStatement::Skip);
    let tail = c_return(c_int32_literal(1));
    let function = c_function(
        CType::Int32,
        "early",
        Vec::new(),
        c_seq(branch, tail.clone()),
    );
    let entry_state = c_function_entry_state(&CState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    core.record_condition_transition(
        &function,
        &[],
        Theorem::new(Proposition::CConditionEvaluates {
            state: entry_state.clone(),
            condition,
            outcome: crate::kernel::CConditionOutcome::Value(true),
        }),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the condition decides the entry `if`");
    assert_eq!(core.reached_state(), &entry_state);
    // The driver moves its frontier past the `if` but drifts its own state.
    core.frontier.position = crate::kernel::proof::FrontierPosition::StatementEntry {
        remaining: std::sync::Arc::new(tail.clone()),
    };
    let drifted = entry_state.clone().with_local("x", int32(1));
    core.state = drifted.clone().into();
    let returning = |state: CState| {
        Theorem::new(Proposition::CStatementVerifies {
            state: state.clone(),
            statement: tail.clone(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        })
    };
    assert_eq!(
        core.record_statement_transition(
            &function,
            &[],
            returning(drifted),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("evidence does not start from the running state")
    );
    core.record_statement_transition(
        &function,
        &[],
        returning(entry_state.clone()),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the return from the reached state is accepted");
    assert_eq!(core.reached_state(), &entry_state);
    assert_eq!(
        core.record_statement_transition(
            &function,
            &[],
            returning(entry_state),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("evidence was recorded after the trace completed")
    );
}

#[test]
fn recorded_evidence_consumes_the_source_not_the_driver_frontier() {
    // Once evidence is recorded, the next theorem is checked against the
    // source the evidence has yet to consume, whatever the driver's
    // frontier says.
    let condition = c_less_than(c_int32_literal(0), c_int32_literal(1));
    let branch = c_if(
        condition.clone(),
        c_return(c_int32_literal(0)),
        CStatement::Skip,
    );
    let tail = c_return(c_int32_literal(1));
    let function = c_function(
        CType::Int32,
        "early",
        Vec::new(),
        c_seq(branch, tail.clone()),
    );
    let entry_state = c_function_entry_state(&CState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let returning = |statement: CStatement, value: u32| {
        Theorem::new(Proposition::CStatementVerifies {
            state: entry_state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(value),
                state: entry_state.clone(),
            },
        })
    };
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    // Selecting the empty else arm leaves the tail to consume.
    core.record_condition_transition(
        &function,
        &[],
        Theorem::new(Proposition::CConditionEvaluates {
            state: entry_state.clone(),
            condition,
            outcome: crate::kernel::CConditionOutcome::Value(false),
        }),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the condition decides the entry `if`");
    assert_eq!(core.evidence_source.as_deref(), Some(&tail));
    // The driver's frontier still names the `if`'s then arm.
    core.frontier.position = crate::kernel::proof::FrontierPosition::StatementEntry {
        remaining: std::sync::Arc::new(c_return(c_int32_literal(0))),
    };
    let refusal = core
        .record_statement_transition(
            &function,
            &[],
            returning(c_return(c_int32_literal(0)), 0),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect_err("the driver's frontier does not decide the source");
    assert_eq!(
        refusal.reason,
        "statement evidence does not prove the frontier's next source statement"
    );
    assert_eq!(refusal.expected.as_ref(), Some(&tail));
    assert_eq!(refusal.proved, Some(c_return(c_int32_literal(0))));
    core.record_statement_transition(
        &function,
        &[],
        returning(tail, 1),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the tail is the source the evidence has yet to consume");
    assert!(core.evidence_source.is_none());
}

#[test]
fn void_fallthrough_completion_requires_consuming_the_entire_source() {
    for (return_type, pending_return) in [
        (CType::Void, false),
        (CType::Void, true),
        (CType::Int32, false),
    ] {
        let body = if pending_return {
            CStatement::Seq(
                std::sync::Arc::new(CStatement::Skip),
                std::sync::Arc::new(c_return(c_void_value())),
            )
        } else {
            CStatement::Skip
        };
        let function = c_function(return_type, "fallthrough", Vec::new(), body);
        let caller = CState::new();
        let entry = c_function_entry_state(&caller, &function, &[]).expect("entry");
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            caller.clone(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        core.record_statement_transition(
            &function,
            &[],
            Theorem::new(Proposition::CStatementVerifies {
                state: entry.clone(),
                statement: CStatement::Skip,
                outcome: CStatementOutcome::Normal(entry.clone()),
            }),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("checked next statement");
        let (outcome, obligations) = c_function_outcome_from_statement_outcome(
            &caller,
            &function,
            CStatementOutcome::Return {
                value: CValue::Void,
                state: entry,
            },
            Vec::new(),
            &PureFactContext::new(),
        );
        let candidates = c_function_execution_candidates_from_outcomes(
            caller,
            function.clone(),
            Vec::new(),
            vec![(outcome, Vec::new(), obligations)],
        );
        let result = core.checked_function_execution(
            &candidates,
            &function,
            PureFactContext::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            CFunctionContractExecutionMode::VerifyLoops,
        );
        assert_eq!(
            result.is_ok(),
            return_type == CType::Void && !pending_return
        );
    }
}

#[test]
fn a_completed_proof_object_yields_its_checked_execution() {
    // Completion composes the checked traces into one path per trace
    // concluding the candidate's outcome; an open trace yields nothing.
    let entry_state = c_function_entry_state(
        &CState::new(),
        &c_function(CType::Int32, "early", Vec::new(), CStatement::Skip),
        &[],
    )
    .expect("entry state");
    let returning = CStatementOutcome::Return {
        value: int32(0),
        state: entry_state.clone(),
    };
    let (candidates, function, trace) = early_return_inputs(returning);
    let theorem = match trace.to_vec().into_iter().next() {
        Some(crate::kernel::proof::CheckedExecutionEvent::Statement(theorem)) => theorem,
        _ => unreachable!("the trace begins with its returning theorem"),
    };
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    core.record_statement_transition(&function, &[], theorem, PureFactContext::new(), &[], &[])
        .expect("the returning branch theorem advances the entry frontier");
    let completed = core
        .checked_function_execution(
            &candidates,
            &function,
            PureFactContext::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            CFunctionContractExecutionMode::VerifyLoops,
        )
        .expect("a completed proof object yields its checked function execution");
    assert_eq!(completed.paths().len(), 1);
    let mut conclusion = completed.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(matches!(
        conclusion,
        Proposition::CFunctionVerifies { outcome, .. } if outcome == candidates.paths()[0].outcome()
    ));

    let mut open = crate::kernel::proof::ExecutionProofCore::at_entry(
        CState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    open.record_statement_transition(
        &function,
        &[],
        Theorem::new(Proposition::CStatementVerifies {
            state: entry_state.clone(),
            statement: CStatement::Skip,
            outcome: CStatementOutcome::Normal(entry_state),
        }),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("a `Skip` theorem consumes nothing");
    assert_eq!(
        open.checked_function_execution(
            &candidates,
            &function,
            PureFactContext::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            CFunctionContractExecutionMode::VerifyLoops,
        )
        .err(),
        Some("a trace does not reach a return")
    );
}

#[test]
fn completion_key_folds_trivial_conditions_the_proof_lowering_folds() {
    use crate::kernel::api::completion_key;
    let x = Bitvector32Term::Variable(Variable(1));
    let y = Bitvector32Term::Variable(Variable(2));
    let truth = |value: bool| Proposition::ConditionIs(ConditionTerm::Constant(value), true);
    let equal = |left: &Bitvector32Term, right: &Bitvector32Term, value: bool| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
            value,
        )
    };
    let nontrivial = equal(&x, &y, true);

    // A term compared with itself is a constant.
    assert_eq!(completion_key(&equal(&x, &x, true)), truth(true));
    assert_eq!(completion_key(&equal(&x, &x, false)), truth(false));
    // A constant condition folds to the canonical truth value.
    assert_eq!(
        completion_key(&Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            false
        )),
        truth(true)
    );
    // Negating a constant stays in the canonical truth form.
    assert_eq!(
        completion_key(&Proposition::Not(Box::new(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )))),
        truth(true)
    );
    // Negating a condition flips its value.
    assert_eq!(
        completion_key(&Proposition::Not(Box::new(nontrivial.clone()))),
        equal(&x, &y, false)
    );
    // Constant premises and conjuncts disappear.
    assert_eq!(
        completion_key(&Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Constant(false),
                false
            )),
            Box::new(nontrivial.clone()),
        )),
        nontrivial
    );
    assert_eq!(
        completion_key(&Proposition::And(
            Box::new(equal(&y, &y, true)),
            Box::new(nontrivial.clone()),
        )),
        nontrivial
    );
    assert_eq!(
        completion_key(&Proposition::Or(
            Box::new(nontrivial.clone()),
            Box::new(truth(true))
        )),
        truth(true)
    );
    // A quantifier folds its body, and over a constant body is the constant.
    let quantified = |body: Proposition| Proposition::ForAll {
        var: Variable(3),
        sort: Sort::CInt32,
        body: Box::new(body),
    };
    assert_eq!(
        completion_key(&quantified(equal(&x, &x, true))),
        truth(true)
    );
    assert_eq!(
        completion_key(&quantified(Proposition::And(
            Box::new(truth(true)),
            Box::new(nontrivial.clone()),
        ))),
        quantified(nontrivial.clone())
    );
    // Nothing else changes.
    assert_eq!(completion_key(&nontrivial), nontrivial);
}

/// A call requirement the caller cannot discharge becomes a precondition
/// obligation, and that obligation now carries the head chain the lowering
/// that built it recorded: the guards lowering inserted in front of the
/// requirement, in the order an introduction reaches them.
///
/// The requirement here adds one to the symbolic argument, so lowering guards
/// it with the no-overflow premise the caller state does not establish.
/// Nothing pairs that guard with a written connective by shape: the record
/// says it is one lowering inserted.
#[test]
fn call_requirement_obligations_carry_their_lowering_record() {
    let successor_is_positive = SpecProposition::Comparison {
        left: SpecExpression::Add(
            Box::new(SpecExpression::CExpression(c_variable("n"))),
            Box::new(SpecExpression::CExpression(c_int32_literal(1))),
        ),
        operator: CComparisonOperator::GreaterThan,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let returns_one = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("result")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(1)),
    };
    let helper = c_function(
        CType::Int32,
        "successor_is_positive",
        vec![c_parameter("n", CType::Int32)],
        c_return(c_int32_literal(1)),
    )
    .with_contract(
        vec![successor_is_positive],
        vec![returns_one],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: helper,
            loop_semantics: CLoopSemantics::Verify,
        });
    let state = CState::new().with_local("n", int32(Bitvector32Term::Variable(Variable(31_000))));
    let execution = prove_symbolic_c_execution_paths_with_environment(
        state,
        c_call_assign("result", "successor_is_positive", vec![c_variable("n")]),
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("verified call path");
    let obligation = path
        .obligations()
        .iter()
        .find(|obligation| obligation.context() == Some("successor_is_positive precondition"))
        .unwrap_or_else(|| {
            panic!(
                "an undischarged precondition should be emitted: {:#?}",
                path.obligations()
            )
        });
    let recorded = obligation
        .introductions()
        .expect("a kernel-built call requirement carries its lowering record");
    assert!(
        !recorded.is_empty(),
        "lowering guarded this requirement, so the record names those guards: {:?}",
        obligation.proposition()
    );
    // Every recorded node is a guard lowering inserted, and each one is an
    // `Implies` the proposition actually has: the record describes the
    // proposition it was produced with.
    let mut proposition = obligation.proposition();
    for introduction in recorded {
        assert!(
            matches!(
                introduction,
                LoweringIntroduction::PathFactGuard | LoweringIntroduction::ObligationGuard
            ),
            "no Surface connective wrote this requirement's head: {introduction:?}"
        );
        let Proposition::Implies(_, body) = proposition else {
            panic!("the record names more head nodes than the obligation has");
        };
        proposition = body;
    }
}

/// A self-recursive function that declares an expression `decreases` measure.
/// Its body is irrelevant here: what is exercised is the call step.
fn drain_with_expression_measure() -> CFunction {
    c_function(
        CType::Int32,
        "drain",
        vec![c_parameter("n", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    )
    .with_recursion_measure(CRankingComponent::Pure {
        source: "level(n)".to_string(),
        expression: SpecExpression::CExpression(c_variable("n")),
    })
}

fn opaque_rule_environment(function: CFunction) -> CExecutionEnvironment {
    CExecutionEnvironment::new()
        .with_function(function.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function,
            loop_semantics: CLoopSemantics::Verify,
        })
}

fn symbolic_caller_state() -> CState {
    CState::new().with_local("n", int32(Bitvector32Term::Variable(Variable(31_000))))
}

/// The entry `drain` is anchored at: its parameter bound to the same symbolic
/// value the caller state holds, which is what makes M0 that value.
fn symbolic_entry_arguments() -> Vec<CExpression> {
    vec![CExpression::Value(int32(Bitvector32Term::Variable(
        Variable(31_000),
    )))]
}

/// The contexts of the ranking members a call step emitted, in order.
fn recursion_measure_contexts(path: &SymbolicCExecutionPath) -> Vec<String> {
    path.obligations()
        .iter()
        .filter_map(|obligation| obligation.context())
        .filter(|context| context.contains("recursion measure"))
        .map(str::to_string)
        .collect()
}

fn call_path(
    environment: CExecutionEnvironment,
    callee: &str,
    argument: CExpression,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment(
        symbolic_caller_state(),
        c_call_assign("result", callee, vec![argument]),
        PureFactContext::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    )
}

/// The descent is checked at the call step, not by an analysis of the body.
/// This call's argument arithmetic already establishes the strict decrease,
/// so only the nonnegative member remains as an unresolved obligation.
#[test]
fn a_self_call_under_a_recursion_anchor_keeps_only_unresolved_ranking_members() {
    let drain = drain_with_expression_measure();
    let environment = c_execution_environment_with_recursion_anchor(
        opaque_rule_environment(drain.clone()),
        &drain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("the declared measure reads at the entry state");
    let execution = call_path(
        environment,
        "drain",
        c_subtract(c_variable("n"), c_int32_literal(1)),
    );
    let path = execution.paths().first().expect("verified call path");
    assert_eq!(
        recursion_measure_contexts(path),
        vec![
            "drain recursion measure: `level(n)` is nonnegative at the recursive call".to_string(),
        ],
        "{:#?}",
        path.obligations()
    );
}

/// Without the anchor the same call is an ordinary opaque application. A
/// measure on the interface changes nothing by itself: it is the
/// certification of `drain` that owes the descent, and only there.
#[test]
fn a_call_without_a_recursion_anchor_owes_no_ranking_member() {
    let drain = drain_with_expression_measure();
    let execution = call_path(
        opaque_rule_environment(drain),
        "drain",
        c_subtract(c_variable("n"), c_int32_literal(1)),
    );
    let path = execution.paths().first().expect("verified call path");
    assert!(
        recursion_measure_contexts(path).is_empty(),
        "{:#?}",
        path.obligations()
    );
}

/// The anchor names one function. A call to any other verified function,
/// while it is installed, is untouched.
#[test]
fn an_anchor_ranks_only_calls_to_the_function_it_names() {
    let drain = drain_with_expression_measure();
    let other = c_function(
        CType::Int32,
        "other",
        vec![c_parameter("n", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = c_execution_environment_with_recursion_anchor(
        opaque_rule_environment(drain.clone())
            .with_function(other.clone())
            .with_verified_function_rule(CVerifiedFunctionRule {
                function: other,
                loop_semantics: CLoopSemantics::Verify,
            }),
        &drain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("the declared measure reads at the entry state");
    let execution = call_path(environment, "other", c_variable("n"));
    let path = execution.paths().first().expect("verified call path");
    assert!(
        recursion_measure_contexts(path).is_empty(),
        "{:#?}",
        path.obligations()
    );
}

/// A function that declares no measure gets its environment back unchanged,
/// so no certification that exists today changes shape or identity.
#[test]
fn a_function_without_a_declared_measure_installs_no_anchor() {
    let plain = c_function(
        CType::Int32,
        "plain",
        vec![c_parameter("n", CType::Int32)],
        c_return(c_int32_literal(0)),
    );
    let environment = opaque_rule_environment(plain.clone());
    let anchored = c_execution_environment_with_recursion_anchor(
        environment.clone(),
        &plain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("no declared measure is no work");
    assert_eq!(anchored, environment);
}

/// An anchored environment is a different environment. This is what stops a
/// checked execution recorded without the anchor -- one that raised no
/// descent obligation at its self-calls -- from being reused to certify a
/// contract whose function declares a measure.
#[test]
fn a_recursion_anchor_is_part_of_the_environment_identity() {
    let drain = drain_with_expression_measure();
    let plain = opaque_rule_environment(drain.clone());
    let anchored = c_execution_environment_with_recursion_anchor(
        plain.clone(),
        &drain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("the declared measure reads at the entry state");
    assert_ne!(anchored, plain);
}

/// The block a declaration mints is the object's identity, and about seventy
/// kernel sites read two equal blocks as one object. A called frame runs on
/// the caller's memory with its own locals map, so it cannot see the caller's
/// objects; if it minted the plain `local:<name>` anyway, the callee's object
/// and the caller's would be one block, one extent and one cell map.
#[test]
fn a_called_frames_declaration_does_not_take_the_callers_block() {
    let callers = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_memory(
            CMemory::new()
                .with_block("local:x", 4)
                .store(callers.clone(), int32(1)),
        )
        .with_enclosing_frame_holds_locals(true);
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(2)),
            c_return(c_int32_literal(0)),
        ),
    );
    let theorem = prove_symbolic_c_execution(state, statement, PureFactContext::new())
        .expect("a called frame declares its own local");
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Return { state: after, .. },
        ..
    } = theorem.proposition()
    else {
        panic!("expected a return: {:?}", theorem.proposition());
    };

    let minted = after.locals().slot("x").expect("the callee's own slot");
    assert_ne!(minted, &callers);
    assert_eq!(after.memory().cells.get(&callers), Some(&int32(1)));
}

/// An identity is not free again once its object's lifetime has ended: the
/// tombstone is what makes an alias to the old object invalid, so handing the
/// block to a new object would revive every stale pointer to the old one.
#[test]
fn a_declaration_does_not_take_a_block_whose_lifetime_ended() {
    let retired = PointerBlock::from("local:x");
    let state = CState::new().with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .without_local_block(&retired),
    );
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(2)),
            c_return(c_int32_literal(0)),
        ),
    );
    let theorem = prove_symbolic_c_execution(state, statement, PureFactContext::new())
        .expect("a declaration after an ended lifetime executes");
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Return { state: after, .. },
        ..
    } = theorem.proposition()
    else {
        panic!("expected a return: {:?}", theorem.proposition());
    };

    assert_ne!(
        &after
            .locals()
            .slot("x")
            .expect("the new object's slot")
            .block,
        &retired
    );
}

/// An automatic object's lifetime ends when control leaves the block that
/// declared it. An `if` arm is such a block: the address of a local it
/// declared designates no object once the arm is left, so a load through one
/// is undefined behaviour rather than a way to read what the arm wrote.
#[test]
fn an_if_arms_local_stops_existing_when_the_arm_is_left() {
    let arm = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(7)),
            c_assign("p", c_addr_of("x")),
        ),
    );
    let statement = c_seq(
        c_declare("anchor", CType::Int32),
        c_seq(
            c_assign("anchor", c_int32_literal(0)),
            c_seq(
                c_declare("p", CType::Int32Pointer),
                c_seq(
                    c_assign("p", c_addr_of("anchor")),
                    c_seq(
                        c_if(c_variable("c"), arm, CStatement::Skip),
                        c_return(c_load(c_variable("p"))),
                    ),
                ),
            ),
        ),
    );
    let state = CState::new().with_local("c", CValue::Int32(Bitvector32Term::Constant(1)));
    let theorem = prove_symbolic_c_execution(state, statement, PureFactContext::new())
        .expect("the taken arm is the only path");
    let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
        ),
        "reading an `if` arm's local after the arm is undefined behaviour, got {outcome:?}"
    );
}

/// A loop body is a block, and an iteration leaves it at the back edge as
/// well as at every exit, so a pointer to a body local does not outlive the
/// iteration that created it.
#[test]
fn a_loop_bodys_local_stops_existing_at_the_back_edge() {
    let body = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(9)),
            c_seq(
                c_assign("p", c_addr_of("x")),
                c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
            ),
        ),
    );
    let statement = c_seq(
        c_declare("anchor", CType::Int32),
        c_seq(
            c_assign("anchor", c_int32_literal(0)),
            c_seq(
                c_declare("p", CType::Int32Pointer),
                c_seq(
                    c_assign("p", c_addr_of("anchor")),
                    c_seq(
                        c_declare("i", CType::Int32),
                        c_seq(
                            c_assign("i", c_int32_literal(0)),
                            c_seq(
                                c_while(
                                    c_less_than(c_variable("i"), c_int32_literal(2)),
                                    Vec::new(),
                                    body,
                                ),
                                c_return(c_load(c_variable("p"))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let theorem = prove_symbolic_c_execution(CState::new(), statement, PureFactContext::new())
        .expect("a concrete loop has one path");
    let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
        ),
        "reading a loop body's local after the loop is undefined behaviour, got {outcome:?}"
    );
}

/// `break` leaves the body too. An exit that skips the end of a block still
/// leaves the block, so it ends the same lifetimes falling off the end does.
#[test]
fn a_loop_bodys_local_stops_existing_on_break() {
    let body = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(2)),
            c_seq(c_assign("p", c_addr_of("x")), c_break()),
        ),
    );
    let statement = c_seq(
        c_declare("anchor", CType::Int32),
        c_seq(
            c_assign("anchor", c_int32_literal(0)),
            c_seq(
                c_declare("p", CType::Int32Pointer),
                c_seq(
                    c_assign("p", c_addr_of("anchor")),
                    c_seq(
                        c_while(c_int32_literal(1), Vec::new(), body),
                        c_return(c_load(c_variable("p"))),
                    ),
                ),
            ),
        ),
    );
    let theorem = prove_symbolic_c_execution(CState::new(), statement, PureFactContext::new())
        .expect("the loop breaks on its first iteration");
    let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
        ),
        "reading a loop body's local after a `break` is undefined behaviour, got {outcome:?}"
    );
}

/// A `switch` body is one block for all of its cases, because control falls
/// from one case into the next. Leaving the switch leaves that block.
#[test]
fn a_switch_bodys_local_stops_existing_when_the_switch_is_left() {
    let case = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(4)),
            c_seq(c_assign("p", c_addr_of("x")), c_break()),
        ),
    );
    let statement = c_seq(
        c_declare("anchor", CType::Int32),
        c_seq(
            c_assign("anchor", c_int32_literal(0)),
            c_seq(
                c_declare("p", CType::Int32Pointer),
                c_seq(
                    c_assign("p", c_addr_of("anchor")),
                    c_seq(
                        c_switch(
                            c_int32_literal(1),
                            vec![CSwitchCase {
                                value: Some(1),
                                body: Box::new(case),
                            }],
                        ),
                        c_return(c_load(c_variable("p"))),
                    ),
                ),
            ),
        ),
    );
    let theorem = prove_symbolic_c_execution(CState::new(), statement, PureFactContext::new())
        .expect("a constant selector picks one case");
    let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
        ),
        "reading a `switch` body's local after the switch is undefined behaviour, got {outcome:?}"
    );
}

/// A scope exit retires what the scope declared and nothing else: a pointer
/// to an object the enclosing block declared still designates it.
#[test]
fn an_outer_locals_address_survives_an_inner_scope() {
    let arm = c_seq(
        c_declare("x", CType::Int32),
        c_assign("x", c_int32_literal(7)),
    );
    let statement = c_seq(
        c_declare("outer", CType::Int32),
        c_seq(
            c_assign("outer", c_int32_literal(5)),
            c_seq(
                c_declare("p", CType::Int32Pointer),
                c_seq(
                    c_assign("p", c_addr_of("outer")),
                    c_seq(
                        c_if(c_variable("c"), arm, CStatement::Skip),
                        c_return(c_load(c_variable("p"))),
                    ),
                ),
            ),
        ),
    );
    let state = CState::new().with_local("c", CValue::Int32(Bitvector32Term::Constant(1)));
    let theorem = prove_symbolic_c_execution(state, statement, PureFactContext::new())
        .expect("the taken arm is the only path");
    let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    let CStatementOutcome::Return { value, .. } = outcome else {
        panic!("expected a return: {outcome:?}");
    };
    assert_eq!(value, &CValue::Int32(Bitvector32Term::Constant(5)));
}

fn path_exists_at_snapshot(
    ty: &AlgebraicType,
    binder: u64,
    argument: u64,
    memory: CMemory,
    target: u32,
) -> Proposition {
    Proposition::Exists {
        name: "path".into(),
        var: Variable(binder),
        sort: Sort::Algebraic(ty.clone()),
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::ClickFunctionApplication {
                    name: "walk".into(),
                    arguments: vec![
                        PureFunctionArgument::ArrayRef {
                            memory,
                            pointer: CValue::pointer(Pointer {
                                block: "graph".into(),
                                offset: PointerOffsetTerm::Constant(0),
                            }),
                            element_type: CType::Int32,
                        },
                        PureFunctionArgument::Algebraic(AlgebraicTerm {
                            algebraic_type: ty.clone(),
                            node: AlgebraicTermNode::Variable(Variable(argument)),
                        }),
                    ],
                },
                target.into(),
            ),
            true,
        )),
    }
}

#[test]
fn certification_recognizes_only_the_same_algebraic_existential() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = AlgebraicType::parameter("Path".into());
    let before = CMemory::new().with_block("graph", 4);
    let after = before.clone().store(
        Pointer {
            block: "graph".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(1),
    );
    let fact = path_exists_at_snapshot(&ty, 100, 100, before.clone(), 0);
    let facts = PureFactContext::new().assume_proposition(fact);
    let proves = |goal| {
        crate::kernel::api::contract_certification::certification_proves_proposition(&facts, &goal)
    };
    assert!(proves(path_exists_at_snapshot(
        &ty,
        200,
        200,
        before.clone(),
        0
    )));
    assert!(
        !proves(path_exists_at_snapshot(&ty, 200, 200, after, 0)),
        "a changed graph is not alpha renaming"
    );
    assert!(
        !proves(path_exists_at_snapshot(&ty, 200, 100, before.clone(), 0)),
        "a free path is not the existential binder"
    );
    assert!(
        !proves(path_exists_at_snapshot(&ty, 200, 200, before.clone(), 1)),
        "the endpoint must match"
    );
    assert!(
        !proves(path_exists_at_snapshot(
            &AlgebraicType::parameter("OtherPath".into()),
            200,
            200,
            before,
            0
        )),
        "the witness sort must match"
    );
}

#[test]
fn certification_of_algebraic_witness_ignores_unrelated_quantifiers() {
    let mut samples = Vec::new();
    for size in [32, 64, 128, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Path".into());
        let memory = CMemory::new().with_block("graph", 4);
        let mut facts = PureFactContext::new().assume_proposition(path_exists_at_snapshot(
            &ty,
            100,
            100,
            memory.clone(),
            0,
        ));
        for i in 1..=size {
            facts = facts.assume_proposition(path_exists_at_snapshot(
                &ty,
                1_000 + u64::from(i),
                1_000 + u64::from(i),
                memory.clone(),
                i,
            ));
        }
        facts.build_stated_proposition_index();
        let goal = path_exists_at_snapshot(&ty, 200, 200, memory.clone(), 0);
        let missing = path_exists_at_snapshot(&ty, 200, 200, memory, 1_000);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                crate::kernel::api::contract_certification::certification_proves_proposition(
                    &facts, &goal,
                ),
                crate::kernel::api::contract_certification::certification_proves_proposition(
                    &facts, &missing,
                ),
            )
        });
        assert_eq!(verdicts, (true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "certification scanned unrelated quantifiers: {samples:?}"
    );
}

fn conditional_path_universal(
    ty: &AlgebraicType,
    binder: u64,
    memory: CMemory,
    target: u32,
) -> Proposition {
    let Proposition::Exists {
        name: _,
        var,
        sort,
        body,
    } = path_exists_at_snapshot(ty, binder, binder, memory, target)
    else {
        unreachable!()
    };
    Proposition::Implies(
        Box::new(Proposition::ForAll {
            var: Variable(binder + 1),
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(Bitvector32Term::Variable(Variable(binder + 1)), 0.into()),
                true,
            )),
        }),
        Box::new(Proposition::ForAll { var, sort, body }),
    )
}

#[test]
fn certification_keeps_conditional_universal_guards_snapshots_and_sorts() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = AlgebraicType::parameter("Path".into());
    let memory = CMemory::new().with_block("graph", 4);
    let fact = conditional_path_universal(&ty, 100, memory.clone(), 0);
    let proof_facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&fact));
    let facts = PureFactContext::new().assume_proposition(fact);
    let proves = |goal: &Proposition| {
        let certified =
            crate::kernel::api::contract_certification::certification_proves_proposition(
                &facts, goal,
            );
        assert_eq!(proof_facts.pure_assumption_available(goal), certified);
        certified
    };
    let goal = conditional_path_universal(&ty, 200, memory.clone(), 0);
    assert!(proves(&goal));
    let Proposition::Implies(_, body) = &goal else {
        unreachable!()
    };
    assert!(
        !proves(body),
        "a conditional guarantee cannot lose its guard"
    );
    assert!(!proves(&conditional_path_universal(
        &ty,
        200,
        memory.clone(),
        1
    )));
    assert!(!proves(&conditional_path_universal(
        &AlgebraicType::parameter("OtherPath".into()),
        200,
        memory.clone(),
        0,
    )));
    let after = memory.store(
        Pointer {
            block: "graph".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(1),
    );
    assert!(!proves(&conditional_path_universal(&ty, 200, after, 0)));
}

#[test]
fn conditional_universal_certification_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [32, 64, 128, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Path".into());
        let memory = CMemory::new().with_block("graph", 4);
        let mut facts = PureFactContext::new().assume_proposition(conditional_path_universal(
            &ty,
            100,
            memory.clone(),
            0,
        ));
        let mut proof_facts =
            crate::kernel::proof::ProofFacts::from_ordered(&[conditional_path_universal(
                &ty,
                100,
                memory.clone(),
                0,
            )]);
        for i in 1..=size {
            proof_facts = proof_facts.with_kernel_checked_fact(conditional_path_universal(
                &ty,
                1_000 + 2 * u64::from(i),
                memory.clone(),
                i,
            ));
            facts = facts.assume_proposition(conditional_path_universal(
                &ty,
                1_000 + 2 * u64::from(i),
                memory.clone(),
                i,
            ));
        }
        facts.build_stated_proposition_index();
        let goal = conditional_path_universal(&ty, 200, memory.clone(), 0);
        let missing = conditional_path_universal(&ty, 200, memory, 1_000);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                crate::kernel::api::contract_certification::certification_proves_proposition(
                    &facts, &goal,
                ),
                crate::kernel::api::contract_certification::certification_proves_proposition(
                    &facts, &missing,
                ),
                proof_facts.pure_assumption_available(&goal),
                proof_facts.pure_assumption_available(&missing),
            )
        });
        assert_eq!(verdicts, (true, false, true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "conditional lookup scanned unrelated facts: {samples:?}"
    );
}
