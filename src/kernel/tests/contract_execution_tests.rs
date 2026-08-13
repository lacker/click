use super::*;

fn pool_resource_spec(name: &str) -> CResourceSpec {
    CResourceSpec::Composite {
        access: CResourceAccessMode::Own,
        name: name.to_string(),
        arguments: vec![c_variable("pool"), c_variable("object")],
        parameter_types: vec![CType::Int32, CType::Int32],
    }
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
        &Assumptions::new(),
    )
    .expect("the checked resource transition should replay");
    assert!(obligations.is_empty());
    let CFunctionOutcome::Return { state, .. } = outcome else {
        panic!("resource transition did not return");
    };
    state
}

fn pool_count(state: &CState, pool: u32) -> Bitvector32Term {
    state.counted_population_sum(
        "pool_object",
        &[Some(int32(pool)), None],
        &Assumptions::new(),
    )
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
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
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
fn symbolic_execution_stops_without_needed_overflow_fact() {
    let left = Variable(20);
    let right = Variable(21);
    let state = CState::new()
        .with_local("left", int32(Bitvector32Term::Variable(left)))
        .with_local("right", int32(Bitvector32Term::Variable(right)));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));

    assert!(prove_symbolic_c_execution(state, statement, Assumptions::new()).is_none());
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
        prove_symbolic_c_execution_paths(state.clone(), c_max_body(), Assumptions::new());

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
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

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
    let assumptions = Assumptions::new().assume_condition(no_overflow.clone(), false);
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
    let assumptions = Assumptions::new()
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
    let assumptions = Assumptions::new().assume_condition(x_lt_int_max.clone(), true);
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
    let assumptions = Assumptions::new().assume_condition(assumption, true);

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
    let assumptions = Assumptions::new()
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
    let assumptions = Assumptions::new()
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
    let mut assumptions = Assumptions::new();
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
    let assumptions = Assumptions::new()
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
    let theorem = prove_symbolic_c_execution(CState::new(), statement.clone(), Assumptions::new())
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
    let execution = prove_c_function_contract_execution_paths_with_environment(
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
        &Assumptions::new(),
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
        Assumptions::new(),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("result", "opaque_helper", vec![c_int32_literal(5)]),
        c_return(c_variable("result")),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement.clone(),
        Assumptions::new(),
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
    let assumptions = assumptions_with_propositions(&Assumptions::new(), &propositions);
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
        Assumptions::new(),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call_assign("result", "pointer_is_null", vec![c_int32_literal(0)]),
        Assumptions::new(),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new().with_memory(CMemory::new().with_block("heap", 8).store(stored, int32(0))),
        c_call_assign(
            "result",
            "opaque_alias_probe",
            vec![c_pointer_value(queried)],
        ),
        Assumptions::new(),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call_assign(
            "result",
            "opaque_identity_pointer",
            vec![c_pointer_value(argument.clone())],
        ),
        Assumptions::new(),
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
        &Assumptions::new(),
        &path
            .facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::pointer_equal(result.clone(), argument),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
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
        Assumptions::new(),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let mut budget = ExecutionBudget::default();

    let (first_execution, _) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            CState::new(),
            c_call_assign("first", "opaque_identity", vec![c_int32_literal(5)]),
            Assumptions::new(),
            environment.clone(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let first_next = budget.next_verification_variable();
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
            Assumptions::new(),
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
    assert!(budget.next_verification_variable() > first_next);
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
    let execution = prove_c_function_contract_execution_paths_with_environment(
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
    let impostor_execution = prove_c_function_contract_execution_paths_with_environment(
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
        Assumptions::new(),
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

    let extra_assumption = Assumptions::new().assume_condition(
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
        1,
        "an artifact with an unproved entry assumption must not be reused"
    );
    assert!(c_verified_function_contract_claims(&function, &fallback).is_some());
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
        Assumptions::new().assume_condition(branch.clone(), true),
        environment.clone(),
        semantics,
        mode,
    );
    let checked_false = prove_checked_c_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new().assume_condition(branch, false),
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
        1,
        "one side of an entry partition is not a complete contract frontier"
    );
    assert!(c_verified_function_contract_claims(&function, &fallback).is_some());
}

#[test]
fn contract_certification_reuses_definitionally_equal_entry_resources() {
    let unit = CResourceFact::own_token("entry_unit".to_string(), vec![int32(7)]);
    let proof_resources = ResourceContext::new()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit.clone());
    let contract_resources = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit], &Assumptions::new())
        .expect("the contract representation should normalize the two units");
    assert_ne!(proof_resources, contract_resources);
    assert!(resource_contexts_definitionally_equal_with_definitions(
        &[],
        &CMemory::new(),
        &proof_resources,
        &CMemory::new(),
        &contract_resources,
        &Assumptions::new(),
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
        Assumptions::new(),
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
        Assumptions::new(),
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
        1,
        "recursive resource representations must fall back without attempting entry rebasing"
    );
    assert!(
        c_verified_function_contract_claims(&recursive_function, &recursive_execution).is_some()
    );
}

#[test]
fn contract_claim_rejects_same_source_function_with_a_different_contract() {
    let body = c_return(c_int32_literal(0));
    let uncontracted = c_function(CType::Int32, "contract_identity", Vec::new(), body.clone());
    let execution = prove_c_function_contract_execution_paths_with_environment(
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
        assumptions: Assumptions::new(),
        facts: Vec::new(),
        effect_facts: Vec::new(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &Assumptions::new(),
            &[],
            &[obligation],
        )),
    };
    let execution = CFunctionContractExecution {
        execution: SymbolicCExecution {
            paths: vec![path],
            limit: None,
        },
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
        assumptions: Assumptions::new(),
        facts: vec![fact.clone()],
        effect_facts: Vec::new(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &Assumptions::new(),
            &[fact],
            &[obligation],
        )),
    };
    let execution = CFunctionContractExecution {
        execution: SymbolicCExecution {
            paths: vec![path],
            limit: None,
        },
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
        &Assumptions::new(),
    ));

    let external = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let changed_external = after.store(external, int32(9));
    assert!(!crate::kernel::api::c_effect_memories_definitionally_equal(
        &before,
        &changed_external,
        &Assumptions::new(),
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
            &Assumptions::new(),
        )
    );
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
    let execution = prove_c_function_contract_execution_paths_with_environment(
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
    let assumes_true = Assumptions::new().assume_condition(below.clone(), true);
    let assumes_false = Assumptions::new().assume_condition(below.clone(), false);

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
    let first = Assumptions::new().assume_condition(condition.clone(), true);
    let clone = first.clone();
    let idempotent = clone.clone().assume_condition(condition.clone(), true);
    let rebuilt = Assumptions::new().assume_condition(condition.clone(), true);
    let changed = Assumptions::new().assume_condition(condition, false);

    assert!(first.shares_fact_storage_with(&clone));
    assert!(clone.shares_fact_storage_with(&idempotent));
    assert_eq!(first.memo_fingerprint(), rebuilt.memo_fingerprint());
    assert_ne!(first.memo_fingerprint(), changed.memo_fingerprint());
}
