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
    state.counted_population_sum(
        "pool_object",
        &[Some(int32(pool)), None],
        &PureFactContext::new(),
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
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
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
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

fn vacuous_forall_contract(requires_body: SpecProposition) -> CFunction {
    c_function(
        CType::Int32,
        "vac",
        vec![c_parameter("n", CType::Int32)],
        c_return(c_variable("n")),
    )
    .with_contract(
        vec![SpecProposition::ForAllInt32 {
            name: "k".to_string(),
            variable: Variable(919_777),
            body: Box::new(requires_body),
        }],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(7)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    )
}

fn constant_bounds(lo: u32, hi: u32) -> SpecProposition {
    SpecProposition::And(
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::Value(int32(lo)),
            operator: CComparisonOperator::LessEqual,
            right: SpecExpression::CExpression(c_variable("k")),
        }),
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("k")),
            operator: CComparisonOperator::LessThan,
            right: SpecExpression::Value(int32(hi)),
        }),
    )
}

fn n_is_seven() -> SpecProposition {
    SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("n")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    }
}

fn certify_vacuous_forall_ensure(function: &CFunction) -> Option<CVerifiedFunctionContractClaim> {
    let execution = prove_c_function_contract_execution_paths_with_environment(
        CState::new(),
        function.clone(),
        vec![CExpression::Value(int32(Bitvector32Term::Variable(
            Variable(919_778),
        )))],
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    c_verified_function_contract_claim(function, CFunctionContractClaimKey::Ensure(0), &execution)
}

/// `forall k. (0 <= k < 3) -> ((5 <= k < 10) -> n == 7)` is satisfied by every
/// `n`: no `k` meets both bounds. Instantiating it must not inject `n == 7`,
/// so `ensures result == 7` on `return n` must not certify.
#[test]
fn finite_forall_instantiation_checks_every_bound_premise() {
    let function = vacuous_forall_contract(SpecProposition::Implies(
        Box::new(constant_bounds(0, 3)),
        Box::new(SpecProposition::Implies(
            Box::new(constant_bounds(5, 10)),
            Box::new(n_is_seven()),
        )),
    ));
    assert!(
        certify_vacuous_forall_ensure(&function).is_none(),
        "a universal with disjoint bound premises must not certify its conclusion"
    );
}

/// The same instantiation still works when the single bound is satisfiable:
/// `forall k. (0 <= k < 1) -> n == 7` really does give `n == 7`.
#[test]
fn finite_forall_instantiation_still_uses_a_satisfiable_bound() {
    let function = vacuous_forall_contract(SpecProposition::Implies(
        Box::new(constant_bounds(0, 1)),
        Box::new(n_is_seven()),
    ));
    assert!(
        certify_vacuous_forall_ensure(&function).is_some(),
        "a satisfiable bounded universal should still instantiate its conclusion"
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
    };
    let execution = CFunctionContractExecution {
        reuse_diagnostic: None,
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
    };
    let execution = CFunctionContractExecution {
        reuse_diagnostic: None,
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
/// `outcome`. The condition is never evaluated by the sealer, so the
/// theorem's shape is what these tests exercise.
fn early_return_sealing_inputs(
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

fn seal_early_return(
    candidates: &CFunctionExecutionCandidates,
    function: &CFunction,
    trace: crate::kernel::proof::PersistentSequence<crate::kernel::proof::CheckedExecutionEvent>,
) -> Result<CCheckedFunctionExecution, crate::instrumentation::SealRefusal> {
    crate::kernel::api::checked_c_function_execution_from_proof_evidence(
        candidates,
        function,
        None,
        &[trace],
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    )
}

#[test]
fn sealing_accepts_a_return_that_leaves_source_behind_it() {
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
    let (candidates, function, trace) = early_return_sealing_inputs(returning);
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let sealed = seal_early_return(&candidates, &function, trace)
        .expect("a returning `if` seals although `return 1` follows it in the source");
    assert_eq!(sealed.execution.paths().len(), 1);
    let mut conclusion = sealed.execution.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(
        matches!(
            conclusion,
            Proposition::CFunctionVerifies { outcome, .. } if outcome == candidates.paths()[0].outcome()
        ),
        "the sealed theorem concludes the candidate's outcome: {conclusion:?}"
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "sealing composes retained theorems; it never executes the body"
    );
}

#[test]
fn sealing_still_refuses_a_trace_that_stops_before_the_path_ends() {
    let entry_state = c_function_entry_state(
        &CState::new(),
        &c_function(CType::Int32, "early", Vec::new(), CStatement::Skip),
        &[],
    )
    .expect("entry state");
    // A `Normal` outcome for the `if` leaves `return 1` unexecuted: no
    // retained theorem covers it, so the path has no completed outcome.
    let (candidates, function, trace) =
        early_return_sealing_inputs(CStatementOutcome::Normal(entry_state.clone()));
    assert_eq!(
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::IncompleteTrace)
    );

    // A trace that continues past its returning statement is refused too.
    let returning = CStatementOutcome::Return {
        value: int32(0),
        state: entry_state.clone(),
    };
    let (candidates, function, mut trace) = early_return_sealing_inputs(returning);
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
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::IncompleteTrace)
    );
}

/// `int32 early() { if (0 < 1) { return 0; } return 1; }` whose one retained
/// statement theorem has `premises` and whose candidate path retains `facts`.
fn early_return_sealing_inputs_with_facts(
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
fn sealing_finds_a_theorem_premise_inside_a_retained_conjunction() {
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
    let (candidates, function, trace) = early_return_sealing_inputs_with_facts(
        vec![nonnegative.clone(), bounded.clone()],
        vec![invariant.clone()],
    );
    seal_early_return(&candidates, &function, trace)
        .expect("each conjunct of a retained conjunction is a retained premise");

    // A disjunction retains neither side, and a premise mentioning a
    // different variable is not retained by a conjunction that does not
    // contain it.
    let disjunction = Proposition::Or(Box::new(nonnegative.clone()), Box::new(bounded.clone()));
    let (candidates, function, trace) =
        early_return_sealing_inputs_with_facts(vec![nonnegative.clone()], vec![disjunction]);
    assert_eq!(
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::UnretainedPremise)
    );
    let other = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(Variable(1_000_001)),
            Bitvector32Term::Constant(3),
        ),
        true,
    );
    let (candidates, function, trace) =
        early_return_sealing_inputs_with_facts(vec![other], vec![invariant]);
    assert_eq!(
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::UnretainedPremise)
    );
}

/// `int32 skipping() { ; return 1; }`: a body whose first statement is the
/// `Skip` an empty `if` arm leaves behind, with the given retained trace.
fn skip_sealing_inputs(
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
fn sealing_passes_over_skip_on_either_side() {
    let entry = CState::new();
    // The driver stepped through the `Skip`: it consumes the source's `Skip`.
    let (candidates, function, trace) = skip_sealing_inputs(vec![
        skip_theorem(entry.clone()),
        return_one_theorem(entry.clone()),
    ]);
    seal_early_return(&candidates, &function, trace)
        .expect("a `Skip` theorem consumes the `Skip` at the head of the source");
    // The driver completed the empty arm in place: the source's `Skip` is
    // passed over before the real statement is matched.
    let (candidates, function, trace) =
        skip_sealing_inputs(vec![return_one_theorem(entry.clone())]);
    seal_early_return(&candidates, &function, trace)
        .expect("a `Skip` left in the source is passed over");
    // An extra `Skip` theorem touches nothing.
    let (candidates, function, trace) = skip_sealing_inputs(vec![
        skip_theorem(entry.clone()),
        skip_theorem(entry.clone()),
        return_one_theorem(entry.clone()),
    ]);
    seal_early_return(&candidates, &function, trace).expect("a second `Skip` theorem is a no-op");
    // A `Skip` theorem must still describe the sealed state. (The first
    // event names the trace's entry state, so the mismatch is placed second.)
    let elsewhere = CState::new().with_local("x", int32(1));
    let (candidates, function, trace) = skip_sealing_inputs(vec![
        skip_theorem(entry.clone()),
        skip_theorem(elsewhere),
        return_one_theorem(entry),
    ]);
    assert_eq!(
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::StateMismatch)
    );
}

#[test]
fn sealing_accepts_a_case_arm_recorded_after_the_return() {
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
    let (candidates, function, trace) = early_return_sealing_inputs(returning);
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
    crate::kernel::api::checked_c_function_execution_from_proof_evidence(
        &forked,
        &function,
        None,
        &traces,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    )
    .expect("both forked paths seal with their case arms");
    // One arm alone is not exhaustive.
    let one_arm = c_function_execution_candidates_from_outcomes(
        candidates.state().clone(),
        function.clone(),
        Vec::new(),
        vec![copy()],
    );
    assert_eq!(
        crate::kernel::api::checked_c_function_execution_from_proof_evidence(
            &one_arm,
            &function,
            None,
            &traces[..1],
            PureFactContext::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            CFunctionContractExecutionMode::VerifyLoops,
        )
        .err(),
        Some(crate::instrumentation::SealRefusal::CasePartition)
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
    let (sealed, _) = crate::kernel::functions::contract_exit_outcome(
        &caller_state,
        &function,
        &[],
        returning,
        Vec::new(),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("no execution limit")
    .expect("no runtime error");
    assert_eq!(sealed, plain);
}

#[test]
fn sealing_takes_a_premise_from_the_retained_context() {
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
        early_return_sealing_inputs_with_facts(vec![bound.clone()], Vec::new());
    assert_eq!(
        seal_early_return(&candidates, &function, trace.clone()).err(),
        Some(crate::instrumentation::SealRefusal::UnretainedPremise)
    );
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        PureFactContext::new().assume_proposition(bound),
    ));
    seal_early_return(&candidates, &function, trace)
        .expect("the retained context vouches for the theorem's premise");
    // A context that does not hold the premise vouches for nothing.
    let other = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Variable(Variable(1_000_071)),
            Bitvector32Term::Constant(5),
        ),
        true,
    );
    let (candidates, function, mut trace) =
        early_return_sealing_inputs_with_facts(vec![other], Vec::new());
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
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::UnretainedPremise)
    );
}

#[test]
fn sealing_covers_a_loadability_premise_from_the_retained_context() {
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
            ConditionTerm::signed_less_equal(n, Bitvector32Term::Constant(2_147_483_647)),
            true,
        );
    let (candidates, function, mut trace) =
        early_return_sealing_inputs_with_facts(vec![requirement.clone()], Vec::new());
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        context.clone(),
    ));
    seal_early_return(&candidates, &function, trace)
        .expect("the caller's wider loadable range covers the callee's requirement");

    // A requirement outside the covered range is refused.
    let outside = Proposition::CMemoryLoadable {
        memory: CMemory::new().with_block("local:value", 4),
        base: p.offset_by_int32_elements(Bitvector32Term::Variable(Variable(2))),
        bytes: Bitvector32Term::Constant(4),
    };
    let (candidates, function, mut trace) =
        early_return_sealing_inputs_with_facts(vec![outside], Vec::new());
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Context(
        context,
    ));
    assert_eq!(
        seal_early_return(&candidates, &function, trace).err(),
        Some(crate::instrumentation::SealRefusal::UnretainedPremise)
    );
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
    assert_eq!(
        record(
            Theorem::new(verifies(entry_state.clone(), c_return(c_int32_literal(1)))),
            PureFactContext::new(),
        ),
        Err("statement evidence does not prove the frontier's next source statement")
    );
    let elsewhere = entry_state.clone().with_local("x", int32(1));
    assert_eq!(
        record(
            Theorem::new(verifies(elsewhere, branch.clone())),
            PureFactContext::new(),
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
        Box::new(verifies(entry_state, branch)),
    ));
    assert_eq!(
        record(conditional.clone(), PureFactContext::new()),
        Err("evidence assumes a premise the proof did not retain")
    );
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
        ),
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
        ),
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
        ),
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
    assert_eq!(
        core.record_statement_transition(
            &function,
            &[],
            returning(c_return(c_int32_literal(0)), 0),
            PureFactContext::new(),
            &[],
            &[],
        ),
        Err("statement evidence does not prove the frontier's next source statement")
    );
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
fn a_completed_proof_object_yields_the_sealed_execution() {
    // Completion composes the checked traces; it agrees with the
    // end-of-proof walk on the same evidence, and an open trace yields
    // nothing.
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
    let (candidates, function, trace) = early_return_sealing_inputs(returning);
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
    let sealed = seal_early_return(&candidates, &function, core.execution_evidence[0].clone())
        .expect("the same evidence seals");
    assert_eq!(completed.paths(), sealed.paths());

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
