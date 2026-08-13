use super::*;

#[test]
fn scalar_local_updates_share_memory_and_resource_state() {
    let before = CState::new();
    let after = before.clone().with_local("x", int32(1));
    assert!(before.shares_nonlocal_storage_with(&after));
}

#[test]
fn join_state_forgets_changed_scalars_and_memory() {
    let stable_x = int32(Bitvector32Term::Variable(Variable(7)));
    let pointer = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state_zero = CState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(0))
        .with_memory(
            CMemory::new()
                .with_block("heap", 4)
                .store(pointer.clone(), int32(0)),
        )
        .with_resource_context(write_context(pointer.clone(), 0, 1));
    let state_one = CState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(1))
        .with_memory(
            CMemory::new()
                .with_block("heap", 4)
                .store(pointer, int32(1)),
        );
    let stable = BTreeMap::from([("x".to_string(), stable_x.clone())]);

    let abstract_zero = abstract_c_state_for_join(&state_zero, &stable).expect("join abstraction");
    let abstract_one = abstract_c_state_for_join(&state_one, &stable).expect("join abstraction");

    assert_eq!(abstract_zero, abstract_one);
    assert_eq!(abstract_zero.locals().get("x"), Some(&stable_x));
    assert_ne!(abstract_zero.locals().get("y"), Some(&int32(0)));
    assert!(abstract_zero.resources().is_empty());
}

#[test]
fn join_state_abstracts_changed_pointer_locals() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let abstract_left = abstract_c_state_for_join(
        &CState::new().with_local("selected", CValue::Pointer(left)),
        &BTreeMap::new(),
    )
    .expect("pointer join abstraction");
    let abstract_right = abstract_c_state_for_join(
        &CState::new().with_local("selected", CValue::Pointer(right)),
        &BTreeMap::new(),
    )
    .expect("pointer join abstraction");

    assert_eq!(abstract_left, abstract_right);
    let Some(CValue::Pointer(selected)) = abstract_left.locals().get("selected") else {
        panic!("selected should remain a pointer local");
    };
    assert!(selected.has_symbolic_block());
}

#[test]
fn join_state_fresh_variables_do_not_collide_with_symbolic_pointer_blocks() {
    let state = CState::new().with_local(
        "selected",
        CValue::Pointer(Pointer::symbolic(Variable(1_000_000))),
    );
    let abstract_state =
        abstract_c_state_for_join(&state, &BTreeMap::new()).expect("pointer join abstraction");
    let Some(CValue::Pointer(selected)) = abstract_state.locals().get("selected") else {
        panic!("selected should remain a pointer local");
    };

    assert_eq!(selected.block, PointerBlock::Symbolic(Variable(1_000_001)));
}

#[test]
fn symbolic_pointer_blocks_do_not_imply_non_aliasing() {
    let symbolic = Pointer::symbolic(Variable(21_000));
    let concrete = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert!(!pointers_proven_distinct(
        &symbolic,
        &concrete,
        &Assumptions::new()
    ));
    assert_eq!(
        Assumptions::new().decide(&ConditionTerm::pointer_equal(symbolic, concrete)),
        None
    );
}

#[test]
fn concrete_pointer_block_names_cannot_create_symbolic_identity() {
    let misleading_name = Pointer {
        block: "symbolic-pointer:21000".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let heap = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert!(!misleading_name.has_symbolic_block());
    assert!(misleading_name.blocks_proven_distinct(&heap));
}

#[test]
fn concrete_max_executes_without_list_encoding() {
    let state = c_max_state(int32(0), int32(1));
    let theorem =
        prove_c_statement_execution(state.clone(), c_max_body()).expect("max should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement: c_max_body(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );
}

#[test]
fn concrete_max_function_call_preserves_caller_locals() {
    let state = CState::new().with_local("caller", int32(99));
    let function = c_max_function();
    let arguments = vec![c_int32_literal(0), c_int32_literal(1)];
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    )
    .expect("max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: CFunctionOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );
}

#[test]
fn symbolic_max_function_call_reports_branch_facts() {
    let a = Variable(14);
    let b = Variable(15);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = CState::new();
    let function = c_max_function();
    let arguments = vec![
        CExpression::Value(int32(a_bits.clone())),
        CExpression::Value(int32(b_bits.clone())),
    ];
    let execution = prove_symbolic_c_function_execution_paths(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
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
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: CFunctionOutcome::Return {
                    value: int32(b_bits),
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
            Box::new(Proposition::CFunctionExecutes {
                state: state.clone(),
                function,
                arguments,
                outcome: CFunctionOutcome::Return {
                    value: int32(a_bits),
                    state,
                },
            }),
        )
    );
}

#[test]
fn resource_representation_requires_certified_replay_facts_and_exact_state() {
    let certified_result = Bitvector32Term::Variable(Variable(31));
    let other_argument = Bitvector32Term::Variable(Variable(32));
    let desired_result = Bitvector32Term::Variable(Variable(33));
    let state = CState::new();
    let execution = prove_symbolic_c_function_execution_paths(
        state.clone(),
        c_max_function(),
        vec![
            CExpression::Value(int32(other_argument)),
            CExpression::Value(int32(certified_result.clone())),
        ],
        Assumptions::new(),
    );
    let certified_path = &execution.paths()[0];
    let desired_outcome = CFunctionOutcome::Return {
        value: int32(desired_result.clone()),
        state,
    };
    let replay_equality = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(desired_result),
            Box::new(certified_result.clone()),
        ),
        true,
    );

    assert!(
        certify_c_function_execution_path_resource_representation(
            certified_path,
            desired_outcome.clone(),
            &[ExecutionPureFact::certified(replay_equality.clone())],
        )
        .is_some(),
        "a kernel-certified replay equality should align fresh return values"
    );
    assert!(
        certify_c_function_execution_path_resource_representation(
            certified_path,
            desired_outcome,
            &[ExecutionPureFact::new(replay_equality)],
        )
        .is_none(),
        "an untrusted replay fact must not certify a representation change"
    );

    let changed_pointer = Pointer {
        block: "changed".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert!(
        certify_c_function_execution_path_resource_representation(
            certified_path,
            CFunctionOutcome::Return {
                value: int32(certified_result.clone()),
                state: CState::new()
                    .with_memory(CMemory::new().store(changed_pointer.clone(), int32(7))),
            },
            &[],
        )
        .is_none(),
        "a genuinely changed external memory must still be rejected"
    );
    assert!(
        certify_c_function_execution_path_resource_representation(
            certified_path,
            CFunctionOutcome::Return {
                value: int32(certified_result),
                state: CState::new().with_resource_context(write_context(changed_pointer, 0, 1)),
            },
            &[],
        )
        .is_none(),
        "a genuinely changed ghost resource must still be rejected"
    );
}

#[test]
fn execution_provenance_matches_only_equivalent_call_havoc() {
    let assumptions = Assumptions::new();
    let base = CMemory::new().with_block("arc", 16);
    let first_range = memory_range(arc_pointer(0), 0, 1);
    let other_range = memory_range(arc_pointer(4), 0, 1);
    let left = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new().with_memory(base.clone().with_call_memory_havoc(
            Variable(41),
            std::slice::from_ref(&first_range),
            &assumptions,
        )),
    };
    let equivalent = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new().with_memory(base.clone().with_call_memory_havoc(
            Variable(42),
            std::slice::from_ref(&first_range),
            &assumptions,
        )),
    };
    let different = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new().with_memory(base.with_call_memory_havoc(
            Variable(43),
            &[other_range],
            &assumptions,
        )),
    };

    assert!(
        c_function_outcomes_program_state_equal_by_execution_provenance(
            &left,
            &[],
            &equivalent,
            &[],
            &assumptions,
        ),
        "fresh marker names should not distinguish the same call havoc"
    );
    assert!(
        !c_function_outcomes_program_state_equal_by_execution_provenance(
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
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_local("caller", int32(42))
        .with_resource_context(resources.clone());
    let function = c_function(
        CType::Int32,
        "store_and_load",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_load(c_variable("p"))),
        ),
    );
    let arguments = vec![c_pointer_value(pointer.clone())];
    let final_state = CState::new()
        .with_local("caller", int32(42))
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    )
    .expect("store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: CFunctionOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn function_call_does_not_inherit_undeclared_resources() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources);
    let helper = c_function(
        CType::Int32,
        "store_and_load",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_load(c_variable("p"))),
        ),
    );
    let caller = c_function(
        CType::Int32,
        "caller",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_call_assign("result", "store_and_load", vec![c_variable("p")]),
    );
    let arguments = vec![c_pointer_value(pointer.clone())];
    let theorem = prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        arguments.clone(),
        Assumptions::new(),
        CExecutionEnvironment::new().with_function(helper),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("call should report missing callee permission");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments,
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource: write_element(pointer, 0, 1),
            }),
        }
    );
}

#[test]
fn concrete_function_specification_is_native_theorem() {
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![c_int32_literal(0), c_int32_literal(1)],
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        Assumptions::new(),
    )
    .expect("concrete max specification should prove");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionSatisfiesSpecification {
            function,
            specification
        }
    );
}

#[test]
fn symbolic_function_specification_uses_requirements_as_execution_pure_facts() {
    let a = Variable(16);
    let b = Variable(17);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![
            CExpression::Value(int32(a_bits)),
            CExpression::Value(int32(b_bits)),
        ],
        vec![Proposition::ConditionIs(condition.clone(), true)],
        CFunctionOutcome::Return {
            value: int32(Bitvector32Term::Variable(b)),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        Assumptions::new(),
    )
    .expect("symbolic branch specification should prove under condition");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, true)),
            Box::new(Proposition::CFunctionSatisfiesSpecification {
                function,
                specification
            }),
        )
    );
}

#[test]
fn symbolic_max_branch_specifications_include_bounds() {
    let a = Variable(60);
    let b = Variable(61);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let function = c_max_function();
    let arguments = vec![
        CExpression::Value(int32(a_bits.clone())),
        CExpression::Value(int32(b_bits.clone())),
    ];
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());

    let right_specification = c_function_specification(
        CState::new(),
        arguments.clone(),
        vec![Proposition::ConditionIs(condition.clone(), true)],
        CFunctionOutcome::Return {
            value: int32(b_bits.clone()),
            state: CState::new(),
        },
    );
    prove_c_function_satisfies_specification_and_propositions(
        function.clone(),
        right_specification,
        Assumptions::new(),
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(b_bits.clone(), a_bits.clone()),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(b_bits.clone(), b_bits.clone()),
                true,
            ),
        ],
    )
    .expect("under a < b, max returns b and b is >= both inputs");

    let left_specification = c_function_specification(
        CState::new(),
        arguments,
        vec![Proposition::ConditionIs(condition, false)],
        CFunctionOutcome::Return {
            value: int32(a_bits.clone()),
            state: CState::new(),
        },
    );
    prove_c_function_satisfies_specification_and_propositions(
        function,
        left_specification,
        Assumptions::new(),
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(a_bits.clone(), a_bits.clone()),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_greater_equal(a_bits, b_bits), true),
        ],
    )
    .expect("under not (a < b), max returns a and a is >= both inputs");
}

#[test]
fn symbolic_clamp_branch_specifications_include_bounds_under_ordered_limits() {
    let x = Variable(62);
    let lo = Variable(63);
    let hi = Variable(64);
    let x_bits = Bitvector32Term::Variable(x);
    let lo_bits = Bitvector32Term::Variable(lo);
    let hi_bits = Bitvector32Term::Variable(hi);
    let ordered_limits = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lo_bits.clone(), hi_bits.clone()),
        true,
    );
    let below_lo = ConditionTerm::signed_less_than(x_bits.clone(), lo_bits.clone());
    let above_hi = ConditionTerm::signed_greater_than(x_bits.clone(), hi_bits.clone());
    let function = c_function(
        CType::Int32,
        "clamp",
        vec![
            c_parameter("x", CType::Int32),
            c_parameter("lo", CType::Int32),
            c_parameter("hi", CType::Int32),
        ],
        c_if(
            c_less_than(c_variable("x"), c_variable("lo")),
            c_return(c_variable("lo")),
            c_if(
                c_greater_than(c_variable("x"), c_variable("hi")),
                c_return(c_variable("hi")),
                c_return(c_variable("x")),
            ),
        ),
    );
    let arguments = vec![
        CExpression::Value(int32(x_bits.clone())),
        CExpression::Value(int32(lo_bits.clone())),
        CExpression::Value(int32(hi_bits.clone())),
    ];

    for (requires, result, message) in [
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), true),
            ],
            lo_bits.clone(),
            "x below lo returns lo within bounds",
        ),
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), false),
                Proposition::ConditionIs(above_hi.clone(), true),
            ],
            hi_bits.clone(),
            "x above hi returns hi within bounds",
        ),
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), false),
                Proposition::ConditionIs(above_hi.clone(), false),
            ],
            x_bits.clone(),
            "x already in range returns x within bounds",
        ),
    ] {
        let specification = c_function_specification(
            CState::new(),
            arguments.clone(),
            requires,
            CFunctionOutcome::Return {
                value: int32(result.clone()),
                state: CState::new(),
            },
        );
        prove_c_function_satisfies_specification_and_propositions(
            function.clone(),
            specification,
            Assumptions::new(),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(result.clone(), lo_bits.clone()),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(result, hi_bits.clone()),
                    true,
                ),
            ],
        )
        .expect(message);
    }
}

#[test]
fn incomplete_symbolic_function_specification_does_not_prove() {
    let a = Variable(18);
    let b = Variable(19);
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![
            CExpression::Value(int32(Bitvector32Term::Variable(a))),
            CExpression::Value(int32(Bitvector32Term::Variable(b))),
        ],
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(Bitvector32Term::Variable(b)),
            state: CState::new(),
        },
    );

    assert!(
        prove_c_function_satisfies_specification(function, specification, Assumptions::new())
            .is_none()
    );
}

#[test]
fn call_assign_uses_function_environment() {
    let increment = c_function(
        CType::Int32,
        "increment",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_add(c_variable("x"), c_int32_literal(1))),
    );
    let environment = CExecutionEnvironment::new().with_function(increment);
    let state = CState::new();
    let statement = c_seq(
        c_call_assign("result", "increment", vec![c_int32_literal(41)]),
        c_return(c_variable("result")),
    );
    let final_state = CState::new().with_local("result", int32(42));
    let theorem = prove_symbolic_c_execution_with_environment(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("known function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(42),
                state: final_state,
            },
        }
    );
}

#[test]
fn loop_semantics_explicitly_select_verification_or_verified_rules() {
    let state = CState::new().with_local("i", int32(0));
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
    );
    let assumptions = Assumptions::new();
    let (certified, loop_rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            assumptions.clone(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
    let loop_rule = loop_rule.expect("loop verification should produce a rule");
    assert!(certified.paths().iter().all(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(proposition, Proposition::CStatementVerifies { .. })
    }));

    let missing = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(missing.paths().is_empty());

    let mut ignored_rule = loop_rule.clone();
    ignored_rule.paths.clear();
    let base_environment = CExecutionEnvironment::new();
    let cloned_environment = base_environment.clone();
    assert!(base_environment.shares_all_storage_with(&cloned_environment));
    let loop_environment =
        cloned_environment.with_verified_loop_rules([ignored_rule]);
    assert!(base_environment.shares_project_storage_with(&loop_environment));
    let verified_directly = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        loop_environment,
        CExecutionSemantics::EXECUTE_BODIES,
    );
    assert!(!verified_directly.paths().is_empty());

    let reused = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions
            .clone()
            .assume_condition(ConditionTerm::Constant(true), true),
        CExecutionEnvironment::new().with_verified_loop_rules([loop_rule.clone()]),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(reused.paths().len(), certified.paths().len());
    assert!(reused.paths().iter().all(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(proposition, Proposition::CStatementVerifies { .. })
    }));

    let mismatched = prove_symbolic_c_statement_verification_paths_with_environment(
        state.with_local("unrelated", int32(0)),
        statement,
        assumptions,
        CExecutionEnvironment::new().with_verified_loop_rules([loop_rule]),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(mismatched.paths().is_empty());
}

#[test]
fn perpetual_loop_verifies_safety_without_minting_a_concrete_exit() {
    let state = CState::new();
    let statement = c_while_with_invariant_checks(
        c_int32_literal(1),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
            Some("perpetual loop entry".to_string()),
            Some("perpetual loop preservation".to_string()),
        )],
        c_skip(),
    );
    let (verification, rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
    assert!(rule.is_some());
    assert_eq!(verification.paths().len(), 1);
    let mut proposition = verification.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::CStatementVerifies {
            outcome: CStatementOutcome::VerificationDiverges,
            ..
        }
    ));

    let concrete = prove_symbolic_c_execution_paths(state, statement, Assumptions::new());
    assert!(concrete.paths().is_empty());
    assert!(concrete.limit().is_some());
}

#[test]
fn loop_exit_rule_with_proven_preservation_does_not_reverify_the_body() {
    let state = CState::new().with_local("i", int32(0));
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_int32_literal(u32::MAX)),
    );
    let assumptions = Assumptions::new();
    let automatic = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    );
    assert!(
        automatic
            .paths()
            .iter()
            .flat_map(SymbolicCExecutionPath::obligations)
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );

    let (after_proof, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        false,
        true,
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
    let state = CState::new().with_local("i", int32(u32::MAX));
    let statement = c_while_with_invariant_checks(
        c_int32_literal(1),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_int32_literal(u32::MAX)),
    );
    let (execution, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases(
        state,
        statement,
        Assumptions::new(),
        CExecutionEnvironment::new(),
        true,
        false,
    );

    assert!(loop_rule.is_none());
    let obligations = execution
        .paths()
        .iter()
        .flat_map(SymbolicCExecutionPath::obligations)
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
    let state = CState::new();
    let statement = c_call_assign("result", "missing", Vec::new());
    let theorem = prove_symbolic_c_execution_with_environment(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("unknown function should produce a single runtime-error path");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                "missing".to_string(),
            )),
        }
    );
}

#[test]
fn while_loop_executes_concrete_countdown() {
    let state = CState::new().with_local("x", int32(3));
    let loop_statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        Vec::new(),
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let statement = c_seq(loop_statement, c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(0));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete countdown loop should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: final_state,
            },
        }
    );
}

#[test]
fn loop_budget_exhaustion_is_executor_failure_not_c_runtime_error() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_while(
        c_int32_literal(1),
        Vec::new(),
        c_assign("x", c_variable("x")),
    );
    let budget = ExecutionBudget::new().with_loop_unrolls(2);
    let execution = prove_symbolic_c_execution_paths_with_budget(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        budget.clone(),
    );

    assert_eq!(execution.limit(), Some(ExecutionLimit::LoopUnrolls));
    assert_eq!(execution.paths(), &[] as &[SymbolicCExecutionPath]);
    assert!(
        prove_symbolic_c_execution_with_budget(state, statement, Assumptions::new(), budget,)
            .is_none()
    );
}

#[test]
fn executor_budgets_cap_steps_calls_and_paths() {
    let state = CState::new();
    let statement = c_return(c_int32_literal(1));

    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            ExecutionBudget::new().with_statement_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::StatementSteps)
    );
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement,
            Assumptions::new(),
            ExecutionBudget::new().with_expression_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::ExpressionSteps)
    );

    let function = c_function(
        CType::Int32,
        "id",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    );
    assert_eq!(
        prove_symbolic_c_function_execution_paths_with_budget(
            CState::new(),
            function,
            vec![c_int32_literal(1)],
            Assumptions::new(),
            ExecutionBudget::new().with_function_calls(0),
        )
        .limit(),
        Some(ExecutionLimit::FunctionCalls)
    );

    let a = Variable(75);
    let b = Variable(76);
    let branchy_statement = c_return(c_less_than(
        CExpression::Value(int32(Bitvector32Term::Variable(a))),
        CExpression::Value(int32(Bitvector32Term::Variable(b))),
    ));
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state,
            branchy_statement,
            Assumptions::new(),
            ExecutionBudget::new().with_paths(3),
        )
        .limit(),
        Some(ExecutionLimit::Paths)
    );
}

#[test]
fn while_invariant_is_proof_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invariant = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let state = CState::new().with_local("x", int32(0));
    let statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        vec![invariant.clone()],
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("false loop should execute under invariant obligation");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(invariant),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(state),
            }),
        )
    );
}
