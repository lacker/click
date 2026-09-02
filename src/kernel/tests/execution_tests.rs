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
        .with_resource_context(own_memory_context(pointer.clone(), 0, 1));
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
fn sibling_join_abstraction_is_deterministic_after_a_nested_join() {
    let nested_source = CState::new().with_local("y", int32(0));
    let nested = abstract_c_state_for_join(&nested_source, &BTreeMap::new())
        .expect("nested join abstraction");
    let sibling = CState::new().with_local("y", int32(1));
    let states = [&nested, &sibling];

    let abstract_nested = abstract_c_state_for_join_across(&nested, &states, &BTreeMap::new())
        .expect("outer nested-arm abstraction");
    let abstract_sibling = abstract_c_state_for_join_across(&sibling, &states, &BTreeMap::new())
        .expect("outer sibling abstraction");

    assert_eq!(abstract_nested, abstract_sibling);

    let inner_empty = abstract_c_state_for_join(&CState::new(), &BTreeMap::new())
        .expect("inner empty-state abstraction");
    let raw_empty = CState::new();
    let empty_states = [&inner_empty, &raw_empty];
    let outer_nested =
        abstract_c_state_for_join_across(&inner_empty, &empty_states, &BTreeMap::new())
            .expect("outer nested empty-state abstraction");
    let outer_raw = abstract_c_state_for_join_across(&raw_empty, &empty_states, &BTreeMap::new())
        .expect("outer raw empty-state abstraction");
    assert_eq!(outer_nested, outer_raw);
    assert_ne!(outer_nested, inner_empty);
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
        &PureFactContext::new()
    ));
    assert_eq!(
        PureFactContext::new().decide(&ConditionTerm::pointer_equal(symbolic, concrete)),
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
        PureFactContext::new(),
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
fn execution_provenance_matches_only_equivalent_call_havoc() {
    let assumptions = PureFactContext::new();
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
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
        PureFactContext::new(),
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
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
        PureFactContext::new(),
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
                resource: own_memory_fact(pointer, 0, 1),
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
        PureFactContext::new(),
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
        PureFactContext::new(),
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
        PureFactContext::new(),
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
        PureFactContext::new(),
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
            PureFactContext::new(),
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
        prove_c_function_satisfies_specification(function, specification, PureFactContext::new())
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
        PureFactContext::new(),
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
    let assumptions = PureFactContext::new();
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
    let loop_environment = cloned_environment.with_verified_loop_rules([ignored_rule]);
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
fn statement_checks_share_one_execution_environment_variable_index() {
    let reserved = Variable(1_000_000);
    let indexed_function = c_function(
        CType::Int32,
        "indexed",
        Vec::new(),
        c_return(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(reserved),
        ))),
    );
    let environment = CExecutionEnvironment::new().with_function(indexed_function);
    let cloned_before_initialization = environment.clone();
    assert_eq!(environment.variable_index.build_count(), 0);

    for candidate in [environment.clone(), cloned_before_initialization] {
        let execution = prove_symbolic_c_statement_verification_paths_with_environment(
            CState::new(),
            c_skip(),
            PureFactContext::new(),
            candidate,
            CExecutionSemantics::EXECUTE_BODIES,
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
    let mut generator = KernelVariableGenerator::fresh_for_with_shared_reservations(
        1_000_000,
        BTreeSet::from([Variable(1_000_001)]),
        indexed,
    );
    assert_eq!(
        generator.next(),
        Variable(1_000_002),
        "fresh variables must avoid both shared environment and local reservations"
    );

    let changed = environment.with_function(c_function(
        CType::Int32,
        "changed",
        Vec::new(),
        c_return(CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(1_000_001)),
        ))),
    ));
    assert_eq!(changed.variable_index.build_count(), 0);
    let changed_index = execution_environment_variable_index(&changed);
    assert!(changed_index.contains(&reserved));
    assert!(changed_index.contains(&Variable(1_000_001)));
    assert_eq!(changed.variable_index.build_count(), 1);
}

#[test]
fn environment_variable_scans_do_not_multiply_by_statement_count() {
    for size in [8, 32, 128, 512] {
        let mut body = c_return(CExpression::Value(int32(0)));
        for index in (0..size).rev() {
            body = c_seq(
                c_assign(
                    "symbolic",
                    CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(
                        1_000_000 + index,
                    )))),
                ),
                body,
            );
        }
        let environment = CExecutionEnvironment::new().with_function(c_function(
            CType::Int32,
            format!("indexed_{size}"),
            Vec::new(),
            body,
        ));

        for _ in 0..size {
            let execution = prove_symbolic_c_statement_verification_paths_with_environment(
                CState::new(),
                c_skip(),
                PureFactContext::new(),
                environment.clone(),
                CExecutionSemantics::EXECUTE_BODIES,
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
            PureFactContext::new(),
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

    let concrete = prove_symbolic_c_execution_paths(state, statement, PureFactContext::new());
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
    let assumptions = PureFactContext::new();
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
        PureFactContext::new(),
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
        PureFactContext::new(),
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
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
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
        PureFactContext::new(),
        budget.clone(),
    );

    assert_eq!(execution.limit(), Some(ExecutionLimit::LoopUnrolls));
    assert_eq!(execution.paths(), &[] as &[SymbolicCExecutionPath]);
    assert!(
        prove_symbolic_c_execution_with_budget(state, statement, PureFactContext::new(), budget,)
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
            PureFactContext::new(),
            ExecutionBudget::new().with_statement_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::StatementSteps)
    );
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement,
            PureFactContext::new(),
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
            PureFactContext::new(),
            ExecutionBudget::new().with_function_calls(0),
        )
        .limit(),
        Some(ExecutionLimit::FunctionCalls)
    );

    let straight_line = (0..128).fold(c_return(c_int32_literal(1)), |tail, _| {
        c_seq(CStatement::Skip, tail)
    });
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
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

    let branchy_statement = c_if(
        CExpression::Value(int32(Bitvector32Term::Variable(Variable(75)))),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
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
        .map(|_| c_assign("x", c_variable("x")))
        .chain(std::iter::once(c_return(c_variable("x"))))
        .collect::<Vec<_>>();
    while statements.len() > 1 {
        let mut next = Vec::with_capacity(statements.len().div_ceil(2));
        let mut pairs = statements.into_iter();
        while let Some(first) = pairs.next() {
            next.push(match pairs.next() {
                Some(second) => c_seq(first, second),
                None => first,
            });
        }
        statements = next;
    }
    let function = c_function(
        CType::Int32,
        "large_identity",
        vec![c_parameter("x", CType::Int32)],
        statements.pop().expect("nonempty function body"),
    );
    let arguments = vec![c_int32_literal(1)];

    let fixed_budget_execution =
        prove_symbolic_c_function_verification_paths_with_environment_and_budget(
            CState::new(),
            function.clone(),
            arguments.clone(),
            PureFactContext::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
            ExecutionBudget::default(),
        );
    assert_eq!(
        fixed_budget_execution.limit(),
        Some(ExecutionLimit::ExpressionSteps),
        "explicit budgets remain exact and still bound evaluator work"
    );

    let source_sized_execution = prove_symbolic_c_function_verification_paths_with_environment(
        CState::new(),
        function,
        arguments,
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
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
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
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
