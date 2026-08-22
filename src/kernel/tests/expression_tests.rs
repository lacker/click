use super::*;

#[test]
fn bitwise_xor_normalizes_swap_identities() {
    let x = Bitvector32Term::Variable(Variable(1));
    let y = Bitvector32Term::Variable(Variable(2));
    let x_xor_y = Bitvector32Term::bitwise_xor(x.clone(), y.clone());
    let recovered_x = Bitvector32Term::bitwise_xor(y.clone(), x_xor_y.clone());
    let recovered_y = Bitvector32Term::bitwise_xor(x_xor_y, x.clone());

    assert_eq!(recovered_x, x);
    assert_eq!(recovered_y, y);
}
#[test]
fn signed_add_overflow_is_native_undefined_behavior() {
    let state = CState::new();
    let theorem = prove_c_expression_evaluation(
        state.clone(),
        c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
    )
    .expect("concrete add should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn condition_evaluation_certifies_c_truthiness_directly() {
    let state = CState::new();
    let condition = c_less_than(c_int32_literal(1), c_int32_literal(2));
    let evaluation = prove_symbolic_c_condition_evaluation(
        state.clone(),
        condition.clone(),
        PureFactContext::new(),
    );

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state,
            condition,
            outcome: CConditionOutcome::Value(true),
        }
    );
}

#[test]
fn void_truthiness_is_an_explicit_type_error() {
    let state = CState::new();
    let condition = c_void_value();
    let evaluation = prove_symbolic_c_condition_evaluation(
        state.clone(),
        condition.clone(),
        PureFactContext::new(),
    );

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state: state.clone(),
            condition,
            outcome: CConditionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        }
    );

    for expression in [
        c_not(c_void_value()),
        c_and(c_void_value(), c_int32_literal(1)),
        c_or(c_void_value(), c_int32_literal(1)),
    ] {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("invalid void truthiness should retain its runtime-error frontier");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            }
        );
    }
}

#[test]
fn void_local_declaration_is_an_explicit_type_error() {
    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_declare("invalid", CType::Void),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("invalid void declarations should execute to a type error");

    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    );

    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_if(c_void_value(), CStatement::Skip, CStatement::Skip),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a void condition should execute to a type error");
    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    );
}

#[test]
fn symbolic_condition_evaluation_exposes_both_truthiness_paths() {
    let x = Variable(90);
    let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(x)));
    let condition = c_greater_equal(c_variable("x"), c_int32_literal(0));
    let evaluation =
        prove_symbolic_c_condition_evaluation(state, condition, PureFactContext::new());

    let outcomes = evaluation
        .paths()
        .iter()
        .map(
            |path| match path.theorem().proposition().peel_implications() {
                Proposition::CConditionEvaluates { outcome, .. } => outcome.clone(),
                proposition => panic!("unexpected condition theorem {proposition:?}"),
            },
        )
        .collect::<BTreeSet<_>>();
    assert_eq!(
        outcomes,
        BTreeSet::from([
            CConditionOutcome::Value(false),
            CConditionOutcome::Value(true),
        ])
    );
}

#[test]
fn int32_subtraction_is_native() {
    let state = CState::new();
    let statement = c_return(c_subtract(c_int32_literal(7), c_int32_literal(2)));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("concrete subtraction should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state,
            },
        }
    );
}

#[test]
fn nonnegative_ordered_subtraction_does_not_overflow() {
    let position = Bitvector32Term::Variable(Variable(24));
    let length = Bitvector32Term::Variable(Variable(25));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(position.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(length.clone(), position.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(length, position)),
        Some(false)
    );
}

#[test]
fn signed_subtract_overflow_is_native_undefined_behavior() {
    let state = CState::new();
    let theorem = prove_c_expression_evaluation(
        state.clone(),
        c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
    )
    .expect("concrete subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn int32_comparisons_return_c_int32_zero_or_one() {
    let state = CState::new();
    let examples = [
        (
            c_less_equal(c_int32_literal(2), c_int32_literal(2)),
            int32(1),
        ),
        (
            c_greater_than(c_int32_literal(3), c_int32_literal(2)),
            int32(1),
        ),
        (
            c_greater_equal(c_int32_literal(2), c_int32_literal(3)),
            int32(0),
        ),
        (c_equal(c_int32_literal(4), c_int32_literal(4)), int32(1)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("comparison should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn pointer_equality_returns_c_int32_zero_or_one() {
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let other = Pointer {
        block: "other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(p))
        .with_local("same", CValue::Pointer(same))
        .with_local("next", CValue::Pointer(next))
        .with_local("other", CValue::Pointer(other));
    let examples = [
        (c_equal(c_variable("p"), c_variable("same")), int32(1)),
        (c_equal(c_variable("p"), c_variable("next")), int32(0)),
        (c_equal(c_variable("p"), c_variable("other")), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("pointer equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn spec_pointer_equality_lowers_to_a_pure_fact() {
    let left = Pointer::symbolic(Variable(22_100));
    let right = Pointer::symbolic(Variable(22_101));
    let equality = ConditionTerm::pointer_equal(left.clone(), right.clone());

    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left.clone()),
            CComparisonOperator::Equal,
            &CValue::Pointer(right.clone()),
        ),
        Some(Proposition::ConditionIs(equality.clone(), true)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left.clone()),
            CComparisonOperator::NotEqual,
            &CValue::Pointer(right),
        ),
        Some(Proposition::ConditionIs(equality, false)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left),
            CComparisonOperator::LessThan,
            &CValue::Int32(Bitvector32Term::Constant(0)),
        ),
        None,
    );
}

#[test]
fn symbolic_pointer_truthiness_keeps_null_and_nonnull_paths() {
    let paths = c_truthiness_paths(
        CValue::Pointer(Pointer::symbolic(Variable(22_000))),
        Vec::new(),
        Vec::new(),
        &PureFactContext::new(),
    );

    assert_eq!(paths.len(), 2);
    assert!(paths.iter().any(|path| path.is_true));
    assert!(paths.iter().any(|path| !path.is_true));
}

#[test]
fn pointer_equality_accepts_int32_zero_as_null_pointer_constant() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("nullp", CValue::Pointer(null))
        .with_local("p", CValue::Pointer(nonnull));
    let examples = [
        (c_equal(c_variable("nullp"), c_int32_literal(0)), int32(1)),
        (c_equal(c_int32_literal(0), c_variable("nullp")), int32(1)),
        (c_equal(c_variable("p"), c_int32_literal(0)), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("null equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    let invalid = c_equal(c_variable("p"), c_int32_literal(1));
    let theorem = prove_c_expression_evaluation(state.clone(), invalid.clone())
        .expect("invalid pointer equality should evaluate");
    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: invalid,
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        }
    );
}

#[test]
fn not_equal_and_not_return_c_int32_zero_or_one() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("nullp", CValue::Pointer(null))
        .with_local("p", CValue::Pointer(p))
        .with_local("same", CValue::Pointer(same))
        .with_local("next", CValue::Pointer(next));
    let examples = [
        (
            c_not_equal(c_int32_literal(4), c_int32_literal(5)),
            int32(1),
        ),
        (c_not_equal(c_variable("p"), c_variable("same")), int32(0)),
        (c_not_equal(c_variable("p"), c_variable("next")), int32(1)),
        (
            c_not_equal(c_variable("nullp"), c_int32_literal(0)),
            int32(0),
        ),
        (c_not(c_int32_literal(0)), int32(1)),
        (c_not(c_int32_literal(7)), int32(0)),
        (c_not(c_variable("nullp")), int32(1)),
        (c_not(c_variable("p")), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("logical expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn logical_and_or_short_circuit_right_operand() {
    let invalid_pointer = Pointer {
        block: "missing".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invalid_load = c_typed_load(c_pointer_value(invalid_pointer), CType::Int32);
    let state = CState::new().with_resource_context(read_context(
        Pointer {
            block: "missing".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let examples = [
        (c_and(c_int32_literal(0), invalid_load.clone()), int32(0)),
        (c_or(c_int32_literal(1), invalid_load.clone()), int32(1)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("short-circuit expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    assert!(
        prove_c_expression_evaluation(
            state.clone(),
            c_and(c_int32_literal(1), invalid_load.clone()),
        )
        .is_none()
    );
    assert!(prove_c_expression_evaluation(state, c_or(c_int32_literal(0), invalid_load)).is_none());
}

#[test]
fn untyped_pointer_operations_report_indeterminate_pointee_type() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer_value = || c_pointer_value(pointer.clone());
    let expressions = [
        c_load(pointer_value()),
        c_index(pointer_value(), c_int32_literal(1)),
        c_add(pointer_value(), c_int32_literal(1)),
        c_add(c_int32_literal(1), pointer_value()),
    ];

    for expression in expressions {
        let theorem = prove_c_expression_evaluation(CState::new(), expression.clone())
            .expect("an untyped pointer operation should produce an explicit model error");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: CState::new(),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType,),
            }
        );
    }
}

#[test]
fn symbolic_pointer_equality_reports_branch_facts() {
    let offset = Variable(80);
    let left = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Variable(offset),
    };
    let condition = ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone());
    let state = CState::new()
        .with_local("p", CValue::Pointer(left))
        .with_local("q", CValue::Pointer(right));
    let statement = c_if(
        c_equal(c_variable("p"), c_variable("q")),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement: statement.clone(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state: state.clone(),
            },
        }
    );
    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition, false)]
    );
    assert_eq!(
        execution.paths()[1]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state,
            },
        }
    );
}

#[test]
fn if_uses_c_int32_truthiness() {
    let state = CState::new();
    let statement = c_if(
        c_int32_literal(7),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("nonzero int32 condition should take then branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );

    let state = CState::new();
    let statement = c_if(
        c_int32_literal(0),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("zero int32 condition should take else branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state,
            },
        }
    );
}

#[test]
fn assignment_and_sequence_update_native_state() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_seq(c_assign("x", c_int32_literal(2)), c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(2));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn store_then_load_threads_native_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources.clone());
    let statement = c_seq(
        c_typed_store(
            c_pointer_value(pointer.clone()),
            c_int32_literal(9),
            CType::Int32,
        ),
        c_return(c_typed_load(c_pointer_value(pointer.clone()), CType::Int32)),
    );
    let final_state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("store then load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn read_element_permits_symbolic_external_load_from_incomplete_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(pointer.clone()))
        .with_resource_context(read_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                // The symbolic read is canonical at creation: its load
                // variable, which names this load.
                value: int32(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(pointer),
                ))),
                state,
            },
        }
    );
}

#[test]
fn block_backed_store_then_load_needs_no_memory_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 16);
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let statement = c_seq(
        c_typed_store(
            c_pointer_value(pointer.clone()),
            c_int32_literal(9),
            CType::Int32,
        ),
        c_return(c_typed_load(c_pointer_value(pointer.clone()), CType::Int32)),
    );
    let final_state = CState::new()
        .with_memory(memory.store(pointer, int32(9)))
        .with_resource_context(resources);
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("in-range block store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn block_backed_missing_load_returns_symbolic_value_without_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new().with_block("block", 16);
    let state = CState::new()
        .with_local("p", CValue::Pointer(pointer.clone()))
        .with_memory(memory.clone())
        .with_resource_context(read_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("in-range missing load should produce symbolic value");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(pointer)
                ))),
                state,
            },
        }
    );
}

#[test]
fn pointer_addition_scales_int32_offsets_for_loads() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), int32(23));
    let resources = read_context(base.clone(), 1, 2);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("pointer arithmetic load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(23),
                state: CState::new()
                    .with_local(
                        "p",
                        CValue::Pointer(Pointer {
                            block: "block".into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                    )
                    .with_memory(
                        CMemory::new()
                            .with_block("block", 16)
                            .store(second, int32(23),),
                    )
                    .with_resource_context(resources),
            },
        }
    );
}

#[test]
fn read_element_permits_pointer_addition_load_beyond_memory_block() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let derived = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new().with_block("block", 4);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_memory(memory.clone())
        .with_resource_context(read_context(base, 1, 2));
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(derived),
                ))),
                state,
            },
        }
    );
}

#[test]
fn fixed_bound_store_loop_touches_only_valid_pointer_range() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 12);
    let resources = write_context(base.clone(), 0, 3);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_local("i", int32(0))
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let loop_statement = c_while(
        c_less_than(c_variable("i"), c_int32_literal(3)),
        Vec::new(),
        c_seq(
            c_store(c_add(c_variable("p"), c_variable("i")), c_variable("i")),
            c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
        ),
    );
    let statement = c_seq(loop_statement, c_return(c_variable("i")));
    let final_memory = memory
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            int32(0),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(4),
            },
            int32(1),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(8),
            },
            int32(2),
        );
    let final_state = CState::new()
        .with_local(
            "p",
            CValue::Pointer(Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
        .with_local("i", int32(3))
        .with_memory(final_memory)
        .with_resource_context(resources);
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), PureFactContext::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(3),
                state: final_state,
            },
        }
    );
}

#[test]
fn symbolic_loadable_discharges_pointer_access_obligation() {
    let i = Variable(67);
    let n = Variable(68);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let memory = CMemory::new();
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_local("i", int32(i_bits.clone()))
        .with_memory(memory.clone())
        .with_resource_context(write_context(base.clone(), 0, n_bits.clone()));
    let statement = c_store(c_add(c_variable("p"), c_variable("i")), c_int32_literal(7));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::Multiply(
                Box::new(n_bits.clone()),
                Box::new(Bitvector32Term::Constant(4)),
            ),
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits),
            true,
        );
    let execution = prove_symbolic_c_execution_paths(state, statement, assumptions);

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
}

#[test]
fn interval_arithmetic_proves_increment_bounds_and_no_overflow() {
    let i = Variable(69);
    let n = Variable(70);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new().with_local("i", int32(i_bits.clone()));
    let statement = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits.clone()),
            true,
        );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(i_bits.clone(), incremented.clone()),
        true,
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(i_bits.clone(), incremented.clone()),
        true,
    )));
    let theorem = prove_c_statement_executes_and_propositions(
        state,
        statement,
        assumptions,
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    incremented.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_less_equal(incremented, n_bits), true),
        ],
    )
    .expect("interval facts should prove i + 1 bounds and no signed overflow");

    assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
}

#[test]
fn signed_order_solver_knows_int32_universal_bounds() {
    let x = Bitvector32Term::Variable(Variable(71));
    let int_min = Bitvector32Term::Constant(i32::MIN as u32);
    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
    let assumptions = PureFactContext::new();

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            x.clone(),
            int_max.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_than(x.clone(), int_max)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            x.clone(),
            int_min.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(x, int_min)),
        Some(false)
    );
}

#[test]
fn strict_positive_bound_rules_out_decrement_overflow() {
    let value = Bitvector32Term::Variable(Variable(72_001));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(
            value,
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
}

#[test]
fn nonnegative_bound_rules_out_decrement_overflow() {
    let value = Bitvector32Term::Variable(Variable(72_002));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(
            value,
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
}

#[test]
fn interval_arithmetic_uses_lower_bound_for_incremented_values() {
    let i = Variable(73);
    let i_bits = Bitvector32Term::Variable(i);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    // A lower bound alone is not enough: `i + 1` wraps at INT_MAX, so
    // `i >= 1` does not entail `i + 1 >= 1` (false at i = INT_MAX).
    let lower_only = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    assert!(!lower_only.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
        true,
    )));

    // Knowing `i < INT_MAX` rules out signed overflow of `i + 1`, so the
    // lower bound carries to the incremented value.
    let assumptions = lower_only.assume_condition(
        ConditionTerm::signed_less_than(i_bits, Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
        true,
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(incremented, Bitvector32Term::Constant(0)),
        true,
    )));
}

#[test]
fn nonnegative_successor_requires_no_overflow_evidence() {
    let x = Bitvector32Term::Variable(Variable(74_001));
    let successor = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            successor.clone(),
            Bitvector32Term::Constant(0),
        )),
        None,
    );
    assert!(
        assumptions
            .derive_simp_proposition(&Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(successor, Bitvector32Term::Constant(0),),
                true,
            ))
            .is_none()
    );
}

#[test]
fn additive_upper_bound_covers_incremented_pointer_access() {
    let j = Variable(74);
    let j_bits = Bitvector32Term::Variable(j);
    let incremented = Bitvector32Term::add(j_bits.clone(), Bitvector32Term::Constant(1));
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_int32_elements(incremented.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(2)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            incremented,
            Bitvector32Term::Constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.pointer_access_in_range(
        &pointer,
        4,
        &base,
        &Bitvector32Term::Constant(0),
        &Bitvector32Term::Constant(3),
    ));
}

#[test]
fn relative_dependent_range_is_covered_by_owned_range() {
    let owner = Bitvector32Term::Variable(Variable(75));
    let backing = Bitvector32Term::Variable(Variable(76));
    let index = Bitvector32Term::Variable(Variable(77));
    let length = Bitvector32Term::Variable(Variable(78));
    let capacity = Bitvector32Term::Variable(Variable(79));
    let base = Pointer {
        block: "owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let backing_start = Bitvector32Term::subtract(backing.clone(), owner.clone());
    let indexed_start =
        Bitvector32Term::subtract(Bitvector32Term::add(backing, index.clone()), owner);
    let available = CResourceFact::own_memory(CMemoryRange::new(
        base.clone(),
        backing_start.clone(),
        Bitvector32Term::add(backing_start, capacity.clone()),
    ));
    let required = CResourceFact::own_memory(CMemoryRange::new(
        base,
        indexed_start.clone(),
        Bitvector32Term::add(indexed_start, Bitvector32Term::Constant(1)),
    ));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(length, capacity), true);
    let resources = ResourceContext::new().unchecked_with_fact(available);

    assert!(resources.satisfies_fact(&required, &assumptions));
    assert!(resources.without_fact(&required, &assumptions).is_some());
}

#[test]
fn addition_cancels_a_negated_pointer_base() {
    let base = Bitvector32Term::Variable(Variable(90));
    let index = Bitvector32Term::Variable(Variable(91));
    let negative_base = Bitvector32Term::subtract(Bitvector32Term::Constant(0), base.clone());

    assert_eq!(
        Bitvector32Term::add(negative_base, Bitvector32Term::add(base, index.clone()),),
        index
    );
}

#[test]
fn negative_equality_fact_decides_equality_false() {
    let x = Bitvector32Term::Variable(Variable(79));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
        false,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(Bitvector32Term::Constant(0), x,)),
        Some(false)
    );
}

#[test]
fn equality_facts_are_transitive() {
    let i = Bitvector32Term::Variable(Variable(84));
    let k = Bitvector32Term::Variable(Variable(85));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(k.clone(), i.clone()), true)
        .assume_condition(ConditionTerm::equal(i, Bitvector32Term::Constant(1)), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(1))),
        Some(true)
    );
}

#[test]
fn equality_transports_signed_order_facts_in_both_directions() {
    let selected = Bitvector32Term::Variable(Variable(86));
    let key = Bitvector32Term::Variable(Variable(87));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(selected.clone(), key.clone()), true)
        .assume_condition(
            ConditionTerm::signed_greater_equal(key.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(10), selected.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            selected,
            Bitvector32Term::Constant(0),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(10),
            key,
        )),
        Some(true)
    );
}

#[test]
fn simp_combines_equality_with_discrete_integer_bounds() {
    let length = Bitvector32Term::Variable(Variable(87_100));
    let owner_length = Bitvector32Term::Variable(Variable(87_101));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::equal(owner_length.clone(), length), true);

    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            owner_length,
        )),
        Some(true)
    );
}

#[test]
fn simp_evaluates_equality_arithmetic_chains() {
    let old_split = Bitvector32Term::Variable(Variable(87_102));
    let split = Bitvector32Term::Variable(Variable(87_103));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(old_split.clone(), Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(
                split.clone(),
                Bitvector32Term::add(old_split, Bitvector32Term::Constant(1)),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            split,
        )),
        Some(true)
    );
}

#[test]
fn equality_transport_reaches_chains_and_arithmetic_terms() {
    let x = Bitvector32Term::Variable(Variable(88));
    let y = Bitvector32Term::Variable(Variable(89));
    let z = Bitvector32Term::Variable(Variable(90));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(x.clone(), y), true)
        .assume_condition(ConditionTerm::equal(z.clone(), x), true)
        .assume_condition(
            ConditionTerm::signed_less_than(
                Bitvector32Term::add(z, Bitvector32Term::Constant(1)),
                Bitvector32Term::Constant(8),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(89)),
                Bitvector32Term::Constant(1),
            ),
            Bitvector32Term::Constant(8),
        )),
        Some(true)
    );
}

#[test]
fn excluded_small_integer_range_is_inconsistent() {
    let k = Bitvector32Term::Variable(Variable(80));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(3)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(0)),
            false,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(1)),
            false,
        )
        .assume_condition(ConditionTerm::equal(k, Bitvector32Term::Constant(2)), false);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn singleton_integer_range_forces_equality() {
    let k = Bitvector32Term::Variable(Variable(86));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(1)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(0))),
        Some(true)
    );
}
