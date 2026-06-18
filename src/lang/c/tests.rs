use super::*;

#[test]
fn c0_array_parameter_syntax_lowers_to_pointer_parameter() {
    let function = syntax::parse_function(
        r#"
        int32 first(int32 p[3]) {
            return p[0];
        }
        "#,
    )
    .expect("array parameter should parse");

    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );
    assert_eq!(
        function.to_megakernel_function().parameters()[0].c_type(),
        crate::megakernel::CType::Int32Pointer
    );
}

#[test]
fn c0_syntax_targets_megakernel_max_body() {
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");
    let statement = function.body_megakernel_statement();

    assert_eq!(statement, crate::megakernel::c_max_body());

    let a = crate::megakernel::Variable(30);
    let b = crate::megakernel::Variable(31);
    let a_bits = crate::megakernel::Bitvector32Term::Variable(a);
    let b_bits = crate::megakernel::Bitvector32Term::Variable(b);
    let condition = crate::megakernel::c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = crate::megakernel::c_max_state(
        crate::megakernel::int32(a_bits),
        crate::megakernel::int32(b_bits),
    );
    let assumptions =
        crate::megakernel::Assumptions::new().assume_condition(condition.clone(), true);
    let theorem = crate::megakernel::prove_symbolic_c_execution(
        state.clone(),
        statement.clone(),
        assumptions,
    )
    .expect("parsed max should symbolically execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::Implies(
            Box::new(crate::megakernel::Proposition::ConditionIs(condition, true)),
            Box::new(crate::megakernel::Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: crate::megakernel::CStatementOutcome::Return {
                    value: crate::megakernel::int32(crate::megakernel::Bitvector32Term::Variable(
                        b
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn c0_syntax_targets_megakernel_max_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");
    let function = function.to_megakernel_function();

    assert_eq!(function, crate::megakernel::c_max_function());

    let state = crate::megakernel::CState::new();
    let arguments = vec![
        crate::megakernel::c_int32_literal(0),
        crate::megakernel::c_int32_literal(1),
    ];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_assignment_and_sequence() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let statement = function.body_megakernel_statement();
    let initial = crate::megakernel::CState::new().with_local("x", crate::megakernel::int32(1));
    let final_state = crate::megakernel::CState::new().with_local("x", crate::megakernel::int32(2));
    let theorem = crate::megakernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CStatementExecutes {
            state: initial,
            statement,
            outcome: crate::megakernel::CStatementOutcome::Return {
                value: crate::megakernel::int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_assignment_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let function = function.to_megakernel_function();
    let state = crate::megakernel::CState::new().with_local("caller", crate::megakernel::int32(5));
    let arguments = vec![crate::megakernel::c_int32_literal(1)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed assignment function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(2),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_store_and_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse");

    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );

    let pointer = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let statement = function.body_megakernel_statement();
    let initial = crate::megakernel::CState::new()
        .with_local("p", crate::megakernel::CValue::Pointer(pointer.clone()));
    let final_state = crate::megakernel::CState::new()
        .with_local("p", crate::megakernel::CValue::Pointer(pointer.clone()))
        .with_memory(
            crate::megakernel::CMemory::new().store(pointer.clone(), crate::megakernel::int32(9)),
        );
    let store_obligation = crate::megakernel::Proposition::CMemoryCanStore {
        memory: crate::megakernel::CMemory::new(),
        pointer,
    };
    let theorem = crate::megakernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::Implies(
            Box::new(store_obligation),
            Box::new(crate::megakernel::Proposition::CStatementExecutes {
                state: initial,
                statement,
                outcome: crate::megakernel::CStatementOutcome::Return {
                    value: crate::megakernel::int32(9),
                    state: final_state,
                },
            }),
        )
    );
}

#[test]
fn c0_syntax_targets_megakernel_store_and_load_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse")
    .to_megakernel_function();

    let pointer = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::megakernel::CState::new().with_local("caller", crate::megakernel::int32(7));
    let arguments = vec![crate::megakernel::c_pointer_value(pointer.clone())];
    let final_state = crate::megakernel::CState::new()
        .with_local("caller", crate::megakernel::int32(7))
        .with_memory(
            crate::megakernel::CMemory::new().store(pointer.clone(), crate::megakernel::int32(9)),
        );
    let store_obligation = crate::megakernel::Proposition::CMemoryCanStore {
        memory: crate::megakernel::CMemory::new(),
        pointer,
    };
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::Implies(
            Box::new(store_obligation),
            Box::new(crate::megakernel::Proposition::CFunctionExecutes {
                state,
                function,
                arguments,
                outcome: crate::megakernel::CFunctionOutcome::Return {
                    value: crate::megakernel::int32(9),
                    state: final_state,
                },
            }),
        )
    );
}

#[test]
fn c0_syntax_targets_megakernel_pointer_addition_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_second(int32* p) {
            return *(p + 1);
        }
        "#,
    )
    .expect("pointer-add load function should parse")
    .to_megakernel_function();

    let base = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::megakernel::CMemory::new()
        .with_block("block", 16)
        .store(second, crate::megakernel::int32(23));
    let state = crate::megakernel::CState::new().with_memory(memory.clone());
    let arguments = vec![crate::megakernel::c_pointer_value(base)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed pointer-add load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(23),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_array_index_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_second(int32* p) {
            return p[1];
        }
        "#,
    )
    .expect("array-index load function should parse")
    .to_megakernel_function();

    let base = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::megakernel::CMemory::new()
        .with_block("block", 16)
        .store(second, crate::megakernel::int32(23));
    let state = crate::megakernel::CState::new().with_memory(memory.clone());
    let arguments = vec![crate::megakernel::c_pointer_value(base)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed array-index load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(23),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_array_index_store() {
    let function = syntax::parse_function(
        r#"
        int32 store_second(int32* p) {
            p[1] = 7;
            return p[1];
        }
        "#,
    )
    .expect("array-index store function should parse")
    .to_megakernel_function();

    let base = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::megakernel::CMemory::new().with_block("block", 16);
    let state = crate::megakernel::CState::new().with_memory(memory);
    let final_state = crate::megakernel::CState::new().with_memory(
        crate::megakernel::CMemory::new()
            .with_block("block", 16)
            .store(second, crate::megakernel::int32(7)),
    );
    let arguments = vec![crate::megakernel::c_pointer_value(base)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed array-index store should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_address_of_array_index() {
    let function = syntax::parse_function(
        r#"
        int32 load_second_through_address(int32* p) {
            int32* q;
            q = &p[1];
            return *q;
        }
        "#,
    )
    .expect("address-of array-index function should parse")
    .to_megakernel_function();

    let base = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(4),
    };
    let local_q = crate::megakernel::Pointer {
        block: "local:q".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let memory = crate::megakernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::megakernel::int32(23));
    let state = crate::megakernel::CState::new().with_memory(memory);
    let final_state = crate::megakernel::CState::new().with_memory(
        crate::megakernel::CMemory::new()
            .with_block("block", 16)
            .with_block("local:q", 8)
            .store(second.clone(), crate::megakernel::int32(23))
            .store(local_q, crate::megakernel::CValue::Pointer(second.clone())),
    );
    let arguments = vec![crate::megakernel::c_pointer_value(base)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed address-of array-index should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(23),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_pointer_null_equality() {
    let function = syntax::parse_function(
        r#"
        int32 is_null(int32* p) {
            if (p == 0) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("pointer null check should parse")
    .to_megakernel_function();

    let null = crate::megakernel::Pointer {
        block: "null".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::megakernel::CState::new();
    let arguments = vec![crate::megakernel::c_pointer_value(null)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        crate::megakernel::Assumptions::new(),
    )
    .expect("parsed pointer null check should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_logical_short_circuiting() {
    let function = syntax::parse_function(
        r#"
        int32 safe_is_three(int32* p) {
            if (p == 0 || (p != 0 && *p == 3)) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("logical short-circuit function should parse")
    .to_megakernel_function();

    let null = crate::megakernel::Pointer {
        block: "null".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let pointer = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let cases = [
        (
            crate::megakernel::CState::new(),
            vec![crate::megakernel::c_pointer_value(null)],
            crate::megakernel::int32(1),
        ),
        (
            crate::megakernel::CState::new().with_memory(
                crate::megakernel::CMemory::new()
                    .with_block("block", 4)
                    .store(pointer.clone(), crate::megakernel::int32(3)),
            ),
            vec![crate::megakernel::c_pointer_value(pointer.clone())],
            crate::megakernel::int32(1),
        ),
        (
            crate::megakernel::CState::new().with_memory(
                crate::megakernel::CMemory::new()
                    .with_block("block", 4)
                    .store(pointer.clone(), crate::megakernel::int32(4)),
            ),
            vec![crate::megakernel::c_pointer_value(pointer)],
            crate::megakernel::int32(0),
        ),
    ];

    for (state, arguments, expected) in cases {
        let theorem = crate::megakernel::prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            arguments.clone(),
            crate::megakernel::Assumptions::new(),
        )
        .expect("logical short-circuit function should execute");

        assert_eq!(
            theorem.proposition(),
            &crate::megakernel::Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments,
                outcome: crate::megakernel::CFunctionOutcome::Return {
                    value: expected,
                    state,
                },
            }
        );
    }
}

#[test]
fn c0_syntax_targets_megakernel_unary_not() {
    let function = syntax::parse_function(
        r#"
        int32 not_null(int32* p) {
            if (!(p == 0)) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("unary not function should parse")
    .to_megakernel_function();

    let pointer = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::megakernel::CState::new();
    let arguments = vec![crate::megakernel::c_pointer_value(pointer)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        crate::megakernel::Assumptions::new(),
    )
    .expect("unary not function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_local_address_of() {
    let function = syntax::parse_function(
        r#"
        int32 local_read() {
            int32 x;
            x = 5;
            return *(&x);
        }
        "#,
    )
    .expect("local address-of function should parse")
    .to_megakernel_function();

    let local_pointer = crate::megakernel::Pointer {
        block: "local:x".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::megakernel::CState::new();
    let final_state = crate::megakernel::CState::new().with_memory(
        crate::megakernel::CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, crate::megakernel::int32(5)),
    );
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("parsed local address-of function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_local_array_storage() {
    let function = syntax::parse_function(
        r#"
        int32 local_array_roundtrip() {
            int32 a[3];
            a[0] = 5;
            a[1] = 7;
            return a[1];
        }
        "#,
    )
    .expect("local array function should parse")
    .to_megakernel_function();

    let a0 = crate::megakernel::Pointer {
        block: "local:a".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let a1 = crate::megakernel::Pointer {
        block: "local:a".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(4),
    };
    let state = crate::megakernel::CState::new();
    let final_state = crate::megakernel::CState::new().with_memory(
        crate::megakernel::CMemory::new()
            .with_block("local:a", 12)
            .store(a0, crate::megakernel::int32(5))
            .store(a1, crate::megakernel::int32(7)),
    );
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local array function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_local_array_decays_to_pointer_argument() {
    let read_first = syntax::parse_function(
        r#"
        int32 read_first(int32* p) {
            return p[0];
        }
        "#,
    )
    .expect("helper function should parse")
    .to_megakernel_function();
    let caller = syntax::parse_function(
        r#"
        int32 caller() {
            int32 a[2];
            a[0] = 11;
            int32 result;
            result = read_first(a);
            return result;
        }
        "#,
    )
    .expect("caller function should parse")
    .to_megakernel_function();

    let a0 = crate::megakernel::Pointer {
        block: "local:a".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let result_pointer = crate::megakernel::Pointer {
        block: "local:result".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let environment = crate::megakernel::CFunctionEnvironment::new().with_function(read_first);
    let state = crate::megakernel::CState::new();
    let final_state = crate::megakernel::CState::new().with_memory(
        crate::megakernel::CMemory::new()
            .with_block("local:a", 8)
            .with_block("local:result", 4)
            .store(a0, crate::megakernel::int32(11))
            .store(result_pointer, crate::megakernel::int32(11)),
    );
    let theorem = crate::megakernel::prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        environment,
    )
    .expect("local array should decay to pointer argument");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments: Vec::new(),
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(11),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_rejects_assignment_to_local_array_object() {
    let function = syntax::parse_function(
        r#"
        int32 bad_assign(int32* p) {
            int32 a[3];
            a = p;
            return 0;
        }
        "#,
    )
    .expect("array assignment function should parse")
    .to_megakernel_function();

    let pointer = crate::megakernel::Pointer {
        block: "block".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::megakernel::CState::new();
    let arguments = vec![crate::megakernel::c_pointer_value(pointer)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("array assignment should execute to a type error");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::RuntimeError(
                crate::megakernel::CRuntimeError::TypeMismatch
            ),
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_int32_subtraction_and_comparisons() {
    let function = syntax::parse_function(
        r#"
        int32 adjust(int32 x) {
            if (x >= 3) {
                return x - 1;
            } else {
                if (x == 0) {
                    return x + 2;
                } else {
                    return x + 1;
                }
            }
        }
        "#,
    )
    .expect("int32 operator function should parse")
    .to_megakernel_function();

    let state = crate::megakernel::CState::new();
    let arguments = vec![crate::megakernel::c_int32_literal(4)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed int32 operator function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(3),
                state,
            },
        }
    );
}

#[test]
fn c0_if_condition_uses_c_int32_truthiness() {
    let function = syntax::parse_function(
        r#"
        int32 truthy(int32 x) {
            if (x) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("truthiness function should parse")
    .to_megakernel_function();

    let state = crate::megakernel::CState::new();
    let arguments = vec![crate::megakernel::c_int32_literal(7)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("nonzero int32 condition should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function: function.clone(),
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(1),
                state: state.clone(),
            },
        }
    );

    let arguments = vec![crate::megakernel::c_int32_literal(0)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("zero int32 condition should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(0),
                state,
            },
        }
    );
}

#[test]
fn c0_clamp_demo_proves_symbolic_branch_specifications() {
    let function = syntax::parse_function(
        r#"
        int32 clamp(int32 x, int32 lo, int32 hi) {
            if (x < lo) {
                return lo;
            } else {
                if (x > hi) {
                    return hi;
                } else {
                    return x;
                }
            }
        }
        "#,
    )
    .expect("clamp should parse")
    .to_megakernel_function();

    let x = crate::megakernel::Variable(40);
    let lo = crate::megakernel::Variable(41);
    let hi = crate::megakernel::Variable(42);
    let x_bits = crate::megakernel::Bitvector32Term::Variable(x);
    let lo_bits = crate::megakernel::Bitvector32Term::Variable(lo);
    let hi_bits = crate::megakernel::Bitvector32Term::Variable(hi);
    let arguments = vec![
        crate::megakernel::CExpression::Value(crate::megakernel::int32(x_bits.clone())),
        crate::megakernel::CExpression::Value(crate::megakernel::int32(lo_bits.clone())),
        crate::megakernel::CExpression::Value(crate::megakernel::int32(hi_bits.clone())),
    ];
    let below_lo = crate::megakernel::ConditionTerm::Bitvector32SignedLessThan(
        Box::new(x_bits.clone()),
        Box::new(lo_bits.clone()),
    );
    let above_hi = crate::megakernel::ConditionTerm::Bitvector32SignedGreaterThan(
        Box::new(x_bits.clone()),
        Box::new(hi_bits.clone()),
    );
    let cases = vec![
        (
            vec![crate::megakernel::Proposition::ConditionIs(
                below_lo.clone(),
                true,
            )],
            crate::megakernel::int32(lo_bits),
        ),
        (
            vec![
                crate::megakernel::Proposition::ConditionIs(below_lo.clone(), false),
                crate::megakernel::Proposition::ConditionIs(above_hi.clone(), true),
            ],
            crate::megakernel::int32(hi_bits),
        ),
        (
            vec![
                crate::megakernel::Proposition::ConditionIs(below_lo, false),
                crate::megakernel::Proposition::ConditionIs(above_hi, false),
            ],
            crate::megakernel::int32(x_bits),
        ),
    ];

    for (requires, value) in cases {
        let specification = crate::megakernel::c_function_specification(
            crate::megakernel::CState::new(),
            arguments.clone(),
            requires.clone(),
            crate::megakernel::CFunctionOutcome::Return {
                value,
                state: crate::megakernel::CState::new(),
            },
        );
        let theorem = crate::megakernel::prove_c_function_satisfies_specification(
            function.clone(),
            specification.clone(),
            crate::megakernel::Assumptions::new(),
        )
        .expect("clamp branch specification should prove");
        let expected = requires.iter().rev().fold(
            crate::megakernel::Proposition::CFunctionSatisfiesSpecification {
                function: function.clone(),
                specification: specification.clone(),
            },
            |body, requirement| {
                crate::megakernel::Proposition::Implies(
                    Box::new(requirement.clone()),
                    Box::new(body),
                )
            },
        );

        assert_eq!(theorem.proposition(), &expected);
    }
}

#[test]
fn c0_syntax_targets_megakernel_known_function_call_assignment() {
    let increment = syntax::parse_function(
        r#"
        int32 increment(int32 x) {
            return x + 1;
        }
        "#,
    )
    .expect("increment function should parse")
    .to_megakernel_function();
    let caller = syntax::parse_function(
        r#"
        int32 caller() {
            int32 result;
            result = increment(41);
            return result;
        }
        "#,
    )
    .expect("caller function should parse")
    .to_megakernel_function();

    let local_pointer = crate::megakernel::Pointer {
        block: "local:result".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let environment = crate::megakernel::CFunctionEnvironment::new().with_function(increment);
    let state = crate::megakernel::CState::new();
    let final_state = crate::megakernel::CState::new().with_memory(
        crate::megakernel::CMemory::new()
            .with_block("local:result", 4)
            .store(local_pointer, crate::megakernel::int32(42)),
    );
    let theorem = crate::megakernel::prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        environment,
    )
    .expect("known C0 function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments: Vec::new(),
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(42),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_while_countdown() {
    let function = syntax::parse_function(
        r#"
        int32 countdown(int32 x) {
            while (x > 0) {
                x = x - 1;
            }
            return x;
        }
        "#,
    )
    .expect("while countdown function should parse")
    .to_megakernel_function();

    let state = crate::megakernel::CState::new();
    let arguments = vec![crate::megakernel::c_int32_literal(3)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("while countdown function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(0),
                state: crate::megakernel::CState::new(),
            },
        }
    );
}

#[test]
fn c0_memory_safety_demo_fill_three_ints() {
    let function = syntax::parse_function(
        r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                *(p + i) = i;
                i = i + 1;
            }
            return *(p + 2);
        }
        "#,
    )
    .expect("fill3 demo should parse")
    .to_megakernel_function();

    let base = crate::megakernel::Pointer {
        block: "buf".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let first = crate::megakernel::Pointer {
        block: "buf".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::megakernel::Pointer {
        block: "buf".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(4),
    };
    let third = crate::megakernel::Pointer {
        block: "buf".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(8),
    };
    let local_i = crate::megakernel::Pointer {
        block: "local:i".to_string(),
        offset: crate::megakernel::PointerOffsetTerm::Constant(0),
    };
    let initial_memory = crate::megakernel::CMemory::new().with_block("buf", 12);
    let state = crate::megakernel::CState::new().with_memory(initial_memory);
    let final_memory = crate::megakernel::CMemory::new()
        .with_block("buf", 12)
        .with_block("local:i", 4)
        .store(first, crate::megakernel::int32(0))
        .store(second, crate::megakernel::int32(1))
        .store(third, crate::megakernel::int32(2))
        .store(local_i, crate::megakernel::int32(3));
    let arguments = vec![crate::megakernel::c_pointer_value(base)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("fill3 should execute without memory obligations");

    assert_eq!(
        theorem.proposition(),
        &crate::megakernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(2),
                state: crate::megakernel::CState::new().with_memory(final_memory),
            },
        }
    );
}
