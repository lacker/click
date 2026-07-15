use super::*;

fn memory_range(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::CMemoryRange {
    crate::kernel::CMemoryRange::new(base, start.into(), end.into())
}

fn read_context(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::ResourceContext {
    crate::kernel::ResourceContext::new().unchecked_with_fact(
        crate::kernel::CResourceFact::view_memory(memory_range(base, start, end)),
    )
}

fn write_context(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::ResourceContext {
    crate::kernel::ResourceContext::new().unchecked_with_fact(
        crate::kernel::CResourceFact::own_memory(memory_range(base, start, end)),
    )
}

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
        function.to_kernel_function().parameters()[0].c_type(),
        crate::kernel::CType::Int32Pointer
    );
}

#[test]
fn c0_syntax_targets_kernel_max_body() {
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
    let statement = function.body_kernel_statement();

    assert_eq!(statement, crate::kernel::c_max_body());

    let a = crate::kernel::Variable(30);
    let b = crate::kernel::Variable(31);
    let a_bits = crate::kernel::Bitvector32Term::Variable(a);
    let b_bits = crate::kernel::Bitvector32Term::Variable(b);
    let condition = crate::kernel::c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state =
        crate::kernel::c_max_state(crate::kernel::int32(a_bits), crate::kernel::int32(b_bits));
    let assumptions = crate::kernel::Assumptions::new().assume_condition(condition.clone(), true);
    let theorem =
        crate::kernel::prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
            .expect("parsed max should symbolically execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::Implies(
            Box::new(crate::kernel::Proposition::ConditionIs(condition, true)),
            Box::new(crate::kernel::Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: crate::kernel::CStatementOutcome::Return {
                    value: crate::kernel::int32(crate::kernel::Bitvector32Term::Variable(b)),
                    state,
                },
            }),
        )
    );
}

#[test]
fn c0_syntax_targets_kernel_max_function_call() {
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
    let function = function.to_kernel_function();

    assert_eq!(function, crate::kernel::c_max_function());

    let state = crate::kernel::CState::new();
    let arguments = vec![
        crate::kernel::c_int32_literal(0),
        crate::kernel::c_int32_literal(1),
    ];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_assignment_and_sequence() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let statement = function.body_kernel_statement();
    let initial = crate::kernel::CState::new().with_local("x", crate::kernel::int32(1));
    let final_state = crate::kernel::CState::new().with_local("x", crate::kernel::int32(2));
    let theorem = crate::kernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: initial,
            statement,
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_assignment_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let function = function.to_kernel_function();
    let state = crate::kernel::CState::new().with_local("caller", crate::kernel::int32(5));
    let arguments = vec![crate::kernel::c_int32_literal(1)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed assignment function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(2),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_store_and_load() {
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

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let statement = function.body_kernel_statement();
    let resources = write_context(pointer.clone(), 0, 1);
    let initial = crate::kernel::CState::new()
        .with_local("p", crate::kernel::CValue::Pointer(pointer.clone()))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_local("p", crate::kernel::CValue::Pointer(pointer.clone()))
        .with_memory(crate::kernel::CMemory::new().store(pointer.clone(), crate::kernel::int32(9)))
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: initial,
            statement,
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_struct_field_load() {
    let function = syntax::parse_function(
        r#"
        struct json_object {
            int32 ref_count;
        };

        int32 json_object_get_ref_count(struct json_object* obj) {
            return obj->ref_count;
        }
        "#,
    )
    .expect("pilot struct getter should parse");

    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );
    assert_eq!(function.parameters()[0].struct_name(), Some("json_object"));

    let pointer = crate::kernel::Pointer {
        block: "object".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let statement = function.body_kernel_statement();
    let memory = crate::kernel::CMemory::new()
        .with_block("object", 4)
        .store(pointer.clone(), crate::kernel::int32(3));
    let initial = crate::kernel::CState::new()
        .with_local("obj", crate::kernel::CValue::Pointer(pointer.clone()))
        .with_memory(memory)
        .with_resource_context(read_context(pointer, 0, 1));
    let theorem = crate::kernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed struct getter should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: initial.clone(),
            statement,
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::int32(3),
                state: initial,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_struct_field_store() {
    let function = syntax::parse_function(
        r#"
        struct json_object {
            int32 ref_count;
        };

        int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
            obj->ref_count = count;
            return obj->ref_count;
        }
        "#,
    )
    .expect("pilot struct setter should parse")
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "object".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("object", 4))
        .with_resource_context(resources.clone());
    let arguments = vec![
        crate::kernel::c_pointer_value(pointer.clone()),
        crate::kernel::c_int32_literal(5),
    ];
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("object", 4)
                .store(pointer, crate::kernel::int32(5)),
        )
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed struct setter should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_multifield_struct_offset_load() {
    let function = syntax::parse_function(
        r#"
        struct pair {
            int32 first;
            int32 second;
        };

        int32 pair_second(struct pair* p) {
            return p->second;
        }
        "#,
    )
    .expect("multi-field struct getter should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "pair".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "pair".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("pair", 8)
        .store(second, crate::kernel::int32(7));
    let state = crate::kernel::CState::new()
        .with_memory(memory)
        .with_resource_context(read_context(base.clone(), 1, 2));
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed multi-field struct getter should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_struct_pointer_field_roundtrip() {
    let function = syntax::parse_function(
        r#"
        struct owner {
            int32 len;
            int32* data;
        };

        int32 set_owned_first(struct owner* owner, int32 data[]) {
            int32* current;
            owner->len = 1;
            owner->data = data;
            current = owner->data;
            current[0] = owner->len;
            return current[0];
        }
        "#,
    )
    .expect("struct pointer field roundtrip should parse")
    .to_kernel_function();

    let owner = crate::kernel::Pointer {
        block: "owner".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let owner_data = crate::kernel::Pointer {
        block: "owner".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let data = crate::kernel::Pointer {
        block: "data".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = crate::kernel::ResourceContext::new().unchecked_with_facts(vec![
        crate::kernel::CResourceFact::own_memory(memory_range(owner.clone(), 0, 3)),
        crate::kernel::CResourceFact::own_memory(memory_range(data.clone(), 0, 1)),
    ]);
    let state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("owner", 12)
                .with_block("data", 4),
        )
        .with_resource_context(resources);
    let arguments = vec![
        crate::kernel::c_pointer_value(owner.clone()),
        crate::kernel::c_pointer_value(data.clone()),
    ];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed struct pointer field roundtrip should execute");

    let crate::kernel::Proposition::CFunctionExecutes {
        outcome:
            crate::kernel::CFunctionOutcome::Return {
                value,
                state: final_state,
            },
        ..
    } = theorem.proposition()
    else {
        panic!("expected function execution theorem, got {:#?}", theorem);
    };

    assert_eq!(value, &crate::kernel::int32(1));
    assert_eq!(
        final_state.memory().load(&owner),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::int32(1))
    );
    assert_eq!(
        final_state.memory().load(&owner_data),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::CValue::Pointer(data.clone()))
    );
    assert_eq!(
        final_state.memory().load(&data),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::int32(1))
    );
}

#[test]
fn c0_syntax_targets_kernel_store_and_load_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse")
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = crate::kernel::CState::new()
        .with_local("caller", crate::kernel::int32(7))
        .with_resource_context(resources.clone());
    let arguments = vec![crate::kernel::c_pointer_value(pointer.clone())];
    let final_state = crate::kernel::CState::new()
        .with_local("caller", crate::kernel::int32(7))
        .with_memory(crate::kernel::CMemory::new().store(pointer.clone(), crate::kernel::int32(9)))
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_pointer_addition_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_second(int32* p) {
            return *(p + 1);
        }
        "#,
    )
    .expect("pointer-add load function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::kernel::int32(23));
    let resources = read_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed pointer-add load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(23),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_array_index_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_second(int32* p) {
            return p[1];
        }
        "#,
    )
    .expect("array-index load function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::kernel::int32(23));
    let resources = read_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed array-index load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(23),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_array_index_store() {
    let function = syntax::parse_function(
        r#"
        int32 store_second(int32* p) {
            p[1] = 7;
            return p[1];
        }
        "#,
    )
    .expect("array-index store function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new().with_block("block", 16);
    let resources = write_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("block", 16)
                .store(second, crate::kernel::int32(7)),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed array-index store should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_address_of_array_index() {
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
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let local_q = crate::kernel::Pointer {
        block: "local:q".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::kernel::int32(23));
    let resources = read_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("block", 16)
                .with_block("local:q", 8)
                .store(second.clone(), crate::kernel::int32(23))
                .store(local_q, crate::kernel::CValue::Pointer(second.clone())),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed address-of array-index should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(23),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_pointer_null_equality() {
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
    .to_kernel_function();

    let null = crate::kernel::Pointer {
        block: "null".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_pointer_value(null)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        crate::kernel::Assumptions::new(),
    )
    .expect("parsed pointer null check should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_logical_short_circuiting() {
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
    .to_kernel_function();

    let null = crate::kernel::Pointer {
        block: "null".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let cases = [
        (
            crate::kernel::CState::new(),
            vec![crate::kernel::c_pointer_value(null)],
            crate::kernel::int32(1),
        ),
        (
            crate::kernel::CState::new()
                .with_memory(
                    crate::kernel::CMemory::new()
                        .with_block("block", 4)
                        .store(pointer.clone(), crate::kernel::int32(3)),
                )
                .with_resource_context(read_context(pointer.clone(), 0, 1)),
            vec![crate::kernel::c_pointer_value(pointer.clone())],
            crate::kernel::int32(1),
        ),
        (
            crate::kernel::CState::new()
                .with_memory(
                    crate::kernel::CMemory::new()
                        .with_block("block", 4)
                        .store(pointer.clone(), crate::kernel::int32(4)),
                )
                .with_resource_context(read_context(pointer.clone(), 0, 1)),
            vec![crate::kernel::c_pointer_value(pointer.clone())],
            crate::kernel::int32(0),
        ),
    ];

    for (state, arguments, expected) in cases {
        let theorem = crate::kernel::prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            arguments.clone(),
            crate::kernel::Assumptions::new(),
        )
        .expect("logical short-circuit function should execute");

        assert_eq!(
            theorem.proposition(),
            &crate::kernel::Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments,
                outcome: crate::kernel::CFunctionOutcome::Return {
                    value: expected,
                    state,
                },
            }
        );
    }
}

#[test]
fn c0_syntax_targets_kernel_unary_not() {
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
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_pointer_value(pointer)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        crate::kernel::Assumptions::new(),
    )
    .expect("unary not function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_local_address_of() {
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
    .to_kernel_function();

    let local_pointer = crate::kernel::Pointer {
        block: "local:x".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, crate::kernel::int32(5)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("parsed local address-of function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_local_array_storage() {
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
    .to_kernel_function();

    let a0 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let a1 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:a", 12)
            .store(a0, crate::kernel::int32(5))
            .store(a1, crate::kernel::int32(7)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local array function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
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
    .to_kernel_function();
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
    .to_kernel_function();

    let a0 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let result_pointer = crate::kernel::Pointer {
        block: "local:result".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let environment = crate::kernel::CFunctionEnvironment::new().with_function(read_first);
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:a", 8)
            .with_block("local:result", 4)
            .store(a0, crate::kernel::int32(11))
            .store(result_pointer, crate::kernel::int32(11)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        environment,
        crate::kernel::CCallSemantics::ExecuteBodies,
    )
    .expect("local array should decay to pointer argument");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(11),
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
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_pointer_value(pointer)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("array assignment should execute to a type error");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::RuntimeError(
                crate::kernel::CRuntimeError::TypeMismatch
            ),
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_int32_subtraction_and_comparisons() {
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
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_int32_literal(4)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed int32 operator function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(3),
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
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_int32_literal(7)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("nonzero int32 condition should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function: function.clone(),
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state: state.clone(),
            },
        }
    );

    let arguments = vec![crate::kernel::c_int32_literal(0)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("zero int32 condition should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(0),
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
    .to_kernel_function();

    let x = crate::kernel::Variable(40);
    let lo = crate::kernel::Variable(41);
    let hi = crate::kernel::Variable(42);
    let x_bits = crate::kernel::Bitvector32Term::Variable(x);
    let lo_bits = crate::kernel::Bitvector32Term::Variable(lo);
    let hi_bits = crate::kernel::Bitvector32Term::Variable(hi);
    let arguments = vec![
        crate::kernel::CExpression::Value(crate::kernel::int32(x_bits.clone())),
        crate::kernel::CExpression::Value(crate::kernel::int32(lo_bits.clone())),
        crate::kernel::CExpression::Value(crate::kernel::int32(hi_bits.clone())),
    ];
    let below_lo = crate::kernel::ConditionTerm::Bitvector32SignedLessThan(
        Box::new(x_bits.clone()),
        Box::new(lo_bits.clone()),
    );
    let above_hi = crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan(
        Box::new(x_bits.clone()),
        Box::new(hi_bits.clone()),
    );
    let cases = vec![
        (
            vec![crate::kernel::Proposition::ConditionIs(
                below_lo.clone(),
                true,
            )],
            crate::kernel::int32(lo_bits),
        ),
        (
            vec![
                crate::kernel::Proposition::ConditionIs(below_lo.clone(), false),
                crate::kernel::Proposition::ConditionIs(above_hi.clone(), true),
            ],
            crate::kernel::int32(hi_bits),
        ),
        (
            vec![
                crate::kernel::Proposition::ConditionIs(below_lo, false),
                crate::kernel::Proposition::ConditionIs(above_hi, false),
            ],
            crate::kernel::int32(x_bits),
        ),
    ];

    for (requires, value) in cases {
        let specification = crate::kernel::c_function_specification(
            crate::kernel::CState::new(),
            arguments.clone(),
            requires.clone(),
            crate::kernel::CFunctionOutcome::Return {
                value,
                state: crate::kernel::CState::new(),
            },
        );
        let theorem = crate::kernel::prove_c_function_satisfies_specification(
            function.clone(),
            specification.clone(),
            crate::kernel::Assumptions::new(),
        )
        .expect("clamp branch specification should prove");
        let expected = requires.iter().rev().fold(
            crate::kernel::Proposition::CFunctionSatisfiesSpecification {
                function: function.clone(),
                specification: specification.clone(),
            },
            |body, requirement| {
                crate::kernel::Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
            },
        );

        assert_eq!(theorem.proposition(), &expected);
    }
}

#[test]
fn c0_syntax_targets_kernel_known_function_call_assignment() {
    let increment = syntax::parse_function(
        r#"
        int32 increment(int32 x) {
            return x + 1;
        }
        "#,
    )
    .expect("increment function should parse")
    .to_kernel_function();
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
    .to_kernel_function();

    let local_pointer = crate::kernel::Pointer {
        block: "local:result".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let environment = crate::kernel::CFunctionEnvironment::new().with_function(increment);
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:result", 4)
            .store(local_pointer, crate::kernel::int32(42)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        environment,
        crate::kernel::CCallSemantics::ExecuteBodies,
    )
    .expect("known C0 function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(42),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_while_countdown() {
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
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_int32_literal(3)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("while countdown function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(0),
                state: crate::kernel::CState::new(),
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
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let first = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let third = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(8),
    };
    let local_i = crate::kernel::Pointer {
        block: "local:i".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let initial_memory = crate::kernel::CMemory::new().with_block("buf", 12);
    let resources = write_context(base.clone(), 0, 3);
    let state = crate::kernel::CState::new()
        .with_memory(initial_memory)
        .with_resource_context(resources.clone());
    let final_memory = crate::kernel::CMemory::new()
        .with_block("buf", 12)
        .with_block("local:i", 4)
        .store(first, crate::kernel::int32(0))
        .store(second, crate::kernel::int32(1))
        .store(third, crate::kernel::int32(2))
        .store(local_i, crate::kernel::int32(3));
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("fill3 should execute without memory obligations");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(2),
                state: crate::kernel::CState::new()
                    .with_memory(final_memory)
                    .with_resource_context(resources),
            },
        }
    );
}
