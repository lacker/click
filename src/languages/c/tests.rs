use super::*;

fn memory_range(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::CMemoryRange {
    crate::kernel::CMemoryRange::new(base, start.into(), end.into())
}

fn view_memory_context(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::ResourceContext {
    crate::kernel::ResourceContext::new().unchecked_with_fact(
        crate::kernel::CResourceFact::view_memory(memory_range(base, start, end)),
    )
}

fn own_memory_context(
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
fn c0_syntax_ignores_line_and_block_comments() {
    let function = syntax::parse_function(
        r#"
        /* the imported source may retain its documentation */
        int32 identity(int32 value) {
            // comments do not become syntax
            return /* including inline comments */ value;
        }
        "#,
    )
    .expect("ordinary C comments should parse");

    assert_eq!(function.name(), "identity");
}

#[test]
fn large_straight_line_block_parses_and_lowers_on_a_small_stack() {
    std::thread::Builder::new()
        .name("large-straight-line-c-block".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut source = String::from("int32 straight(int32 x) {\n");
            for _ in 0..10_000 {
                source.push_str("x = x;\n");
            }
            source.push_str("return x;\n}\n");

            let function = syntax::parse_function(&source)
                .expect("a large straight-line C block should parse");
            let _lowered = function.to_kernel_function();
        })
        .expect("the small-stack C parser thread should start")
        .join()
        .expect("large straight-line parsing and lowering should be stack bounded");
}

#[test]
fn c0_void_functions_accept_return_and_fallthrough() {
    let explicit = syntax::parse_function("void stop() { return; }")
        .expect("a void function may return without a value");
    let fallthrough = syntax::parse_function("void stop() { int32 value = 0; }")
        .expect("a void function may fall through");

    assert_eq!(explicit.return_type(), syntax::C0Type::Void);
    assert_eq!(fallthrough.return_type(), syntax::C0Type::Void);
    assert_eq!(
        explicit.to_kernel_function().return_type(),
        crate::kernel::CType::Void
    );
}

#[test]
fn c0_void_and_nonvoid_returns_do_not_mix() {
    let void_error = syntax::parse_function("void bad() { return 1; }")
        .expect_err("a void function cannot return a value");
    assert_eq!(void_error.message(), "void functions cannot return a value");

    let value_error = syntax::parse_function("int32 bad() { return; }")
        .expect_err("a non-void function must return a value");
    assert_eq!(
        value_error.message(),
        "non-void functions must return a value"
    );
}

#[test]
fn c0_parses_standalone_calls() {
    let function =
        syntax::parse_function("int32 caller(int32 value) { observe(value); return 0; }")
            .expect("a function result may be discarded");

    fn contains_call(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::Call { function_name, .. } => function_name == "observe",
            syntax::C0Statement::Seq(first, second) => {
                contains_call(first) || contains_call(second)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_call(then_branch) || contains_call(else_branch),
            syntax::C0Statement::While { body, .. } => contains_call(body),
            _ => false,
        }
    }

    assert!(contains_call(function.body()));
}

#[test]
fn c0_syntax_reports_unterminated_block_comments() {
    let error = syntax::parse_function("/* never closed")
        .expect_err("an unterminated block comment should be rejected");

    assert_eq!(error.message(), "unterminated block comment");
}

#[test]
fn c0_syntax_errors_carry_source_positions() {
    let error = syntax::parse_function("int32 broken(int32 x) {\n    return x\n}\n")
        .expect_err("a missing semicolon should be rejected");

    assert_eq!(error.message(), "expected `;`, got `}`");
    assert_eq!(
        error.position(),
        Some(crate::source::SourcePosition::new(3, 1))
    );
    assert_eq!(error.to_string(), "line 3, column 1: expected `;`, got `}`");
}

#[test]
fn c0_syntax_positions_point_at_the_offending_token() {
    let error =
        syntax::parse_function("int32 broken() {\n    int32 x;\n    x = $;\n    return x;\n}\n")
            .expect_err("an unexpected character should be rejected");

    assert_eq!(error.message(), "unexpected character `$`");
    assert_eq!(
        error.position(),
        Some(crate::source::SourcePosition::new(3, 9))
    );
}

#[test]
fn c0_syntax_lowers_scalar_declaration_initializers_in_source_order() {
    let function = syntax::parse_function(
        r#"
        int32 initialized() {
            int32 value = 7;
            return value;
        }
        "#,
    )
    .expect("a scalar declaration initializer should parse");

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Seq(first, _)
            if matches!(
                first.as_ref(),
                syntax::C0Statement::Seq(declaration, assignment)
                    if matches!(
                        declaration.as_ref(),
                        syntax::C0Statement::Declare {
                            c_type: syntax::C0Type::Int32,
                            name
                        } if name == "value"
                    )
                    && matches!(
                        assignment.as_ref(),
                        syntax::C0Statement::Assign {
                            name,
                            expression: syntax::C0Expression::Int32Literal(7)
                        } if name == "value"
                    )
            )
    ));
}

#[test]
fn c0_syntax_accepts_declaration_initializer_in_for_loop() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 total = 0;
            for (int32 i = 0; i < 3; i++) {
                total += 1;
            }
            return total;
        }
        "#,
    )
    .expect("a scalar for-loop declaration initializer should parse");
}

#[test]
fn c0_syntax_names_unsupported_local_array_initializers() {
    let error = syntax::parse_function(
        r#"
        int32 unsupported() {
            int32 values[2] = 0;
            return 0;
        }
        "#,
    )
    .expect_err("array initialization is not in the C0 subset");

    assert_eq!(
        error.message(),
        "local array initializers are not supported"
    );
}

#[test]
fn c0_syntax_models_missing_else_and_empty_statements_as_skip() {
    let function = syntax::parse_function(
        r#"
        int32 nonnegative(int32 value) {
            ;
            if (value < 0) {
                return 0;
            }
            if (value == 0) {
            }
            return value;
        }
        "#,
    )
    .expect("if statements should not require artificial else branches");

    fn contains_skip(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::Skip => true,
            syntax::C0Statement::Seq(first, second) => {
                contains_skip(first) || contains_skip(second)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_skip(then_branch) || contains_skip(else_branch),
            syntax::C0Statement::While { body, .. } => contains_skip(body),
            syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::Assign { .. }
            | syntax::C0Statement::Call { .. }
            | syntax::C0Statement::CallAssign { .. }
            | syntax::C0Statement::HeapAllocate { .. }
            | syntax::C0Statement::HeapFree { .. }
            | syntax::C0Statement::Return(_)
            | syntax::C0Statement::Store { .. } => false,
        }
    }

    assert!(contains_skip(function.body()));
}

#[test]
fn kernel_skip_preserves_state_without_facts_or_obligations() {
    let state = crate::kernel::CState::new();
    let theorem = crate::kernel::prove_symbolic_c_execution(
        state.clone(),
        crate::kernel::c_skip(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("skip should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: state.clone(),
            statement: crate::kernel::c_skip(),
            outcome: crate::kernel::CStatementOutcome::Normal(state),
        }
    );
}

#[test]
fn c0_syntax_parses_negative_literals_and_unary_minus() {
    let literal = syntax::parse_function(
        r#"
        int32 negative_one() {
            return -1;
        }
        "#,
    )
    .expect("negative literals should parse");
    assert!(matches!(
        literal.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Int32Literal(value))
            if *value == (-1i32) as u32
    ));

    let minimum = syntax::parse_function(
        r#"
        int32 minimum() {
            return -2147483648;
        }
        "#,
    )
    .expect("the minimum int32 literal should parse");
    assert!(matches!(
        minimum.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Int32Literal(0x8000_0000))
    ));

    let negation = syntax::parse_function(
        r#"
        int32 negate(int32 value) {
            return -value;
        }
        "#,
    )
    .expect("general unary minus should parse");
    assert!(matches!(
        negation.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Subtract(left, right))
            if matches!(
                left.as_ref(),
                syntax::C0Expression::Int32Literal(0)
            ) && matches!(
                right.as_ref(),
                syntax::C0Expression::Variable(name) if name == "value"
            )
    ));
}

#[test]
fn c0_unary_minus_preserves_signed_overflow_semantics() {
    let function = syntax::parse_function(
        r#"
        int32 negate(int32 value) {
            return -value;
        }
        "#,
    )
    .expect("unary minus function should parse");
    let state = crate::kernel::CState::new().with_local(
        "value",
        crate::kernel::int32(crate::kernel::Bitvector32Term::Constant(0x8000_0000)),
    );
    let theorem = crate::kernel::prove_symbolic_c_execution(
        state.clone(),
        function.body_kernel_statement(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("concrete signed overflow should have an execution theorem");
    let mut proposition = theorem.proposition();
    while let crate::kernel::Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        crate::kernel::Proposition::CStatementExecutes {
            outcome: crate::kernel::CStatementOutcome::UndefinedBehavior(
                crate::kernel::CUndefinedBehavior::SignedOverflow
            ),
            ..
        }
    ));
}

#[test]
fn c0_syntax_retains_struct_pointee_types_across_chained_fields() {
    let function = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };
        struct node {
            struct leaf* child;
        };

        int32 read_nested(struct node* root) {
            return root->child->value;
        }
        "#,
    )
    .expect("chained struct-pointer fields should parse");

    let child = function
        .structs()
        .get("node")
        .and_then(|layout| layout.field("child"))
        .expect("node child field");
    assert_eq!(child.struct_name(), Some("leaf"));

    let syntax::C0Statement::Return(syntax::C0Expression::Field {
        pointer,
        field_type: syntax::C0Type::Int32,
        field_struct_name: None,
    }) = function.body()
    else {
        panic!("the terminal scalar field should retain its resolved type")
    };
    assert!(matches!(
        pointer.as_ref(),
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32Pointer,
            field_struct_name: Some(name),
            ..
        } if name == "leaf"
    ));
}

#[test]
fn c0_syntax_lowers_struct_malloc_sizeof_and_free() {
    fn contains_heap_operations(statement: &syntax::C0Statement) -> (bool, bool) {
        match statement {
            syntax::C0Statement::HeapAllocate { target, bytes } => {
                assert_eq!(target, "item");
                assert_eq!(
                    *bytes,
                    syntax::C0Expression::SizeOfStruct {
                        name: "item".to_string(),
                        bytes: 16,
                    }
                );
                (true, false)
            }
            syntax::C0Statement::HeapFree { pointer } => {
                assert_eq!(pointer, &syntax::C0Expression::Variable("item".to_string()));
                (false, true)
            }
            syntax::C0Statement::Seq(first, second) => {
                let first = contains_heap_operations(first);
                let second = contains_heap_operations(second);
                (first.0 || second.0, first.1 || second.1)
            }
            _ => (false, false),
        }
    }

    let function = syntax::parse_function(
        r#"
        struct item {
            int32 value;
            struct item* next;
        };

        int32 allocate_then_free() {
            struct item* item = malloc(sizeof(struct item));
            free(item);
            return 0;
        }
        "#,
    )
    .expect("the supported malloc/free slice should parse");

    assert_eq!(contains_heap_operations(function.body()), (true, true));
}

#[test]
fn c0_syntax_rejects_malloc_size_that_does_not_match_its_target() {
    let error = syntax::parse_function(
        r#"
        struct left { int32 value; };
        struct right { int32 value; };
        struct left* wrong() {
            struct left* value = malloc(sizeof(struct right));
            return value;
        }
        "#,
    )
    .expect_err("malloc must use the target pointee's exact layout");

    assert!(error.message().contains("does not match target type"));
}

#[test]
fn c0_syntax_accepts_runtime_sized_int32_allocation() {
    let function = syntax::parse_function(
        r#"
        int32 allocate(int32 count) {
            int32* data = malloc(count * 4);
            free(data);
            return 0;
        }
        "#,
    )
    .expect("runtime-sized scalar allocation should parse");

    assert!(matches!(function.body(), syntax::C0Statement::Seq(_, _)));
}

#[test]
fn c0_syntax_rejects_dynamic_struct_malloc_and_wrong_free_arity() {
    let malloc_error = syntax::parse_function(
        r#"
        struct item { int32 value; };
        struct item* dynamic(int32 bytes) {
            struct item* item = malloc(bytes);
            return item;
        }
        "#,
    )
    .expect_err("struct allocation still needs its exact layout");
    assert!(
        malloc_error
            .message()
            .contains("requires `sizeof(struct item)`")
    );

    let free_error = syntax::parse_function(
        r#"
        int32 bad_free(int32* value) {
            free(value, value);
            return 0;
        }
        "#,
    )
    .expect_err("free must have one argument");
    assert!(
        free_error
            .message()
            .contains("expects one pointer argument")
    );
}

#[test]
fn c0_chained_field_load_executes_through_typed_pointer_memory() {
    let function = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };
        struct node {
            struct leaf* child;
        };

        int32 read_nested(struct node* root) {
            return root->child->value;
        }
        "#,
    )
    .expect("chained struct-pointer fields should parse");
    let root = crate::kernel::Pointer {
        block: "root".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let leaf = crate::kernel::Pointer {
        block: "leaf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let memory = crate::kernel::CMemory::new()
        .store(root.clone(), crate::kernel::CValue::Pointer(leaf.clone()))
        .store(leaf.clone(), crate::kernel::int32(9));
    let resources = crate::kernel::ResourceContext::new()
        .unchecked_with_fact(crate::kernel::CResourceFact::view_memory(memory_range(
            root.clone(),
            0,
            2,
        )))
        .unchecked_with_fact(crate::kernel::CResourceFact::view_memory(memory_range(
            leaf, 0, 1,
        )));
    let state = crate::kernel::CState::new()
        .with_local("root", crate::kernel::CValue::Pointer(root))
        .with_memory(memory)
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_execution(
        state,
        function.body_kernel_statement(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("the nested typed loads should execute");
    let mut proposition = theorem.proposition();
    while let crate::kernel::Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        crate::kernel::Proposition::CStatementExecutes {
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::CValue::Int32(crate::kernel::Bitvector32Term::Constant(9)),
                ..
            },
            ..
        }
    ));
}

#[test]
fn c0_syntax_parses_chained_field_store_targets() {
    let function = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };
        struct node {
            struct leaf* child;
        };

        int32 write_nested(struct node* root, int32 value) {
            root->child->value = value;
            return value;
        }
        "#,
    )
    .expect("a chained field should remain a typed assignment target");

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Seq(first, _)
            if matches!(
                first.as_ref(),
                syntax::C0Statement::Store {
                    pointer: syntax::C0Expression::Field {
                        field_type: syntax::C0Type::Int32Pointer,
                        field_struct_name: Some(name),
                        ..
                    },
                    value_type: Some(syntax::C0Type::Int32),
                    ..
                } if name == "leaf"
            )
    ));
}

#[test]
fn c0_syntax_names_invalid_field_chains() {
    let error = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };

        int32 invalid(struct leaf* root) {
            return root->value->missing;
        }
        "#,
    )
    .expect_err("a scalar field cannot be dereferenced as a struct pointer");

    assert_eq!(
        error.message(),
        "cannot access field `missing` through a non-struct-pointer expression"
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
    let assumptions =
        crate::kernel::PureFactContext::new().assume_condition(condition.clone(), true);
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
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
        .with_resource_context(view_memory_context(pointer, 0, 1));
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
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
fn c0_syntax_accepts_indexed_store_through_struct_pointer_field() {
    syntax::parse_function(
        r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 set_at(struct vector* owner, int32 index, int32 value) {
            owner->data[index] = value;
            return owner->data[index];
        }
        "#,
    )
    .expect("indexed store through pointer field should parse")
    .to_kernel_function();
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
        .with_resource_context(view_memory_context(base.clone(), 1, 2));
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
        offset: crate::kernel::PointerOffsetTerm::Constant(8),
    };
    let data = crate::kernel::Pointer {
        block: "data".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = crate::kernel::ResourceContext::new().unchecked_with_facts(vec![
        crate::kernel::CResourceFact::own_memory(memory_range(owner.clone(), 0, 4)),
        crate::kernel::CResourceFact::own_memory(memory_range(data.clone(), 0, 1)),
    ]);
    let state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("owner", 16)
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
    let resources = own_memory_context(pointer.clone(), 0, 1);
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
    let resources = view_memory_context(base.clone(), 1, 2);
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
    let resources = view_memory_context(base.clone(), 1, 2);
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
    let resources = own_memory_context(base.clone(), 1, 2);
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
    let resources = view_memory_context(base.clone(), 1, 2);
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
        crate::kernel::PureFactContext::new(),
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
                .with_resource_context(view_memory_context(pointer.clone(), 0, 1)),
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
                .with_resource_context(view_memory_context(pointer.clone(), 0, 1)),
            vec![crate::kernel::c_pointer_value(pointer.clone())],
            crate::kernel::int32(0),
        ),
    ];

    for (state, arguments, expected) in cases {
        let theorem = crate::kernel::prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            arguments.clone(),
            crate::kernel::PureFactContext::new(),
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
        crate::kernel::PureFactContext::new(),
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
    let environment = crate::kernel::CExecutionEnvironment::new().with_function(read_first);
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
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
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
fn c0_struct_layout_uses_lp64_alignment_and_tail_padding() {
    let function = syntax::parse_function(
        r#"
        struct mixed {
            int32 tag;
            int32* data;
            int32 length;
        };

        int32 read_tag(struct mixed* value) {
            return value->tag;
        }
        "#,
    )
    .expect("LP64 struct should parse");
    let layout = function.structs().get("mixed").expect("mixed layout");

    assert_eq!(layout.field("tag").unwrap().offset_bytes(), 0);
    assert_eq!(layout.field("data").unwrap().offset_bytes(), 8);
    assert_eq!(layout.field("length").unwrap().offset_bytes(), 16);
    assert_eq!(layout.alignment_bytes(), 8);
    assert_eq!(layout.size_bytes(), 24);
}

#[test]
fn c0_lp64_layout_matches_the_host_c_abi() {
    #[repr(C)]
    struct HostMixed {
        tag: i32,
        data: *mut i32,
        length: i32,
    }

    assert_eq!(
        std::mem::size_of::<*mut i32>(),
        8,
        "this cross-check requires an LP64 host"
    );
    let function = syntax::parse_function(
        r#"
        struct mixed {
            int32 tag;
            int32* data;
            int32 length;
        };

        int32 read_tag(struct mixed* value) {
            return value->tag;
        }
        "#,
    )
    .expect("LP64 struct should parse");
    let layout = function.structs().get("mixed").expect("mixed layout");

    assert_eq!(
        layout.field("tag").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostMixed, tag)
    );
    assert_eq!(
        layout.field("data").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostMixed, data)
    );
    assert_eq!(
        layout.field("length").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostMixed, length)
    );
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostMixed>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostMixed>()
    );
}

#[test]
fn c0_struct_field_lowering_uses_explicit_byte_offsets() {
    let function = syntax::parse_function(
        r#"
        struct mixed {
            int32 tag;
            int32* data;
        };

        int32* get_data(struct mixed* value) {
            return value->data;
        }
        "#,
    )
    .expect("mixed struct getter should parse");
    let syntax::C0Statement::Return(syntax::C0Expression::Field { pointer, .. }) = function.body()
    else {
        panic!("getter should return a field load")
    };
    assert!(matches!(
        pointer.as_ref(),
        syntax::C0Expression::PointerOffsetBytes { bytes: 8, .. }
    ));
    let crate::kernel::CStatement::Return(crate::kernel::CExpression::TypedLoad {
        pointer,
        value_type: crate::kernel::CType::Int32Pointer,
    }) = function.body_kernel_statement()
    else {
        panic!("field load should retain its value type")
    };
    assert!(matches!(
        pointer.as_ref(),
        crate::kernel::CExpression::PointerOffsetBytes { bytes: 8, .. }
    ));
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
            crate::kernel::PureFactContext::new(),
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
fn c0_equality_binds_looser_than_relational_comparison() {
    let mixed = syntax::parse_function(
        r#"
        int32 mixed(int32 a, int32 b, int32 c) {
            return a == b < c;
        }
        "#,
    )
    .expect("a mixed equality and relational chain should parse");
    assert!(matches!(
        mixed.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Equal(left, right))
            if matches!(left.as_ref(), syntax::C0Expression::Variable(name) if name == "a")
                && matches!(right.as_ref(), syntax::C0Expression::LessThan(_, _))
    ));

    let paired = syntax::parse_function(
        r#"
        int32 paired(int32 a, int32 b, int32 c, int32 d) {
            return a < b == c < d;
        }
        "#,
    )
    .expect("relational operands on both sides of `==` should parse");
    assert!(matches!(
        paired.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Equal(left, right))
            if matches!(left.as_ref(), syntax::C0Expression::LessThan(_, _))
                && matches!(right.as_ref(), syntax::C0Expression::LessThan(_, _))
    ));
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
    let environment = crate::kernel::CExecutionEnvironment::new().with_function(increment);
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
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
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
    let resources = own_memory_context(base.clone(), 0, 3);
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
