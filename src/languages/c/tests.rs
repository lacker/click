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
fn c0_accepts_standard_integer_spellings_and_struct_typedefs() {
    let function = syntax::parse_function(
        r#"
        struct record {
            int value;
            unsigned char tag;
        };
        typedef struct record record_t;
        typedef int32_t index_t;

        int read_record(record_t* record, index_t index) {
            int result;
            uint8_t tag;
            result = record->value + index;
            tag = record->tag;
            return result + tag;
        }
        "#,
    )
    .expect("standard C spellings and typedefs should parse");

    assert_eq!(function.return_type(), syntax::C0Type::Int32);
    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );
    assert_eq!(function.parameters()[0].struct_name(), Some("record"));
    assert_eq!(function.parameters()[1].c_type(), syntax::C0Type::Int32);
    assert_eq!(
        function.structs()["record"].field("tag").unwrap().c_type(),
        syntax::C0Type::UInt8
    );
}

#[test]
fn c0_rejects_unmodeled_standard_integer_widths_and_char() {
    for (source, spelling) in [
        ("long unsupported() { return 0; }", "long"),
        ("size_t unsupported() { return 0; }", "size_t"),
        ("char unsupported() { return 0; }", "char"),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unmodeled standard C types should be rejected");
        assert!(
            error.message().contains(spelling),
            "diagnostic for `{spelling}` did not mention the spelling: {}",
            error.message()
        );
    }
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
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                contains_call(body)
            }
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
fn c0_syntax_accepts_a_comma_separated_for_step() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            int32 j = 3;
            for (i = 0; i < 3; i++, j--) {
                j = j + 1;
            }
            return j;
        }
        "#,
    )
    .expect("a for-loop step may sequence scalar updates with commas");
}

#[test]
fn c0_syntax_accepts_omitted_for_initializer_and_step() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            for (; i < 3;) {
                i++;
            }
            return i;
        }
        "#,
    )
    .expect("a for loop may omit its initializer and step");
}

#[test]
fn c0_syntax_accepts_unary_plus_and_a_for_initializer_list() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i;
            int32 j;
            for (i = +0, j = +3; i < 3; i++) {
                j = j + 1;
            }
            return j;
        }
        "#,
    )
    .expect("unary plus and comma-separated scalar for initializers should parse");
}

#[test]
fn c0_syntax_accepts_multiple_declarations_in_a_for_initializer() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 total = 0;
            for (int32 i = 0, j = 3; i < 3; i++, j--) {
                total = total + j;
            }
            return total;
        }
        "#,
    )
    .expect("a for-loop initializer may declare multiple initialized scalars");
}

#[test]
fn c0_syntax_accepts_a_do_while_loop_with_an_unbraced_body() {
    let function = syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            do
                i++;
            while (i < 3);
            return i;
        }
        "#,
    )
    .expect("a do-while loop may control one statement without braces");

    fn contains_do_while(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::DoWhile { .. } => true,
            syntax::C0Statement::Seq(first, second) => {
                contains_do_while(first) || contains_do_while(second)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_do_while(then_branch) || contains_do_while(else_branch),
            syntax::C0Statement::While { body, .. } => contains_do_while(body),
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().any(|case| contains_do_while(case.body()))
            }
            _ => false,
        }
    }

    assert!(contains_do_while(function.body()));
}

#[test]
fn c0_syntax_accepts_break_and_continue_in_while_bodies() {
    let function = syntax::parse_function(
        r#"
        int32 control() {
            int32 i = 0;
            while (i < 4) {
                i++;
                if (i == 1) {
                    continue;
                }
                if (i == 3) {
                    break;
                }
            }
            return i;
        }
        "#,
    )
    .expect("break and continue should parse in a while body");

    fn count_controls(statement: &syntax::C0Statement) -> (usize, usize) {
        match statement {
            syntax::C0Statement::Break => (1, 0),
            syntax::C0Statement::Continue => (0, 1),
            syntax::C0Statement::Seq(first, second) => {
                let (breaks, continues) = count_controls(first);
                let (more_breaks, more_continues) = count_controls(second);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let (breaks, continues) = count_controls(then_branch);
                let (more_breaks, more_continues) = count_controls(else_branch);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                count_controls(body)
            }
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().map(|case| count_controls(case.body())).fold(
                    (0, 0),
                    |(breaks, continues), (more_breaks, more_continues)| {
                        (breaks + more_breaks, continues + more_continues)
                    },
                )
            }
            _ => (0, 0),
        }
    }

    assert_eq!(count_controls(function.body()), (1, 1));
}

#[test]
fn c0_syntax_accepts_break_and_continue_in_do_while_bodies() {
    let function = syntax::parse_function(
        r#"
        int32 control() {
            int32 i = 0;
            do {
                i++;
                if (i == 1) {
                    continue;
                }
                break;
            } while (i < 4);
            return i;
        }
        "#,
    )
    .expect("break and continue should parse in a do-while body");

    fn count_controls(statement: &syntax::C0Statement) -> (usize, usize) {
        match statement {
            syntax::C0Statement::Break => (1, 0),
            syntax::C0Statement::Continue => (0, 1),
            syntax::C0Statement::Seq(first, second) => {
                let (breaks, continues) = count_controls(first);
                let (more_breaks, more_continues) = count_controls(second);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let (breaks, continues) = count_controls(then_branch);
                let (more_breaks, more_continues) = count_controls(else_branch);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::DoWhile { body, .. } => count_controls(body),
            _ => (0, 0),
        }
    }

    assert_eq!(count_controls(function.body()), (1, 1));
}

#[test]
fn c0_syntax_accepts_switch_cases_and_nested_loop_control() {
    let function = syntax::parse_function(
        r#"
        int32 choose(int32 kind) {
            int32 result = 0;
            while (kind < 2) {
                switch (kind) {
                    case 0:
                        result = 1;
                    case '1':
                        result = 2;
                        continue;
                    default:
                        result = 3;
                        break;
                }
                break;
            }
            return result;
        }
        "#,
    )
    .expect("switch cases should parse inside a while body");

    fn find_switch(statement: &syntax::C0Statement) -> Option<&syntax::C0Statement> {
        match statement {
            syntax::C0Statement::Switch { .. } => Some(statement),
            syntax::C0Statement::Seq(first, second) => {
                find_switch(first).or_else(|| find_switch(second))
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => find_switch(then_branch).or_else(|| find_switch(else_branch)),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                find_switch(body)
            }
            _ => None,
        }
    }

    let Some(syntax::C0Statement::Switch { expression, cases }) = find_switch(function.body())
    else {
        panic!("expected native switch statement");
    };
    assert!(matches!(expression, syntax::C0Expression::Variable(name) if name == "kind"));
    assert_eq!(cases.len(), 3);
    assert_eq!(cases[0].value(), Some(0));
    assert_eq!(cases[1].value(), Some(u32::from(b'1')));
    assert_eq!(cases[2].value(), None);
}

#[test]
fn c0_syntax_rejects_unsupported_switch_shapes() {
    for (source, expected) in [
        (
            "int32 bad(int32 kind) { switch (kind) { case 1: break; case 1: break; } return 0; }",
            "duplicate `case` label",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) { default: break; default: break; } return 0; }",
            "only one `default`",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) { case kind: break; } return 0; }",
            "integer or character literal",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) { kind = 1; case 0: break; } return 0; }",
            "must begin with a `case` or `default` label",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) {} return 0; }",
            "must contain a `case` or `default` label",
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported switch shape should be rejected");
        assert!(
            error.message().contains(expected),
            "diagnostic did not contain `{expected}`: {}",
            error.message()
        );
    }
}

#[test]
fn c0_syntax_rejects_loop_control_outside_its_supported_loop() {
    for (source, expected) in [
        (
            "int32 bad() { break; return 0; }",
            "`break` must be inside a loop or switch",
        ),
        (
            "int32 bad() { continue; return 0; }",
            "`continue` must be inside a loop",
        ),
        (
            "int32 bad() { for (; 0;) { continue; } return 0; }",
            "`continue` in a `for` loop is not supported",
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported loop-control placement should be rejected");
        assert!(
            error.message().contains(expected),
            "diagnostic did not contain `{expected}`: {}",
            error.message()
        );
    }
}

#[test]
fn c0_syntax_accepts_prefix_scalar_updates() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            ++i;
            --i;
            for (; i < 3; ++i) {
            }
            return i;
        }
        "#,
    )
    .expect("prefix scalar updates should parse as standalone statements and for steps");
}

#[test]
fn c0_syntax_accepts_a_local_declaration_list() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0, j = 1, k = 2;
            return i + j + k;
        }
        "#,
    )
    .expect("a local declaration may contain multiple initialized declarators");
}

#[test]
fn c0_syntax_accepts_a_struct_field_declaration_list() {
    syntax::parse_function(
        r#"
        struct pair {
            int32 first, second;
            uint8 low, high;
        };

        int32 sum_pair(struct pair* value) {
            return value->first + value->second;
        }
        "#,
    )
    .expect("a struct declaration may contain multiple fields");
}

#[test]
fn c0_syntax_accepts_the_remaining_scalar_compound_assignments() {
    syntax::parse_function(
        r#"
        int32 updates() {
            int32 value = 255;
            value /= 3;
            value %= 10;
            value <<= 1;
            value >>= 1;
            value &= 3;
            value |= 4;
            return value;
        }
        "#,
    )
    .expect("scalar compound arithmetic, shift, and bitwise updates should parse");
}

#[test]
fn c0_syntax_accepts_memory_lvalue_updates() {
    let function = syntax::parse_function(
        r#"
        struct counter {
            int32 count;
        };

        int32 updates(int32 values[], struct counter* counter) {
            values[0] += 1;
            ++counter->count;
            counter->count--;
            return values[0] + counter->count;
        }
        "#,
    )
    .expect("indexed and field compound updates should parse");

    fn update_targets<'a>(
        statement: &'a syntax::C0Statement,
        targets: &mut Vec<&'a syntax::C0Expression>,
    ) {
        match statement {
            syntax::C0Statement::Update { target, .. } => targets.push(target),
            syntax::C0Statement::Seq(first, second) => {
                update_targets(first, targets);
                update_targets(second, targets);
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                update_targets(then_branch, targets);
                update_targets(else_branch, targets);
            }
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                update_targets(body, targets)
            }
            _ => {}
        }
    }

    let mut targets = Vec::new();
    update_targets(function.body(), &mut targets);
    assert_eq!(targets.len(), 3);
    assert!(matches!(targets[0], syntax::C0Expression::Index(_, _)));
    assert!(matches!(
        targets[1],
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32,
            ..
        }
    ));
    assert!(matches!(
        targets[2],
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32,
            ..
        }
    ));
}

#[test]
fn c0_syntax_accepts_scalar_casts_and_conditional_expressions() {
    let function = syntax::parse_function(
        r#"
        int32 choose(int32 condition, uint8 left, int32 right) {
            return condition ? (int32) left : right + 1;
        }
        "#,
    )
    .expect("scalar casts and conditional expressions should parse");

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Conditional {
            condition,
            then_branch,
            else_branch,
        }) if matches!(condition.as_ref(), syntax::C0Expression::Variable(name) if name == "condition")
            && matches!(
                then_branch.as_ref(),
                syntax::C0Expression::Cast {
                    c_type: syntax::C0Type::Int32,
                    expression,
                } if matches!(expression.as_ref(), syntax::C0Expression::Variable(name) if name == "left")
            )
            && matches!(
                else_branch.as_ref(),
                syntax::C0Expression::Add(left, right)
                    if matches!(left.as_ref(), syntax::C0Expression::Variable(name) if name == "right")
                        && matches!(right.as_ref(), syntax::C0Expression::Int32Literal(1))
            )
    ));
}

#[test]
fn c0_syntax_rejects_non_scalar_casts() {
    let error = syntax::parse_function(
        r#"
        int32 bad(int32* value) {
            return (int32*) value;
        }
        "#,
    )
    .expect_err("pointer casts are outside the scalar cast subset");
    assert!(error.message().contains("scalar values"));
}

#[test]
fn c0_syntax_rejects_overlong_local_array_initializers() {
    let error = syntax::parse_function(
        r#"
        int32 unsupported() {
            int32 values[2] = {1, 2, 3};
            return 0;
        }
        "#,
    )
    .expect_err("an array initializer cannot exceed the declared length");

    assert_eq!(error.message(), "too many initializers for `values[2]`");
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
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                contains_skip(body)
            }
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().any(|case| contains_skip(case.body()))
            }
            syntax::C0Statement::Break
            | syntax::C0Statement::Continue
            | syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::Assign { .. }
            | syntax::C0Statement::Call { .. }
            | syntax::C0Statement::CallAssign { .. }
            | syntax::C0Statement::HeapAllocate { .. }
            | syntax::C0Statement::HeapFree { .. }
            | syntax::C0Statement::Return(_)
            | syntax::C0Statement::Store { .. }
            | syntax::C0Statement::Update { .. } => false,
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
fn c0_syntax_parses_c_integer_literal_radices_and_suffixes() {
    let literals = syntax::parse_function(
        r#"
        int32 literals() {
            return 0x0Fu | 010U;
        }
        "#,
    )
    .expect("C integer literal radices and suffixes should parse");
    assert!(matches!(
        literals.body(),
        syntax::C0Statement::Return(syntax::C0Expression::BitwiseOr(left, right))
            if matches!(left.as_ref(), syntax::C0Expression::Int32Literal(15))
                && matches!(right.as_ref(), syntax::C0Expression::Int32Literal(8))
    ));

    let minimum = syntax::parse_function(
        r#"
        int32 minimum() {
            return -0x80000000L;
        }
        "#,
    )
    .expect("negative hexadecimal literals should preserve int32 minimum");
    assert!(matches!(
        minimum.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Int32Literal(0x8000_0000))
    ));
}

#[test]
fn c0_syntax_rejects_invalid_octal_literals() {
    let error = syntax::parse_function(
        r#"
        int32 invalid() {
            return 08;
        }
        "#,
    )
    .expect_err("digits outside the octal range must not silently become decimal");
    assert!(
        error.message().contains("octal literal"),
        "{}",
        error.message()
    );
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
fn c0_struct_layout_preserves_embedded_struct_shape() {
    #[repr(C)]
    struct HostInner {
        value: i32,
        flag: u8,
    }
    #[repr(C)]
    struct HostOuter {
        tag: u8,
        inner: HostInner,
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
            int32 tail;
        };

        int32 read_nested(struct outer* packet) {
            return packet->inner.value;
        }
        "#,
    )
    .expect("embedded struct fields should parse");
    let inner = function.structs().get("inner").expect("inner layout");
    let outer = function.structs().get("outer").expect("outer layout");

    assert_eq!(
        inner.size_bytes() as usize,
        std::mem::size_of::<HostInner>()
    );
    assert_eq!(
        inner.alignment_bytes() as usize,
        std::mem::align_of::<HostInner>()
    );
    assert_eq!(outer.field("tag").unwrap().offset_bytes() as usize, 0);
    assert_eq!(
        outer.field("inner").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, inner)
    );
    assert_eq!(outer.field("inner").unwrap().struct_name(), Some("inner"));
    assert_eq!(
        outer.field("inner").unwrap().byte_width() as usize,
        std::mem::size_of::<HostInner>()
    );
    assert_eq!(
        outer.field("tail").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, tail)
    );
    assert_eq!(
        outer.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
    assert_eq!(
        outer.alignment_bytes() as usize,
        std::mem::align_of::<HostOuter>()
    );
}

#[test]
fn c0_embedded_struct_field_access_lowers_to_nested_scalar_offset() {
    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
        };

        int32 write_nested(struct outer* packet) {
            packet->inner.value = 7;
            return packet->inner.value;
        }
        "#,
    )
    .expect("nested embedded field access should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 4);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 8))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 8).store(
            crate::kernel::Pointer {
                block: "packet".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(4),
            },
            crate::kernel::int32(7),
        ))
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("nested embedded field access should execute");

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
fn c0_rejects_embedded_struct_values_outside_member_access() {
    let error = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
        };
        struct outer {
            struct inner inner;
        };

        int32 invalid(struct outer* packet) {
            return packet->inner;
        }
        "#,
    )
    .expect_err("embedded struct values should not be loaded as scalars");

    assert!(
        error
            .to_string()
            .contains("embedded struct fields are only supported through member access")
    );
}

#[test]
fn c0_syntax_lowers_struct_malloc_sizeof_and_free() {
    fn contains_heap_operations(statement: &syntax::C0Statement) -> (bool, bool) {
        match statement {
            syntax::C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => {
                assert_eq!(target, "item");
                assert!(!zeroed);
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
fn c0_syntax_accepts_realloc_with_two_arguments() {
    let function = syntax::parse_function(
        r#"
        int32* resize(int32* data, int32 bytes) {
            int32* result = realloc(data, bytes);
            return result;
        }
        "#,
    )
    .expect("realloc should parse as a two-argument pointer call");

    fn find_realloc(statement: &syntax::C0Statement) -> Option<usize> {
        match statement {
            syntax::C0Statement::CallAssign {
                function_name,
                arguments,
                ..
            } if function_name == "realloc" => Some(arguments.len()),
            syntax::C0Statement::Seq(first, second) => {
                find_realloc(first).or_else(|| find_realloc(second))
            }
            _ => None,
        }
    }

    assert_eq!(find_realloc(function.body()), Some(2));

    let error = syntax::parse_function(
        "int32* bad(int32* data) { int32* result = realloc(data); return result; }",
    )
    .expect_err("realloc must have two arguments");
    assert!(error.message().contains("`realloc` expects two arguments"));
}

#[test]
fn c0_syntax_lowers_calloc_to_zeroed_runtime_allocation() {
    fn find_allocation(
        statement: &syntax::C0Statement,
    ) -> Option<(&str, &syntax::C0Expression, bool)> {
        match statement {
            syntax::C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => Some((target, bytes, *zeroed)),
            syntax::C0Statement::Seq(first, second) => {
                find_allocation(first).or_else(|| find_allocation(second))
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => find_allocation(then_branch).or_else(|| find_allocation(else_branch)),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                find_allocation(body)
            }
            _ => None,
        }
    }

    let function = syntax::parse_function(
        r#"
        int32* allocate_zeroed(int32 count) {
            int32* data = calloc(count, sizeof(int32));
            return data;
        }
        "#,
    )
    .expect("calloc should parse for int32 allocations");
    let (target, bytes, zeroed) = find_allocation(function.body()).expect("calloc should lower");
    assert_eq!(target, "data");
    assert!(zeroed);
    assert_eq!(
        bytes,
        &syntax::C0Expression::Multiply(
            Box::new(syntax::C0Expression::Variable("count".to_string())),
            Box::new(syntax::C0Expression::SizeOfType {
                c_type: syntax::C0Type::Int32,
                struct_name: None,
                bytes: 4,
            }),
        )
    );
}

#[test]
fn c0_syntax_accepts_matching_struct_calloc() {
    let function = syntax::parse_function(
        r#"
        struct item { int32 value; };
        int32 allocate_zeroed(int32 count) {
            struct item* item = calloc(count, sizeof(struct item));
            return item->value;
        }
        "#,
    )
    .expect("calloc should accept a matching struct element size");

    fn find_allocation(
        statement: &syntax::C0Statement,
    ) -> Option<(&str, &syntax::C0Expression, bool)> {
        match statement {
            syntax::C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => Some((target, bytes, *zeroed)),
            syntax::C0Statement::Seq(first, second) => {
                find_allocation(first).or_else(|| find_allocation(second))
            }
            _ => None,
        }
    }

    let (target, bytes, zeroed) =
        find_allocation(function.body()).expect("struct calloc should lower");
    assert_eq!(target, "item");
    assert!(zeroed);
    assert_eq!(
        bytes,
        &syntax::C0Expression::Multiply(
            Box::new(syntax::C0Expression::Variable("count".to_string())),
            Box::new(syntax::C0Expression::SizeOfStruct {
                name: "item".to_string(),
                bytes: 4,
            }),
        )
    );
}

#[test]
fn c0_syntax_accepts_sizeof_for_scalar_and_pointer_types() {
    let function = syntax::parse_function(
        r#"
        int32 sizes() {
            return sizeof(int32) + sizeof(uint8) + sizeof(int32*) + sizeof(uint8**);
        }
        "#,
    )
    .expect("sizeof should accept every supported scalar and pointer type");

    let syntax::C0Statement::Return(expression) = function.body() else {
        panic!("sizeof expression should remain in the return statement");
    };
    let kernel_expression = expression.to_kernel_expression();
    assert_eq!(
        kernel_expression,
        crate::kernel::c_add(
            crate::kernel::c_add(
                crate::kernel::c_add(
                    crate::kernel::c_int32_literal(4),
                    crate::kernel::c_int32_literal(1),
                ),
                crate::kernel::c_int32_literal(8),
            ),
            crate::kernel::c_int32_literal(8),
        )
    );
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
        .store(root.clone(), crate::kernel::CValue::pointer(leaf.clone()))
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
        .with_local("root", crate::kernel::CValue::pointer(root))
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
        .with_local("p", crate::kernel::CValue::pointer(pointer.clone()))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_local("p", crate::kernel::CValue::pointer(pointer.clone()))
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
        .with_local("obj", crate::kernel::CValue::pointer(pointer.clone()))
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
        crate::kernel::CExpressionOutcome::Value(crate::kernel::CValue::pointer(data.clone()))
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
                .store(local_q, crate::kernel::CValue::pointer(second.clone())),
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
fn c0_syntax_lowers_local_array_initializer_stores() {
    let function = syntax::parse_function(
        r#"
        int32 local_array_initializer() {
            int32 a[3] = {1, 2};
            return a[2];
        }
        "#,
    )
    .expect("local array initializer should parse")
    .to_kernel_function();

    let a0 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let a1 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let a2 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(8),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:a", 12)
            .store(a0, crate::kernel::int32(1))
            .store(a1, crate::kernel::int32(2))
            .store(a2, crate::kernel::int32(0)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local array initializer should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(0),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_flattens_multidimensional_local_array_indices() {
    let function = syntax::parse_function(
        r#"
        int32 matrix_roundtrip() {
            int32 values[2][3];
            values[0][0] = 1;
            values[1][2] = 7;
            return values[1][2];
        }
        "#,
    )
    .expect("multidimensional local array should parse")
    .to_kernel_function();

    let first = crate::kernel::Pointer {
        block: "local:values".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let last = crate::kernel::Pointer {
        block: "local:values".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(20),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:values", 24)
            .store(first, crate::kernel::int32(1))
            .store(last, crate::kernel::int32(7)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("multidimensional local array should execute");

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
fn c0_syntax_lowers_nested_multidimensional_array_initializers() {
    let function = syntax::parse_function(
        r#"
        int32 matrix_initializer() {
            int32 values[2][3] = {{1, 2, 3}, {4, 5, 6}};
            return values[1][2];
        }
        "#,
    )
    .expect("nested multidimensional array initializers should parse")
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:values", 24)
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                },
                crate::kernel::int32(1),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(4),
                },
                crate::kernel::int32(2),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(8),
                },
                crate::kernel::int32(3),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(12),
                },
                crate::kernel::int32(4),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(16),
                },
                crate::kernel::int32(5),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(20),
                },
                crate::kernel::int32(6),
            ),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("nested multidimensional array initializers should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(6),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_lowers_local_struct_array_fields_with_abi_stride() {
    let function = syntax::parse_function(
        r#"
        struct item {
            uint8 tag;
            int32 value;
        };

        int32 struct_array_roundtrip() {
            struct item items[2];
            items[0].tag = 3;
            items[1].value = 7;
            return items[0].tag + items[1].value;
        }
        "#,
    )
    .expect("local arrays of structs should parse")
    .to_kernel_function();

    let tag = crate::kernel::Pointer {
        block: "local:items".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let value = crate::kernel::Pointer {
        block: "local:items".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(12),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:items", 16)
            .store(tag, crate::kernel::uint8(3))
            .store(value, crate::kernel::int32(7)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local struct array fields should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(10),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_struct_array_parameter_retains_abi_stride() {
    let function = syntax::parse_function(
        r#"
        struct item {
            uint8 tag;
            int32 value;
        };

        int32 read_item(struct item items[2]) {
            return items[1].value;
        }
        "#,
    )
    .expect("struct array parameters should parse");

    let parameter = &function.parameters()[0];
    assert_eq!(parameter.c_type(), syntax::C0Type::Int32Pointer);
    assert_eq!(parameter.array_element_width(), Some(8));
    assert_eq!(
        parameter.to_kernel_parameter().c_type(),
        crate::kernel::CType::UInt8Pointer
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
fn c0_struct_layout_preserves_inline_scalar_array_shape() {
    #[repr(C)]
    struct HostPacket {
        buf: [u8; 16],
        values: [i32; 2],
        count: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 buf[16];
            int32 values[2];
            int32 count;
        };

        int32 read_packet(struct packet* packet) {
            return packet->buf[2] + packet->count;
        }
        "#,
    )
    .expect("inline scalar array fields should parse");
    let layout = function.structs().get("packet").expect("packet layout");

    assert_eq!(
        layout.field("buf").unwrap().c_type(),
        syntax::C0Type::UInt8Array(16)
    );
    assert_eq!(
        layout.field("buf").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, buf)
    );
    assert_eq!(
        layout.field("values").unwrap().c_type(),
        syntax::C0Type::Int32Array(2)
    );
    assert_eq!(
        layout.field("values").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, values)
    );
    assert_eq!(
        layout.field("count").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, count)
    );
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );
}

#[test]
fn c0_struct_inline_scalar_array_field_supports_indexed_load_and_store() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 buf[16];
        };

        uint8 write_packet(struct packet* packet) {
            packet->buf[2] = 7;
            return packet->buf[2];
        }
        "#,
    )
    .expect("indexed inline scalar array access should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 4);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 16))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 16)
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(2),
                    },
                    crate::kernel::uint8(7),
                ),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("indexed inline scalar array access should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::uint8(7),
                state: final_state,
            },
        }
    );
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
fn c0_syntax_rejects_a_declaration_that_shadows_an_enclosing_local() {
    let error = syntax::parse_function(
        r#"
        int32 shadow(int32 c) {
            int32 y = 10;
            if (c < 0) { int32 y = 5; } else { int32 y = 5; }
            return y;
        }
        "#,
    )
    .expect_err("an inner `int32 y` shadows the outer local");
    assert!(
        error
            .message()
            .contains("`y` is already declared in an enclosing scope"),
        "{}",
        error.message()
    );
    assert!(
        error.position().is_some(),
        "the diagnostic names the declaration"
    );
}

#[test]
fn c0_syntax_rejects_a_declaration_that_shadows_a_parameter() {
    let error = syntax::parse_function(
        r#"
        struct S { int32 a; int32 b; };
        struct T { int32 b; int32 z; };
        int32 pick2(struct S* p, struct T* q, int32 c) {
            if (c < 0) { struct T *p = q; p->b = 1; }
            return p->b;
        }
        "#,
    )
    .expect_err("an inner `struct T *p` shadows the parameter");
    assert!(
        error
            .message()
            .contains("`p` is already declared in an enclosing scope"),
        "{}",
        error.message()
    );
}

#[test]
fn c0_syntax_accepts_sibling_scopes_reusing_a_name() {
    // `q->z` exists only in `T` and `q->a` only in `S`: the second arm parses
    // only if the first arm's struct binding for `q` ended with its block.
    syntax::parse_function(
        r#"
        struct S { int32 a; int32 b; };
        struct T { int32 b; int32 z; };
        int32 siblings(struct S* s, struct T* t, int32 c) {
            int32 r;
            if (c < 0) { int32 v = 1; r = v; } else { int32 v = 2; r = v; }
            for (int32 i = 0; i < 2; i++) { r = r + i; }
            for (int32 i = 0; i < 2; i++) { r = r + i; }
            if (c < 0) { struct T *q = t; r = q->z; } else { struct S *q = s; r = q->a; }
            return r;
        }
        "#,
    )
    .expect("names reused in sibling scopes are distinct objects");
}

#[test]
fn c0_syntax_accepts_else_if_and_unbraced_controlled_statements() {
    let function = syntax::parse_function(
        r#"
        int32 classify(int32 x) {
            if (x < 0)
                return -1;
            else if (x == 0)
                return 0;
            else
                return 1;
        }
        "#,
    )
    .expect("else-if arms may contain one unbraced statement");
    assert!(matches!(
        function.body(),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } if matches!(then_branch.as_ref(), syntax::C0Statement::Return(_))
            && matches!(else_branch.as_ref(), syntax::C0Statement::If { .. })
    ));

    syntax::parse_function(
        r#"
        int32 advance(int32 n) {
            int32 i = 0;
            while (i < n)
                i = i + 1;
            for (int32 j = 0; j < 2; j++)
                i = i + j;
            return i;
        }
        "#,
    )
    .expect("while and for may control one unbraced statement");
}

#[test]
fn c0_syntax_rejects_a_declaration_as_an_unbraced_controlled_statement() {
    let error = syntax::parse_function(
        r#"
        int32 invalid(int32 condition) {
            if (condition)
                int32 value;
            return 0;
        }
        "#,
    )
    .expect_err("C declarations need a compound statement body");
    assert!(
        error
            .message()
            .contains("declaration controlled by `if` must be enclosed in braces"),
        "{}",
        error.message()
    );
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
fn c0_function_pointers_preserve_signature_and_dispatch_callback() {
    let callback =
        syntax::parse_function("int32 compare(int32 left, int32 right) { return left - right; }")
            .expect("callback should parse")
            .to_kernel_function();
    let apply = syntax::parse_function(
        "int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {\
             int32 result; result = callback(left, right); return result;\
         }",
    )
    .expect("callback parameter and indirect call should parse")
    .to_kernel_function();
    let caller = syntax::parse_function(
        "int32 caller() { int32 result; result = apply(&compare, 40, 2); return result; }",
    )
    .expect("function address should parse")
    .to_kernel_function();

    assert!(matches!(
        apply.parameters()[0].c_type(),
        crate::kernel::CType::FunctionPointer(_)
    ));

    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        crate::kernel::CState::new(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        crate::kernel::CExecutionEnvironment::new()
            .with_function(callback)
            .with_function(apply),
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("compatible callback should execute");
    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: crate::kernel::CState::new(),
            function: caller,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(38),
                state: crate::kernel::CState::new().with_memory(
                    crate::kernel::CMemory::new()
                        .with_block("local:result", 4)
                        .store(
                            crate::kernel::Pointer {
                                block: "local:result".into(),
                                offset: crate::kernel::PointerOffsetTerm::Constant(0),
                            },
                            crate::kernel::int32(38),
                        )
                ),
            },
        }
    );
}

#[test]
fn c0_function_pointers_reject_incompatible_callback_targets() {
    let wrong =
        syntax::parse_function("uint8 wrong(uint8 left, uint8 right) { return left - right; }")
            .expect("incompatible callback should parse")
            .to_kernel_function();
    let apply = syntax::parse_function(
        "int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {\
             int32 result; result = callback(left, right); return result;\
         }",
    )
    .expect("callback parameter and indirect call should parse")
    .to_kernel_function();
    let caller = syntax::parse_function(
        "int32 caller() { int32 result; result = apply(&wrong, 40, 2); return result; }",
    )
    .expect("function address should parse")
    .to_kernel_function();

    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        crate::kernel::CState::new(),
        caller,
        Vec::new(),
        Default::default(),
        crate::kernel::CExecutionEnvironment::new()
            .with_function(wrong)
            .with_function(apply),
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("incompatible callback should produce a runtime-error theorem");
    let crate::kernel::Proposition::CFunctionExecutes {
        outcome:
            crate::kernel::CFunctionOutcome::RuntimeError(
                crate::kernel::CRuntimeError::FunctionContract(message),
            ),
        ..
    } = theorem.proposition()
    else {
        panic!("expected incompatible callback error, got {:#?}", theorem);
    };
    assert!(message.contains("incompatible signature"));
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
