use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_00")]
fn integer_parameter_preserves_machine_literal_and_cast_behavior() {
    for (interface_type, expression) in [
        ("int32", "-2147483648"),
        ("int64", "2147483648"),
        ("int64", "-2147483649"),
        ("uint64", "18446744073709551615"),
        ("uint32", "1 as uint32"),
        ("uint32", "(-1) as uint32"),
        ("uint32", "(1 + 2) as uint32"),
    ] {
        for extra in ["", ", unused: Integer"] {
            let source = format!(
                "theorem compatibility(x: {interface_type}{extra}) {{
                    requires x == {expression};
                    ensures x == {expression} by {{ close(); }}
                }}"
            );
            verify_click_theorems(&source)
                .unwrap_or_else(|error| panic!("{source}: {}", error.message()));
        }
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_00")]
fn integer_constant_aliases_stay_shared_before_a_tactic_starts() {
    // Setup retains the repeated-squaring DAG instead of allocating an
    // exponentially large numeral. Reflexivity needs no evaluation.
    for depth in [8, 16, 32, 64] {
        let mut source = String::from("theorem bounded() { let a0: Integer = 2;\n");
        for index in 1..=depth {
            source.push_str(&format!(
                "let a{index}: Integer = a{} * a{};\n",
                index - 1,
                index - 1
            ));
        }
        source.push_str(&format!(
            "requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ close(); }} }}"
        ));
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 1000,
            smart: 1000,
            control: 1000,
        };
        crate::instrumentation::with_tactic_work_limits(limits, || verify_click_theorems(&source))
            .expect("constant aliases stay structural during setup");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_00")]
fn integer_solve_expansion_rechecks_without_smart_search() {
    for (parameters, requires, claim, proof) in [
        ("x: Integer", "", "2 * x + 1 > x + x", "close();"),
        (
            "x: Integer, y: Integer",
            "requires x <= y; requires y <= x;",
            "x == y",
            "close() using { x <= y; y <= x; }",
        ),
    ] {
        let source = format!(
            "theorem expansion({parameters}) {{ {requires} ensures {claim} by {{ {proof} }} }}"
        );
        let verified = verify_click_theorems(&source).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        if parameters.contains("y: Integer") {
            assert!(expanded.contains("le_antisymmetric"), "{expanded}");
        } else {
            assert!(expanded.contains("close();"), "{expanded}");
            assert!(!expanded.contains("normalize("), "{expanded}");
        }
        assert!(!expanded.contains("solve"), "{expanded}");
        let rechecked = source.replace(&format!("by {{ {proof} }}"), &expanded);
        without_implicit_solve(|| verify_click_theorems(&rechecked))
            .unwrap_or_else(|error| panic!("{rechecked}: {}", error.message()));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_01")]
fn integer_alias_certificates_preserve_types_and_linear_source_on_expansion() {
    for depth in [8, 16, 32, 64] {
        let mut source = String::from("theorem aliases(x: Integer) { let a0: Integer = x;\n");
        for index in 1..=depth {
            source.push_str(&format!(
                "let a{index}: Integer = a{} + a{};\n",
                index - 1,
                index - 1
            ));
        }
        source.push_str(&format!(
            "ensures a{depth} + 1 > a{depth} by {{ close() using {{}}; }} }}"
        ));
        let verified = verify_click_theorems(&source).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(expanded.contains("close();"), "{expanded}");
        assert!(
            expanded.len() < 400 * (depth + 1),
            "expansion must retain aliases"
        );
        let rewritten = source.replace("by { close() using {}; }", &expanded);
        assert_ne!(rewritten, source, "the expanded proof must be substituted");
        without_implicit_solve(|| verify_click_theorems(&rewritten))
            .unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_01")]
fn parser_deep_const_rejects_qualification_beyond_first_pointer_level() {
    for spelling in [
        "const int **",
        "int const **",
        "const char **",
        "const int *const *",
        "const struct node **",
        "struct node const **",
        "const struct node *const *",
    ] {
        for signature in [
            format!("int probe({spelling} p)"),
            format!("{spelling} probe()"),
        ] {
            let source = format!("{signature} {{ ensures result == 0; }}");
            let error = parser::parse_file_items(&source).expect_err(
                "deep pointee const must not be conflated with immediate pointee const",
            );
            assert!(
                error.message().contains(
                    "const qualification beyond the first pointer level is not supported"
                ),
                "{signature}: {}",
                error.message()
            );
        }
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_01")]
fn parser_deep_const_preserves_supported_pointer_qualifier_levels() {
    for (spelling, constant, pointee_constant) in [
        ("int **", false, false),
        ("int *const *", false, true),
        ("int **const", true, false),
        ("int *const *const", true, true),
        ("const int *", false, true),
        ("struct node **", false, false),
        ("struct node *const *", false, true),
        ("struct node **const", true, false),
        ("struct node *const *const", true, true),
        ("const struct node *", false, true),
    ] {
        let source = format!("int probe({spelling} p) {{ ensures result == 0; }}");
        let file = parser::parse_file_items(&source).expect("supported qualifiers should parse");
        let parameter = &file.function_blocks()[0].signature().parameters()[0];
        assert_eq!(parameter.is_constant(), constant, "{spelling}");
        assert_eq!(
            parameter.pointee_is_constant(),
            pointee_constant,
            "{spelling}"
        );
        let c_source =
            format!("struct node {{ int value; }}; int probe({spelling} p) {{ return 0; }}");
        let function =
            syntax::parse_function(&c_source).expect("C must accept the same qualifiers");
        let program_parameter = &function.parameters()[0];
        assert_eq!(
            parameter.interface_type(),
            program_parameter.interface_type(),
            "{spelling}"
        );
        assert_eq!(
            parameter.is_constant(),
            program_parameter.is_constant(),
            "{spelling}"
        );
        assert_eq!(
            parameter.pointee_is_constant(),
            program_parameter.pointee_is_constant(),
            "{spelling}"
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_01")]
fn plain_char_needs_a_c_target_and_takes_its_signedness() {
    use crate::languages::c::syntax::PlainChar;
    let source = "int is_negative(char c) { ensures result == 0; }";
    let error = match parser::parse_with_layouts_and_aggregate_objects(
        source,
        parser::ProgramLayouts::default(),
    ) {
        Ok(_) => panic!("plain char without a C target must be refused"),
        Err(error) => error,
    };
    assert!(
        error.message().contains("no C target is selected"),
        "{}",
        error.message()
    );
    for (target, plain) in [
        (
            crate::languages::c::target::CTarget::X86_64LinuxKernel,
            PlainChar::Unsigned,
        ),
        (
            crate::languages::c::target::CTarget::X86_64LinuxUserspace,
            PlainChar::Signed,
        ),
    ] {
        let file = parser::parse_with_layouts_and_aggregate_objects(
            source,
            parser::ProgramLayouts {
                plain_char: Some(target.plain_char()),
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            file.function_blocks()[0].signature().parameters()[0].interface_type(),
            InterfaceType::Char(plain)
        );
    }
    // A character constant at 0x80 or above is the target's plain `char`
    // value, and is refused where no target fixes it.
    let high = "int f() { ensures result == '\\xc8'; }";
    assert!(
        parser::parse_with_layouts_and_aggregate_objects(high, parser::ProgramLayouts::default())
            .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_02")]
fn parser_plain_char_sidecars_preserve_source_compatibility() {
    use crate::surface::validation::click_types_compatible;
    let file = parser::parse_file_items(
        "char *identity(char *p, unsigned char *q, char bytes[], char **pp) { ensures result == p; }",
    ).expect("plain char sidecar types should parse");
    let signature = file.function_blocks()[0].signature();
    // A sidecar's plain `char` takes the default target's signedness.
    let plain = crate::languages::c::target::CTarget::SUPPORTED.plain_char();
    assert_eq!(signature.return_type(), InterfaceType::CharPointer(plain));
    assert_eq!(
        signature
            .parameters()
            .iter()
            .map(FunctionParameter::interface_type)
            .collect::<Vec<_>>(),
        vec![
            InterfaceType::CharPointer(plain),
            InterfaceType::UInt8Pointer,
            InterfaceType::CharPointer(plain),
            InterfaceType::CharPointerPointer(plain)
        ]
    );
    assert!(!click_types_compatible(
        InterfaceType::CharPointer(plain),
        InterfaceType::UInt8Pointer
    ));
    assert!(!click_types_compatible(
        InterfaceType::CharPointerPointer(plain),
        InterfaceType::UInt8PointerPointer
    ));
    assert!(click_types_compatible(
        InterfaceType::CharArray(plain, 2),
        InterfaceType::CharPointer(plain)
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_02")]
fn false_library_list_equality_has_a_bounded_diagnostic() {
    let error = verify_click_theorems(
        r#"
        theorem false_order() {
            ensures List<int32>::Cons(1, List<int32>::Nil)
                == List<int32>::Cons(2, List<int32>::Nil) by { close(); }
        }
    "#,
    )
    .expect_err("different list elements must not be equal");
    assert!(
        error.message().contains(
            "could not establish `List<int32>::Cons(1, List<int32>::Nil()) == \
             List<int32>::Cons(2, List<int32>::Nil())`"
        ),
        "{}",
        error.message()
    );
    assert!(!error.message().contains("AlgebraicSchemas"));
    assert!(error.message().contains("search candidates:"));
    assert!(error.message().len() < 4000, "{}", error.message());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_02")]
fn parser_accepts_its_supported_parenthesis_depth() {
    let source = super::scaling_tests::theorem_with_parenthesized_requirement(
        parser::PARENTHESIS_NESTING_LIMIT,
    );
    parser::parse_file_items(&source).expect("supported parenthesis depth should parse");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_02")]
fn parser_accepts_standard_c_type_spellings_in_sidecars() {
    let file = parser::parse_file_items(
        r#"
        int standard_types(int p[], unsigned char byte, int32_t index, uint8_t tag) {
            ensures result == 0;
        }
        "#,
    )
    .expect("standard C type spellings should parse in sidecars");

    assert_eq!(
        file.function_blocks()[0].signature().return_type(),
        InterfaceType::Int32
    );
    assert_eq!(
        file.function_blocks()[0]
            .signature()
            .parameters()
            .iter()
            .map(FunctionParameter::interface_type)
            .collect::<Vec<_>>(),
        vec![
            InterfaceType::Int32Pointer,
            InterfaceType::UInt8,
            InterfaceType::Int32,
            InterfaceType::UInt8,
        ]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_03")]
fn parser_accepts_bodyless_external_function_contracts() {
    let file = parse(
        r#"
        extern int32 external_identity(int32 x) {
            requires x >= 0;
            ensures result == x;
        }
        "#,
    )
    .expect("bodyless external contracts should parse");

    assert_eq!(file.verifying_sources(), &[] as &[String]);
    assert_eq!(file.function_blocks().len(), 1);
    assert!(file.function_blocks()[0].is_external());
    assert_eq!(
        file.function_blocks()[0].signature().name(),
        "external_identity"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_03")]
fn parser_rejects_excessive_parenthesis_depth_with_a_source_diagnostic() {
    let source = super::scaling_tests::theorem_with_parenthesized_requirement(
        parser::PARENTHESIS_NESTING_LIMIT + 1,
    );
    let error = parser::parse_file_items(&source)
        .expect_err("excessive parenthesis depth should be rejected before recursive parsing");
    assert!(
        error
            .message()
            .contains("parenthesis nesting exceeds Click's supported depth of 16"),
        "unexpected diagnostic: {}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_03")]
fn parser_bounds_non_parenthesized_surface_nesting_before_ast_construction() {
    let supported_not = "not ".repeat(32);
    let supported_source = format!(
        "theorem shallow() {{ requires {supported_not}0 == 0; ensures 0 == 0 by {{ normalize(); }} }}"
    );
    let supported = parse(&supported_source).expect("the supported unary boundary should validate");
    verify_click_theorems(&supported_source)
        .expect("the supported unary boundary should verify through the public API");
    let requirement = supported.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .expect("the test requirement should be a proposition");
    let rendered = diagnostics::describe_click_proposition(&requirement);
    assert!(rendered.starts_with("not not "));
    drop(rendered);
    drop(requirement);
    drop(supported);

    let too_deep_not = "not ".repeat(128);
    let not_error = parser::parse_file_items(&format!(
        "theorem too_deep_not() {{ requires {too_deep_not}0 == 0; ensures 0 == 0; }}"
    ))
    .expect_err("an over-deep unary proposition should fail at the parser boundary");
    assert!(
        not_error
            .message()
            .contains("proposition unary nesting exceeds Click's supported depth")
    );
    assert!(not_error.message().len() < 1024);

    let implications = (0..=512)
        .map(|_| "0 == 0")
        .collect::<Vec<_>>()
        .join(" implies ");
    let implication_error = parser::parse_file_items(&format!(
        "theorem too_deep_implies() {{ requires {implications}; ensures 0 == 0; }}"
    ))
    .expect_err("an over-deep implication chain should fail at the parser boundary");
    assert!(
        implication_error
            .message()
            .contains("proposition operator nesting exceeds Click's supported depth")
    );

    let additions = (0..=1024).map(|_| "0").collect::<Vec<_>>().join(" + ");
    let addition_error = parser::parse_file_items(&format!(
        "theorem too_deep_add() {{ requires {additions} == 0; ensures 0 == 0; }}"
    ))
    .expect_err("an over-deep left-associated expression should fail at the parser boundary");
    assert!(
        addition_error
            .message()
            .contains("expression operator nesting exceeds Click's supported depth")
    );

    let mut quantifier_body = String::from("0 == 0");
    for index in 0..parser::STRUCTURAL_NESTING_LIMIT {
        quantifier_body = format!("forall (q{index}: Integer) {{ {quantifier_body} }}");
    }
    let structural_error = parser::parse_file_items(&format!(
        "theorem too_deep_braces() {{ requires {quantifier_body}; ensures 0 == 0; }}"
    ))
    .expect_err("over-deep quantifier bodies should fail during proposition parsing");
    assert!(
        structural_error
            .message()
            .contains("quantifier nesting exceeds Click's supported depth")
    );
    assert!(structural_error.message().len() < 1024);

    let mut nested_sequence = String::from("0");
    for _ in 0..=parser::STRUCTURAL_NESTING_LIMIT {
        nested_sequence = format!("[{nested_sequence}]");
    }
    let bracket_error = parser::parse_file_items(&format!(
        "theorem too_deep_brackets() {{ ensures {nested_sequence} == {nested_sequence}; }}"
    ))
    .expect_err("over-deep bracket expressions should fail during expression parsing");
    assert!(
        bracket_error
            .message()
            .contains("bracket nesting exceeds Click's supported depth")
    );

    let mut proof_body = String::from("normalize();");
    for _ in 0..=parser::STRUCTURAL_NESTING_LIMIT {
        proof_body = format!("have 0 == 0 by {{ {proof_body} }} normalize();");
    }
    let proof_error = parser::parse_file_items(&format!(
        "theorem too_deep_proof() {{ ensures 0 == 0 by {{ {proof_body} }} }}"
    ))
    .expect_err("over-deep proof blocks should fail during proof parsing");
    assert!(
        proof_error
            .message()
            .contains("proof nesting exceeds Click's supported depth")
    );

    let body_expression = (0..=parser::EXPRESSION_CHAIN_LIMIT)
        .map(|_| "0")
        .collect::<Vec<_>>()
        .join(" + ");
    let body_error = parser::parse_file_items(&format!(
        "function too_deep_body() -> int32 {{ {body_expression} }}"
    ))
    .expect_err("over-deep C result expressions should fail at the parser boundary");
    assert!(
        body_error
            .message()
            .contains("expression operator nesting exceeds Click's supported depth")
    );

    let nested_lets = (0..=parser::CONTRACT_LET_CHAIN_LIMIT)
        .rev()
        .fold("0 == 0".to_string(), |body, index| {
            format!("let value{index} = 0; {body}")
        });
    let let_error = parser::parse_file_items(&format!(
        "theorem too_deep_lets() {{ requires {nested_lets}; ensures 0 == 0; }}"
    ))
    .expect_err("over-deep value-binding expressions should fail at the parser boundary");
    assert!(
        let_error
            .message()
            .contains("contract value-binding chain exceeds Click's supported depth")
    );

    let nested_conditionals = (0..=parser::CONTRACT_IF_NESTING_LIMIT)
        .fold("0".to_string(), |body, _| {
            format!("if 0 == 0 {{ {body} }} else {{ 0 }}")
        });
    let conditional_error = parser::parse_file_items(&format!(
        "theorem too_deep_conditionals() {{ requires {nested_conditionals} == 0; ensures 0 == 0; }}"
    ))
    .expect_err("over-deep conditional expressions should fail at the parser boundary");
    assert!(
        conditional_error
            .message()
            .contains("contract conditional expression nesting exceeds Click's supported depth")
    );

    let nested_generic_type = (0..=parser::ALGEBRAIC_TYPE_NESTING_LIMIT)
        .fold("Integer".to_string(), |type_name, _| {
            format!("Box<{type_name}>")
        });
    let generic_type_error = parser::parse_file_items(&format!(
        "theorem too_deep_generic(value: {nested_generic_type}) {{ ensures 0 == 0; }}"
    ))
    .expect_err("over-deep algebraic type applications should fail at the parser boundary");
    assert!(
        generic_type_error
            .message()
            .contains("algebraic datatype nesting exceeds Click's supported depth")
    );

    let nested_generic_field = (0..=parser::ALGEBRAIC_TYPE_NESTING_LIMIT)
        .fold("Integer".to_string(), |type_name, _| {
            format!("Box<{type_name}>")
        });
    let generic_field_error = parser::parse_file_items(&format!(
        "spec enum too_deep<T> {{ Wrapped({nested_generic_field}) }}"
    ))
    .expect_err("over-deep algebraic field types should fail at the parser boundary");
    assert!(
        generic_field_error
            .message()
            .contains("algebraic datatype nesting exceeds Click's supported depth")
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_03")]
fn representative_surface_depths_survive_consumption() {
    // Exercise every consumer in the gate; the full supported limits are
    // audited nightly. Parser rejection beyond those limits stays in this batch.
    surface_depths_survive_consumption(8, 4, 4, 4);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full supported-depth validation, verification, printing and destruction audit"]
fn supported_surface_depth_boundaries_survive_consumption() {
    surface_depths_survive_consumption(
        parser::EXPRESSION_CHAIN_LIMIT,
        parser::STRUCTURAL_NESTING_LIMIT,
        parser::ALGEBRAIC_TYPE_NESTING_LIMIT,
        parser::CONTRACT_IF_NESTING_LIMIT,
    );
}

fn surface_depths_survive_consumption(
    expression_chain_depth: usize,
    structural_depth: usize,
    algebraic_depth: usize,
    conditional_depth: usize,
) {
    let implications = (0..expression_chain_depth)
        .map(|_| "0 == 0")
        .collect::<Vec<_>>()
        .join(" implies ");
    let implication_source =
        format!("theorem at_limit_implies() {{ requires {implications}; ensures 0 == 0; }}");
    verify_click_theorems(&implication_source)
        .expect("the supported implication boundary should validate");
    let implication_file = parser::parse_file_items(&implication_source)
        .expect("the supported implication boundary should parse");
    let implication = implication_file.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .expect("the implication requirement should be a proposition");
    let printed_implication = super::super::printing::source_click_proposition(&implication);
    assert!(printed_implication.contains("implies"));
    drop(printed_implication);
    drop(implication_file);

    let additions = (0..expression_chain_depth)
        .map(|_| "0")
        .collect::<Vec<_>>()
        .join(" + ");
    let expression_source =
        format!("theorem at_limit_expression() {{ requires {additions} == 0; ensures 0 == 0; }}");
    verify_click_theorems(&expression_source)
        .expect("the supported expression boundary should validate");
    let expression_file = parser::parse_file_items(&expression_source)
        .expect("the supported expression boundary should parse");
    let expression = expression_file.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .expect("the expression requirement should be a proposition");
    let printed_expression = diagnostics::describe_click_proposition(&expression);
    assert!(printed_expression.contains(" + "));
    drop(printed_expression);
    drop(expression_file);

    let mut quantifier_body = String::from("0 == 0");
    for index in (0..structural_depth - 1).rev() {
        quantifier_body = format!("forall (q{index}: Integer) {{ {quantifier_body} }}");
    }
    let quantifier_source = format!(
        "theorem at_limit_quantifiers() {{ requires {quantifier_body}; ensures 0 == 0 by {{ normalize(); }} }}"
    );
    verify_click_theorems(&quantifier_source)
        .expect("the supported quantifier boundary should verify");
    let quantifier_file =
        parser::parse_file_items(&quantifier_source).expect("the supported quantifier boundary");
    let quantifier = quantifier_file.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .expect("the quantifier requirement should be a proposition");
    let printed_quantifier = super::super::printing::source_click_proposition(&quantifier);
    assert!(printed_quantifier.contains("forall"));
    drop(printed_quantifier);
    drop(quantifier_file);

    let mut nested_sequence = String::from("0");
    for _ in 0..structural_depth - 1 {
        nested_sequence = format!("[{nested_sequence}]");
    }
    let sequence_source = format!(
        "theorem at_limit_brackets() {{ ensures {nested_sequence} == {nested_sequence}; }}"
    );
    // Nested sequence values are intentionally parser-valid but not a valid
    // semantic value: the current sequence type is scalar-element only.
    // Keep this boundary at parse/print/destruction coverage until nested
    // sequence types are introduced independently.
    let sequence_file =
        parser::parse_file_items(&sequence_source).expect("the supported bracket boundary");
    let Ensure::Proposition(sequence) =
        sequence_file.theorem_definitions()[0].ensures()[0].ensure()
    else {
        panic!("the sequence ensure should be a proposition");
    };
    let printed_sequence = diagnostics::describe_click_proposition(sequence);
    assert!(printed_sequence.starts_with("[") && printed_sequence.ends_with("]"));
    drop(printed_sequence);
    drop(sequence_file);

    let proof_goal = "0 == 0";
    let mut proof_body = String::from("normalize();");
    for _ in 0..structural_depth - 2 {
        proof_body = format!("have 0 == 0 by {{ {proof_body} }} normalize();");
    }
    let proof_source =
        format!("theorem at_limit_proof() {{ ensures {proof_goal} by {{ {proof_body} }} }}");
    verify_click_theorems(&proof_source).expect("the supported proof boundary should verify");
    let proof_file = parser::parse_file_items(&proof_source).expect("the supported proof boundary");
    let SourceProof::Script(tactics) = proof_file.theorem_definitions()[0].ensures()[0].proof()
    else {
        panic!("the supported proof boundary should remain a script");
    };
    let printed_proof = super::super::printing::format_partial_tactic_sequence(tactics);
    assert!(printed_proof.contains("have 0 == 0 by"));
    drop(printed_proof);
    drop(proof_file);

    let nested_type = (0..algebraic_depth).fold("Integer".to_string(), |type_name, _| {
        format!("Box<{type_name}>")
    });
    let type_source = format!(
        "spec enum Box<T> {{ Wrapped(T) }} theorem at_limit_type(value: {nested_type}) {{ ensures 0 == 0; }}"
    );
    verify_click_theorems(&type_source)
        .expect("the supported algebraic type boundary should verify");
    let type_file =
        parser::parse_file_items(&type_source).expect("the supported algebraic type boundary");
    let type_name = validation::describe_click_type(
        type_file.theorem_definitions()[0].parameters()[0].click_type(),
    );
    assert!(type_name.starts_with("Box<") && type_name.ends_with(">"));
    drop(type_name);
    drop(type_file);

    let nested_conditionals = (0..conditional_depth - 1).fold("0".to_string(), |body, _| {
        format!("if 0 == 0 {{ {body} }} else {{ 0 }}")
    });
    let conditional_source = format!(
        "theorem at_limit_conditionals() {{ requires {nested_conditionals} == 0; ensures 0 == 0 by {{ normalize(); }} }}"
    );
    verify_click_theorems(&conditional_source)
        .expect("the supported conditional boundary should verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_04")]
fn parser_preserves_mixed_grouped_proposition_and_contract_expression_syntax() {
    let source = r#"
        theorem mixed_parentheses(x: int32, y: int32) {
            requires (x < y) and ((x + 1) == y);
            ensures x == x by { close(); }
        }
    "#;
    parser::parse_file_items(source)
        .expect("mixed proposition and contract-expression parentheses should parse");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_04")]
fn parses_expanded_typed_loads_and_old_loadability() {
    let source = r#"
        int32 example(int32 owner[], int32 data[]) {
            ensures result == 0;
        } by {
            close() using {
                viewable(old(owner[0..6]));
                load<int32*>((owner + 2)) == data;
                separate(
                    memory(owner[0..6]),
                    memory(load<int32*>((owner + 2))[0..load<int32>(owner)])
                );
            }
        }
    "#;
    let file = parser::parse(source).expect("expanded premise syntax should parse");
    let SourceProof::Script(tactics) = file.function_blocks[0]
        .grouped_proof()
        .expect("example should have a grouped proof")
    else {
        panic!("expected a proof script");
    };
    let ProofTactic::SolveUsing(solve_using) = &tactics[0] else {
        panic!("expected a close() using tactic");
    };
    let premises = &solve_using.premises;
    assert!(matches!(
        &premises[0],
        ClickProposition::Loadable { segment }
            if segment.state == ContractSegmentState::Old
    ));
    assert_eq!(
        diagnostics::describe_click_proposition(&premises[0]),
        "viewable(old(owner[0..6]))"
    );
    assert!(matches!(
        &premises[1],
        ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
                value_type: ProgramType::Int32Pointer,
                ..
            }),
            operator: ComparisonOperator::Equal,
            ..
        }
    ));
    assert!(matches!(&premises[2], ClickProposition::Separate { .. }));
}

/// The `target` directive selects the C implementation target. Absent, the
/// file keeps the default; the accepted spellings come from `CTarget`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_04")]
fn parses_the_c_target_directive() {
    let file = parse("verifying \"fill3.c\";").expect("a sidecar without a target should parse");
    assert_eq!(file.declared_c_target(), None);
    assert_eq!(
        file.selected_c_target(),
        crate::languages::c::target::CTarget::SUPPORTED
    );

    let file = parse("target \"x86_64-unknown-linux-gnu\";\nverifying \"fill3.c\";")
        .expect("a declared target should parse");
    assert_eq!(
        file.declared_c_target(),
        Some(crate::languages::c::target::CTarget::X86_64LinuxUserspace)
    );
    assert_eq!(
        file.selected_c_target(),
        crate::languages::c::target::CTarget::X86_64LinuxUserspace
    );
}

/// Include expansion needs the target before the sidecar is parsed, so the
/// pre-parse scan must agree with the parser about what a directive is.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_04")]
fn the_pre_parse_target_scan_agrees_with_the_parser() {
    use crate::languages::c::target::CTarget;

    for (source, expected) in [
        ("verifying \"fill3.c\";", CTarget::SUPPORTED),
        (
            "target \"x86_64-unknown-linux-gnu\";\nmode \"kernel\";\nverifying \"fill3.c\";",
            CTarget::X86_64LinuxKernel,
        ),
        (
            "target \"x86_64-unknown-linux-gnu\";\nverifying \"fill3.c\";",
            CTarget::X86_64LinuxUserspace,
        ),
    ] {
        assert_eq!(
            crate::surface::selected_c_target(source).expect("pre-parse scan"),
            expected
        );
        assert_eq!(
            parse(source)
                .expect("sidecar should parse")
                .selected_c_target(),
            expected
        );
    }

    // A `target "..."` spelling inside braces is not a file item. The scan
    // must not preprocess C under a target the parser would never select;
    // whatever this source means, the parser decides it.
    assert_eq!(
        crate::surface::selected_c_target(
            "theorem nested() { target \"x86_64-unknown-linux-gnu\"; }"
        )
        .expect("pre-parse scan"),
        CTarget::SUPPORTED
    );

    let error = crate::surface::selected_c_target(
        "target \"x86_64-unknown-linux-gnu\";\nmode \"kernel\";\ntarget \"x86_64-unknown-linux-gnu\";",
    )
    .expect_err("a file selects at most one target");
    assert!(
        error.message().contains("more than one `target`"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_05")]
fn rejects_an_unknown_or_repeated_c_target() {
    let error = parse("target \"x86_64-linux-embedded\";").expect_err("unknown target name");
    assert!(
        error.message().contains("unknown C target")
            && error
                .message()
                .contains("the accepted target is `x86_64-unknown-linux-gnu`"),
        "{error:?}"
    );
    let error = parse("target \"x86_64-unknown-linux-gnu\";\nmode \"kernel\";\ntarget \"x86_64-unknown-linux-gnu\"; mode \"kernel\";")
        .expect_err("a file selects at most one target");
    assert!(
        error.message().contains("more than one `target`"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_05")]
fn parses_checked_signature_and_contract_clauses() {
    let file = parse(FILL3_CLICK).expect("sidecar should parse");

    assert_eq!(file.verifying_sources(), &["fill3.c".to_string()]);
    assert_eq!(file.function_blocks().len(), 1);
    let function = &file.function_blocks()[0];
    assert_eq!(function.signature().return_type(), InterfaceType::Int32);
    assert_eq!(function.signature().name(), "fill3");
    assert_eq!(
        function.signature().parameters(),
        &[FunctionParameter {
            slice_length: None,
            click_type: ClickType::Program(InterfaceType::Int32Pointer),
            name: "p".to_string(),
            struct_name: None,
            function_pointer_signature: None,
            constant: false,
            pointee_constant: false,
            reference: false,
        }]
    );
    assert_eq!(
        function.requires(),
        &[
            Requirement::LoadableSegment {
                segment: ContractSegment {
                    uninitialized: false,
                    state: ContractSegmentState::Current,
                    base: ProgramExpression::Variable(("p".to_string()).into()),
                    start: ProgramExpression::Value(int32(0)),
                    end: ProgramExpression::Value(int32(3)),
                    surface: ContractSegmentSurface::Range {
                        base: current_var("p"),
                        start: current_int(0),
                        end: current_int(3),
                    },
                },
            },
            Requirement::Resource(ResourceClause::OwnMemory(ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: ProgramExpression::Variable(("p".to_string()).into()),
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(3)),
                surface: ContractSegmentSurface::Range {
                    base: current_var("p"),
                    start: current_int(0),
                    end: current_int(3),
                },
            }))
        ]
    );
    assert_eq!(function.ensures().len(), 1);
    let ensure = &function.ensures()[0];
    assert_eq!(ensure.name(), Some("returns_second"));
    assert_eq!(
        ensure.ensure(),
        &ensure_comparison(
            current_var("result"),
            ComparisonOperator::Equal,
            current_int(2),
        )
    );
    assert!(ensure.proof().uses_implicit_tail());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_05")]
fn parses_void_c_function_contracts_without_a_result_binding() {
    let source = r#"
        verifying "destroy.c";

        void destroy(int32* value) {
            consumes value[0..1];
        }
    "#;
    let file = parse(source).expect("void C contracts should parse");
    assert_eq!(
        file.function_blocks()[0].signature().return_type(),
        InterfaceType::Void
    );

    let error = verify_c_sources(
        r#"
            verifying "destroy.c";
            void destroy(int32* value) {
                ensures result == 0;
            }
        "#,
        &[("destroy.c", "void destroy(int32* value) { return; }")],
    )
    .expect_err("void contracts must not expose `result`");
    assert!(
        error.message().contains("`result` is not available"),
        "unexpected error: {}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_05")]
fn parses_pure_theorem_definition() {
    let source = r#"
            theorem preserves_nonnegative(x: int32) {
                requires x >= 0;
                ensures output_nonnegative: x >= 0;
            }
        "#;

    let file = parse(source).expect("theorem should parse");
    assert_eq!(file.theorem_definitions().len(), 1);
    let theorem = &file.theorem_definitions()[0];
    assert_eq!(theorem.name(), "preserves_nonnegative");
    assert_eq!(
        theorem.parameters(),
        &[FunctionParameter {
            slice_length: None,
            click_type: ClickType::Program(InterfaceType::Int32),
            name: "x".to_string(),
            struct_name: None,
            function_pointer_signature: None,
            constant: false,
            pointee_constant: false,
            reference: false,
        }]
    );
    assert_eq!(theorem.requires().len(), 1);
    assert_eq!(theorem.ensures().len(), 1);
    assert_eq!(theorem.ensures()[0].name(), Some("output_nonnegative"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_06")]
fn parses_integer_theorem_parameters_and_keeps_decimal_spelling() {
    let source = r#"
        theorem exact_integer(x: Integer) {
            ensures x == 100000000000000000000000000000000000001;
        }
    "#;
    let file = parse(source).expect("Integer theorem should parse");
    let theorem = &file.theorem_definitions()[0];
    assert_eq!(theorem.parameters()[0].click_type(), &ClickType::Integer);
    let Ensure::Proposition(ClickProposition::Comparison { right, .. }) =
        theorem.ensures()[0].ensure()
    else {
        panic!("expected Integer comparison");
    };
    assert!(
        matches!(right, ContractExpression::IntegerLiteral(value) if value == "100000000000000000000000000000000000001")
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_06")]
fn rejects_integer_as_an_algebraic_type_name() {
    let error = parse("spec enum Integer { zero }").expect_err("Integer is reserved");
    assert!(error.message().contains("reserved"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_06")]
fn parses_c_function_pointer_type_in_pure_theorem_parameter() {
    let source = r#"
            theorem callback_identity(
                callback: int32 (*)(int32, struct item*)
            ) {
                ensures callback == callback by close();
            }
        "#;

    let file = parse(source).expect("function-pointer theorem parameter should parse");
    let parameter = &file.theorem_definitions()[0].parameters()[0];
    assert!(matches!(
        parameter.interface_type(),
        InterfaceType::FunctionPointer(_)
    ));
    let signature = parameter
        .function_pointer_signature()
        .expect("the parameter should retain its nominal signature");
    assert_eq!(signature.return_type(), InterfaceType::Int32);
    assert_eq!(signature.parameters().len(), 2);
    assert_eq!(
        signature.parameters()[0].interface_type(),
        InterfaceType::Int32
    );
    assert_eq!(
        signature.parameters()[1].interface_type(),
        InterfaceType::Int32Pointer
    );
    assert_eq!(signature.parameters()[1].struct_name(), Some("item"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_06")]
fn parses_and_prints_pure_induction_tactics() {
    let source = r#"
        theorem induction_shape(n: int32) {
            requires n >= 0;
            ensures n == n by {
                let ih = induct(n);
                apply(ih(n - 1));
                close();
            }
        }
    "#;
    let file = parse(source).expect("induction proof should parse");
    let SourceProof::Script(tactics) = file.theorem_definitions()[0].ensures()[0].proof() else {
        panic!("expected an explicit theorem proof");
    };
    assert!(matches!(
        &tactics[0],
        ProofTactic::Induct { parameter, hypothesis }
            if parameter == "n" && hypothesis == "ih"
    ));
    assert!(matches!(
        &tactics[1],
        ProofTactic::ApplyInduction { hypothesis, arguments }
            if hypothesis == "ih" && arguments.len() == 1
    ));

    let legacy = source.replace("apply(ih(n - 1));", "apply(ih(n - 1)) using { n > 0; };");
    let error = parse(&legacy).unwrap_err();
    assert!(error.message().contains("takes no `using` list"), "{error}");

    let printable = vec![tactics[0].clone(), tactics[1].clone(), ProofTactic::Known];
    let printed = super::printing::format_partial_tactic_sequence(&printable);
    let reparsed = parse(&format!(
        "theorem induction_shape(n: int32) {{ requires n >= 0; ensures n == n by {{ {printed} }} }}"
    ))
    .expect("printed induction proof should parse");
    let SourceProof::Script(reparsed) = reparsed.theorem_definitions()[0].ensures()[0].proof()
    else {
        panic!("expected reparsed induction script")
    };
    assert!(matches!(
        &reparsed[1],
        ProofTactic::ApplyInduction { hypothesis, .. } if hypothesis == "ih"
    ));
    assert!(matches!(&reparsed[2], ProofTactic::Close));

    let source = r#"
        spec enum Nodes { End, Next(Nodes) }
        theorem smaller(n: Integer) { ensures n == n; }
        theorem scoped_hypothesis(xs: Nodes) {
            ensures true by {
                apply(smaller(0));
                if true {
                    let smaller = induct(xs);
                    have true by apply(smaller(xs));
                } else {
                    apply(smaller(1));
                }
                apply(smaller(2));
            }
        }
        theorem another_proof() { ensures true by apply(smaller(3)); }
    "#;
    let file = parse(source).expect("local induction binding can shadow a theorem");
    let SourceProof::Script(tactics) = file.theorem_definitions()[1].ensures()[0].proof() else {
        panic!("expected an explicit theorem proof");
    };
    let ProofTactic::If(branch) = &tactics[1] else {
        panic!("expected proof branches");
    };
    let ProofTactic::Have(have) = &branch.then_tactics[1] else {
        panic!("expected a nested fact proof");
    };
    assert!(matches!(
        have.proof.tactics().unwrap(),
        [ProofTactic::ApplyInduction { hypothesis, arguments }]
            if hypothesis == "smaller" && arguments.len() == 1
    ));
    let following_proof = file.theorem_definitions()[2].ensures()[0].proof();
    for call in [
        &tactics[0],
        &branch.else_tactics[0],
        &tactics[2],
        &following_proof.tactics().unwrap()[0],
    ] {
        assert!(matches!(
            call,
            ProofTactic::ApplyTheorem(application) if application.name == "smaller"
        ));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_07")]
fn parses_and_prints_structural_induction_arms() {
    let source = r#"
        spec enum TestList<T> {
            Nil,
            Cons(T, TestList<T>),
        }

        theorem induction_shape(xs: TestList<int32>) {
            ensures xs == xs by {
                let ih = induct(xs);
                match xs {
                    TestList::Nil => {
                        close();
                    }
                    TestList::Cons(head, tail) => {
                        apply(ih(tail));
                        close();
                    }
                }
            }
        }
    "#;
    let file = parse(source).expect("structural induction proof should parse");
    let SourceProof::Script(tactics) = file.theorem_definitions()[0].ensures()[0].proof() else {
        panic!("expected an explicit theorem proof");
    };
    let [
        ProofTactic::Induct {
            parameter,
            hypothesis,
        },
        ProofTactic::Match(proof_match),
    ] = tactics.as_slice()
    else {
        panic!("expected an induction declaration followed by a match");
    };
    assert_eq!(parameter, "xs");
    assert_eq!(hypothesis, "ih");
    let arms = &proof_match.arms;
    assert_eq!(arms.len(), 2);
    assert_eq!(arms[0].type_name, "TestList");
    assert_eq!(arms[0].variant, "Nil");
    assert!(arms[0].bindings.is_empty());
    assert_eq!(arms[1].bindings, ["head", "tail"]);
    assert!(matches!(
        &arms[1].tactics[0],
        ProofTactic::ApplyInduction { hypothesis, arguments }
            if hypothesis == "ih" && arguments.len() == 1
    ));

    let printed = super::printing::format_partial_tactic_sequence(tactics);
    let reparsed = parse(&format!(
        "spec enum TestList<T> {{ Nil, Cons(T, TestList<T>), }} theorem induction_shape(xs: TestList<int32>) {{ ensures xs == xs by {{ {printed} }} }}"
    ))
    .expect("printed structural induction should reparse");
    assert_eq!(
        reparsed.theorem_definitions()[0].ensures()[0].proof(),
        file.theorem_definitions()[0].ensures()[0].proof()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_07")]
fn parses_and_prints_pure_function_unfold() {
    let source = r#"
        function clamp(n: int32) -> int32 {
            if n <= 0 { 0 } else { n }
        }

        theorem clamp_nonpositive(n: int32) {
            requires n <= 0;
            ensures clamp(n) == 0 by {
                unfold(clamp(n));
                normalize();
            }
        }
    "#;
    let file = parse(source).expect("pure-function unfold should parse");
    let SourceProof::Script(tactics) = file.theorem_definitions()[0].ensures()[0].proof() else {
        panic!("expected an explicit theorem proof");
    };
    assert!(matches!(
        &tactics[0],
        ProofTactic::UnfoldFunction(application)
            if application.name == "clamp" && application.arguments.len() == 1
    ));
    let printed = super::printing::format_partial_tactic_sequence(tactics);
    assert!(printed.contains("unfold(clamp(n));"), "{printed}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_07")]
fn rejects_removed_fold_tactic_syntax() {
    for tactic in ["peel(total(n));", "peel(total(n)) using { n <= 0; };"] {
        let source = format!(
            "function total(n: int32) -> Integer {{ (0..n).fold(0, |acc, k| {{ acc + 1 }}) }} \
             theorem empty(n: int32) {{ requires n <= 0; ensures total(n) == 0 by {{ {tactic} }} }}"
        );
        let error = parse(&source).expect_err("the retired tactic has no compatibility alias");
        assert!(error.message().contains("unknown tactic `peel`"), "{error}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_07")]
fn parses_and_prints_solve_using_premise_lists() {
    let source = r#"
        theorem arithmetic_forms(n: int32) {
            requires 1 < n;
            ensures 0 <= n - 2 by {
                have n == n by { close() using {}; }
                close() using {
                    1 < n;
                }
            }
        }
    "#;
    let file = parse(source).expect("`close() using` premise lists should parse");
    let SourceProof::Script(tactics) = file.theorem_definitions()[0].ensures()[0].proof() else {
        panic!("expected an explicit theorem proof");
    };
    let ProofTactic::Have(have) = &tactics[0] else {
        panic!("expected a nested have");
    };
    let SourceProof::Script(have_tactics) = &have.proof else {
        panic!("expected a nested arithmetic proof");
    };
    assert!(matches!(
        have_tactics.as_slice(),
        [ProofTactic::SolveUsing(solve)] if solve.premises.is_empty()
    ));
    assert!(matches!(
        &tactics[1],
        ProofTactic::SolveUsing(solve) if solve.premises.len() == 1
    ));

    let printed = super::printing::format_partial_tactic_sequence(tactics);
    assert!(printed.contains("close() using {};"), "{printed}");
    assert!(printed.contains("close() using {"), "{printed}");
    let reparsed = parse(&format!(
        "theorem arithmetic_forms(n: int32) {{ requires 1 < n; ensures 0 <= n - 2 by {{ {printed} }} }}"
    ))
    .expect("printed `close() using` premise lists should parse");
    assert_eq!(
        reparsed.theorem_definitions()[0].ensures()[0].proof(),
        file.theorem_definitions()[0].ensures()[0].proof()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_09")]
fn signed_compound_expansion_uses_ordinary_operations_and_rejects_false_goal() {
    let source = r#"
        theorem signed_compound_certificate(n: int32) {
            requires 0 <= n;
            requires n <= 100;
            ensures to_integer(n + 1) <= to_integer(n + 2) by {
                close() using {
                    0 <= n;
                    n <= 100;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(source).expect("compound arithmetic should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("compound arithmetic should expand");

    let rechecked_source = source.replace(
        "by {\n                close() using {\n                    0 <= n;\n                    n <= 100;\n                }\n            }",
        &expanded,
    );
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_click_theorems(&rechecked_source)
    });
    result.expect("expanded compound certificate should recheck");
    assert_eq!(planning, 0, "explicit certificate recheck must not plan");

    let false_goal = rechecked_source.replacen("<= to_integer(n + 2)", ">= to_integer(n + 2)", 1);
    assert_ne!(false_goal, rechecked_source);
    verify_click_theorems(&false_goal)
        .expect_err("the unchanged ordinary proof cannot establish a false comparison");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_11")]
fn float_reflexive_smart_expansion_replays_as_known() {
    let source = r#"
        theorem finite_float_reflexive(value: float) {
            requires isfinite(value);
            ensures value == value by { close(); }
        }
        theorem finite_double_reflexive(value: double) {
            requires isfinite(value);
            ensures not(value < value) by { close() using { isfinite(value); }; }
        }
    "#;
    let verified = verify_click_theorems(source).expect("finite float reflexivity should verify");
    let mut rechecked = source.to_owned();
    for (theorem, original) in verified.iter().zip([
        "by { close(); }",
        "by { close() using { isfinite(value); }; }",
    ]) {
        let expanded = theorem
            .expanded_proof_source()
            .expect("float reflexivity should expand");
        assert!(expanded.contains("close()"), "{expanded}");
        for forbidden in ["normalize(", "solve("] {
            assert!(!expanded.contains(forbidden), "{expanded}");
        }
        rechecked = rechecked.replace(original, &expanded);
    }
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        crate::surface::without_implicit_solve(|| verify_click_theorems(&rechecked))
    });
    result.expect("expanded float reflexivity should recheck");
    assert_eq!(planning, 0, "ordinary float recheck must not plan");

    for source in [
        "theorem missing(x: float) { ensures x == x by close(); }",
        "theorem omitted(x: double) { requires isfinite(x); ensures x == x by { close() using {}; } }",
        "theorem other(x: float, y: float) { requires isfinite(y); ensures x == x by close(); }",
        "theorem wrong(x: double) { requires isfinite(x); ensures x < x by close(); }",
    ] {
        crate::surface::parse(source).expect("refusal control should parse");
        crate::surface::without_implicit_solve(|| verify_click_theorems(source))
            .expect_err("reflexivity must require the matching premise and polarity");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_11")]
fn signed_arithmetic_smart_planner_expands_to_ordinary_proof() {
    let source = r#"
        theorem signed_smart_double(n: int32) {
            requires 0 <= n;
            requires n <= 100;
            ensures to_integer(n + n) <= 200 by { close() using { 0 <= n; n <= 100; } }
        }
    "#;
    let verified = verify_click_theorems(source).expect("smart signed arithmetic should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("smart arithmetic should expand");
    assert!(
        !expanded.contains("normalize("),
        "signed interval expansion must use ordinary proof steps: {expanded}"
    );
    let rechecked = source.replace("by { close() using { 0 <= n; n <= 100; } }", &expanded);
    assert!(
        !expanded.contains("close() using"),
        "expanded proof must retain ordinary checked operations: {expanded}"
    );
    let (rechecked_result, planning) =
        crate::surface::proof::count_planning_statement_transitions(|| {
            verify_click_theorems(&rechecked)
        });
    rechecked_result
        .unwrap_or_else(|error| panic!("expanded ordinary proof failed: {}", error.message()));
    assert_eq!(planning, 0, "explicit signed recheck must not plan");
    let tampered = expanded.replace("100", "99");
    assert_ne!(tampered, expanded, "the source bound must remain explicit");
    let tampered_source = source.replace("by { close() using { 0 <= n; n <= 100; } }", &tampered);
    verify_click_theorems(&tampered_source)
        .expect_err("an unavailable tightened source bound must be rejected");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_12")]
fn signed_arithmetic_using_requires_every_needed_exact_premise() {
    let source = r#"
        theorem signed_missing_explicit_premise(n: int32) {
            requires 0 <= n;
            requires n <= 100;
            ensures to_integer(n + n) <= 200 by { close() using { 0 <= n; } }
        }
    "#;
    let error = verify_click_theorems(source)
        .expect_err("an omitted exact bound must not be recovered from ambient facts");
    assert!(
        error.message().contains("exactly the listed premises")
            || error.message().contains("could not construct"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_12")]
fn integer_arithmetic_uses_checked_unified_certificate_without_replanning() {
    let source = r#"
        theorem integer_smart_bound(x: Integer) {
            requires x == 1;
            ensures x <= 2 by { close() using { x == 1; } }
        }
    "#;
    let verified = verify_click_theorems(source).expect("Integer arithmetic should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("Integer arithmetic should expand");
    assert!(!expanded.contains("close() using"), "{expanded}");
    let rechecked = source.replace("by { close() using { x == 1; } }", &expanded);
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_click_theorems(&rechecked)
    });
    result.expect("expanded Integer composition should recheck");
    assert_eq!(planning, 0, "explicit Integer composition must not replan");
}

/// The bounded affine planner combines at most three listed premises; a
/// longer chain needs simplex, the last engine `arithmetic` tries.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_12")]
fn integer_arithmetic_using_proves_a_chain_longer_than_three_premises() {
    let source = r#"
        theorem integer_chain(a: Integer, b: Integer, c: Integer, d: Integer, e: Integer) {
            requires a <= b;
            requires b < c;
            requires c <= d;
            requires d <= e;
            ensures a < e by {
                close() using { a <= b; b < c; c <= d; d <= e; }
            }
        }
    "#;
    let verified = verify_click_theorems(source).expect("simplex should prove the chain");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("the chain proof should expand");
    assert!(expanded.contains("click::integer::"), "{expanded}");
    let rechecked = source.replace(
        "by {\n                close() using { a <= b; b < c; c <= d; d <= e; }\n            }",
        &expanded,
    );
    assert_ne!(rechecked, source);
    verify_click_theorems(&rechecked).expect("the expanded chain certificate should recheck");
    let missing = source.replace(" c <= d; d <= e; }", " d <= e; }");
    verify_click_theorems(&missing).expect_err("a chain with a missing link must not close");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_12")]
fn integer_arithmetic_using_rejects_an_unavailable_irrelevant_extra() {
    let source = r#"
        theorem integer_missing_extra(x: Integer) {
            requires x == 1;
            ensures x <= 2 by { close() using { x == 1; x == 9; } }
        }
    "#;
    let error = verify_click_theorems(source)
        .expect_err("every listed Integer premise must be exactly available");
    assert!(
        error
            .message()
            .contains("using` premise 1 is not exactly available"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_13")]
fn signed_arithmetic_smart_planner_preserves_explicit_definedness() {
    let source = r#"
        theorem defined_addition(a: int32, b: int32) {
            requires 0 <= a;
            requires 0 <= b;
            requires defined(a + b);
            ensures 0 <= to_integer(a + b) by {
                close() using {
                    0 <= a;
                    0 <= b;
                    defined(a + b);
                }
            }
        }
    "#;
    let verified = verify_click_theorems(source)
        .expect("explicit definedness should support signed arithmetic");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("definedness proof should expand");
    assert!(expanded.contains("defined"), "{expanded}");
    let rechecked = source.replace(
        "by {\n                close() using {\n                    0 <= a;\n                    0 <= b;\n                    defined(a + b);\n                }\n            }",
        &expanded,
    );
    verify_click_theorems(&rechecked).expect("expanded definedness proof should recheck");
    let missing_definedness = source.replace("                    defined(a + b);\n", "");
    verify_click_theorems(&missing_definedness)
        .expect_err("omitting explicit definedness must fail");
    let mismatched_definedness = source.replace(
        "                    defined(a + b);",
        "                    defined(a + a);",
    );
    verify_click_theorems(&mismatched_definedness).expect_err("mismatched definedness must fail");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn signed_arithmetic_smart_planner_handles_deep_supported_terms_iteratively() {
    let depth = 40;
    let mut bindings = String::from("let a0: int32 = n;\n");
    for index in 1..=depth {
        bindings.push_str(&format!("let a{index}: int32 = a{} + 1;\n", index - 1));
    }
    let source = format!(
        "theorem deep_signed_add(n: int32) {{\n\
            requires 0 <= n;\n\
            requires n <= 100;\n\
            {bindings}\
            ensures 0 <= a{depth} by {{ close() using {{ 0 <= n; n <= 100; }} }}\n\
        }}"
    );
    let verified = verify_click_theorems(&source).expect("deep supported arithmetic should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("deep arithmetic should expand");
    let rechecked = source.replace("by { close() using { 0 <= n; n <= 100; } }", &expanded);
    crate::surface::without_implicit_solve(|| verify_click_theorems(&rechecked))
        .expect("deep ordinary expansion should replay without search");

    let overflowing = "theorem overflowing_intermediate(n: int32) {
        requires n == 1;
        ensures 0 <= (n + 2147483647) % 2 by {
            close() using { n == 1; }
        }
    }";
    verify_click_theorems(overflowing)
        .expect_err("an overflowing intermediate must not be justified by its final value");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_13")]
fn verifies_pure_theorem_definition() {
    let source = r#"
            theorem preserves_nonnegative(x: int32) {
                requires x >= 0;
                ensures x >= 0;
            }
        "#;

    let verified = verify_click_theorems(source).expect("theorem should verify");
    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].theorem_definition.name(),
        "preserves_nonnegative"
    );
    assert_eq!(verified[0].proof_kind, ProofKind::Pure);
    verified[0]
        .proof_certificate()
        .expect("default pure proof should commit a surface certificate");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_13")]
fn pure_bare_apply_builds_a_checked_proof_object_certificate() {
    let source = r#"
        theorem equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by close();
        }

        theorem use_equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by {
                apply(equality_symmetric(first, second));
            }
        }

        theorem use_equality_from_conjunction(first: int32, second: int32) {
            requires (first == second) and (second == second);
            ensures second == first by {
                have first == second by close();
                apply(equality_symmetric(first, second));
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("bare apply should verify");
    assert!(matches!(
        verified[1].proof_tactics().as_deref(),
        Some([ProofTactic::ApplyTheorem(application), ..])
            if application.name == "equality_symmetric"
    ));
    assert!(matches!(
        verified[2].proof_tactics().as_deref(),
        Some([ProofTactic::Have(_), ProofTactic::ApplyTheorem(application), ..])
            if application.name == "equality_symmetric"
    ));

    let (lemma, caller) = source.split_once("theorem use_equality_symmetric").unwrap();
    let corrupted = format!(
        "{lemma}theorem use_equality_symmetric{}",
        caller.replacen("requires first == second;", "", 1),
    );
    let error = verify_click_theorems(&corrupted)
        .expect_err("a theorem application requires its instantiated premise");
    assert!(
        error.message().contains("has an unproved obligation"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_13")]
fn pure_solve_exposes_explicit_arithmetic_steps() {
    let source = r#"
        theorem positive_is_nonnegative(x: int32) {
            requires 0 < x;
            ensures 0 <= x by close();
        }
    "#;

    let verified = verify_click_theorems(source).expect("solve theorem should verify");
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("click::integer::"), "{expanded}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_14")]
fn pure_solve_after_unfold_exposes_an_explicit_certificate() {
    let source = r#"
        predicate equality_chain(x: int32, y: int32, z: int32) {
            x == y and y == z
        }

        theorem equality_transitive_after_unfold(x: int32, y: int32, z: int32) {
            requires equality_chain(x, y, z);
            ensures x == z by {
                unfold(equality_chain(x, y, z));
                close();
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("unfolded solve theorem should verify");
    let tactics = verified[0]
        .proof_tactics()
        .expect("unfolded solve should commit a surface certificate");
    assert!(tactics.iter().any(
        |tactic| matches!(tactic, ProofTactic::UnfoldFunction(application) if application.name == "equality_chain")
    ));
    assert!(
        tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Known))
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_14")]
fn branching_pure_solve_exposes_explicit_branch_certificates() {
    let source = r#"
        theorem equality_is_decidable(x: int32) {
            ensures x == 0 or not (x == 0) by {
                if x == 0 {
                    close();
                } else {
                    close();
                }
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("branching solve theorem should verify");
    let tactics = verified[0]
        .proof_tactics()
        .expect("branching solve should commit a surface certificate");
    let [ProofTactic::If(proof_if)] = tactics.as_slice() else {
        panic!("expected one explicit case split, got {tactics:?}");
    };
    assert!(!proof_if.then_tactics.is_empty());
    assert!(!proof_if.else_tactics.is_empty());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_14")]
fn verifies_explicit_structural_logic_tactics() {
    let source = r#"
        theorem conjunction_rule(x: int32) {
            requires x == x;
            ensures x == x and x == x by {
                close();
            }
        }

        theorem left_rule(x: int32) {
            requires x == x;
            ensures x == x or x != x by {
                close();
            }
        }

        theorem right_rule(x: int32) {
            requires x == x;
            ensures x != x or x == x by {
                close();
            }
        }

        theorem left_condition_polarity_rule(x: int32, y: int32) {
            requires not (x < y);
            ensures x >= y or x == y by {
                close();
            }
        }

        theorem right_condition_polarity_rule(x: int32, y: int32) {
            requires not (x < y);
            ensures x == y or x >= y by {
                close();
            }
        }

        theorem negated_conjunction_rule(x: int32) {
            requires x == x;
            ensures not (x != x and x == x) by {
                if x != x and x == x {
                    contradiction(x == x);
                } else {
                    close();
                }
            }
        }

        theorem intro_implication_rule(x: int32) {
            ensures x == x implies x == x by {
                intro();
                close();
            }
        }

        theorem intro_forall_rule() {
            ensures forall (k: int32) { k == k } by {
                intro();
                close();
            }
        }

        theorem vacuous_rule(x: int32) {
            requires not (x != x);
            ensures x != x implies x == 0 by {
                intro();
                contradiction(x != x);
            }
        }

        theorem contradiction_rule(x: int32) {
            requires x == 0;
            requires not (x == 0);
            ensures x == 1 by {
                contradiction(x == 0);
            }
        }

        theorem condition_polarity_contradiction_rule(x: int32, y: int32) {
            requires x < y;
            requires not (x < y);
            ensures x == 0 by {
                contradiction(x < y);
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("logical tactics should verify");
    assert_eq!(verified.len(), 11);
    assert!(verified.iter().all(|theorem| {
        theorem.proof_kind == ProofKind::TacticScript && theorem.proof_certificate().is_ok()
    }));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_14")]
fn verifies_atomic_derivation_from_explicit_premises() {
    let source = r#"
        theorem derives_nonnegative(x: int32) {
            requires 1 <= x;
            ensures 0 <= x by {
                close() using {
                    1 <= x;
                }
            }
        }

        theorem calculates_nonnegative(x: int32) {
            requires 1 <= x;
            ensures 0 <= x by {
                close() using {
                    1 <= x;
                }
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("atomic derivations should verify");
    assert_eq!(verified.len(), 2);
    assert!(
        verified
            .iter()
            .all(|theorem| { theorem.proof_certificate().is_ok() })
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_15")]
fn records_checked_surface_forms_for_lowered_propositions() {
    let left = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::GreaterThan,
        right: current_int(0),
    };
    let right = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::LessThan,
        right: current_int(10),
    };
    let surface = ClickProposition::And(Box::new(left.clone()), Box::new(right.clone()));
    let values = ProgramValueBindings::from([(
        "x".to_string(),
        ProgramValue::Int32(MachineTerm::Variable(Variable(42))),
    )]);
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let state = ExecutionState::new();
    let kernel = crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        &surface,
        &PureFactContext::new(),
        ContractEnvironment::new(&values, &BTreeMap::new()),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicates, &functions),
    )
    .expect("surface proposition should lower");
    let Proposition::And(kernel_left, kernel_right) = &kernel else {
        panic!("expected conjunction lowering");
    };
    let mut forms = SurfacePropositionMap::default();
    forms
        .record_lowering(&surface, &kernel)
        .expect("matching logical structure should record");

    assert_eq!(forms.surface(&kernel).unwrap(), &surface);
    assert_eq!(forms.surface(kernel_left).unwrap(), &left);
    assert_eq!(forms.surface(kernel_right).unwrap(), &right);
    assert!(
        forms
            .surface(&Proposition::Not(kernel_left.clone()))
            .is_err()
    );

    assert_eq!(
        forms
            .checked_surface(&kernel, |_| Ok(kernel.clone()))
            .expect("the same fixed-state lowering should remain usable"),
        surface
    );
    let error = forms
        .checked_surface(&kernel, |_| Ok(kernel_left.as_ref().clone()))
        .expect_err("a surface form from another proof state must not be reused");
    assert!(
        error
            .message()
            .contains("none of the recorded surface forms"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_15")]
fn surface_synthesis_qualifies_a_c_local_named_result() {
    let local = MachineTerm::Variable(Variable(42));
    let proposition = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(local.clone()),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let state = ExecutionState::new().with_local("result", ProgramValue::Int32(local));

    let surface = synthesize_surface_proposition(&proposition, ParameterBinding::default(), &state)
        .expect("the local comparison should have a surface form");
    let ClickProposition::Comparison { left, .. } = surface else {
        panic!("expected a comparison form");
    };
    assert_eq!(
        left,
        ContractExpression::ProgramBinding("result".to_string())
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_15")]
fn surface_synthesis_omits_a_predicates_hidden_resource_state_argument() {
    let function = syntax::parse_function(
        r#"
            struct pool {
                int32 capacity;
            };
            void inspect(struct pool* pool) {}
        "#,
    )
    .expect("struct pointer parameter should parse");
    let pool = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let proposition = Proposition::Predicate {
        name: "valid_pool".to_string(),
        arguments: vec![
            Term::ExecutionState(Box::new(ExecutionState::new())),
            Term::ProgramValue((ProgramValue::pointer(pool.clone())).into()),
        ],
    };

    let surface = synthesize_surface_proposition(
        &proposition,
        ParameterBinding::new(
            function.parameters(),
            &[ProgramExpression::Value(ProgramValue::pointer(pool))],
        ),
        &ExecutionState::new(),
    )
    .expect("the hidden state should not need a surface spelling");
    assert_eq!(
        surface,
        ClickProposition::PredicateCall {
            name: "valid_pool".to_string(),
            arguments: vec![ContractExpression::ProgramExpression(
                ProgramExpression::Variable(("pool".to_string()).into(),)
            )],
        }
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_15")]
fn surface_synthesis_spells_reserved_predicates_by_their_click_names() {
    let function =
        syntax::parse_function("void lock(int32* m) {}").expect("parameter should parse");
    let mutex = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let synthesize = |name: String, arguments: Vec<Term>| {
        synthesize_surface_proposition(
            &Proposition::Predicate { name, arguments },
            ParameterBinding::new(
                function.parameters(),
                &[ProgramExpression::Value(ProgramValue::pointer(
                    mutex.clone(),
                ))],
            ),
            &ExecutionState::new(),
        )
    };
    let state = Term::ExecutionState(Box::new(ExecutionState::new()));
    assert_eq!(
        synthesize(
            crate::kernel::FunctionContract::predicate_name_for("ordered"),
            vec![
                state.clone(),
                Term::ProgramValue(
                    (ProgramValue::pointer(Address::function("compare".to_string()))).into()
                ),
            ],
        ),
        Some(ClickProposition::PredicateCall {
            name: "ordered".to_string(),
            arguments: vec![ContractExpression::ProgramExpression(
                ProgramExpression::FunctionAddress("compare".to_string(),)
            )],
        })
    );
    assert_eq!(
        synthesize(
            format!("{}4", crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX),
            vec![Term::ProgramValue(
                (ProgramValue::pointer(mutex.clone())).into()
            )],
        ),
        None,
        "bookkeeping has no Click spelling"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_16")]
fn surface_synthesis_prefers_struct_field_places_to_typed_loads() {
    let function = syntax::parse_function(
        r#"
            struct vector {
                int32 len;
                int32 cap;
                int32* data;
            };
            int32 vector_len(struct vector* owner) {
                return owner->len;
            }
        "#,
    )
    .expect("struct parameter layout should parse");
    let owner = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let proposition = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::read_named(
                crate::kernel::ProgramPoint::at(
                    &(crate::kernel::intern_memory(SymbolicMemory::new())),
                ),
                Box::new(owner.clone()),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let surface = synthesize_surface_proposition(
        &proposition,
        ParameterBinding::new(
            function.parameters(),
            &[ProgramExpression::Value(ProgramValue::pointer(
                owner.clone(),
            ))],
        ),
        &ExecutionState::new(),
    )
    .expect("known struct field load should have a surface spelling");
    let ClickProposition::Comparison { left, .. } = surface else {
        panic!("expected a comparison spelling");
    };
    assert!(matches!(
        &left,
        ContractExpression::Field { field, .. } if field == "len"
    ));
    assert_eq!(describe_contract_expression(&left), "owner->len");

    let data_pointer = MachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
        Box::new(owner.offset_by_bytes(8)),
        crate::kernel::LoadKind::Int32,
    );
    let first_data_cell = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scaled_int32_node(data_pointer, 4),
    };
    let proposition = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::read_named(
                crate::kernel::ProgramPoint::at(
                    &(crate::kernel::intern_memory(SymbolicMemory::new())),
                ),
                Box::new(first_data_cell),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let surface = synthesize_surface_proposition(
        &proposition,
        ParameterBinding::new(
            function.parameters(),
            &[ProgramExpression::Value(ProgramValue::pointer(owner))],
        ),
        &ExecutionState::new(),
    )
    .expect("indexed pointer field load should have a surface spelling");
    let ClickProposition::Comparison { left, .. } = surface else {
        panic!("expected a comparison spelling");
    };
    assert_eq!(describe_contract_expression(&left), "owner->data[0]");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_16")]
fn proof_source_printing_preserves_proposition_precedence() {
    let comparison = |operator, value| ClickProposition::Comparison {
        left: current_var("x"),
        operator,
        right: current_int(value),
    };
    let proposition = ClickProposition::And(
        Box::new(ClickProposition::Or(
            Box::new(comparison(ComparisonOperator::Equal, 0)),
            Box::new(comparison(ComparisonOperator::Equal, 1)),
        )),
        Box::new(comparison(ComparisonOperator::LessThan, 2)),
    );
    let source = super::printing::format_partial_tactic_sequence(&[ProofTactic::Have(ProofHave {
        proposition,
        proof: SourceProof::Script(vec![ProofTactic::Known]),
    })]);

    assert!(
        source.contains("have (x == 0 or x == 1) and x < 2 by"),
        "{source}"
    );

    let quantified = ClickProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "k".to_string().into(),
        written_name: None,
        body: Box::new(ClickProposition::Implies(
            Box::new(ClickProposition::And(
                Box::new(comparison(ComparisonOperator::LessEqual, 0)),
                Box::new(comparison(ComparisonOperator::LessThan, 2)),
            )),
            Box::new(comparison(ComparisonOperator::Equal, 1)),
        )),
    };
    let source = super::printing::format_partial_tactic_sequence(&[ProofTactic::Have(ProofHave {
        proposition: quantified,
        proof: SourceProof::Script(vec![ProofTactic::Known]),
    })]);

    assert!(
        source.contains("forall (k: int32) { x <= 0 and x < 2 implies x == 1 }"),
        "{source}"
    );
    let proof_source =
        format!("int32 example(int32 x) {{ ensures result == x; }} by {{\n{source}\n}}");
    parser::parse(&proof_source).expect("printed quantified proof source should parse");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_16")]
fn proof_source_printing_preserves_long_sum_association_without_nested_prefixes() {
    for size in [8, 16, 32, 64] {
        let sum = std::iter::repeat_n("a", size)
            .collect::<Vec<_>>()
            .join(" + ");
        let source = format!(
            "theorem sum(a: Integer) {{ ensures a == a by {{ have {sum} == {size} * a by {{ close() using {{}}; }} close(); }} }}"
        );
        let file = parse(&source).unwrap();
        let proof = file.theorem_definitions()[0].ensures()[0].proof();
        let SourceProof::Script(tactics) = proof else {
            panic!("expected sum proof");
        };
        let printed = super::printing::format_partial_tactic_sequence(tactics);
        let reparsed = parse(&format!(
            "theorem sum(a: Integer) {{ ensures a == a by {{ {printed} }} }}"
        ))
        .expect("flat source sums must remain parseable after printing");
        assert_eq!(
            reparsed.theorem_definitions()[0].ensures()[0].proof(),
            proof
        );
        assert!(printed.len() < source.len() + 64, "{printed}");
    }
    // C addition may overflow at an intermediate result. In particular the
    // right-associated operand must not be folded into the left spine.
    let source = "int32 sum(int32 a, int32 b, int32 c) { ensures result == a; } by { have to_integer(a + (b + c)) == to_integer((a + b) + c) by { close(); } }";
    let file = parse(source).unwrap();
    let proof = file.function_blocks()[0].grouped_proof().unwrap();
    let SourceProof::Script(tactics) = proof else {
        panic!("expected C sum proof");
    };
    let printed = super::printing::format_partial_tactic_sequence(tactics);
    assert!(
        printed.contains("to_integer((a + (b + c))) == to_integer((a + b + c))"),
        "{printed}"
    );
    let reparsed = parse(&format!(
        "int32 sum(int32 a, int32 b, int32 c) {{ ensures result == a; }} by {{ {printed} }}"
    ))
    .unwrap();
    assert_eq!(
        reparsed.function_blocks()[0].grouped_proof().unwrap(),
        proof
    );
}

/// A quantifier is a proof step, not a normalization.
///
/// From the kernel-search cleanup: `normalize` no longer closes a
/// `forall` or `exists` goal. A vacuous range is discharged by the explicit
/// `enumerate`, which checks the quantifier's own named instances -- here,
/// none.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_16")]
fn normalize_does_not_close_quantified_contradictions() {
    let opaque = r#"
theorem impossible_interval() {
    ensures forall (k: int32) {
        0 <= k and k < 0 implies k == 7
    } by {
        normalize();
    }
}
"#;
    let error =
        verify_c_sources(opaque, &[]).expect_err("normalize must not construct a quantified proof");
    assert!(error.message().contains("normalize"), "{error:?}");

    let explicit = r#"
theorem impossible_interval() {
    ensures forall (k: int32) {
        0 <= k and k < 0 implies k == 7
    } by {
        enumerate();
    }
}
"#;
    verify_c_sources(explicit, &[]).expect("the explicit enumeration should verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_17")]
fn normalization_does_not_hide_context_free_conjunction_derivation() {
    let opaque = r#"
theorem reflexive_pair() {
    ensures 1 == 1 and 2 == 2 by { normalize(); }
}
"#;
    let error = verify_c_sources(opaque, &[])
        .expect_err("normalize must not construct a conjunction proof");
    assert!(error.message().contains("normalize"), "{error:?}");

    let explicit = r#"
theorem reflexive_pair() {
    ensures 1 == 1 and 2 == 2 by {
        all { 1 == 1 => { normalize(); } 2 == 2 => { normalize(); } }
    }
}
"#;
    verify_c_sources(explicit, &[]).expect("the explicit conjunction proof should verify");

    let opaque_using = r#"
theorem cited_pair(x: int32) {
    requires x == 0;
    ensures x == 0 and x == x by { normalize() using { x == 0; } }
}
"#;
    let error = verify_c_sources(opaque_using, &[])
        .expect_err("normalize using must not construct a conjunction proof");
    assert!(error.message().contains("normalize"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_17")]
fn normalization_does_not_hide_context_free_disjunction_derivation() {
    let opaque = r#"
theorem reflexive_choice() {
    ensures 1 == 1 or 2 == 3 by { normalize(); }
}
"#;
    let error = verify_c_sources(opaque, &[])
        .expect_err("normalize must not construct a disjunction proof");
    assert!(error.message().contains("normalize"), "{error:?}");

    let explicit_left = r#"
theorem reflexive_choice() {
    ensures 1 == 1 or 2 == 3 by {
        have 1 == 1 by { normalize(); }
        close();
    }
}
"#;
    verify_c_sources(explicit_left, &[]).expect("the explicit left-disjunct proof should verify");

    let explicit_right = r#"
theorem reflexive_choice() {
    ensures 2 == 3 or 1 == 1 by {
        have 1 == 1 by { normalize(); }
        close();
    }
}
"#;
    verify_c_sources(explicit_right, &[]).expect("the explicit right-disjunct proof should verify");

    let opaque_using = r#"
theorem cited_choice(x: int32) {
    requires x == 0;
    ensures x == 1 or x == 0 by { normalize() using { x == 0; } }
}
"#;
    let error = verify_c_sources(opaque_using, &[])
        .expect_err("normalize using must not construct a disjunction proof");
    assert!(error.message().contains("normalize"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_17")]
fn smart_context_free_disjunction_retains_known_leaf() {
    let source = r#"
theorem choose_left() {
    ensures 1 == 1 or 2 == 3 by { close(); }
}

theorem choose_right() {
    ensures 2 == 3 or 1 == 1 by { close(); }
}
"#;
    let verified =
        verify_click_theorems(source).expect("smart context-free disjunction proofs should verify");

    for theorem in &verified {
        assert!(matches!(
            theorem
                .proof_tactics()
                .expect("expected a checked certificate")
                .as_slice(),
            [ProofTactic::Known]
        ));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_17")]
fn normalization_does_not_hide_context_free_implication_derivation() {
    let opaque = r#"
theorem reflexive_implication(x: int32) {
    ensures x == 0 implies x == 0 by { normalize(); }
}
"#;
    let error = verify_c_sources(opaque, &[])
        .expect_err("normalize must not construct an implication proof");
    assert!(error.message().contains("normalize"), "{error:?}");

    let explicit = r#"
theorem reflexive_implication(x: int32) {
    ensures x == 0 implies x == 0 by {
        intro();
        close();
    }
}
"#;
    verify_c_sources(explicit, &[]).expect("the explicit implication proof should verify");

    let opaque_using = r#"
theorem cited_implication(x: int32) {
    requires x == 0;
    ensures x == 0 implies x == 0 by { normalize() using { x == 0; } }
}
"#;
    let error = verify_c_sources(opaque_using, &[])
        .expect_err("normalize using must not construct an implication proof");
    assert!(error.message().contains("normalize"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_18")]
fn smart_context_free_implication_retains_explicit_introduction() {
    let source = r#"
theorem reflexive_implication(x: int32) {
    ensures x == 0 implies x == 0 by { close(); }
}

theorem true_consequent(x: int32) {
    ensures x == 0 implies 1 == 1 by { close(); }
}

theorem nested_choice(x: int32) {
    ensures x == 0 implies (x == 0 or 1 == 2) by { close(); }
}

theorem conjunctive_guard(x: int32, y: int32) {
    ensures (x == 0 and y == 1) implies x == 0 by { close(); }
}

theorem false_guard(x: int32) {
    ensures 1 == 2 implies x == 0 by { close(); }
}
"#;
    let verified =
        verify_click_theorems(source).expect("smart context-free implication proofs should verify");

    assert_eq!(
        verified[0]
            .proof_tactics()
            .expect("expected reflexive implication certificate"),
        &[ProofTactic::Intro, ProofTactic::Known]
    );
    // `known` closes an implication whose consequent is available, here by
    // computation, without introducing the antecedent.
    assert_eq!(
        verified[1]
            .proof_tactics()
            .expect("expected true-consequent certificate"),
        &[ProofTactic::Known]
    );
    assert!(matches!(
        verified[2]
            .proof_tactics()
            .expect("expected nested disjunction certificate")
            .as_slice(),
        [ProofTactic::Intro, ProofTactic::Known]
    ));
    assert!(matches!(
        verified[3]
            .proof_tactics()
            .expect("expected conjunctive-guard certificate")
            .as_slice(),
        [ProofTactic::Intro, ProofTactic::Known]
    ));
    assert!(matches!(
        verified[4]
            .proof_tactics()
            .expect("expected false-guard certificate")
            .as_slice(),
        [ProofTactic::Intro, ProofTactic::Contradiction(_)]
    ));
    verify_click_theorems(
        r#"
theorem false_guard(x: int32) {
    ensures 1 == 2 implies x == 0 by {
        intro();
        contradiction(0u32 == 1u32);
    }
}
"#,
    )
    .expect("the false guard's shorter certificate should verify independently");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_18")]
fn retains_distinct_surface_spellings_for_the_same_kernel_fact() {
    let current = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let retained_state = ClickProposition::Comparison {
        left: ContractExpression::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(5),
                kind: ProgramPointKind::Entry,
            }),
            expression: Box::new(current_var("x")),
        },
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let kernel = Proposition::condition_is(ConditionTerm::Constant(true), true);
    let wrong = Proposition::condition_is(ConditionTerm::Constant(false), true);
    let mut spellings = SurfacePropositionMap::default();
    spellings.record_lowering(&current, &kernel).unwrap();
    spellings.record_lowering(&retained_state, &kernel).unwrap();

    assert_eq!(spellings.surface(&kernel).unwrap(), &retained_state);
    assert_eq!(
        spellings
            .checked_surface(&kernel, |surface| {
                Ok(if surface == &current {
                    kernel.clone()
                } else {
                    wrong.clone()
                })
            })
            .unwrap(),
        current
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_18")]
fn recorded_surface_fact_resolves_only_one_available_kernel_fact() {
    let surface = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let first = Proposition::condition_is(ConditionTerm::Constant(true), true);
    let second = Proposition::condition_is(ConditionTerm::Constant(false), false);
    let mut spellings = SurfacePropositionMap::default();
    spellings.record_lowering(&surface, &first).unwrap();
    spellings.record_lowering(&surface, &second).unwrap();

    assert_eq!(
        spellings.available_kernel(&surface, std::slice::from_ref(&first)),
        Some(&first)
    );
    assert_eq!(spellings.available_kernel(&surface, &[first, second]), None);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_18")]
fn surface_lowering_map_forks_and_local_updates_scale_logarithmically() {
    fn indexed_pair(index: u32) -> (ClickProposition, Proposition) {
        (
            ClickProposition::Comparison {
                left: ContractExpression::ProgramBinding(format!("x{index}")),
                operator: ComparisonOperator::Equal,
                right: current_int(index),
            },
            Proposition::condition_is(ConditionTerm::Variable(Variable(index.into())), true),
        )
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut spellings = SurfacePropositionMap::default();
        for index in 0..size {
            let (surface, kernel) = indexed_pair(index);
            spellings.record_lowering(&surface, &kernel).unwrap();
        }
        let ancestor = spellings.clone();
        assert!(spellings.shares_persistent_storage_with(&ancestor));

        let (surface, kernel) = indexed_pair(size);
        let before = crate::persistent::persistent_node_allocations();
        spellings.record_lowering(&surface, &kernel).unwrap();
        let allocations = crate::persistent::persistent_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 8 * logarithmic_height + 16;
        assert!(
            allocations <= allocation_bound,
            "size {size} surface update allocated {allocations} map nodes (bound {allocation_bound})"
        );
        assert!(ancestor.surface(&kernel).is_err());
        assert_eq!(spellings.surface(&kernel).unwrap(), &surface);
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_19")]
fn rejects_byte_counting_loadable_syntax() {
    let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires viewable(p, n * 4);
                ensures result == n;
            }
        "#;
    let error = parse(source).expect_err("byte-counting viewable syntax should be retired");
    assert!(error.message().contains("expected"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_19")]
fn parses_loadable_segment_syntax() {
    let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires viewable(p[0..n]);
                ensures result == n;
            }
        "#;
    let file = parse(source).expect("segment viewable should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[Requirement::LoadableSegment {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: ProgramExpression::Variable(("p".to_string()).into()),
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Variable(("n".to_string()).into()),
                surface: ContractSegmentSurface::Range {
                    base: current_var("p"),
                    start: current_int(0),
                    end: current_var("n"),
                },
            },
        }]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_19")]
fn parses_parenthesized_loaded_pointer_segment_base() {
    let source = r#"
            verifying "read.c";

            int32 read(int32* owner) {
                requires at(function.entry, viewable((load<int32*>((owner + 2)) + 0)[0..1]));
                ensures result == 0;
            }
        "#;

    parse(source).expect("a parenthesized loaded-pointer segment base should parse");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_19")]
fn parses_loadable_segment_proposition() {
    let source = r#"
            verifying "read.c";

            predicate shifted_loadable(p: int32*, n: int32) {
                viewable((p + 1)[0..n])
            }

            int32 read(int32* p, int32 n) {
                requires viewable((p + 1)[0..n]);
                requires shifted_loadable(p, n);
                ensures result == 0;
            }
        "#;
    let file = parse(source).expect("viewable proposition should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[
            Requirement::LoadableSegment {
                segment: ContractSegment {
                    uninitialized: false,
                    state: ContractSegmentState::Current,
                    base: ProgramExpression::Add(
                        Box::new(ProgramExpression::Variable(("p".to_string()).into())),
                        Box::new(ProgramExpression::Value(int32(1))),
                    ),
                    start: ProgramExpression::Value(int32(0)),
                    end: ProgramExpression::Variable(("n".to_string()).into()),
                    surface: ContractSegmentSurface::Range {
                        base: ContractExpression::Add(
                            Box::new(current_var("p")),
                            Box::new(current_int(1)),
                        ),
                        start: current_int(0),
                        end: current_var("n"),
                    },
                },
            },
            Requirement::Proposition(ClickProposition::PredicateCall {
                name: "shifted_loadable".to_string(),
                arguments: vec![
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        ("p".to_string()).into()
                    )),
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        ("n".to_string()).into()
                    )),
                ],
            }),
        ]
    );
    assert!(matches!(
        file.predicate_definitions()[0].body(),
        ClickProposition::Loadable { .. }
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_20")]
fn parses_resource_relation_propositions() {
    let source = r#"
            resource backing(p: int32*, n: int32) {
                owns p[0..n];
            }

            predicate separated_backing(p: int32*, q: int32*, n: int32) {
                separate(memory(p[0..n]), backing(q, n))
            }

            verifying "read.c";

            int32 read(int32* p, int32* q, int32 n) {
                requires contains(backing(p, n), memory(p[0..n]));
                requires separated_backing(p, q, n);
                ensures result == 0;
            }
        "#;
    let file = parse(source).expect("resource relation propositions should parse");
    let function = &file.function_blocks()[0];

    assert!(matches!(
        file.predicate_definitions()[0].body(),
        ClickProposition::Separate { .. }
    ));
    assert!(matches!(
        function.requires()[0],
        Requirement::Proposition(ClickProposition::Contains { .. })
    ));
    let Requirement::Proposition(ClickProposition::Contains { parent, .. }) =
        &function.requires()[0]
    else {
        panic!("expected contains proposition");
    };
    assert!(matches!(
        parent,
        ResourceSubject::Declared {
            kind: ResourceKind::Composite,
            parameter_types,
            ..
        } if parameter_types == &[InterfaceType::Int32Pointer, InterfaceType::Int32]
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_20")]
fn parses_memory_separate_requirement() {
    let source = r#"
            verifying "copy.c";

            int32 copy(int32* dst, int32* src, int32 n) {
                requires separate(memory(dst[0..n]), memory(src[0..n]));
                ensures result == n;
            }
        "#;
    let file = parse(source).expect("memory separation requirement should parse");
    let function = &file.function_blocks()[0];

    assert!(matches!(
        function.requires()[0],
        Requirement::Proposition(ClickProposition::Separate { .. })
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_20")]
fn restricted_solve_premises_retain_declared_resource_argument_types() {
    let source = r#"
        resource wrapper(owner: int32*) {}

        int32 inspect(int32* owner) {
            ensures result == 0;
        } by {
            have separate(wrapper(owner), memory(owner[0..1])) by {
                close() using {
                    separate(wrapper(owner), memory(owner[0..1]));
                }
            }
        }
    "#;
    let file = parse(source).expect("restricted solve resource premise should parse");
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected grouped proof script");
    };
    let ProofTactic::Have(ProofHave {
        proof: SourceProof::Script(have_tactics),
        ..
    }) = &tactics[0]
    else {
        panic!("expected have proof");
    };
    let ProofTactic::SolveUsing(ProofSolveUsing { premises }) = &have_tactics[0] else {
        panic!("expected restricted solve");
    };
    assert!(matches!(
        &premises[0],
        ClickProposition::Separate {
            left: ResourceSubject::Declared { parameter_types, .. },
            ..
        } if parameter_types == &[InterfaceType::Int32Pointer]
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_20")]
fn transport_using_retains_declared_resource_argument_types() {
    let source = r#"
        resource wrapper(owner: int32*) {}

        int32 inspect(int32* owner) {
            ensures result == 0;
        } by {
            have contains(wrapper(owner), memory(owner[0..1])) by {
                transport(
                    contains(wrapper(owner), memory(owner[0..1])),
                    contains(wrapper(owner), memory(owner[0..1]))
                ) using {
                    contains(wrapper(owner), memory(owner[0..1]));
                }
                close();
            }
        }
    "#;
    let file = parse(source).expect("transport resource premises should parse");
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected grouped proof script");
    };
    let ProofTactic::Have(ProofHave {
        proof: SourceProof::Script(have_tactics),
        ..
    }) = &tactics[0]
    else {
        panic!("expected have proof");
    };
    let ProofTactic::TransportUsing {
        source,
        target,
        premises,
    } = &have_tactics[0]
    else {
        panic!("expected explicit transport");
    };
    for proposition in [source, target, &premises[0]] {
        assert!(matches!(
            proposition,
            ClickProposition::Contains {
                parent: ResourceSubject::Declared { parameter_types, .. },
                ..
            } if parameter_types == &[InterfaceType::Int32Pointer]
        ));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_21")]
fn rejects_reversed_constant_loadable_segment() {
    let c_source = r#"
            int32 read_second(int32* p) {
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "read_second.c";

            int32 read_second(int32* p) {
                requires viewable(p[3..1]);
                ensures reads: result == p[1];
            }
        "#;

    let error = verify_c_sources(click_source, &[("read_second.c", c_source)])
        .expect_err("reversed concrete segment should fail");

    assert!(
        error
            .message()
            .contains("`viewable` segment has an end before its start"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_21")]
fn parses_array_parameter_signature_as_pointer() {
    let source = FILL3_CLICK.replace("int32* p", "int32 p[3]");
    let file = parse(&source).expect("array parameter signature should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.signature().parameters(),
        &[FunctionParameter {
            slice_length: None,
            click_type: ClickType::Program(InterfaceType::Int32Pointer),
            name: "p".to_string(),
            struct_name: None,
            function_pointer_signature: None,
            constant: false,
            pointee_constant: false,
            reference: false,
        }]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_21")]
fn parses_pilot_struct_pointer_signature_and_field_load() {
    let source = r#"
            verifying "json_object_ref_count.c";

            int32 json_object_get_ref_count(struct json_object* obj) {
                requires viewable(obj->ref_count);
                ensures returns_ref_count: result == obj->ref_count;
            }
        "#;
    let file = parse(source).expect("pilot struct pointer signature should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(function.signature().return_type(), InterfaceType::Int32);
    assert_eq!(
        function.signature().parameters(),
        &[FunctionParameter {
            slice_length: None,
            click_type: ClickType::Program(InterfaceType::Int32Pointer),
            name: "obj".to_string(),
            struct_name: Some("json_object".to_string()),
            function_pointer_signature: None,
            constant: false,
            pointee_constant: false,
            reference: false,
        }]
    );
    assert_eq!(
        function.requires(),
        &[Requirement::LoadableSegment {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: ProgramExpression::Variable(("obj".to_string()).into()),
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Field {
                    value_bytes: None,
                    base: Some(Box::new(ContractExpression::ProgramExpression(
                        ProgramExpression::Variable(("obj".to_string()).into())
                    ))),
                    name: "ref_count".to_string(),
                    element_width: None,
                    element_type: None,
                },
            },
        }]
    );
    assert!(matches!(
        function.ensures()[0].ensure(),
        Ensure::Proposition(ClickProposition::Comparison { right, .. })
            if matches!(
                right,
                ContractExpression::Field { field, .. } if field == "ref_count"
            )
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_21")]
fn parses_struct_pointer_callback_signature() {
    let source = r#"
            verifying "struct_callback.c";

            int32 apply(struct node* (*callback)(struct node*), struct node* node) {
                ensures result == result;
            }
        "#;
    let file = parse(source).expect("struct-pointer callback signature should parse");
    let callback = file.function_blocks()[0].signature().parameters()[0]
        .function_pointer_signature()
        .expect("callback metadata");
    assert_eq!(callback.return_struct_name(), Some("node"));
    assert_eq!(callback.parameters()[0].struct_name(), Some("node"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_22")]
fn parses_chained_struct_fields_with_imported_pointee_types() {
    let c_source = r#"
        struct leaf {
            int32 padding;
            int32 value;
        };
        struct node {
            int32 tag;
            struct leaf* child;
        };

        int32 read_nested(struct node* root) {
            return root->child->value;
        }
    "#;
    let click_source = r#"
        verifying "read_nested.c";

        int32 read_nested(struct node* root) {
            ensures result == root->child->value;
        } by {
            close();
        }
    "#;
    let file = parse_click_file_with_c_sources(click_source, &[("read_nested.c", c_source)])
        .expect("contract field chains should use imported struct pointee types");
    let Ensure::Proposition(ClickProposition::Comparison { right, .. }) =
        file.function_blocks()[0].ensures()[0].ensure()
    else {
        panic!("expected comparison ensure")
    };

    assert_eq!(
        super::diagnostics::describe_contract_expression(right),
        "root->child->value"
    );
    assert!(matches!(
        right,
        ContractExpression::Field {
            field,
            ..
        } if field == "value"
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_22")]
fn nested_field_segments_keep_the_terminal_field_offset() {
    let c_source = r#"
        struct leaf {
            int32 padding;
            int32 value;
        };
        struct node {
            int32 tag;
            struct leaf* child;
        };

        int32 write_nested(struct node* root) {
            root->child->value = 7;
            return 7;
        }
    "#;
    let click_source = r#"
        verifying "write_nested.c";

        int32 write_nested(struct node* root) {
            views root->child;
            consumes root->child->value;
            ensures result == 7;
        }
    "#;
    let file = parse_click_file_with_c_sources(click_source, &[("write_nested.c", c_source)])
        .expect("nested field segments should retain imported terminal field metadata");
    let Requirement::Resource(ResourceClause::OwnMemory(required)) =
        &file.function_blocks()[0].requires()[1]
    else {
        panic!("expected a nested owned field requirement")
    };
    {
        let segment = required;
        assert_eq!(segment.start, ProgramExpression::Value(int32(1)));
        assert_eq!(segment.end, ProgramExpression::Value(int32(2)));
        assert!(matches!(
            segment.base,
            ProgramExpression::TypedLoad {
                value_type: ProgramType::Int32Pointer,
                ..
            }
        ));
    }

    verify_c_sources(click_source, &[("write_nested.c", c_source)])
        .expect("the corrected nested segment should verify the write");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_22")]
fn parses_struct_object_segments_without_exposing_layout_cells() {
    let c_source = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 initialize(struct vector* owner) {
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "initialize.c";

        int32 initialize(struct vector* owner) {
            requires viewable(owner->data[0..owner->cap]);
            owns *owner;
            ensures separate(memory(*owner), memory(owner->data[0..owner->cap]));
        }
    "#;
    let file = parse_click_file_with_c_sources(click_source, &[("initialize.c", c_source)])
        .expect("whole struct objects should have a source-level segment spelling");
    let function = &file.function_blocks()[0];
    let Requirement::LoadableSegment { segment: range } = &function.requires()[0] else {
        panic!("expected a field-backed viewable range")
    };
    assert_eq!(
        super::diagnostics::describe_contract_segment(range),
        "owner->data[0..owner->cap]"
    );

    let Requirement::Resource(ResourceClause::OwnMemory(segment)) = &function.requires()[1] else {
        panic!("expected an owned object requirement")
    };

    assert_eq!(
        super::diagnostics::describe_contract_segment(segment),
        "*owner"
    );
    assert_eq!(segment.start, ProgramExpression::Value(int32(0)));
    assert_eq!(segment.end, ProgramExpression::Value(int32(4)));
    assert_eq!(
        segment.surface,
        ContractSegmentSurface::Object("vector".to_string())
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_22")]
fn an_embedded_struct_is_viewed_as_a_place() {
    let c_source = r#"
        struct inner {
            int32 count;
            uint8 flag;
        };

        struct outer {
            uint8 tag;
            struct inner inner;
        };

        int32 read_inner(struct outer* packet) {
            return packet->inner.count;
        }
    "#;
    let click_source = r#"
        verifying "aggregate_resource_places.c";

        int32 read_inner(struct outer* packet) {
            views packet->inner;
            ensures result == packet->inner.count;
        }
    "#;
    // An embedded struct is viewed like any other place.
    verify_c_sources(click_source, &[("aggregate_resource_places.c", c_source)]).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_23")]
fn parses_pilot_struct_field_owned_segment() {
    let source = r#"
            verifying "json_object_set_ref_count.c";

            int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
                requires viewable(obj->ref_count);
                owns obj->ref_count;
                ensures returns_count: result == count;
            }
        "#;
    let file = parse(source).expect("pilot struct field ownership should parse");
    let function = &file.function_blocks()[0];

    let Requirement::Resource(ResourceClause::OwnMemory(segment)) = &function.requires()[1] else {
        panic!("expected an owned struct-field segment")
    };
    assert_eq!(
        segment,
        &ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: ProgramExpression::Variable(("obj".to_string()).into()),
            start: ProgramExpression::Value(int32(0)),
            end: ProgramExpression::Value(int32(1)),
            surface: ContractSegmentSurface::Field {
                value_bytes: None,
                base: Some(Box::new(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(("obj".to_string()).into())
                ))),
                name: "ref_count".to_string(),
                element_width: None,
                element_type: None,
            },
        }
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_23")]
fn rejects_legacy_mutable_field_effect_spelling() {
    let source = r#"
            verifying "json_object_set_ref_count.c";

            int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
                mutable_field(obj->ref_count);
                ensures returns_count: result == count;
            }
        "#;
    let error = parse(source).expect_err("legacy mutable-field syntax should be retired");

    assert!(
        error.message().contains("expected `let`, `requires`"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_23")]
fn rejects_legacy_read_write_resource_spelling() {
    for resource_clause in ["views read(p[0..1]);", "owns write(p[0..1]);"] {
        let source = format!(
            r#"
                resource wrapper(p: int32*) {{
                    {resource_clause}
                }}
            "#
        );
        let error =
            parse(&source).expect_err("legacy read/write resource syntax should be retired");
        assert!(
            error.message().contains("expected `]`") && error.message().contains("got `..`"),
            "unexpected diagnostic for `{resource_clause}`: {}",
            error.message()
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_23")]
fn parses_block_by_clause() {
    let source = FILL3_CLICK.replace("== 2;", "== 2 by { close(); }");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some([ProofTactic::Close].as_slice())
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_24")]
fn parses_sequence_literals_states_and_concatenation() {
    let source = r#"
        verifying "join.c";

        void join(int32 dst[], int32 left[], int32 right[]) {
            ensures [dst[0], dst[1]] ++ [dst[2]]
                == old([left[0], left[1]] ++ [right[0]]);
        }
    "#;
    let file = parse(source).expect("sequence contract should parse");
    let Ensure::Proposition(ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    }) = file.function_blocks()[0].ensures()[0].ensure()
    else {
        panic!("expected sequence equality");
    };

    assert!(matches!(left, ContractExpression::SequenceConcat(_, _)));
    assert!(matches!(
        right,
        ContractExpression::Old(inner)
            if matches!(inner.as_ref(), ContractExpression::SequenceConcat(_, _))
    ));
    assert_eq!(
        describe_contract_expression(left),
        "[dst[0], dst[1]] ++ [dst[2]]"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_24")]
fn integer_datatype_match_bindings_shadow_each_source_carrier() {
    let source = r#"
        spec enum Pair { Make(int32, Integer) }
        theorem extraction(value: Integer) {
            ensures match Pair::Make(0, value) {
                Pair::Make(value, inner) => inner,
            } == value by { close(); }
        }
    "#;
    verify_click_theorems(source).unwrap();
    let bad = source.replace("=> inner,", "=> value,");
    assert!(
        verify_click_theorems(&bad).is_err(),
        "a C field must not resolve to a same-named outer Integer"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_24")]
fn integer_datatype_match_iota_survives_function_substitution_and_recheck() {
    let source = r#"
        spec enum Box { Empty, Wrapped(Integer) }
        spec enum Pair { Make(int32, Integer, Box) }
        function make(value: Integer) -> Pair {
            Pair::Make(0, value, Box::Wrapped(value))
        }
        function observe(value: Integer) -> Integer {
            value
        }
        theorem extraction(value: Integer) {
            ensures match make(value) {
                Pair::Make(c, inner, boxed) => match boxed {
                    Box::Empty => observe(inner),
                    Box::Wrapped(nested) => observe(nested),
                },
            } == observe(value) by {
                unfold(make(value));
                unfold(observe(value));
                normalize();
            }
        }
    "#;
    let verified = verify_click_theorems(source).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let rechecked = source.replace(
        "by {\n                unfold(make(value));\n                unfold(observe(value));\n                normalize();\n            }",
        &expanded,
    );
    verify_click_theorems(&rechecked).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_24")]
fn integer_datatype_match_numeral_arm_inherits_integer_result_and_rechecks() {
    let source = r#"
        spec enum Box { Empty, Wrapped(Integer) }
        function project(value: Box) -> Integer {
            match value {
                Box::Empty => 0,
                Box::Wrapped(inner) => inner,
            }
        }
        function constants(value: Box) -> Integer {
            match value {
                Box::Empty => 0,
                Box::Wrapped(inner) => 1,
            }
        }
        theorem extraction(value: Integer) {
            ensures project(Box::Wrapped(value)) == value by {
                unfold(project(Box::Wrapped(value)));
                normalize();
            }
        }
        theorem arithmetic_match() {
            ensures match Box::Empty {
                Box::Empty => 0,
                Box::Wrapped(inner) => inner + 1,
            } == 0 by { normalize(); }
        }
    "#;
    let verified = verify_click_theorems(source).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let rechecked = source.replace(
        "by {\n                unfold(project(Box::Wrapped(value)));\n                normalize();\n            }",
        &expanded,
    );
    verify_click_theorems(&rechecked).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_25")]
fn integer_match_constructor_fields_retain_unused_conversion_definedness() {
    let source = r#"
        spec enum Pair { Make(Integer, Integer) }
        function make(value: int32) -> Pair {
            Pair::Make(to_integer(value + 1), 0)
        }
        theorem guarded(value: int32) {
            requires value < 2147483647;
            requires defined(value + 1);
            ensures match make(value) {
                Pair::Make(unused, kept) => kept,
            } == 0 by {
                unfold(make(value));
                normalize();
            }
        }
    "#;
    let verified = verify_click_theorems(source).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let rechecked = source.replace(
        "by {\n                unfold(make(value));\n                normalize();\n            }",
        &expanded,
    );
    verify_click_theorems(&rechecked).unwrap();

    let missing_guard = source
        .replace("            requires value < 2147483647;\n", "")
        .replace("            requires defined(value + 1);\n", "");
    assert!(
        verify_click_theorems(&missing_guard).is_err(),
        "an unused constructor conversion field must still require definedness"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_25")]
fn symbolic_integer_datatype_matches_reject_invalid_arms() {
    let missing = r#"
        spec enum Box { Empty, Wrapped(Integer) }
        function project(value: Box) -> Integer {
            match value {
                Box::Empty => to_integer(0),
            }
        }
    "#;
    assert!(verify_click_theorems(missing).is_err());

    let wrong_carrier = r#"
        spec enum Box { Empty, Wrapped(Integer), Machine(int32) }
        function project(value: Box) -> Integer {
            match value {
                Box::Empty => to_integer(0),
                Box::Wrapped(inner) => inner,
                Box::Machine(machine) => machine,
            }
        }
    "#;
    assert!(verify_click_theorems(wrong_carrier).is_err());

    let partial_binding = r#"
        spec enum Box { Empty, Wrapped(Integer) }
        function project(value: Box) -> Integer {
            match value {
                Box::Empty => to_integer(0),
                Box::Wrapped => to_integer(0),
            }
        }
    "#;
    assert!(verify_click_theorems(partial_binding).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_25")]
fn symbolic_integer_datatype_match_does_not_capture_outer_binding() {
    let source = r#"
        spec enum Box { Empty, Wrapped(Integer) }
        theorem capture(boxed: Box, value: Integer) {
            ensures match boxed {
                Box::Empty => to_integer(0),
                Box::Wrapped(value) => value,
            } == value by { normalize(); }
        }
    "#;
    let error =
        verify_click_theorems(source).expect_err("symbolic fields must not capture outer names");
    assert!(
        !error
            .message()
            .contains("symbolic Integer-valued datatype matches"),
        "symbolic match should be implemented, but the invalid capture proof must still fail: {}",
        error.message()
    );
}

/// `diverges` is contextual: it means "may not return" only right after a
/// parameter list, so existing C spellings keep working.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_25")]
fn diverges_stays_an_ordinary_identifier_elsewhere() {
    let c_source = r#"
            int32 diverges(int32 diverges) {
                return diverges;
            }
        "#;
    let click_source = r#"
            verifying "diverges.c";

            int32 diverges(int32 diverges) {
                ensures result == diverges;
            }
        "#;
    verify_c_sources(click_source, &[("diverges.c", c_source)])
        .expect("`diverges` must still name a C function and a parameter");
}

/// The signature markers have one order, so a reader never has to know that
/// two spellings mean the same thing.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_26")]
fn diverges_must_follow_throws_in_a_signature() {
    let c_source = "int32 f(int32 x) { return x; }";
    let click_source = r#"
            verifying "f.c";

            int32 f(int32 x) diverges throws int32 {
                ensures result == x;
            }
        "#;
    let error = verify_c_sources(click_source, &[("f.c", c_source)])
        .expect_err("`diverges throws` must be refused");
    assert!(
        error
            .message()
            .contains("`throws` must come before `diverges`"),
        "{}",
        error.message()
    );

    // The accepted order parses; `f` has no loop or call that could fail to
    // return, so the marker itself is then refused as unjustified.
    let ordered = click_source.replace("diverges throws int32", "throws int32 diverges");
    let error = verify_c_sources(&ordered, &[("f.c", c_source)])
        .expect_err("a marker with nothing to justify it is refused");
    assert!(
        error.message().contains("`f` is declared `diverges`, but"),
        "{}",
        error.message()
    );
}

/// An `external` contract is a signature too, so it takes the marker; it
/// still has no body to rank, so `decreases` stays refused there.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_26")]
fn external_contracts_accept_diverges_and_still_reject_decreases() {
    let c_source = r#"
            int32 caller(int32 fd) {
                int32 result;
                result = wait_event(fd);
                return result;
            }
        "#;
    let marked = r#"
            verifying "wait.c";

            extern int32 wait_event(int32 fd) diverges {
                ensures result == 0;
            }

            int32 caller(int32 fd) diverges {
                ensures result == 0;
            }
        "#;
    verify_c_sources(marked, &[("wait.c", c_source)])
        .expect("an external contract takes the marker");

    let ranked = marked.replace(
        "extern int32 wait_event(int32 fd) diverges {",
        "extern int32 wait_event(int32 fd) diverges {\n                decreases fd;",
    );
    let error = verify_c_sources(&ranked, &[("wait.c", c_source)])
        .expect_err("an external contract cannot carry a `decreases` clause");
    assert!(
        error
            .message()
            .contains("external function contracts cannot carry proof or decreases clauses"),
        "{}",
        error.message()
    );
}

/// Expansion re-emits the proof script it checked, so a `loop diverges` head
/// must survive the round trip.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_26")]
fn loop_diverges_round_trips_through_expansion() {
    let c_source = r#"
            int32 spin() {
                while (1) {
                }
                return 0;
            }
        "#;
    let body = "loop spinning diverges { invariant 0 == 0; initialize by close(); maintain by { step(); } } close();";
    let click_source = format!(
        r#"verifying "spin.c";

            int32 spin() diverges {{
                ensures 0 == 0;
            }} by {{ {body} }}
        "#
    );
    let verified = verify_c_sources(&click_source, &[("spin.c", c_source)])
        .expect("a marked perpetual loop proves partial correctness");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("a checked proof expands");
    assert!(
        expanded.contains("loop spinning diverges {"),
        "expansion must reprint the loop marker:\n{expanded}"
    );
    verify_c_sources(
        &click_source.replace(&format!("by {{ {body} }}"), &expanded),
        &[("spin.c", c_source)],
    )
    .expect("the reprinted proof checks unchanged");

    // Locating the proof body in the source skips the signature markers, so
    // in-place expansion must see past `diverges` as it does past `throws`.
    let closer = click_source
        .rfind("close();")
        .expect("proof should contain its direct closer");
    let line = click_source[..closer]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = closer
        - click_source[..closer]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let in_place = expand_c_tactic_source_at(&click_source, &[("spin.c", c_source)], line, column)
        .expect("a marked signature must not hide the proof body");
    verify_c_sources(&in_place, &[("spin.c", c_source)])
        .expect("the in-place expansion checks unchanged");
}

/// The marker withholds whole-function termination evidence even when the
/// function ranks some of its loops.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_26")]
fn a_diverges_function_never_yields_termination_evidence() {
    let c_source = r#"
            int32 drain_then_wait(int32 n, int32 x) {
                while (n > 0) {
                    n = n - 1;
                }
                while (x != 0) {
                }
                return n;
            }
        "#;
    let click_source = r#"

            verifying "drain_then_wait.c";

            int32 drain_then_wait(int32 n, int32 x) diverges {
                requires n >= 0;
                ensures result == 0;
            } by {
                loop {
                    decreases n;
                    invariant n >= 0;
                    initialize by close();
                    maintain by {
                        have 0 <= to_integer(n - 1) by {
                            close() using { n > 0; }
                        }
                        step();
                    }
                }
                loop diverges {
                    invariant n == 0;
                    initialize by close();
                    maintain by {
                        step();
                    }
                }
                step();
                close();
            }
        "#;
    let (session, _) =
        ProgramVerificationSession::new(click_source, &[("drain_then_wait.c", c_source)])
            .expect("a marked function still verifies its ranked loop's bundle");
    assert!(!session.function_termination_is_verified("drain_then_wait"));
}

/// A typed load `load<T>(...)` and `sizeof` are expression primitives, not
/// user calls. A proposition starting with one must parse as that expression on
/// either side of a comparison, inside arithmetic, and inside parentheses,
/// while user-style calls keep the call interpretation.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_27")]
fn parses_built_in_expressions_on_either_comparison_side() {
    let loads = [
        "load<int32>",
        "load<uint8>",
        "load<int64>",
        "load<uint64>",
        "load<int32*>",
        "load<uint8**>",
    ];
    for load in loads {
        parser::parse_file_items(&format!(
            "theorem side_left(p: uint64*) {{ ensures {load}(p) == 0; }}"
        ))
        .unwrap_or_else(|error| panic!("`{load}(...) == 0` should parse: {error:?}"));
        parser::parse_file_items(&format!(
            "theorem side_right(p: uint64*) {{ ensures 0 == {load}(p); }}"
        ))
        .unwrap_or_else(|error| panic!("`0 == {load}(p)` should parse: {error:?}"));
        parser::parse_file_items(&format!(
            "theorem arithmetic(p: uint64*) {{ ensures 1 + {load}(p) == 0; }}"
        ))
        .unwrap_or_else(|error| panic!("`1 + {load}(p)` should parse: {error:?}"));
        parser::parse_file_items(&format!(
            "theorem parenthesized(p: uint64*) {{ ensures ({load}(p)) == 0; }}"
        ))
        .unwrap_or_else(|error| panic!("`({load}(p)) == 0` should parse: {error:?}"));
    }
    parser::parse_file_items("theorem sizes() { ensures sizeof(int32) == 4; }")
        .expect("`sizeof(int32) == 4` should parse");
    parser::parse_file_items("theorem sizes_arithmetic() { ensures sizeof(int32) + 4 == 8; }")
        .expect("`sizeof(int32) + 4` should parse");
    parser::parse_file_items(
        "theorem address_and_byte_offset(p: uint64*) {
            requires byte_offset(p, 4) == 4;
            ensures 0 == 0;
        }",
    )
    .expect("`byte_offset` keeps its built-in meaning");
}

/// `load<T>(p)` lowers to the kernel's typed load of `T`, and printing that
/// load writes `load<T>(p)` back: raising and then lowering returns the same
/// term, for every kind of type a load reads and for its qualifiers.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_27")]
fn typed_loads_lower_and_raise_back_to_the_same_term() {
    let lowered_load = |text: &str| {
        let file = parser::parse_file_items(&format!(
            "function read(p: uint64*) -> Integer {{ {text} }}"
        ))
        .unwrap_or_else(|error| panic!("`{text}` should parse: {}", error.report()));
        let body = file.click_function_definitions()[0].body().unwrap().clone();
        let (ContractExpression::ProgramExpression(lowered @ ProgramExpression::TypedLoad { .. })
        | ContractExpression::CUnary {
            lowered: lowered @ ProgramExpression::TypedLoad { .. },
            ..
        }) = &body
        else {
            panic!("`{text}` should lower to a typed load: {body:?}");
        };
        (body.clone(), lowered.clone())
    };
    for (text, expected) in [
        ("load<int8>(p)", (ProgramType::Int8, false, false)),
        ("load<uint16>(p)", (ProgramType::UInt16, false, false)),
        ("load<int32>(p)", (ProgramType::Int32, false, false)),
        ("load<uint64>(p)", (ProgramType::UInt64, false, false)),
        ("load<int128>(p)", (ProgramType::Int128, false, false)),
        ("load<Bool>(p)", (ProgramType::Bool, false, false)),
        ("load<float>(p)", (ProgramType::Float32, false, false)),
        ("load<double>(p)", (ProgramType::Float64, false, false)),
        ("load<void*>(p)", (ProgramType::VoidPointer, false, false)),
        ("load<Pointer>(p)", (ProgramType::Pointer, false, false)),
        ("load<int32*>(p)", (ProgramType::Int32Pointer, false, false)),
        (
            "load<uint8**>(p)",
            (ProgramType::UInt8PointerPointer, false, false),
        ),
        (
            "load<const uint8*>(p)",
            (ProgramType::UInt8Pointer, false, true),
        ),
        ("load<volatile int32>(p)", (ProgramType::Int32, true, false)),
        (
            "load<int32 (*)(int32, uint8*)>(p)",
            (
                ProgramType::FunctionPointer(ProgramType::qualified_function_pointer_signature(
                    ProgramType::Int32,
                    false,
                    &[
                        (ProgramType::Int32, false),
                        (ProgramType::UInt8Pointer, false),
                    ],
                )),
                false,
                false,
            ),
        ),
    ] {
        let (body, lowered) = lowered_load(text);
        let ProgramExpression::TypedLoad {
            value_type,
            volatile,
            pointee_constant,
            ..
        } = &lowered
        else {
            unreachable!()
        };
        assert_eq!(
            (*value_type, *volatile, *pointee_constant),
            expected,
            "{text}"
        );
        let raised = crate::surface::diagnostics::describe_contract_expression(&body);
        assert_eq!(raised, text, "raising `{text}`");
        let (_, relowered) = lowered_load(&raised);
        assert_eq!(relowered, lowered, "lowering the raised `{raised}`");
    }
    for refused in [
        "load<const int32>(p)",
        "load<void>(p)",
        "load<Pointer*>(p)",
        "load<pointer>(p)",
    ] {
        assert!(
            parser::parse_file_items(&format!(
                "function read(p: uint64*) -> Integer {{ {refused} }}"
            ))
            .is_err(),
            "`{refused}` should be refused"
        );
    }
}

/// `p as Pointer` lowers to a cast to Click's untyped pointer, and printing
/// it writes `p as Pointer` back, which lowers to the same cast.
#[test]
fn an_untyped_pointer_cast_lowers_and_raises_back_to_the_same_term() {
    let lowered_cast = |text: &str| {
        let file = parser::parse_file_items(&format!(
            "function untyped(p: int32*) -> Pointer {{ {text} }}"
        ))
        .unwrap_or_else(|error| panic!("`{text}` should parse: {}", error.report()));
        let body = file.click_function_definitions()[0].body().unwrap().clone();
        let (ContractExpression::ProgramExpression(lowered @ ProgramExpression::Cast { .. })
        | ContractExpression::CUnary {
            lowered: lowered @ ProgramExpression::Cast { .. },
            ..
        }) = &body
        else {
            panic!("`{text}` should lower to a cast: {body:?}");
        };
        (body.clone(), lowered.clone())
    };
    let (cast, lowered) = lowered_cast("p as Pointer");
    assert!(matches!(
        lowered,
        ProgramExpression::Cast {
            target_type: ProgramType::Pointer,
            ..
        }
    ));
    let raised = crate::surface::diagnostics::describe_contract_expression(&cast);
    // A cast printed alone is parenthesized, as every cast is.
    assert_eq!(raised, "(p as Pointer)");
    assert_eq!(lowered_cast(&raised).1, lowered);
    assert!(
        parser::parse_file_items("function f(p: int32*) -> Pointer { p as pointer }").is_err(),
        "lowercase `pointer` is not a type"
    );
}

#[test]
fn selected_memory_load_keeps_the_written_pointer_and_qualifiers() {
    let parse = |text: &str| {
        let file = parser::parse_file_items(&format!(
            "function read(p: uint64*) -> Integer {{ {text} }}"
        ))
        .unwrap();
        file.click_function_definitions()[0].body().unwrap().clone()
    };
    let read = parse("load<const uint8*>(old(p))");
    assert!(matches!(
        &read,
        ContractExpression::MemoryLoad {
            pointer,
            value_type: ProgramType::UInt8Pointer,
            volatile: false,
            pointee_constant: true,
        } if matches!(pointer.as_ref(), ContractExpression::Old(_))
    ));
    assert_eq!(
        parse(&crate::surface::diagnostics::describe_contract_expression(
            &read
        )),
        read
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_27")]
fn resource_array_size_excludes_struct_padding() {
    let c_source = "struct packet { uint8 bytes[3]; int64 aligned; }; uint8 read(struct packet* p) { return p->bytes[2]; }";
    let click_source = r#"
        verifying "array.c";
        uint8 read(struct packet* p) { views p->bytes; ensures result == p->bytes[2]; }
    "#;
    let file = parse_click_file_with_c_sources(click_source, &[("array.c", c_source)]).unwrap();
    let Requirement::Resource(ResourceClause::ViewMemory(segment)) =
        &file.function_blocks()[0].requires()[0]
    else {
        panic!("expected an array view");
    };
    assert_eq!(segment.start, ProgramExpression::Value(int32(0)));
    assert_eq!(segment.end, ProgramExpression::Value(int32(3)));
    assert_eq!(segment.field_element_width(), Some(1));
}

/// A resource owns a child resource with `owns`, the clause it uses for
/// everything else it holds. A name is for reading the child's fields.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_27")]
fn a_child_resource_is_owned_like_any_other() {
    let c_source = "struct cell { int32 value; int32 other; }; \
        int32 get(struct cell* p) { return p->value; }";
    let proof = "int32 get(struct cell* p) { owns outer(p); ensures result == result; } by { \
        unfold(outer(p)); unfold(inner(p)); step_until(function.exit); fold(inner(p)); fold(outer(p)); close(); }";
    let inner = "resource inner(p: struct cell*) { owns p->value; }";
    let source = format!(
        "{inner} resource outer(p: struct cell*) {{ owns inner(p); owns p->other; }} \
         verifying \"cell.c\"; {proof}"
    );
    verify_c_sources(&source, &[("cell.c", c_source)]).unwrap();
    for (child, expected) in [
        (
            "contains inner(p);",
            "write `owns inner(p);`, not `contains inner(p);`",
        ),
        (
            "owns item: inner(p);",
            "resource `inner` has no fields; use ordinary unnamed ownership",
        ),
    ] {
        let source = format!(
            "{inner} resource outer(p: struct cell*) {{ {child} owns p->other; }} \
             verifying \"cell.c\"; {proof}"
        );
        let error = verify_c_sources(&source, &[("cell.c", c_source)])
            .expect_err("the child clause is not the one spelling");
        assert!(error.message.contains(expected), "{child}: {error:?}");
    }
}

/// An `invariant` takes a label as `ensures` does, and the label names it in
/// a failure, where an unlabelled one is named by position.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_27")]
fn an_invariant_label_names_it_in_a_failure() {
    let c_source = "int32 count(int32 n) { int32 i = 0; while (i < n) { i = i + 1; } return i; }";
    let sidecar = |invariant: &str| {
        format!(
            "verifying \"count.c\"; int32 count(int32 n) {{ requires 0 <= n; ensures result == result; }} by {{ \
             step_until(loop(0).entry); loop {{ decreases n - i; invariant {invariant} i <= n - 1; \
             }} step_until(function.exit); close(); }}"
        )
    };
    let labelled = verify_c_sources(&sidecar("upper:"), &[("count.c", c_source)])
        .expect_err("the invariant does not hold at entry");
    assert!(
        labelled.message.contains("loop 0 invariant `upper` entry"),
        "{labelled:?}"
    );
    let unlabelled = verify_c_sources(&sidecar(""), &[("count.c", c_source)])
        .expect_err("the invariant does not hold at entry");
    assert!(
        unlabelled.message.contains("loop 0 invariant 0 entry"),
        "{unlabelled:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_28")]
fn nonzero_member_addresses_preserve_their_typed_place_when_printed() {
    let c = "struct node { uint64 tag; struct node *other; struct node *next; }; void check(struct node *p, struct node *q) {}";
    let source = r#"
        verifying "member.c";
        void check(struct node *p, struct node *q) {
            requires &p->next == &q->next;
            ensures 1 == 1;
        }
    "#;
    let file = parse_click_file_with_c_sources(source, &[("member.c", c)]).unwrap();
    let Requirement::Proposition(original) = &file.function_blocks()[0].requires()[0] else {
        panic!("expected a pointer comparison");
    };
    let rendered = printing::source_click_proposition(original);
    let rewritten = format!(
        "verifying \"member.c\"; void check(struct node *p, struct node *q) {{ requires {rendered}; ensures 1 == 1; }}"
    );
    let reparsed = parse_click_file_with_c_sources(&rewritten, &[("member.c", c)]).unwrap();
    let Requirement::Proposition(round_trip) = &reparsed.function_blocks()[0].requires()[0] else {
        panic!("expected the printed pointer comparison");
    };
    assert_eq!(original, round_trip, "{rendered}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_28")]
fn pointer_storage_views_name_the_field_alone() {
    let c_source =
        "struct packet { int32* data; }; int32 read(struct packet* p) { return p->data[0]; }";
    let click_source = r#"
        verifying "pointer.c";
        int32 read(struct packet* p) {
            views p->data;
            views p->data[0..1];
            ensures result == p->data[0];
        }
    "#;
    verify_c_sources(click_source, &[("pointer.c", c_source)]).unwrap();
    let file = parse_click_file_with_c_sources(click_source, &[("pointer.c", c_source)]).unwrap();
    let Requirement::Resource(ResourceClause::ViewMemory(segment)) =
        &file.function_blocks()[0].requires()[0]
    else {
        panic!("expected a pointer storage view");
    };
    assert_eq!(
        super::diagnostics::describe_contract_segment(segment),
        "p->data"
    );
}

/// A function cannot return two owners of one place. The contract is refused
/// where it is declared, whether or not it has a proof.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_28")]
fn a_contract_cannot_return_one_place_twice() {
    let c_source = "struct cell { int32 value; int32 other; int32* data; }; \
        int32 get(struct cell* p) { return p->value; }";
    for (contract, expected) in [
        (
            "int32 get(struct cell* p) { owns p->value; produces p->value; ensures result == result; }",
            "`get` both owns and produces `p->value`; `owns` already returns it",
        ),
        (
            "int32 get(struct cell* p) { owns p->value; produces p->value; ensures result == result; }",
            "`get` both owns and produces `p->value`; `owns` already returns it",
        ),
        (
            "contract int32 Twice(struct cell* p) { owns p->value; produces p->value; }",
            "`Twice` both owns and produces `p->value`; `owns` already returns it",
        ),
        (
            "int32 get(struct cell* p) { views p->value; produces p->other; produces p->other; ensures result == result; }",
            "`get` produces `p->other` twice",
        ),
        (
            "int32 get(struct cell* p) { owns *p; produces *p; ensures result == result; }",
            "`get` both owns and produces `*p`",
        ),
    ] {
        let source = format!("verifying \"cell.c\"; {contract}");
        let error = verify_c_sources(&source, &[("cell.c", c_source)])
            .expect_err("the contract returns one place twice");
        assert!(error.message.contains(expected), "{contract}: {error:?}");
        assert!(
            error.message.contains("two owners of one place"),
            "{contract}: {error:?}"
        );
    }
    // Giving a place up and returning it is not twice, and a place reached
    // through a pointer the function may replace is left to the proof.
    for contract in [
        "int32 get(struct cell* p) { consumes p->value; produces p->value; ensures result == result; }",
        "contract int32 Swap(struct cell* p) { owns p->data; owns p->data[0..1]; produces p->data[0..1]; }",
        "contract int32 Fields(struct cell* p) { consumes p->value; consumes p->data; produces p->value; produces p->data; }",
    ] {
        let source = format!("verifying \"cell.c\"; {contract}");
        let refused = match verify_c_sources(&source, &[("cell.c", c_source)]) {
            Err(error) => error.message,
            Ok(_) => String::new(),
        };
        assert!(
            !refused.contains("two owners of one place"),
            "{contract}: {refused}"
        );
        // A fixed place given up and returned is spelled `owns`, in a
        // function contract and a named contract alike.
        if !contract.contains("Swap") {
            assert!(
                refused.contains(
                    "consumes and produces `p->value`; write the one clause `owns p->value;`"
                ),
                "{contract}: {refused}"
            );
        }
    }
}

/// C has no references, so a C sidecar that declares one does not match its
/// function.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_28")]
fn a_reference_parameter_does_not_match_a_c_pointer() {
    let c_source = "int32 read(int32* p) { return p[0]; }";
    let source = "verifying \"read.c\"; int32 read(int32& p) { views p; ensures result == p; } \
";
    let error = verify_c_sources(source, &[("read.c", c_source)])
        .expect_err("a C parameter is not a reference");
    assert!(
        error
            .message
            .contains(".click has Int32& p, C has Int32Pointer p"),
        "{error:?}"
    );
}

/// Two different clauses that return overlapping memory are refused where
/// the contract is set up, naming both places, with or without a proof.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_29")]
fn a_contract_cannot_return_overlapping_places() {
    let c_source = "struct cell { int32 value; int32 other; }; \
        int32 get(struct cell* p) { return p->value; }";
    for contract in [
        "int32 get(struct cell* p) { owns *p; produces p->value; ensures result == result; }",
        "contract int32 Whole(struct cell* p) { owns *p; produces p->value; } \
         int32 get(struct cell* p) { views p->value; ensures result == result; }",
    ] {
        let source = format!("verifying \"cell.c\"; {contract}");
        let error = verify_c_sources(&source, &[("cell.c", c_source)])
            .expect_err("the contract returns overlapping places");
        assert!(
            error
                .message
                .contains("would return overlapping places: `p->value` and `*p`"),
            "{contract}: {error:?}"
        );
    }
    // An overlap the requirements prove from a symbolic bound is refused the
    // same way; one they leave open is not.
    let range_source = "int32 keep(int32* q, int32 n) { return 0; }";
    for contract in [
        "int32 keep(int32* q, int32 n) { requires n >= 2; owns q[0..n]; produces q[1]; }",
        "contract int32 Range(int32* q, int32 n) { requires n >= 2; owns q[0..n]; produces q[1]; } \
         int32 keep(int32* q, int32 n) { ensures result == 0; }",
    ] {
        let source = format!("verifying \"range.c\"; {contract}");
        let error = verify_c_sources(&source, &[("range.c", range_source)])
            .expect_err("the contract returns overlapping places");
        assert!(
            error
                .message
                .contains("would return overlapping places: `q[0..n]` and `q[1]`"),
            "{contract}: {error:?}"
        );
    }
    let open = "verifying \"range.c\"; int32 keep(int32* q, int32 n) { requires n >= 0; \
        owns q[0..n]; produces q[1]; }";
    let error = verify_c_sources(open, &[("range.c", range_source)])
        .expect_err("the exit state still refuses what the entry could not decide");
    assert!(
        !error.message.contains("would return overlapping places"),
        "{error:?}"
    );
    // Two fields of one struct do not overlap.
    let disjoint = "verifying \"cell.c\"; int32 get(struct cell* p) { owns p->value; \
        owns p->other; ensures result == result; }";
    verify_c_sources(disjoint, &[("cell.c", c_source)]).unwrap();
}

/// A resource that declares no fields keeps a named child's fields in a
/// record the author does not write, so the child must already be declared
/// for the record to be laid out.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_29")]
fn a_hidden_record_needs_its_child_declared_first() {
    let source = "resource pair(p: struct pair*) { owns p->a; owns first: counted(p->a); } \
        resource counted(c: struct cell*) { field v: int32; owns c->value; } \
        verifying \"pair.c\"; \
        int32 get(struct pair* p) { owns x: pair(p); }";
    let c_source = "struct cell { int32 value; }; struct pair { struct cell* a; }; \
        int32 get(struct pair* p) { return 0; }";
    let error = verify_c_sources(source, &[("pair.c", c_source)])
        .expect_err("the child is declared after the parent that names it");
    assert!(
        error.message.contains(
            "resource `counted` must be declared before `pair` names it as the child `first`"
        ),
        "{error:?}"
    );
}

/// A Rust sidecar states a signature as Rust does. It declares the same
/// Rust, like Click and unlike C, binds `^`, `&` and `|` tighter than a
/// comparison, so a Rust sidecar needs no parentheses around a bitwise
/// comparison operand; a C sidecar still does.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_29")]
fn a_rust_sidecar_compares_a_bitwise_operand_without_parentheses() {
    let bare =
        "verifying \"flip.rs\"; fn flip(b: u32) -> u32 { ensures result == b ^ 1u32; } by close();";
    let parenthesized = "verifying \"flip.rs\"; fn flip(b: u32) -> u32 { ensures result == (b ^ 1u32); } by close();";
    assert_eq!(
        parser::parse(bare)
            .expect("a Rust sidecar groups `b ^ 1u32` as Rust does")
            .function_blocks(),
        parser::parse(parenthesized)
            .expect("the parenthesized spelling parses")
            .function_blocks(),
    );
    let c =
        "verifying \"flip.c\"; uint32 flip(uint32 b) { ensures result == b ^ 1u32; } by close();";
    let error = parser::parse(c).expect_err("a C sidecar must parenthesize the operand");
    assert!(
        error.message().contains("parenthesize a `^` operand"),
        "{}",
        error.message()
    );
}

/// contract representation as a C signature, and `expr as T` is the scalar cast.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_29")]
fn a_rust_sidecar_states_its_signature_in_rust_syntax() {
    let c_shaped = "verifying \"arithmetic.c\"; \
        uint32 add_byte(uint32 sum, uint8 byte) { requires sum <= 4294967040u32; \
        ensures result == sum + byte as uint32; } \
        bool touch(uint64 count, bool flag) { ensures result == flag; }";
    let rust = "verifying \"arithmetic.rs\"; \
        fn add_byte(sum: u32, byte: u8) -> u32 { requires sum <= 4294967040u32; \
        ensures result == sum + byte as u32; } \
        fn touch(count: usize, flag: bool) -> bool { ensures result == flag; }";
    assert_eq!(
        parser::parse(rust)
            .expect("the Rust spelling parses")
            .function_blocks(),
        parser::parse(c_shaped)
            .expect("the C-shaped spelling parses")
            .function_blocks(),
    );
    for (source, expected) in [
        (
            "verifying \"bytes.rs\"; uint32 f(const uint8* bytes, uint64 bytes_len) { ensures result == 0u32; } by close();",
            "write `fn f(bytes: &[u8]) -> u32`",
        ),
        (
            "uint32 f(const uint8* bytes, uint64 bytes_len) { ensures result == 0u32; } by close(); verifying \"bytes.rs\";",
            "write `fn f(bytes: &[u8]) -> u32`",
        ),
        (
            "verifying \"borrow.rs\"; fn f(p: &u32) -> u32 { ensures result == p->f; } by close();",
            "replace `p->f` with `p.f`",
        ),
        (
            "verifying \"add.c\"; fn add(a: i32) -> i32 { ensures result == result; }",
            "a `fn` signature is the Rust spelling",
        ),
        (
            "verifying \"add.rs\"; fn read(value: &&i32) -> i32 { ensures result == result; }",
            "a reference to a reference or to `()` in a `fn` signature is not supported",
        ),
        (
            "verifying \"add.rs\"; fn read(bytes: [u8; 4]) -> u8 { ensures result == result; }",
            "an array or slice passed by value in a `fn` signature is not supported",
        ),
        (
            "verifying \"add.rs\"; fn pick<i32>(a: i32) -> i32 { ensures result == a; }",
            "write the contract once, on the generic function",
        ),
        (
            "verifying \"cells.rs\"; impl cells::Cell<i32> { fn get(&self) -> i32 { ensures result == 0; } }",
            "a generic struct's methods are written once",
        ),
    ] {
        let error = parser::parse(source).expect_err("the signature is refused");
        assert!(error.message.contains(expected), "{source}: {error:?}");
    }
    // A reference is the pointer that carries it; `&T` has a constant
    // referent. The contract names the referent `*value`.
    assert_eq!(
        parser::parse(
            "verifying \"borrow.rs\"; \
             fn set(value: &mut i32, seen: &i32) { owns *value; views *seen; \
             ensures *value == *seen; }"
        )
        .expect("the Rust spelling parses")
        .function_blocks(),
        parser::parse(
            "verifying \"borrow.c\"; \
             void set(int32* value, const int32* seen) { owns *value; views *seen; \
             ensures *value == *seen; }"
        )
        .expect("the C-shaped spelling parses")
        .function_blocks(),
    );
    // A contract does not use lifetimes, so it may write them or leave them
    // out, in the generic parameters and on a reference or slice.
    assert_eq!(
        parser::parse(
            "verifying \"borrow.rs\"; \
             fn set<'a, 'b: 'a>(value: &'a mut i32, seen: &'b i32, bytes: &'a [u8]) \
             { owns *value; views *seen; ensures *value == *seen; }"
        )
        .expect("the spelling with lifetimes parses"),
        parser::parse(
            "verifying \"borrow.rs\"; \
             fn set(value: &mut i32, seen: &i32, bytes: &[u8]) \
             { owns *value; views *seen; ensures *value == *seen; }"
        )
        .expect("the spelling without lifetimes parses"),
    );
    // A character literal is still one byte between quotes.
    let byte = parser::parse("verifying \"c.rs\"; fn f(x: u8) -> u8 { ensures result == 'a'; }");
    assert!(byte.is_ok(), "{byte:?}");
    // A slice is one name over the pointer and length Rust passes.
    let slices = parser::parse(
        "verifying \"bytes.rs\"; fn length(bytes: &[u8], out: &mut [u32]) -> usize { \
         ensures result == bytes.len() + out.len(); }",
    )
    .expect("the Rust spelling parses");
    let parameters = slices.function_blocks()[0].signature().parameters();
    assert_eq!(
        parameters[1].binding_name(),
        crate::kernel::BindingName::slice_length("bytes"),
    );
    assert_eq!(
        parameters[3].binding_name(),
        crate::kernel::BindingName::slice_length("out"),
    );
    // `*bytes` is the whole slice, and a `usize` parameter written alone
    // as an index is the 32-bit index a place takes. The importer test
    // verifies what these mean; here they parse.
    parser::parse(
        "verifying \"bytes.rs\"; fn read(bytes: &[u8], index: usize) -> u8 { \
         views *bytes; ensures result == bytes[index]; }",
    )
    .expect("the Rust spelling parses");
    // A trait's type argument names the method as the importer does:
    // a scalar by its name, a reference as `ref_`, a record as `value_`.
    for (header, method, name, parameter, program_parameter) in [
        (
            "MulAssign<u32>",
            "mul_assign",
            "Lanes_mul_assign_u32",
            "rhs: u32",
            "uint32 rhs",
        ),
        (
            "AddAssign<&Lanes>",
            "add_assign",
            "Lanes_add_assign_ref_Lanes",
            "other: &Lanes",
            "const struct Lanes* other",
        ),
        (
            "AddAssign<&mut Lanes>",
            "add_assign",
            "Lanes_add_assign_ref_mut_Lanes",
            "other: &mut Lanes",
            "struct Lanes* other",
        ),
    ] {
        assert_eq!(
            parser::parse(&format!(
                "verifying \"l.rs\"; impl {header} for Lanes {{ fn {method}(&mut self, {parameter}) {{ \
                 ensures 0 == 0; }} }}"
            ))
            .unwrap_or_else(|error| panic!("{header}: {error:?}")).function_blocks(),
            parser::parse(&format!(
                "verifying \"l.c\"; void {name}(struct Lanes* self, {program_parameter}) {{ \
                 ensures 0 == 0; }}"
            ))
            .expect("the C-shaped spelling parses").function_blocks(),
            "{header}"
        );
    }
    // A path names an item of a crate as the importer names it: a function,
    // a type, and an inherent method of a type in the type's own module.
    for (rust, c_shaped) in [
        (
            "fn quad::walk(byte: &u8) -> u32 { ensures result == 0u32; } @",
            "uint32 __rust_q_I4_quad_I4_walk(const uint8* byte) \
             { ensures result == 0u32; }",
        ),
        (
            "fn demo::set(words: &mut demo::inner::Words, value: u32) { ensures 0 == 0; } @",
            "void __rust_q_I4_demo_I3_set(struct __rust_q_I4_demo_I5_inner_I5_Words* words, \
             uint32 value) { ensures 0 == 0; }",
        ),
        (
            "impl demo::Value { fn new(seed: u32) -> u32 { ensures result == seed; } @ }",
            "uint32 __rust_q_I4_demo_T25___rust_q_I4_demo_I5_Value_I3_new(uint32 seed) \
             { ensures result == seed; }",
        ),
        // An item inside a method follows the method's own name.
        (
            "impl demo::Value { fn new::LIMIT() -> u32 { ensures result == 7u32; } @ }",
            "uint32 __rust_q_I4_demo_T25___rust_q_I4_demo_I5_Value_I3_new_I5_LIMIT() \
             { ensures result == 7u32; }",
        ),
        (
            "impl Drop for demo::Token { fn drop(&mut self) { ensures 0 == 0; } @ }",
            "void __rust_q_I4_demo_I5_Token_drop(struct __rust_q_I4_demo_I5_Token* self) \
             { ensures 0 == 0; }",
        ),
        (
            "impl AddAssign<&a::b::Lanes> for a::b::Lanes { fn add_assign(&mut self, \
             other: &a::b::Lanes) { ensures 0 == 0; } @ }",
            "void __rust_q_I1_a_I1_b_I5_Lanes_add_assign_ref___rust_q_I1_a_I1_b_I5_Lanes(\
             struct __rust_q_I1_a_I1_b_I5_Lanes* self, \
             const struct __rust_q_I1_a_I1_b_I5_Lanes* other) { ensures 0 == 0; }",
        ),
    ] {
        let rust = rust.replace('@', "");
        assert_eq!(
            parser::parse(&format!("verifying \"lib.rs\"; {rust}"))
                .unwrap_or_else(|error| panic!("{rust}: {error:?}"))
                .function_blocks(),
            parser::parse(&format!("verifying \"lib.c\"; {c_shaped}"))
                .unwrap_or_else(|error| panic!("{c_shaped}: {error:?}"))
                .function_blocks(),
            "{rust}"
        );
    }
    // The importer names an inherent method by the module its `impl`
    // block is in, which a sidecar does not write. With the import's
    // functions at hand the method is found by its type and name; without
    // them the block is taken to be in its type's module.
    let method = "impl adler2::Adler32 { fn compute(&mut self, seed: u32) { ensures 0 == 0; } \
}";
    let source = format!("verifying \"lib.rs\"; {method}");
    let elsewhere = "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute";
    let beside = "__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I7_compute";
    let parse_with_functions = |functions: &[&str]| {
        parser::parse_with_layouts_and_aggregate_objects(
            &source,
            parser::ProgramLayouts {
                local_struct_pointers: functions
                    .iter()
                    .map(|name| ((*name).to_string(), parser::FunctionLocals::default()))
                    .collect(),
                ..Default::default()
            },
        )
    };
    let named = |file: ClickFile| file.function_blocks()[0].signature().name().to_string();
    assert_eq!(named(parse_with_functions(&[]).unwrap()), beside);
    assert_eq!(
        named(parse_with_functions(&[elsewhere, "__rust_q_I6_adler2_I4_algo_I4_load"]).unwrap()),
        elsewhere
    );
    // Another type's method of the same name is not this one.
    assert_eq!(
        named(
            parse_with_functions(&[
                "__rust_q_I6_adler2_I4_algo_T27___rust_q_I6_adler2_I5_Other_I7_compute"
            ])
            .unwrap()
        ),
        beside
    );
    assert!(
        parse_with_functions(&[elsewhere, beside])
            .expect_err("two imported methods of one name are ambiguous")
            .message
            .contains("more than one method `compute`")
    );
    // An `impl` block holds `fn` contracts and nothing else, and is Rust.
    for (source, expected) in [
        (
            "verifying \"g.rs\"; impl Guard { resource r() { } }",
            "an `impl` block holds `fn` contracts",
        ),
        (
            "verifying \"g.rs\"; impl MulAssign<u32> { fn mul_assign(&mut self, rhs: u32) { ensures 0 == 0; } }",
            "a trait with a type argument is implemented `for` a type",
        ),
        (
            "verifying \"g.c\"; impl Guard { fn drop(&mut self) { ensures 0 == 0; } }",
            "unknown C type `impl`",
        ),
    ] {
        let error = parser::parse(source).expect_err("the impl block is refused");
        assert!(error.message.contains(expected), "{source}: {error:?}");
    }
    // A reference to an array is the pointer to its first element.
    assert_eq!(
        parser::parse(
            "verifying \"arrays.rs\"; fn first(bytes: &[u8; 4], words: &mut [u32; 1 + 2]) -> u8 { \
             views bytes[0..4]; ensures result == bytes[0]; }"
        )
        .expect("the Rust spelling parses")
        .function_blocks(),
        parser::parse(
            "verifying \"arrays.c\"; uint8 first(const uint8* bytes, uint32* words) { \
             views bytes[0..4]; ensures result == bytes[0]; }"
        )
        .expect("the C-shaped spelling parses")
        .function_blocks(),
    );
    // `as` before anything but a scalar type is not a cast.
    parser::parse("verifying \"add.c\"; int32 add(int32 a) { ensures result == a; }")
        .expect("a C sidecar is unchanged");
}

/// A missing memory fact is reported as the place a clause would name.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_30")]
fn a_missing_memory_fact_is_reported_as_a_place() {
    let c_source = "struct cell { int32 value; int32 other; }; \
        struct pad { int32* data; int32 n; }; \
        struct outer { int32 head; struct cell inner; }; \
        int32 read_n(struct pad* a) { return a->n; } \
        int32 read_data(struct pad* a) { return a->data[0]; } \
        int32 write_other(struct cell* p) { p->other = 1; return 0; } \
        int32 read_inner(struct outer* o) { return o->inner.other; } \
        int32 read_q(int32* q) { return q[1]; }";
    for (contract, expected) in [
        (
            "int32 read_n(struct pad* a) { owns allocation(a, sizeof(struct pad)); owns a->data; }",
            "missing resource fact `views a->n`",
        ),
        (
            "int32 read_data(struct pad* a) { owns allocation(a, sizeof(struct pad)); views a->n; }",
            "missing resource fact `views a->data`",
        ),
        (
            "int32 read_data(struct pad* a) { views a->data; }",
            "missing resource fact `views a->data[0..1]`",
        ),
        (
            "int32 write_other(struct cell* p) { views *p; }",
            "missing resource fact `owns p->other`",
        ),
        (
            "int32 read_inner(struct outer* o) { owns allocation(o, sizeof(struct outer)); views o->head; }",
            "missing resource fact `views o->inner.other`",
        ),
        (
            "int32 read_q(int32* q) { views q[0]; }",
            "held `views q[0]` does not cover `q[1]`",
        ),
    ] {
        let source = format!("verifying \"place.c\"; {contract}");
        let error = verify_c_sources(&source, &[("place.c", c_source)])
            .expect_err("the access is not authorized");
        assert!(error.message.contains(expected), "{contract}: {error:?}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_30")]
fn memory_ranges_use_fields_or_correctly_scaled_source_elements() {
    use crate::kernel::{
        Address, AddressBase, AddressOffset, MachineTerm, MemoryRange, Pointer, ProgramType,
    };
    let c_source = "struct cell { int32 a; int32 b; int32 c; }; struct outer { int32 head; struct cell inner; int32 tail; }; int32 read(struct outer* p) { return p->tail; }";
    let functions = syntax::parse_functions(c_source).unwrap();
    let parameters = functions[0].parameters();
    let base = Address {
        base: AddressBase::Concrete("range_base".into()),
        offset: AddressOffset::Constant(0),
    };
    let arguments = [ProgramExpression::Value(ProgramValue::Pointer(
        Pointer::new(base.clone(), ProgramType::Int32Pointer),
    ))];
    for (low, high, width, expected) in [
        (0, 2, 4, "{p->head, p->inner.a}"),
        (1, 3, 4, "{p->inner.a, p->inner.b}"),
        (1, 4, 4, "p->inner"),
        (0, 5, 4, "*p"),
        (5, 6, 4, "p[1].head"),
        (5, 10, 4, "p[1]"),
        (1, 6, 4, "((char *)p)[4..24]"),
        (0, 10, 4, "p[0..2]"),
        (1, 3, 1, "((char *)p)[1..3]"),
    ] {
        let range = MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(low),
            MachineTerm::constant(high),
            width,
        );
        assert_eq!(
            super::diagnostics::describe_memory_range(
                &range,
                ParameterBinding::new(parameters, &arguments)
            ),
            expected
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_30")]
fn held_recursive_struct_range_and_bound_load_name_their_fields() {
    let c_source = "struct node { struct node* left; struct node* right; int32 augmented; }; void relink(struct node* node) { node->right = 0; }";
    let click_source = r#"
resource pair(node: struct node*) { field weight: int32; owns node->left; owns node->right; }
verifying "relink.c";
void relink(struct node* node) { requires node != 0; owns links: pair(node); owns node->right->augmented; }
"#;
    let error = verify_c_sources(click_source, &[("relink.c", c_source)]).unwrap_err();
    assert!(
        error
            .message
            .contains("missing resource fact `owns node->right`"),
        "{error:?}"
    );
    // The held field of the struct `node->right` points at is named by its
    // chain, and is not compared with `node->right` as a byte offset from
    // `node`: the view of `node->right` is what explains the refusal.
    assert!(
        error.message.contains("owns node->right->augmented"),
        "{error:?}"
    );
    assert!(
        error.message.contains(
            "available `views node->right` covers the requested range but permits reading only"
        ),
        "{error:?}"
    );
    assert!(!error.message.contains("((node->right - "), "{error:?}");
    assert!(!error.message.contains("load("), "{error:?}");
    assert!(!error.message.contains("byte offsets from"), "{error:?}");
    assert!(!error.message.contains("node[2]"), "{error:?}");
    assert!(!error.message.contains("right[4..6]"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_30")]
fn a_production_obligation_names_the_same_struct_place_as_its_missing_fact() {
    let c_source = "struct cell { int32 a; int32 b; }; int32 release(struct cell* p) { return 0; }";
    let source = r#"verifying "cell.c"; int32 release(struct cell* p) { produces p[0..1]; ensures result == 0; }"#;
    let error = verify_c_sources(source, &[("cell.c", c_source)]).unwrap_err();
    assert!(
        error.message.contains("missing resource fact `owns *p`"),
        "{error:?}"
    );
    assert!(
        error.message.contains("Requires produces owns *p"),
        "{error:?}"
    );
}

/// A range on a struct pointer counts structs, and `*link` for a
/// `struct T**` is one pointer slot, not a struct.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_31")]
fn a_struct_pointer_range_counts_structs() {
    let c_source = "struct cell { int32 value; int32 other; }; \
        int32 second(struct cell* p) { return p[1].other; } \
        struct cell* first(struct cell** link) { return *link; }";
    let contract = |clause: &str| {
        format!("verifying \"cells.c\"; int32 second(struct cell* p) {{ {clause} }}")
    };
    verify_c_sources(&contract("views p[0..2];"), &[("cells.c", c_source)]).unwrap();
    let error = verify_c_sources(&contract("views p[0..1];"), &[("cells.c", c_source)])
        .expect_err("one struct does not cover the second");
    assert!(
        error
            .message
            .contains("pointer arithmetic left the pointed-to object"),
        "{error:?}"
    );

    let link = "verifying \"cells.c\"; struct cell* first(struct cell** link) { views *link; }";
    let file = parse_click_file_with_c_sources(link, &[("cells.c", c_source)]).unwrap();
    let Requirement::Resource(ResourceClause::ViewMemory(segment)) =
        &file.function_blocks()[0].requires()[0]
    else {
        panic!("expected a view of the pointer slot");
    };
    assert!(matches!(
        segment.surface,
        ContractSegmentSurface::Range { .. }
    ));
    assert_eq!(segment.end, ProgramExpression::Value(int32(1)));
}

/// `*p` is the object behind a pointer, and a place written alone is its own
/// storage: a global, an element, a field.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_31")]
fn a_resource_clause_names_a_place() {
    let c_source = "struct cell { int32 value; int32 other; }; \
        struct node { struct node* next; int32 v; }; \
        struct cell g; int32 total; \
        int32 read_g(void) { return g.other; } \
        int32 read_total(void) { return total; } \
        int32 read_p(struct cell* p) { return p->other; } \
        int32 read_q(int32* q) { return q[1]; } \
        int32 read_first(int32* q) { return q[0]; } \
        int32 read_next(struct node* n) { return n->next->v; }";
    for contract in [
        "int32 read_g() { owns g; ensures result == g.other; }",
        "int32 read_total() { owns total; ensures result == total; }",
        "int32 read_p(struct cell* p) { owns *p; ensures result == p->other; }",
        "int32 read_q(int32* q) { views q[1]; ensures result == q[1]; }",
        "int32 read_first(int32* q) { views *q; ensures result == q[0]; }",
        "int32 read_next(struct node* n) { views n->next; owns *n->next; }",
    ] {
        let source = format!("verifying \"place.c\"; {contract}");
        verify_c_sources(&source, &[("place.c", c_source)])
            .unwrap_or_else(|error| panic!("{contract}: {error:?}"));
    }
    for (contract, expected) in [
        (
            "int32 read_p(struct cell* p) { owns p; }",
            "write `*p` for the object it points at",
        ),
        (
            "int32 read_q(int32* q) { views q; }",
            "write `*q` for the object it points at",
        ),
        (
            "int32 read_p(struct cell* p) { owns *p[0..1]; }",
            "`*` names one object and takes no range",
        ),
        ("int32 read_g() { owns *g; }", "`*` expects a pointer"),
        (
            "int32 read_p(struct cell* p) { owns &p->other; }",
            "write `p->next`, not `&p->next`",
        ),
        (
            "int32 read_total() { owns &total[0..1]; }",
            "`counter`, not `&counter[0..1]`",
        ),
        (
            "int32 read_p(struct cell* p) { owns p->other[0..1]; }",
            "field `other` is one value, not a pointer or an array, so it takes no range",
        ),
        (
            "int32 read_p(struct cell* p) { owns object(p); }",
            "`object(p)` is now written `*p`",
        ),
    ] {
        let source = format!("verifying \"place.c\"; {contract}");
        let error = verify_c_sources(&source, &[("place.c", c_source)])
            .expect_err("the clause names no ownable place");
        assert!(error.message.contains(expected), "{contract}: {error:?}");
    }
}

/// A whole struct is viewed like any other place: it reads every field and
/// writes none.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_31")]
fn a_whole_struct_view_reads_and_does_not_write() {
    let c_source = "struct packet { int32 data; int32 other; }; \
        int32 read(struct packet* p) { return p->other; } \
        int32 write(struct packet* p) { p->other = 1; return 0; }";
    let read = "verifying \"pointer.c\"; int32 read(struct packet* p) { views *p; \
        ensures result == p->other; }";
    verify_c_sources(read, &[("pointer.c", c_source)]).unwrap();
    let write = "verifying \"pointer.c\"; int32 write(struct packet* p) { views *p; } \
";
    let error = verify_c_sources(write, &[("pointer.c", c_source)])
        .expect_err("a view does not authorize a write");
    assert!(error.message.contains("missing resource fact"), "{error:?}");
}

/// A function-entry alignment fact cited after execution is qualified side
/// by side, `at(S, address(p) & 7u64) == at(S, 0u64)`. Click has no cast
/// spelling for the address inside, so it renders as the `aligned` sugar
/// read at that state rather than as an unparseable `p as uint64`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_31")]
fn state_read_alignment_fact_renders_as_aligned() {
    let source = "theorem entry_alignment(arena: int32*) { \
        requires at(function.entry, address(arena) & 7u64) == at(function.entry, 0u64); \
        ensures 0 == 0; }";
    let file = parser::parse_file_items(source).expect("the alignment fact should parse");
    let fact = file.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .expect("the requirement should be a proposition");
    let rendered = diagnostics::describe_click_proposition(&fact);
    assert_eq!(rendered, "at(function.entry, aligned(arena, 8))");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_32")]
fn inline_callback_identity_rejects_ambiguous_translation_units() {
    let source = r#"
        verifying "alpha.c";
        verifying "beta.c";
        contract int32 One() { ensures result == 1; }
        int32 callback() { ensures result == 1; } by { step_until(function.exit); normalize(); }
        theorem callback_contract() {
            ensures One(&callback) by { unfold(One(&callback)); close(); }
        }
    "#;
    let inputs = [
        ("alpha.c", "static inline int callback(void) { return 1; }"),
        ("beta.c", "static inline int callback(void) { return 2; }"),
    ];
    let file = parse_click_file_with_c_sources(source, &inputs).unwrap();
    assert!(!file.program_function_names.contains_key("callback"));
    let error = verify_c_sources(source, &inputs).unwrap_err();
    assert!(
        error
            .message()
            .contains("not a verified or external function compatible with contract `One`"),
        "{}",
        error.message()
    );
}

/// A Rust sidecar writes a pure function's, predicate's and theorem's types
/// in Rust: scalars, `bool`, and `*const T` for the bytes a slice points at.
/// `as` casts, and a parenthesized comparison is a `bool` value. The C
/// spellings read the same types. (The mdtest format has no Rust source, so
/// these verify a sidecar of theorems beside an empty source.)
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_32")]
fn a_rust_sidecar_writes_click_types_in_rust() {
    let rust_source = [("bytes.rs", "")];
    let accepted = "verifying \"bytes.rs\";
        function low(x: u32) -> u8 { x as u8 }
        function big(x: u32) -> bool { x > 255u32 }
        function prefix(bytes: *const u8, end: usize) -> Integer {
            (0..end).fold(0, |acc, k| { acc + to_integer(bytes[k] as i32) })
        }
        function c_prefix(bytes: const uint8*, end: uint64) -> Integer {
            (0..end).fold(0, |acc, k| { acc + to_integer(bytes[k] as int32) })
        }
        theorem three_hundred_is_big() {
            ensures big(300u32) by { unfold(big(300u32)); normalize(); }
        }
        theorem three_hundred_keeps_its_low_byte() {
            ensures low(300u32) == 44 by { unfold(low(300u32)); normalize(); }
        }
        theorem a_comparison_is_a_bool_value(b: bool) {
            requires b == (5u32 > 3u32);
            ensures b by close();
        }
        theorem an_index_is_a_usize(n: usize) {
            ensures forall (k: usize) { k < n implies k < n };
        }";
    verify_c_sources(accepted, &rust_source).expect("the Rust spellings verify");
    let error = verify_c_sources(
        "verifying \"bytes.rs\"; function big(x: u32) -> bool { x > 255u32 }
         theorem two_hundred_is_big() {
             ensures big(200u32) by { unfold(big(200u32)); normalize(); }
         }",
        &rust_source,
    )
    .expect_err("200 is not big");
    assert!(
        error.message.contains("did not normalize to true"),
        "{}",
        error.message
    );
    let error = verify_c_sources(
        "verifying \"bytes.rs\"; theorem wrong(b: bool) {
             requires b == (3u32 > 5u32);
             ensures b by close();
         }",
        &rust_source,
    )
    .expect_err("the comparison is false");
    assert!(!error.message.is_empty());
    for (source, expected) in [
        // A slice `&[T]` is a value, but no binder takes another reference
        // `&T`.
        (
            "verifying \"bytes.rs\"; theorem t(byte: &u8) { ensures true; }",
            "takes values, not references",
        ),
        (
            "verifying \"bytes.rs\"; function first(p: &u32) -> u32 { *p }",
            "takes values, not references",
        ),
        (
            "verifying \"bytes.rs\"; theorem t(p: &u32) { ensures true; }",
            "takes values, not references",
        ),
        (
            "verifying \"bytes.rs\"; function first(bytes: *u8) -> u8 { bytes[0] }",
            "a Rust pointer type is `*const T` or `*mut T`",
        ),
        (
            "verifying \"bytes.rs\"; function first(flags: *const bool) -> bool { flags[0] }",
            "a pointer to `bool` is not a Click binder type",
        ),
        (
            "verifying \"bytes.rs\"; function nonzero(x: u32) -> bool { x as bool }",
            "Rust does not cast to `bool`",
        ),
        // A C sidecar keeps a comparison a proposition.
        (
            "verifying \"bytes.c\"; theorem t(x: uint32) { ensures 1 == (x > 3u32); }",
            "expected `)`",
        ),
    ] {
        let error = parser::parse(source).expect_err("the spelling is refused");
        assert!(error.message.contains(expected), "{source}: {error:?}");
    }
}

/// A Rust `as` cast to an integer type reads its operand's observed value,
/// so it may cast an expression over `old(...)` and `at(...)` values, as a
/// C-style integer cast may; a cast to another type still needs a current
/// expression.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_32")]
fn rust_integer_casts_read_historical_operands() {
    let contract = |cast: &str| {
        format!(
            "verifying \"bytes.rs\";
             fn bytes::bump(x: u32) -> u32 {{
                 ensures ({cast}) == ({cast});
             }} by {{ mark before; step_until(function.exit); close(); }}"
        )
    };
    for cast in [
        "old(x) as u64",
        "(old(x) + 1) as i64",
        "(at(before, x) + old(x)) as i32",
    ] {
        parser::parse(&contract(cast)).unwrap_or_else(|error| panic!("`{cast}` parses: {error:?}"));
    }
    let error = parser::parse(&contract("(old(x) + 1) as f64"))
        .expect_err("a floating cast keeps the current-expression requirement");
    assert!(
        error
            .message
            .contains("scalar cast expects a current C expression"),
        "{error:?}"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/tests/surface_syntax.rs");
}

/// A crate trait method's implementation inherits its interface: the
/// interface's `ensures`, labeled as the interface's, and its `requires`
/// when the implementation writes none, whichever block comes first.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_33")]
fn a_rust_trait_implementation_inherits_its_interface() {
    let interface = "trait shapes::Shape { fn area(&self, scale: i32) -> i32 { \
        requires 0 <= scale and scale <= 1000; ensures scale < result; } }";
    let implementation = "impl shapes::Shape for shapes::Circle { \
        fn area(&self, scale: i32) -> i32 { ensures result == scale + scale + 1; } \
}";
    for source in [
        format!("verifying \"shapes.rs\"; {interface} {implementation}"),
        format!("verifying \"shapes.rs\"; {implementation} {interface}"),
    ] {
        let file = parser::parse(&source).expect("the trait and implementation parse");
        let interface = file
            .function_blocks()
            .iter()
            .find(|block| block.is_external())
            .unwrap();
        let circle = file
            .function_blocks()
            .iter()
            .find(|block| !block.is_external())
            .unwrap();
        assert_eq!(circle.requires(), interface.requires());
        assert_eq!(circle.ensures().len(), 2);
        assert_eq!(
            circle.ensures()[1].ensure(),
            interface.ensures()[0].ensure()
        );
        assert_eq!(
            crate::languages::rust::names::display_rust_names(&circle.ensure_claim_label(1)),
            "<shapes::Circle as shapes::Shape>::area.interface_ensures_0"
        );
    }
    // An implementation naming its parameters otherwise reads the
    // interface's clauses with its own names.
    let renamed = implementation.replace("scale", "s");
    let file = parser::parse(&format!("verifying \"shapes.rs\"; {interface} {renamed}"))
        .expect("an implementation renaming its parameters inherits");
    let expected = parser::parse(&format!(
        "verifying \"shapes.rs\"; {}",
        interface.replace("scale", "s")
    ))
    .expect("the renamed interface parses");
    let expected = expected
        .function_blocks()
        .iter()
        .find(|block| block.is_external())
        .unwrap();
    let circle = file
        .function_blocks()
        .iter()
        .find(|block| !block.is_external())
        .unwrap();
    assert_eq!(circle.requires(), expected.requires());
    assert_eq!(circle.ensures()[1].ensure(), expected.ensures()[0].ensure());
    let error = parser::parse(&format!(
        "verifying \"shapes.rs\"; {interface} {}",
        implementation.replace("scale: i32", "scale: i32, extra: i32")
    ))
    .expect_err("an implementation with other parameters cannot inherit");
    assert!(
        error
            .message()
            .contains("takes the parameters the trait's interface does"),
        "{}",
        error.message()
    );
}

// A generic crate trait's block is read at each instance the import uses,
// its type parameter replaced by the instance's argument, and an instance's
// own block adds its clauses to that instance's interface.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_33")]
fn a_generic_rust_trait_block_is_read_at_each_instance() {
    let source = "verifying \"shapes.rs\";
trait shapes::Scale<T> { fn scale(&self, x: T) -> T { ensures result != x; } }
trait shapes::Scale<i32> { fn scale(&self, x: i32) -> i32 { requires 0 <= x; ensures x < result; } }";
    let trait_name = crate::languages::rust::names::qualified_name(["shapes", "Scale"]);
    let layouts = parser::ProgramLayouts {
        rust_trait_instances: [(
            trait_name,
            [vec!["i32".to_string()], vec!["u32".to_string()]].into(),
        )]
        .into(),
        ..Default::default()
    };
    let file = parser::parse_with_layouts_and_aggregate_objects(source, layouts)
        .expect("the generic and instance blocks parse");
    let interface = |name: &str| {
        file.function_blocks()
            .iter()
            .find(|block| {
                crate::languages::rust::names::rust_display_name(block.signature().name())
                    .as_deref()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("{name}"))
    };
    let narrow = interface("shapes::Scale<i32>::scale");
    assert!(narrow.is_external());
    assert_eq!(narrow.requires().len(), 1);
    assert_eq!(narrow.ensures().len(), 2);
    let wide = interface("shapes::Scale<u32>::scale");
    assert!(wide.requires().is_empty());
    assert_eq!(wide.ensures().len(), 1);
    assert_eq!(wide.ensures()[0].ensure(), narrow.ensures()[0].ensure());
    // The generic block is also read once, its type parameter an abstract
    // type, so it is checked for every type whether or not an instance is
    // used.
    let generic = interface("shapes::Scale<T>::scale");
    assert!(generic.signature().has_abstract_types());
    assert_eq!(
        generic.signature().return_type(),
        crate::languages::interface::InterfaceType::Parameter(
            crate::kernel::TypeParameterName::intern("T")
        )
    );
    let unused = parser::parse(
        "verifying \"shapes.rs\"; trait shapes::Scale<T> { fn scale(&self, x: T) -> T { ensures result != x; } }",
    )
    .expect("a generic block with no instance parses");
    assert!(
        unused
            .function_blocks()
            .iter()
            .any(|block| block.signature().has_abstract_types())
    );
    for (block, expected) in [
        (
            "trait shapes::Scale<T, i32> { }",
            "names its type parameters",
        ),
        (
            "trait shapes::Scale<i32> { } trait shapes::Scale<i32> { }",
            "has two `trait` blocks",
        ),
    ] {
        let error =
            parser::parse(&format!("verifying \"shapes.rs\"; {block}")).expect_err(expected);
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

// A generic crate trait's `function`s are the fields of its object, a
// generic sealed resource: the generic block holds it at `T`, and each
// instance at its types, `Bag<i32>`'s at `i32`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_33")]
fn a_generic_rust_trait_object_is_a_generic_resource() {
    let source = "verifying \"shapes.rs\";
trait bags::Bag<T> { function last(self) -> T; fn insert(&mut self, x: T) { ensures last(self) == x; } }";
    let trait_name = crate::languages::rust::names::qualified_name(["bags", "Bag"]);
    let layouts = parser::ProgramLayouts {
        rust_trait_instances: [(
            trait_name,
            [vec!["i32".to_string()], vec!["u8".to_string()]].into(),
        )]
        .into(),
        ..Default::default()
    };
    let file = parser::parse_with_layouts_and_aggregate_objects(source, layouts)
        .expect("the generic block with object state parses");
    let mut objects = file
        .resource_definitions()
        .iter()
        .map(|definition| {
            crate::languages::rust::names::display_rust_names(definition.name()).into_owned()
        })
        .collect::<Vec<_>>();
    objects.sort();
    assert_eq!(
        objects,
        [
            "bags::Bag::object<T>",
            "bags::Bag::object<i32>",
            "bags::Bag::object<u8>"
        ]
    );
    for definition in file.resource_definitions() {
        assert!(definition.is_sealed());
    }
}

/// A crate trait's `function`s are its object's fields: the object is a
/// field-bearing abstract resource, a `&self` method's interface holds it and
/// reads `size(self)` as its field, an implementation's method is stated on
/// its own memory with the interface inherited there, and the struct's pack
/// and unpack carry the definitions.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_33")]
fn a_rust_trait_function_is_its_object_field() {
    let source = "verifying \"shapes.rs\"; \
        trait shapes::Shape { function size(self) -> i32; \
            fn area(&self, scale: i32) -> i32 { ensures result == size(self) + scale; } } \
        impl shapes::Shape for shapes::Square { function size(self) -> i32 { self.side } \
            fn area(&self, s: i32) -> i32 { } }";
    // The importer supplies `Square`'s layout, which `owns *self` reads.
    let parse = |source: &str| {
        parser::parse_with_layouts_and_aggregate_objects(
            source,
            parser::ProgramLayouts {
                struct_layouts: [(
                    "__rust_q_I6_shapes_I6_Square".to_string(),
                    crate::languages::interface::RecordLayout::from_explicit_fields(
                        vec![(
                            "side".into(),
                            crate::languages::interface::InterfaceType::Int32,
                            0,
                            4,
                        )],
                        4,
                        4,
                    )
                    .unwrap(),
                )]
                .into(),
                ..Default::default()
            },
        )
    };
    let file = parse(source).expect("a trait with a function parses");
    let display = |name: &str| crate::languages::rust::names::display_rust_names(name).into_owned();
    let object = file
        .resource_definitions()
        .iter()
        .find(|definition| display(definition.name()) == "shapes::Shape::object")
        .expect("the trait's object is declared");
    assert!(object.is_sealed());
    assert_eq!(object.fields().len(), 1);
    let names = file
        .function_blocks()
        .iter()
        .map(|block| display(block.signature().name()))
        .collect::<Vec<_>>();
    for name in [
        "shapes::Shape::area",
        "<shapes::Square as shapes::Shape>::area",
        "<shapes::Square as shapes::Shape>::__pack",
        "<shapes::Square as shapes::Shape>::__unpack",
    ] {
        assert!(names.iter().any(|found| found == name), "{name}: {names:?}");
    }
    // The implementation renames `scale` and reads `size(self)` as
    // `self.side`, with the interface's guarantee labeled as the interface's.
    let area = file
        .function_blocks()
        .iter()
        .find(|block| {
            display(block.signature().name()) == "<shapes::Square as shapes::Shape>::area"
        })
        .unwrap();
    assert!(
        area.requires()
            .iter()
            .any(|requirement| matches!(requirement, Requirement::Resource(_)))
    );
    let labels = (0..area.ensures().len())
        .map(|index| display(&area.ensure_claim_label(index)))
        .collect::<Vec<_>>();
    assert!(
        labels
            .iter()
            .any(|label| label == "<shapes::Square as shapes::Shape>::area.interface_ensures_0"),
        "{labels:?}"
    );
    let iface = parser::implementation_interface_contract(area.signature().name());
    assert!(
        file.contract_definitions()
            .iter()
            .any(|contract| contract.name() == iface)
    );
    let missing = source.replace("function size(self) -> i32 { self.side }", "");
    let error = parse(&missing).expect_err("an implementation must define the function");
    assert!(
        error.message().contains("defines it for its type"),
        "{}",
        error.message()
    );
}

/// A C++ class block declares its object's functions, which a `const`
/// method and a `const Shape&` parameter read as the object's fields; a
/// direct subclass defines them, and its method is stated on its memory.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_34")]
fn a_cpp_class_function_is_its_object_field() {
    let source = "verifying \"shapes.cpp\"; \
        class Shape { function size(this) -> int32; } \
        extern int Shape::area(int scale) const { ensures result == size(this) + scale; } \
        int total(const Shape& shape, int scale) { ensures result == size(shape) + scale; } \
        class Square : Shape { function size(this) -> int32 { this->side } }";
    use crate::languages::interface::{InterfaceType, RecordLayout};

    let layout = |fields, size| RecordLayout::from_explicit_fields(fields, size, 8).unwrap();
    let parse = |source: &str| {
        parser::parse_with_layouts_and_aggregate_objects(
            source,
            parser::ProgramLayouts {
                language: Some(crate::languages::SourceLanguage::Cpp),
                // The importer's layouts, whose leading vtable pointer no field
                // names.
                struct_layouts: [
                    ("Shape".to_string(), layout(vec![], 8)),
                    (
                        "Square".to_string(),
                        layout(vec![("side".into(), InterfaceType::Int32, 8, 4)], 16),
                    ),
                ]
                .into(),
                ..Default::default()
            },
        )
    };
    let file = parse(source).expect("a class with a function parses");
    let object = file
        .resource_definitions()
        .iter()
        .find(|definition| definition.name() == "Shape__object")
        .expect("the class's object is declared");
    assert!(object.is_sealed());
    let names = file
        .function_blocks()
        .iter()
        .map(|block| block.signature().name().to_string())
        .collect::<Vec<_>>();
    for name in ["Square__click_pack__Shape", "Square__click_unpack__Shape"] {
        assert!(names.iter().any(|found| found == name), "{name}: {names:?}");
    }
    for (from, to, expected) in [
        (
            "    function size(this) -> int32 { this->side }",
            " ",
            "defines `Shape`'s `function size` on its own memory",
        ),
        (
            "class Square : Shape",
            "class Square : Other",
            "names a base without a `class` block",
        ),
    ] {
        let source = source.replace(from.trim_start(), to);
        let error = parse(&source).expect_err(expected);
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_34")]
fn a_conjunct_of_one_source_facts_lowering_finds_that_fact() {
    // `x == 1` stands for a source atom (such as a contract `separate`) whose
    // lowering adds conditions beside the fact it states.
    let surface = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let stated = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(984_500))),
            right: Box::new(MachineTerm::constant(1)),
        },
        true,
    );
    let side = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(MachineTerm::Variable(Variable(984_501))),
            right: Box::new(MachineTerm::constant(7)),
        },
        true,
    );
    let lowered = Proposition::And(Box::new(stated.clone()), Box::new(side.clone()));
    let mut forms = SurfacePropositionMap::default();
    forms.record_lowering(&surface, &lowered).unwrap();
    // The conjunct has no spelling of its own; the whole lowering does.
    assert!(forms.surface(&stated).is_err());
    assert_eq!(
        forms
            .kernels_containing_conjunct(&stated)
            .collect::<Vec<_>>(),
        vec![&lowered]
    );
    assert_eq!(
        forms.kernels_containing_conjunct(&side).collect::<Vec<_>>(),
        vec![&lowered]
    );
    let unrelated = Proposition::condition_is(ConditionTerm::Constant(true), true);
    assert_eq!(forms.kernels_containing_conjunct(&unrelated).count(), 0);
    // A written conjunction records its conjuncts as pairs, not containment.
    let left = ClickProposition::Comparison {
        left: current_var("y"),
        operator: ComparisonOperator::Equal,
        right: current_int(2),
    };
    let left_kernel = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(984_502))),
            right: Box::new(MachineTerm::constant(2)),
        },
        true,
    );
    let mut written = SurfacePropositionMap::default();
    written
        .record_lowering(
            &ClickProposition::And(Box::new(left.clone()), Box::new(surface.clone())),
            &Proposition::And(Box::new(left_kernel.clone()), Box::new(stated.clone())),
        )
        .unwrap();
    assert_eq!(written.surface(&left_kernel).unwrap(), &left);
    assert_eq!(written.kernels_containing_conjunct(&left_kernel).count(), 0);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_34")]
fn printed_machine_arithmetic_keeps_exact_transport_premises() {
    for (ty, one, operator, authored) in [
        (
            "int32",
            ProgramValue::Int32(MachineTerm::constant(1)),
            "-",
            "to_integer(hi - 1) < to_integer(hi)",
        ),
        (
            "uint64",
            ProgramValue::UInt64(MachineTerm::uint64_constant(1)),
            "+",
            "to_integer(hi) < to_integer(hi + 1u64)",
        ),
    ] {
        let variable = ProgramExpression::Variable("hi".into());
        let arithmetic = if operator == "-" {
            ProgramExpression::Subtract(
                Box::new(variable.clone()),
                Box::new(ProgramExpression::Value(one)),
            )
        } else {
            ProgramExpression::Add(
                Box::new(variable.clone()),
                Box::new(ProgramExpression::Value(one)),
            )
        };
        let (left, right) = if operator == "-" {
            (arithmetic, variable)
        } else {
            (variable, arithmetic)
        };
        let premise = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(left),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::ProgramExpression(right),
        };
        let printed = printing::source_click_proposition(&premise);
        let source = format!(
            "theorem retained(hi: {ty}) {{ requires 0 < hi; requires hi < 100; requires {authored}; ensures {printed} by {{ close(); }} }}"
        );
        verify_click_theorems(&source).unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by surface_syntax_batch_34")]
fn synthesized_signed_difference_preserves_its_type_without_literals() {
    let less_equal = |left, right| ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::LessEqual,
        left: Box::new(left),
        right: Box::new(right),
    };
    let hi = MachineTerm::Variable(Variable(984_600));
    let lo = MachineTerm::Variable(Variable(984_601));
    let difference = MachineTerm::subtract_at(MachineIntegerType::Int32, hi.clone(), lo.clone());
    let original =
        Proposition::condition_is(less_equal(MachineTerm::constant(0), difference), true);
    let state = ExecutionState::new()
        .with_local("hi", ProgramValue::Int32(hi.clone()))
        .with_local("lo", ProgramValue::Int32(lo.clone()));
    let surface =
        synthesize_surface_proposition(&original, ParameterBinding::default(), &state).unwrap();
    let printed = printing::source_click_proposition(&surface);
    let file = parser::parse_file_items(&format!(
        "theorem t() {{ requires {printed}; ensures true; }}"
    ))
    .unwrap();
    let reparsed = file.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .unwrap();
    let mut bounds = Vec::new();
    for term in [hi.clone(), lo.clone()] {
        bounds.push(Proposition::condition_is(
            less_equal(MachineTerm::constant(0), term.clone()),
            true,
        ));
        bounds.push(Proposition::condition_is(
            less_equal(term, MachineTerm::constant(100)),
            true,
        ));
    }
    let facts = crate::surface::verification::assumptions_from_propositions(&bounds);
    let values = ProgramValueBindings::from([
        ("hi".to_string(), ProgramValue::Int32(hi)),
        ("lo".to_string(), ProgramValue::Int32(lo)),
    ]);
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let lowered = crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        &reparsed,
        &facts,
        ContractEnvironment::new(&values, &BTreeMap::new()),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicates, &functions),
    )
    .unwrap();
    let Proposition::ConditionIs(condition, truth) = &original else {
        unreachable!()
    };
    let retained = Proposition::condition_is(
        crate::kernel::machine_integer::comparison::retained_arithmetic_comparison(
            condition.native_compat(),
        )
        .unwrap(),
        *truth,
    );
    assert_eq!(lowered, retained, "{printed}");
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "surface_syntax.rs",
    marker: "surface_syntax_batch_",
    surface_syntax_batch_00: [
        integer_parameter_preserves_machine_literal_and_cast_behavior,
        integer_constant_aliases_stay_shared_before_a_tactic_starts,
        integer_solve_expansion_rechecks_without_smart_search,
    ],
    surface_syntax_batch_01: [
        integer_alias_certificates_preserve_types_and_linear_source_on_expansion,
        parser_deep_const_rejects_qualification_beyond_first_pointer_level,
        parser_deep_const_preserves_supported_pointer_qualifier_levels,
        plain_char_needs_a_c_target_and_takes_its_signedness,
    ],
    surface_syntax_batch_02: [
        parser_plain_char_sidecars_preserve_source_compatibility,
        false_library_list_equality_has_a_bounded_diagnostic,
        parser_accepts_its_supported_parenthesis_depth,
        parser_accepts_standard_c_type_spellings_in_sidecars,
    ],
    surface_syntax_batch_03: [
        parser_accepts_bodyless_external_function_contracts,
        parser_rejects_excessive_parenthesis_depth_with_a_source_diagnostic,
        parser_bounds_non_parenthesized_surface_nesting_before_ast_construction,
        representative_surface_depths_survive_consumption,
    ],
    surface_syntax_batch_04: [
        parser_preserves_mixed_grouped_proposition_and_contract_expression_syntax,
        parses_expanded_typed_loads_and_old_loadability,
        parses_the_c_target_directive,
        the_pre_parse_target_scan_agrees_with_the_parser,
    ],
    surface_syntax_batch_05: [
        rejects_an_unknown_or_repeated_c_target,
        parses_checked_signature_and_contract_clauses,
        parses_void_c_function_contracts_without_a_result_binding,
        parses_pure_theorem_definition,
    ],
    surface_syntax_batch_06: [
        parses_integer_theorem_parameters_and_keeps_decimal_spelling,
        rejects_integer_as_an_algebraic_type_name,
        parses_c_function_pointer_type_in_pure_theorem_parameter,
        parses_and_prints_pure_induction_tactics,
    ],
    surface_syntax_batch_07: [
        parses_and_prints_structural_induction_arms,
        parses_and_prints_pure_function_unfold,
        rejects_removed_fold_tactic_syntax,
        parses_and_prints_solve_using_premise_lists,
    ],
    surface_syntax_batch_09: [
        signed_compound_expansion_uses_ordinary_operations_and_rejects_false_goal,
    ],
    surface_syntax_batch_11: [
        float_reflexive_smart_expansion_replays_as_known,
        signed_arithmetic_smart_planner_expands_to_ordinary_proof,
    ],
    surface_syntax_batch_12: [
        signed_arithmetic_using_requires_every_needed_exact_premise,
        integer_arithmetic_uses_checked_unified_certificate_without_replanning,
        integer_arithmetic_using_proves_a_chain_longer_than_three_premises,
        integer_arithmetic_using_rejects_an_unavailable_irrelevant_extra,
    ],
    surface_syntax_batch_13: [
        signed_arithmetic_smart_planner_preserves_explicit_definedness,
        verifies_pure_theorem_definition,
        pure_bare_apply_builds_a_checked_proof_object_certificate,
        pure_solve_exposes_explicit_arithmetic_steps,
    ],
    surface_syntax_batch_14: [
        pure_solve_after_unfold_exposes_an_explicit_certificate,
        branching_pure_solve_exposes_explicit_branch_certificates,
        verifies_explicit_structural_logic_tactics,
        verifies_atomic_derivation_from_explicit_premises,
    ],
    surface_syntax_batch_15: [
        records_checked_surface_forms_for_lowered_propositions,
        surface_synthesis_qualifies_a_c_local_named_result,
        surface_synthesis_omits_a_predicates_hidden_resource_state_argument,
        surface_synthesis_spells_reserved_predicates_by_their_click_names,
    ],
    surface_syntax_batch_16: [
        surface_synthesis_prefers_struct_field_places_to_typed_loads,
        proof_source_printing_preserves_proposition_precedence,
        proof_source_printing_preserves_long_sum_association_without_nested_prefixes,
        normalize_does_not_close_quantified_contradictions,
    ],
    surface_syntax_batch_17: [
        normalization_does_not_hide_context_free_conjunction_derivation,
        normalization_does_not_hide_context_free_disjunction_derivation,
        smart_context_free_disjunction_retains_known_leaf,
        normalization_does_not_hide_context_free_implication_derivation,
    ],
    surface_syntax_batch_18: [
        smart_context_free_implication_retains_explicit_introduction,
        retains_distinct_surface_spellings_for_the_same_kernel_fact,
        recorded_surface_fact_resolves_only_one_available_kernel_fact,
        surface_lowering_map_forks_and_local_updates_scale_logarithmically,
    ],
    surface_syntax_batch_19: [
        rejects_byte_counting_loadable_syntax,
        parses_loadable_segment_syntax,
        parses_parenthesized_loaded_pointer_segment_base,
        parses_loadable_segment_proposition,
    ],
    surface_syntax_batch_20: [
        parses_resource_relation_propositions,
        parses_memory_separate_requirement,
        restricted_solve_premises_retain_declared_resource_argument_types,
        transport_using_retains_declared_resource_argument_types,
    ],
    surface_syntax_batch_21: [
        rejects_reversed_constant_loadable_segment,
        parses_array_parameter_signature_as_pointer,
        parses_pilot_struct_pointer_signature_and_field_load,
        parses_struct_pointer_callback_signature,
    ],
    surface_syntax_batch_22: [
        parses_chained_struct_fields_with_imported_pointee_types,
        nested_field_segments_keep_the_terminal_field_offset,
        parses_struct_object_segments_without_exposing_layout_cells,
        an_embedded_struct_is_viewed_as_a_place,
    ],
    surface_syntax_batch_23: [
        parses_pilot_struct_field_owned_segment,
        rejects_legacy_mutable_field_effect_spelling,
        rejects_legacy_read_write_resource_spelling,
        parses_block_by_clause,
    ],
    surface_syntax_batch_24: [
        parses_sequence_literals_states_and_concatenation,
        integer_datatype_match_bindings_shadow_each_source_carrier,
        integer_datatype_match_iota_survives_function_substitution_and_recheck,
        integer_datatype_match_numeral_arm_inherits_integer_result_and_rechecks,
    ],
    surface_syntax_batch_25: [
        integer_match_constructor_fields_retain_unused_conversion_definedness,
        symbolic_integer_datatype_matches_reject_invalid_arms,
        symbolic_integer_datatype_match_does_not_capture_outer_binding,
        diverges_stays_an_ordinary_identifier_elsewhere,
    ],
    surface_syntax_batch_26: [
        diverges_must_follow_throws_in_a_signature,
        external_contracts_accept_diverges_and_still_reject_decreases,
        loop_diverges_round_trips_through_expansion,
        a_diverges_function_never_yields_termination_evidence,
    ],
    surface_syntax_batch_27: [
        parses_built_in_expressions_on_either_comparison_side,
        typed_loads_lower_and_raise_back_to_the_same_term,
        resource_array_size_excludes_struct_padding,
        a_child_resource_is_owned_like_any_other,
        an_invariant_label_names_it_in_a_failure,
    ],
    surface_syntax_batch_28: [
        nonzero_member_addresses_preserve_their_typed_place_when_printed,
        pointer_storage_views_name_the_field_alone,
        a_contract_cannot_return_one_place_twice,
        a_reference_parameter_does_not_match_a_c_pointer,
    ],
    surface_syntax_batch_29: [
        a_contract_cannot_return_overlapping_places,
        a_hidden_record_needs_its_child_declared_first,
        a_rust_sidecar_compares_a_bitwise_operand_without_parentheses,
        a_rust_sidecar_states_its_signature_in_rust_syntax,
    ],
    surface_syntax_batch_30: [
        a_missing_memory_fact_is_reported_as_a_place,
        memory_ranges_use_fields_or_correctly_scaled_source_elements,
        held_recursive_struct_range_and_bound_load_name_their_fields,
        a_production_obligation_names_the_same_struct_place_as_its_missing_fact,
    ],
    surface_syntax_batch_31: [
        a_struct_pointer_range_counts_structs,
        a_resource_clause_names_a_place,
        a_whole_struct_view_reads_and_does_not_write,
        state_read_alignment_fact_renders_as_aligned,
    ],
    surface_syntax_batch_32: [
        inline_callback_identity_rejects_ambiguous_translation_units,
        a_rust_sidecar_writes_click_types_in_rust,
        rust_integer_casts_read_historical_operands,
    ],
    surface_syntax_batch_33: [
        a_rust_trait_implementation_inherits_its_interface,
        a_generic_rust_trait_block_is_read_at_each_instance,
        a_generic_rust_trait_object_is_a_generic_resource,
        a_rust_trait_function_is_its_object_field,
    ],
    surface_syntax_batch_34: [
        a_cpp_class_function_is_its_object_field,
        a_conjunct_of_one_source_facts_lowering_finds_that_fact,
        printed_machine_arithmetic_keeps_exact_transport_premises,
        synthesized_signed_difference_preserves_its_type_without_literals,
    ],
}

#[test]
fn local_storage_and_resource_stars_have_round_tripping_spellings() {
    let declaration = crate::kernel::prove_execution_statement_execution(
        ExecutionState::new(),
        crate::kernel::ProgramStatement::Declare {
            name: "i".into(),
            program_type: ProgramType::Int32,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            initializer: Some(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(7),
            ))),
            zero_fill: None,
            declared_class: None,
        },
    )
    .unwrap();
    let Proposition::ProgramStatementVerifies {
        outcome: crate::kernel::StatementOutcome::Normal(state),
        ..
    } = declaration.proposition()
    else {
        panic!("local declaration did not finish");
    };
    let local = state.resources().facts()[0].resource().clone();
    let original = Proposition::ResourceSeparate {
        left: Box::new(local.clone()),
        right: Box::new(crate::kernel::Resource::star(
            local,
            crate::kernel::Resource::Emp,
        )),
    };
    let surface = synthesize_surface_proposition(&original, ParameterBinding::default(), state)
        .expect("local storage and separating conjunction must be spellable");
    let printed = printing::source_click_proposition(&surface);
    let file = parser::parse_file_items(&format!(
        "theorem t() {{ requires {printed}; ensures true; }}"
    ))
    .unwrap();
    let reparsed = file.theorem_definitions()[0].requires()[0]
        .theorem_proposition()
        .unwrap();
    let values = ProgramValueBindings::from([(
        "i".to_string(),
        ProgramValue::Int32(MachineTerm::constant(7)),
    )]);
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let lowered = crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        &reparsed,
        &crate::kernel::PureFactContext::new(),
        ContractEnvironment::new(&values, &BTreeMap::new()),
        FixedStateFrame::new(state, state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicates, &functions),
    )
    .unwrap();
    assert_eq!(lowered, original, "{printed}");
}
