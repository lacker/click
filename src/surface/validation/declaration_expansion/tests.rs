use super::*;

fn authority_test_scope(
    kind: ResourceKind,
    parameter_type: C0Type,
    has_fields: bool,
) -> DeclaredResourceScope {
    DeclaredResourceScope {
        family_rules: false,
        definitions: BTreeMap::from([(
            "reference".to_string(),
            DeclaredResourceInfo {
                fields: Default::default(),
                field_schema: None,
                parameter_types: vec![parameter_type],
                resource_parameter_families: Vec::new(),
                kind,
                has_fields,
                authorized: true,
                child_slots: Default::default(),
            },
        )]),
        children: Default::default(),
        instances: Default::default(),
        field_binders: Default::default(),
        unowned_resource_parameters: Default::default(),
    }
}

fn authority_test_protected(argument: ContractExpression) -> ResourceClause {
    ResourceClause::Declared {
        type_schema: None,
        resource_type_arguments: Vec::new(),
        resource_arguments: Vec::new(),
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Token,
        name: "reference".to_string(),
        arguments: vec![argument],
        parameter_types: Vec::new(),
    }
}

#[test]
fn authority_type_argument_requires_exact_unary_pointer_family() {
    let pointer = ContractExpression::CFragment(CExpression::Variable("p".to_string()));
    let accepted = expand_resource_type_arguments(
        "authority",
        vec![authority_test_protected(pointer.clone())],
        &authority_test_scope(ResourceKind::Composite, C0Type::Int32Pointer, false),
    )
    .expect("exact field-free pointer family");
    assert!(matches!(
        &accepted[0],
        ResourceClause::Declared {
            type_schema: Some(_),
            kind: ResourceKind::Composite,
            ..
        }
    ));
    let authority = ResourceClause::Declared {
        type_schema: None,
        resource_type_arguments: accepted,
        resource_arguments: Vec::new(),
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Token,
        name: "authority".to_string(),
        arguments: Vec::new(),
        parameter_types: Vec::new(),
    };
    let spec = crate::surface::verification::resource_clause_to_resource_spec(&authority)
        .expect("checked source authority lowers to a kernel resource term");
    assert!(matches!(
        spec.term(),
        crate::kernel::CResourceTerm::PopulationAuthority { .. }
    ));
    assert!(
        expand_resource_type_arguments(
            "authority",
            vec![authority_test_protected(pointer.clone())],
            &authority_test_scope(ResourceKind::Token, C0Type::Int32Pointer, false),
        )
        .is_ok(),
        "abstract token resource families are valid protected types"
    );
    for (scope, argument) in [
        (
            authority_test_scope(ResourceKind::Composite, C0Type::Int32, false),
            pointer.clone(),
        ),
        (
            authority_test_scope(ResourceKind::Composite, C0Type::Int32Pointer, false),
            ContractExpression::ResourceWildcard,
        ),
    ] {
        assert!(
            expand_resource_type_arguments(
                "authority",
                vec![authority_test_protected(argument)],
                &scope,
            )
            .is_err()
        );
    }
    assert!(
        expand_resource_type_arguments(
            "authority",
            Vec::new(),
            &authority_test_scope(ResourceKind::Composite, C0Type::Int32Pointer, false)
        )
        .is_err()
    );
}

fn check_isolated_program(value: i32, expected: i32) {
    let c_source = format!("int32 answer(void) {{ return {value}; }}");
    let click_source = format!(
        r#"
        verifying "answer.c";
        predicate wanted(x: int32) {{ x == {expected} }}
        int32 answer() {{
            ensures wanted(result) by {{ execute(); unfold(wanted); simp(); }}
        }}
        "#
    );
    let result = verify_c0_sources(&click_source, &[("answer.c", &c_source)]);
    if value == expected {
        result.expect("each program must use its own wanted predicate");
    } else {
        assert!(
            result.is_err(),
            "a preceding successful proof must not leak"
        );
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn standard_library_initialization_is_constant_across_verification_sizes() {
    // Count initialization, not elapsed time: repeated fixture threads must
    // not parse the prelude again as the number of verifications increases.
    for count in [1, 2, 4, 8] {
        std::thread::scope(|scope| {
            let handles = (0..count)
                .map(|value| {
                    scope.spawn(move || {
                        check_isolated_program(value, value);
                        check_isolated_program(value, value + 1);
                        check_isolated_program(value + 1, value + 1);
                    })
                })
                .collect::<Vec<_>>();
            for handle in handles {
                handle.join().unwrap();
            }
        });
        assert_eq!(
            STANDARD_LIBRARY_PARSES.load(std::sync::atomic::Ordering::Relaxed),
            1,
            "prelude initialization must remain constant at {count} fixture threads"
        );
    }
}

/// The prelude parse charges the run that performs it. A run whose budget
/// runs out mid-parse fails alone; the next run still gets the prelude.
#[test]
fn a_budget_exhausted_during_the_prelude_parse_is_not_cached() {
    let exhausted =
        crate::instrumentation::with_run_work_limit(1, || standard_library().map(|_| ()));
    let after = standard_library();
    assert!(
        after.is_ok(),
        "a later run must parse the prelude after {exhausted:?}: {after:?}"
    );
}

#[test]
fn standard_library_syntax_errors_name_the_prelude_file_and_line() {
    for source in ["\n\n/* an unclosed `quoted` comment", "\n\nfunction 42"] {
        let error = load_standard_library(source).expect_err("invalid prelude must fail");
        assert_eq!(error.kind(), ClickErrorKind::Syntax);
        assert!(
            error.message().contains("stdlib/prelude.click:3"),
            "{}",
            error.message()
        );
        let error = error.with_context("while checking module `example.click`");
        assert!(
            error.message().contains("stdlib/prelude.click:3"),
            "module context must preserve the prelude location: {}",
            error.message()
        );
    }
}

#[test]
fn standard_library_cache_preserves_all_declarations() {
    let fresh = load_standard_library(CLICK_STANDARD_LIBRARY).unwrap();
    assert_eq!(standard_library().unwrap(), &fresh);
    // Accessors return independently owned categories, never a mutable view
    // of the process-wide syntax or a clone of unrelated categories.
    let empty = parser::parse_file_items("").unwrap();
    let mut functions = combined_external_function_blocks(&empty).unwrap();
    assert!(!functions.is_empty());
    functions.clear();
    assert_eq!(
        combined_external_function_blocks(&empty).unwrap(),
        fresh.function_blocks()
    );
    assert_eq!(
        combined_algebraic_type_definitions(&empty).unwrap(),
        fresh.algebraic_type_definitions
    );
}

/// The standard library is proved by its own entry point, not by each
/// verification that uses it. This is the gate's proof of every library
/// theorem.
#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn standard_library_theorems_are_proved_by_their_own_entry_point() {
    let theorems = standard_library_theorem_definitions().unwrap();
    let verified = crate::surface::verify_standard_library()
        .unwrap_or_else(|error| panic!("standard library failed: {}", error.message()));
    let ensure_count = theorems
        .iter()
        .map(|theorem| theorem.ensures().len())
        .sum::<usize>();
    assert_eq!(verified.len(), ensure_count);
    for theorem in theorems {
        assert!(
            verified
                .iter()
                .any(|result| result.theorem_definition.name() == theorem.name()),
            "`{}` was not proved",
            theorem.name()
        );
    }
}

fn proved_theorems_during(verify: impl FnOnce()) -> Vec<String> {
    crate::surface::PROVED_THEOREMS.with(|proved| proved.borrow_mut().clear());
    verify();
    crate::surface::PROVED_THEOREMS.with(|proved| proved.take())
}

/// A verification applies library theorems as dependency declarations and
/// proves only its own theorems, however large the library grows.
#[test]
fn verification_does_not_reprove_the_standard_library() {
    let proved = proved_theorems_during(|| {
        let result = verify_click_theorems(
            r#"
            theorem uses_library(value: int32) {
                requires 0 < value;
                ensures 0 <= value by {
                    apply(int32_positive_is_nonnegative(value));
                }
            }
            "#,
        );
        result.unwrap_or_else(|error| panic!("theorem failed: {}", error.message()));
        check_isolated_program(3, 3);
    });
    assert_eq!(proved, ["uses_library"]);
}

/// Certification accepts a pure theorem only with authority from a checked
/// proof, so a C proof that cites a library theorem needing that authority
/// checks exactly the cited theorem, not the rest of the library.
#[test]
fn certification_checks_only_the_cited_library_theorem() {
    let c_source = "int32 remainder(int32 value, int32 amount) { return value - amount; }";
    let click_source = r#"
        verifying "remainder.c";
        int32 remainder(int32 value, int32 amount) {
            requires defined(1 + amount) and value == 1 + amount;
            requires defined(value - amount);
            ensures result == 1;
        } by {
            have value - amount == 1 by {
                apply(int32_subtract_equal_sum_right_cancels(value, 1, amount)) using {
                    defined(1 + amount) and value == 1 + amount;
                    defined(value - amount);
                }
            }
            execute();
            simp();
        }
    "#;
    let proved = proved_theorems_during(|| {
        verify_c0_sources(click_source, &[("remainder.c", c_source)])
            .unwrap_or_else(|error| panic!("C proof failed: {}", error.message()));
    });
    assert_eq!(proved, ["int32_subtract_equal_sum_right_cancels"]);
}

#[test]
fn authority_field_schema_and_count_admission_are_independent_of_instance_fields() {
    let pointer = ContractExpression::CFragment(CExpression::Variable("p".into()));
    let mut scope = authority_test_scope(ResourceKind::Composite, C0Type::Int32Pointer, true);
    scope.definitions.get_mut("reference").unwrap().fields =
        std::sync::Arc::new(BTreeMap::from([(
            "serial".into(),
            (0, ClickType::C(C0Type::Int32)),
        )]));
    let accepted = expand_resource_type_arguments(
        "authority",
        vec![authority_test_protected(pointer.clone())],
        &scope,
    )
    .unwrap();
    assert!(
        matches!(&accepted[0], ResourceClause::Declared { type_schema: Some(schema), .. } if schema.fields().len() == 1)
    );
    let count = ContractExpression::ResourceCount(Box::new(authority_test_protected(pointer)));
    assert!(
        expand_declared_resource_expression(count.clone(), &scope).is_err(),
        "the standard library's expansion applies no family rules"
    );
    scope.family_rules = true;
    assert!(
        matches!(expand_declared_resource_expression(count, &scope).unwrap(), ContractExpression::ResourceCount(resource) if matches!(resource.as_ref(), ResourceClause::Declared { type_schema: Some(schema), .. } if schema.fields().len() == 1))
    );
}

/// Milestone 7's exit gate: field presence no longer selects countability.
/// Under the family rules a count is admitted exactly when the family is
/// `authorized`, whether or not it declares fields.
#[test]
fn authorization_not_field_presence_selects_countability() {
    let pointer = ContractExpression::CFragment(CExpression::Variable("p".into()));
    let count = ContractExpression::ResourceCount(Box::new(authority_test_protected(pointer)));
    for has_fields in [false, true] {
        for authorized in [false, true] {
            let mut scope =
                authority_test_scope(ResourceKind::Composite, C0Type::Int32Pointer, has_fields);
            scope.family_rules = true;
            let info = scope.definitions.get_mut("reference").unwrap();
            info.authorized = authorized;
            if has_fields {
                info.fields = std::sync::Arc::new(BTreeMap::from([(
                    "serial".into(),
                    (0, ClickType::C(C0Type::Int32)),
                )]));
            }
            assert_eq!(
                expand_declared_resource_expression(count.clone(), &scope).is_ok(),
                authorized,
                "has_fields={has_fields} authorized={authorized}"
            );
        }
    }
}
