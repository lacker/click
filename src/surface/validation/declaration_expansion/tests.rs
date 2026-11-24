use super::*;

fn authority_test_scope(
    kind: ResourceKind,
    parameter_type: InterfaceType,
    has_fields: bool,
) -> DeclaredResourceScope {
    DeclaredResourceScope {
        family_rules: false,
        definitions: BTreeMap::from([(
            "reference".to_string(),
            DeclaredResourceInfo {
                witnesses: Default::default(),
                fields: Default::default(),
                field_schema: None,
                parameter_types: vec![parameter_type],
                resource_parameter_families: Vec::new(),
                kind,
                has_fields,
                authorized: true,
                child_slots: Default::default(),
                arm_child_slots: Default::default(),
            },
        )]),
        families: Default::default(),
        family_log: Default::default(),
        selected_arms: Default::default(),
        unowned_resource_parameters: Default::default(),
        character_parameters: Default::default(),
        constructors: ConstructorTypes::inactive(),
    }
}

#[test]
fn negated_resource_fields_receive_their_declared_metadata() {
    let mut scope =
        authority_test_scope(ResourceKind::Composite, InterfaceType::Int32Pointer, true);
    let field_type = ClickType::Program(InterfaceType::Int32);
    scope.definitions.get_mut("reference").unwrap().fields =
        std::sync::Arc::new(BTreeMap::from([("value".into(), (3, field_type.clone()))]));
    for name in ["value", "missing"] {
        let expression = ContractExpression::Negate(Box::new(ContractExpression::Negate(
            Box::new(ContractExpression::ResourceField(ResourceFieldAccess {
                owner: "r".into(),
                resource_name: "reference".into(),
                identity: InstanceId::from_variable(Variable(0)).into(),
                children: vec![],
                field: name.into(),
                field_index: 0,
                click_type: None,
            })),
        )));
        let result = expand_declared_resource_expression(expression, &scope);
        if name == "missing" {
            assert!(
                result
                    .unwrap_err()
                    .message()
                    .contains("has no field `missing`")
            );
            continue;
        }
        let ContractExpression::Negate(outer) = result.unwrap() else {
            panic!()
        };
        let ContractExpression::Negate(inner) = *outer else {
            panic!()
        };
        let ContractExpression::ResourceField(access) = *inner else {
            panic!()
        };
        assert_eq!(access.field_index, 3);
        assert_eq!(access.click_type, Some(field_type.clone()));
    }
}

/// Each alternative arm starts from the state before the arms. Afterwards
/// an instance the arms agree on keeps its resource, one only some arms
/// bind keeps theirs, and one the arms give different resources is refused.
#[test]
fn alternative_arms_join_the_resources_they_give_an_instance() {
    let scope = authority_test_scope(ResourceKind::Composite, InterfaceType::Int32Pointer, true);
    let (agreed, partial, conflicting) = (
        InstanceId::from_variable(Variable(0)),
        InstanceId::from_variable(Variable(1)),
        InstanceId::from_variable(Variable(2)),
    );
    let alternatives = scope.begin_alternatives();
    scope
        .arm(&alternatives, || {
            scope.record_child(agreed, "cell");
            scope.record_child(partial, "cell");
            scope.record_child(conflicting, "cellA");
            Ok(())
        })
        .unwrap();
    assert_eq!(scope.family(agreed), None, "an arm's changes are undone");
    scope
        .arm(&alternatives, || {
            scope.record_instance(agreed, "cell", true);
            scope.record_instance(conflicting, "cellB", true);
            Ok(())
        })
        .unwrap();
    scope.finish_alternatives(alternatives);
    assert_eq!(scope.instance_resource(agreed).as_deref(), Some("cell"));
    assert_eq!(scope.instance_resource(partial).as_deref(), Some("cell"));
    assert_eq!(scope.instance_resource(conflicting), None);
    let refusal = scope.refuse_ambiguous(conflicting, "x").unwrap_err();
    assert!(
        refusal.message().contains("`cellA` instance on one path"),
        "{refusal}"
    );
}

/// An inferred constructor leaves expansion fully applied, as a written one
/// is, so no later pass sees the short form; a constructor nothing fixes is
/// left as written for validation to refuse.
#[test]
fn inferred_constructor_type_arguments_are_written_into_the_declaration() {
    let file = crate::surface::parser::parse(
        "function singleton(x: int32) -> List<int32> { List::Cons(x, List::Nil) }",
    )
    .expect("the short constructors are inferred");
    let function = &file.click_function_definitions()[0];
    let ContractExpression::AlgebraicConstructor {
        algebraic_type,
        arguments,
        ..
    } = function.body().unwrap()
    else {
        panic!("the body is a constructor");
    };
    let int32_list = vec![ClickType::Program(InterfaceType::Int32)];
    assert_eq!(algebraic_type.arguments, int32_list);
    let ContractExpression::AlgebraicConstructor { algebraic_type, .. } = &arguments[1] else {
        panic!("the tail is a constructor");
    };
    assert_eq!(algebraic_type.arguments, int32_list);
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
    let pointer = ContractExpression::ProgramExpression(ProgramExpression::Variable(
        ("p".to_string()).into(),
    ));
    let accepted = expand_resource_type_arguments(
        "authority",
        vec![authority_test_protected(pointer.clone())],
        &authority_test_scope(ResourceKind::Composite, InterfaceType::Int32Pointer, false),
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
        crate::kernel::ResourceTerm::PopulationAuthority { .. }
    ));
    assert!(
        expand_resource_type_arguments(
            "authority",
            vec![authority_test_protected(pointer.clone())],
            &authority_test_scope(ResourceKind::Token, InterfaceType::Int32Pointer, false),
        )
        .is_ok(),
        "abstract token resource families are valid protected types"
    );
    for (scope, argument) in [
        (
            authority_test_scope(ResourceKind::Composite, InterfaceType::Int32, false),
            pointer.clone(),
        ),
        (
            authority_test_scope(ResourceKind::Composite, InterfaceType::Int32Pointer, false),
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
            &authority_test_scope(ResourceKind::Composite, InterfaceType::Int32Pointer, false)
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
            ensures wanted(result) by {{ step_until(function.exit); unfold(wanted(result)); close(); }}
        }}
        "#
    );
    let result = verify_c_sources(&click_source, &[("answer.c", &c_source)]);
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
#[cfg(not(feature = "fast-gate"))]
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
fn library_syntax_errors_name_the_module_file_and_line() {
    for source in ["\n\n/* an unclosed `quoted` comment", "\n\nfunction 42"] {
        let modules = [
            ("library/nat.click", CLICK_LIBRARY_MODULES[1].1),
            ("library/broken.click", source),
        ];
        let error = load_standard_library(&modules).expect_err("an invalid module must fail");
        assert_eq!(error.kind(), ClickErrorKind::Syntax);
        assert!(
            error.message().contains("library/broken.click:3"),
            "{}",
            error.message()
        );
        let error = error.with_context("while checking module `example.click`");
        assert!(
            error.message().contains("library/broken.click:3"),
            "module context must preserve the library location: {}",
            error.message()
        );
    }
}

#[test]
fn standard_library_cache_preserves_all_declarations() {
    let fresh = load_standard_library(CLICK_LIBRARY_MODULES).unwrap();
    assert_eq!(standard_library().unwrap(), &fresh);
    // Accessors return independently owned categories, never a mutable view
    // of the process-wide syntax or a clone of unrelated categories.
    let empty = parser::parse_file_items("").unwrap();
    let mut functions = combined_external_function_blocks(&empty).unwrap();
    assert!(!functions.is_empty());
    functions.clear();
    // An empty file sees only the implicit modules' declarations.
    let implicit = &file_library(&empty).unwrap().file;
    assert_eq!(
        combined_external_function_blocks(&empty).unwrap(),
        implicit.function_blocks()
    );
    assert_eq!(
        combined_algebraic_type_definitions(&empty).unwrap(),
        implicit.algebraic_type_definitions
    );
}

/// The standard library is proved by its own entry point, not by each
/// verification that uses it. This is the gate's proof of every library
/// theorem.
#[test]
fn standard_library_theorems_are_proved_by_their_own_entry_point() {
    let theorems = standard_library_theorem_definitions().unwrap();
    let verified = crate::surface::verify_standard_library()
        .unwrap_or_else(|error| panic!("standard library failed: {}", error.message()));
    // A kernel law over an index type is proved once per index type it
    // admits, so compare the proved clauses rather than counting results.
    let declared = theorems
        .iter()
        .flat_map(|theorem| (0..theorem.ensures().len()).map(|index| (theorem.name(), index)))
        .collect::<BTreeSet<_>>();
    let proved = verified
        .iter()
        .map(|result| (result.theorem_definition.name(), result.ensure_index))
        .collect::<BTreeSet<_>>();
    assert_eq!(proved, declared);
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
            r#"import click::integer;

            theorem uses_library(value: uint32, divisor: uint32) {
                requires divisor != 0u32;
                ensures value % divisor < divisor by {
                    apply(integer::uint32_remainder_less_than_divisor(value, divisor));
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
    let c_source = "int32 keep(int32 value, int32 bound) { return value; }";
    let click_source = r#"import click::integer;

        verifying "keep.c";
        int32 keep(int32 value, int32 bound) {
            requires defined(value % bound);
            requires to_integer(bound) != 0;
            ensures to_integer(value % bound) == truncating_remainder(to_integer(value), to_integer(bound));
        } by {
            have to_integer(value % bound) == truncating_remainder(to_integer(value), to_integer(bound)) by {
                apply(integer::int32_remainder_to_integer(value, bound));
            }
            step_until(function.exit);
            close();
        }
    "#;
    let proved = proved_theorems_during(|| {
        verify_c_sources(click_source, &[("keep.c", c_source)])
            .unwrap_or_else(|error| panic!("C proof failed: {}", error.message()));
    });
    assert_eq!(proved, ["click::integer::int32_remainder_to_integer"]);
}

#[test]
fn authority_field_schema_and_count_admission_are_independent_of_instance_fields() {
    let pointer = ContractExpression::ProgramExpression(ProgramExpression::Variable("p".into()));
    let mut scope =
        authority_test_scope(ResourceKind::Composite, InterfaceType::Int32Pointer, true);
    scope.definitions.get_mut("reference").unwrap().fields =
        std::sync::Arc::new(BTreeMap::from([(
            "serial".into(),
            (0, ClickType::Program(InterfaceType::Int32)),
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
    let pointer = ContractExpression::ProgramExpression(ProgramExpression::Variable("p".into()));
    let count = ContractExpression::ResourceCount(Box::new(authority_test_protected(pointer)));
    for has_fields in [false, true] {
        for authorized in [false, true] {
            let mut scope = authority_test_scope(
                ResourceKind::Composite,
                InterfaceType::Int32Pointer,
                has_fields,
            );
            scope.family_rules = true;
            let info = scope.definitions.get_mut("reference").unwrap();
            info.authorized = authorized;
            if has_fields {
                info.fields = std::sync::Arc::new(BTreeMap::from([(
                    "serial".into(),
                    (0, ClickType::Program(InterfaceType::Int32)),
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

/// A library proof sees only the theorems declared above it, so a missing
/// sibling of its own module is named as declared later, not as a missing
/// import, which would change nothing. Outside the module the hint still
/// suggests the import.
#[test]
fn a_later_sibling_of_a_library_proof_is_not_an_import_hint() {
    let sibling = "click::integer::int32_increment_lower_bound";
    crate::surface::enter_ambient_declaration("click::integer::int32_increment_upper_bound");
    let inside = library_import_hint(sibling);
    crate::surface::enter_ambient_declaration("user_theorem");
    let outside = library_import_hint(sibling);
    crate::surface::clear_ambient_proof_source();
    assert!(
        inside.contains("declared later in Click library module `click::integer`")
            && !inside.contains("import"),
        "{inside}"
    );
    assert!(
        outside.contains("add `import click::integer;`"),
        "{outside}"
    );
}
