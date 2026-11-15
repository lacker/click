use super::*;

fn maybe_type() -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::Program(ProgramType::Int32)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "None".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Some".to_string(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Maybe".to_string(),
        arguments: arguments.clone(),
    };
    AlgebraicType {
        rigid: false,
        name: "Maybe".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

#[test]
fn algebraic_integer_match_reconnects_symbolic_and_concrete_fields() {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![AlgebraicValueType::Integer],
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "Box".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Box".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let payload = IntegerTerm::constant_i64(7);
    let constructor = |field| SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Box".into(),
            fields: vec![SpecAlgebraicValue::Integer(SpecIntegerExpression::Term(
                field,
            ))],
        },
    };
    let arm = SpecAlgebraicResultMatchArm {
        variant: "Box".into(),
        bindings: vec!["n".into()],
        binding_types: vec![AlgebraicValueType::Integer],
        binding_variables: vec![Some(Variable(12345))],
        body: Box::new(constructor(IntegerTerm::var(Variable(12345)))),
    };
    for scrutinee in [
        SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(23456)),
        },
        constructor(payload.clone()),
    ] {
        let concrete = matches!(
            scrutinee.node,
            SpecAlgebraicExpressionNode::Constructor { .. }
        );
        let expression = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![arm.clone()],
            },
        };
        let paths = evaluate_spec_algebraic_at_state_in(
            &ExecutionState::default(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        if !concrete {
            assert!(
                matches!(&paths[0].value, AlgebraicResult::Shared(root) if matches!(root.node(), crate::kernel::KernelTermNode::Match(_)))
            );
        }
        let native = paths[0].value.clone().into_native_compat();
        let (body, expected) = if concrete {
            (&native, AlgebraicValue::Integer(payload.clone()))
        } else {
            let AlgebraicTermNode::Match { arms, .. } = &native.node else {
                panic!("symbolic match must remain a match");
            };
            (&arms[0].body, arms[0].bindings[0].clone())
        };
        let AlgebraicTermNode::Constructor { fields, .. } = &body.node else {
            panic!("arm must return its constructor");
        };
        assert_eq!(fields, &vec![expected]);
    }
    // Missing IDs, mismatched carriers, and duplicate field names cannot
    // authorize an ambiguous payload substitution.
    assert!(spec_algebraic_result_match_arms_are_well_formed(
        &ty,
        std::slice::from_ref(&arm)
    ));
    for metadata in [
        vec![],
        vec![None],
        vec![Some(Variable(1)), Some(Variable(1))],
    ] {
        let mut bad = arm.clone();
        bad.binding_variables = metadata;
        assert!(!spec_algebraic_result_match_arms_are_well_formed(
            &ty,
            &[bad]
        ));
    }
    let mut pair_ty = ty.clone();
    pair_ty.name = "Pair".into();
    pair_ty.variants = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![AlgebraicValueType::Integer; 2],
    }]
    .into();
    pair_ty.schemas = std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
        AlgebraicValueType::Algebraic {
            name: "Pair".into(),
            arguments: vec![],
        },
        pair_ty.variants.clone(),
    )])));
    let mut pair_arm = arm.clone();
    pair_arm.bindings = vec!["a".into(), "b".into()];
    pair_arm.binding_types = vec![AlgebraicValueType::Integer; 2];
    pair_arm.binding_variables = vec![Some(Variable(1)), Some(Variable(2))];
    assert!(spec_algebraic_result_match_arms_are_well_formed(
        &pair_ty,
        &[pair_arm.clone()]
    ));
    pair_arm.binding_variables = vec![Some(Variable(1)); 2];
    assert!(!spec_algebraic_result_match_arms_are_well_formed(
        &pair_ty,
        &[pair_arm.clone()]
    ));
    pair_arm.binding_variables = vec![Some(Variable(1)), Some(Variable(2))];
    pair_arm.bindings = vec!["a".into(), "a".into()];
    assert!(!spec_algebraic_result_match_arms_are_well_formed(
        &pair_ty,
        &[pair_arm]
    ));
    let mut bad = arm;
    bad.binding_types = vec![AlgebraicValueType::Program(ProgramType::Int32)];
    assert!(!spec_algebraic_result_match_arms_are_well_formed(
        &ty,
        &[bad]
    ));
}

fn value_or_match(scrutinee: SpecAlgebraicExpression) -> SpecExpression {
    SpecExpression::AlgebraicMatch {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            SpecAlgebraicMatchArm {
                variant: "None".to_string(),
                bindings: Vec::new(),
                binding_types: Vec::new(),
                body: SpecExpression::Value(int32(9)),
            },
            SpecAlgebraicMatchArm {
                variant: "Some".to_string(),
                bindings: vec!["value".to_string()],
                binding_types: vec![AlgebraicValueType::Program(ProgramType::Int32)],
                body: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                    "value".to_string(),
                )),
            },
        ],
    }
}

fn envelope_type(maybe_type: &AlgebraicType) -> AlgebraicType {
    let maybe_value_type = maybe_type.value_type();
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Missing".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Present".to_string(),
            fields: vec![maybe_value_type.clone()],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Envelope".to_string(),
        arguments: vec![AlgebraicValueType::Program(ProgramType::Int32)],
    };
    let mut schemas = maybe_type.schemas.definitions().clone();
    schemas.insert(value_type, variants.clone());
    AlgebraicType {
        rigid: false,
        name: "Envelope".to_string(),
        arguments: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        variants,
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(schemas)),
    }
}

fn recursive_list_type() -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::Program(ProgramType::Int32)];
    let value_type = AlgebraicValueType::Algebraic {
        name: "List".to_string(),
        arguments: arguments.clone(),
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Nil".to_string(),
            fields: Vec::new(),
        },
        AlgebraicVariantType {
            name: "Cons".to_string(),
            fields: vec![
                AlgebraicValueType::Program(ProgramType::Int32),
                value_type.clone(),
            ],
        },
    ]
    .into();
    AlgebraicType {
        rigid: false,
        name: "List".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn ungrounded_recursive_type() -> AlgebraicType {
    let value_type = AlgebraicValueType::Algebraic {
        name: "Loop".to_string(),
        arguments: Vec::new(),
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Again".to_string(),
        fields: vec![value_type.clone()],
    }]
    .into();
    AlgebraicType {
        rigid: false,
        name: "Loop".to_string(),
        arguments: Vec::new(),
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn wide_type(variant_count: usize) -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::Program(ProgramType::Int32)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = (0..variant_count)
        .map(|index| AlgebraicVariantType {
            name: format!("V{index}"),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        })
        .collect::<Vec<_>>()
        .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Wide".to_string(),
        arguments: arguments.clone(),
    };
    AlgebraicType {
        rigid: false,
        name: "Wide".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

#[test]
fn resource_initializer_capture_keeps_unknowns_and_calls_symbolic() {
    for variant_count in [1, 8, 128] {
        let ty = wide_type(variant_count);
        let variable = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(41)),
        };
        let captured = capture_spec_algebraic_value(
            &ExecutionState::new(),
            &variable,
            None,
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(captured.node, AlgebraicTermNode::Variable(Variable(41)));
        let call = SpecAlgebraicExpression {
            algebraic_type: ty,
            node: SpecAlgebraicExpressionNode::PureFunctionApplication {
                name: "identity".into(),
                arguments: vec![SpecPureFunctionArgument::Algebraic(variable)],
            },
        };
        let captured = capture_spec_algebraic_value(
            &ExecutionState::new(),
            &call,
            None,
            &PureFactContext::new(),
        )
        .unwrap();
        assert!(matches!(
            captured.node,
            AlgebraicTermNode::PureFunctionApplication { .. }
        ));
    }
}

#[test]
fn arbitrary_algebraic_value_is_one_variable_without_eager_cases() {
    for variant_count in [1, 8, 128] {
        let algebraic_type = wide_type(variant_count);
        let expression = SpecAlgebraicExpression {
            algebraic_type: algebraic_type.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(41)),
        };
        let mut execution_budget = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution_budget);
        let next_variable = budget.next_kernel_variable;
        let paths = evaluate_spec_algebraic_at_state_in(
            &ExecutionState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut budget,
        )
        .expect("a logical ADT variable lowers without case analysis");

        assert_eq!(paths.len(), 1);
        assert_eq!(budget.next_kernel_variable, next_variable);
        assert_eq!(
            paths[0].value.clone().into_native_compat(),
            AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Variable(Variable(41)),
            }
        );
    }
}

#[test]
fn cached_pointer_read_equations_do_not_escape_symbolic_match_arms() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer_type = AlgebraicValueType::Program(ProgramType::Int64Pointer);
    let value_type = AlgebraicValueType::Algebraic {
        name: "PointerBox".into(),
        arguments: vec![],
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![pointer_type],
    }]
    .into();
    let result_type = AlgebraicType {
        rigid: false,
        name: "PointerBox".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    };
    let address = Pointer::symbolic(Variable(71_040));
    let value = Pointer::symbolic(Variable(71_041));
    let memory = Memory::new().store(
        address.clone(),
        ProgramValue::typed_pointer(value, ProgramType::Int64Pointer),
    );
    let body = SpecAlgebraicExpression {
        algebraic_type: result_type.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Box".into(),
            fields: vec![SpecAlgebraicValue::Program(SpecExpression::MemoryLoad {
                memory: SpecMemory::Fixed(memory.clone()),
                pointer: Box::new(SpecExpression::Value(ProgramValue::typed_pointer(
                    address.clone(),
                    ProgramType::Int64PointerPointer,
                ))),
                value_type: ProgramType::Int64Pointer,
            })],
        },
    };
    let state = ExecutionState::new();
    let context = PureFactContext::new();
    let direct = evaluate_spec_algebraic_at_state_in(
        &state,
        &body,
        None,
        &context,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .unwrap();
    // The read itself carries its cached-cell equation. Composing it into the
    // constructor may discharge that equation as already decided, but never
    // turns it into another kind of fact.
    let read = crate::kernel::eval::evaluate_logical_memory_load_paths(
        &memory,
        address.clone(),
        ProgramType::Int64Pointer,
        Vec::new().into(),
        Vec::new(),
        &context,
    );
    let [read] = read.as_slice() else {
        panic!("one logical read");
    };
    assert_eq!(read.facts.len(), 1);
    assert!(read.facts[0].is_logical_read_equation());
    let [direct] = direct.as_slice() else {
        panic!("one constructor path");
    };
    assert!(
        direct
            .facts
            .iter()
            .all(|fact| fact.is_logical_read_equation())
    );
    assert!(capture_spec_algebraic_value(&state, &body, None, &context).is_ok());
    let expression = SpecAlgebraicExpression {
        algebraic_type: result_type,
        node: SpecAlgebraicExpressionNode::Match {
            scrutinee: Box::new(SpecAlgebraicExpression {
                algebraic_type: maybe_type(),
                node: SpecAlgebraicExpressionNode::Variable(Variable(71_042)),
            }),
            arms: vec![
                SpecAlgebraicResultMatchArm {
                    variant: "None".into(),
                    bindings: vec![],
                    binding_types: vec![],
                    binding_variables: vec![],
                    body: Box::new(body.clone()),
                },
                SpecAlgebraicResultMatchArm {
                    variant: "Some".into(),
                    bindings: vec!["unused".into()],
                    binding_types: vec![AlgebraicValueType::Program(ProgramType::Int32)],
                    binding_variables: vec![None],
                    body: Box::new(body),
                },
            ],
        },
    };
    let paths = evaluate_spec_algebraic_at_state_in(
        &state,
        &expression,
        None,
        &context,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    assert!(
        paths[0].facts.is_empty(),
        "arm-local equations must not become ambient facts"
    );
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn algebraic_type_schema_is_shared_by_variable_and_constructor_terms() {
    let algebraic_type = wide_type(128);
    let variable = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(7)),
    };
    let constructor = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "V0".to_string(),
            fields: vec![AlgebraicValue::Program(int32(9))],
        },
    };

    assert!(std::sync::Arc::ptr_eq(
        &variable.algebraic_type.variants,
        &constructor.algebraic_type.variants,
    ));
}

#[test]
fn grounded_recursive_schema_accepts_symbolic_recursive_fields() {
    let algebraic_type = recursive_list_type();
    let tail = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(8)),
    };
    let cons = AlgebraicTerm {
        algebraic_type,
        node: AlgebraicTermNode::Constructor {
            variant: "Cons".to_string(),
            fields: vec![
                AlgebraicValue::Program(int32(7)),
                AlgebraicValue::Algebraic(tail),
            ],
        },
    };

    assert!(cons.is_well_formed());
}

#[test]
fn ungrounded_recursive_schema_rejects_an_arbitrary_variable() {
    let term = AlgebraicTerm {
        algebraic_type: ungrounded_recursive_type(),
        node: AlgebraicTermNode::Variable(Variable(9)),
    };

    assert!(!term.is_well_formed());
}

#[test]
fn match_on_symbolic_algebraic_value_remains_one_expression_path() {
    let algebraic_type = maybe_type();
    let expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type: algebraic_type.clone(),
        node: SpecAlgebraicExpressionNode::Variable(Variable(41)),
    });
    let exports = KernelTermExport::machine_export_count();
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &ExecutionState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("a pure match is a symbolic expression, not a path split");

    assert_eq!(paths.len(), 1);
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert!(
        matches!(&paths[0].value, SpecValue::Shared(root) if matches!(root.node(), crate::kernel::KernelTermNode::Match(_)))
    );
    assert!(paths[0].facts.is_empty());
    assert!(paths[0].obligations.is_empty());
    let ProgramValue::Int32(MachineTerm::AlgebraicMatch { scrutinee, arms }) =
        &paths[0].value.clone().into_native()
    else {
        panic!("unknown match should lower to an algebraic-match term");
    };
    assert_eq!(
        scrutinee.as_ref(),
        &AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(41)),
        }
    );
    assert_eq!(arms.len(), 2);
    assert_eq!(arms[0].variant, "None");
    assert_eq!(arms[1].variant, "Some");
}

#[test]
fn nested_match_binder_remains_symbolic_inside_its_arm() {
    let maybe_type = maybe_type();
    let maybe_value_type = maybe_type.value_type();
    let envelope_type = envelope_type(&maybe_type);
    let expression = SpecExpression::AlgebraicMatch {
        scrutinee: Box::new(SpecAlgebraicExpression {
            algebraic_type: envelope_type.clone(),
            node: SpecAlgebraicExpressionNode::Variable(Variable(80)),
        }),
        arms: vec![
            SpecAlgebraicMatchArm {
                variant: "Missing".to_string(),
                bindings: Vec::new(),
                binding_types: Vec::new(),
                body: SpecExpression::Value(int32(9)),
            },
            SpecAlgebraicMatchArm {
                variant: "Present".to_string(),
                bindings: vec!["maybe".to_string()],
                binding_types: vec![maybe_value_type],
                body: value_or_match(SpecAlgebraicExpression {
                    algebraic_type: maybe_type,
                    node: SpecAlgebraicExpressionNode::Binding("maybe".to_string()),
                }),
            },
        ],
    };

    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &ExecutionState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("a nested algebraic binder should remain available to the arm body");

    assert_eq!(paths.len(), 1);
    let SpecValue::Shared(root) = &paths[0].value else {
        panic!("shared outer match");
    };
    let crate::kernel::KernelTermNode::Match(matched) = root.node() else {
        panic!("match root");
    };
    assert!(matches!(
        matched.arguments[2].node(),
        crate::kernel::KernelTermNode::Match(_)
    ));
    let ProgramValue::Int32(MachineTerm::AlgebraicMatch { arms, .. }) =
        &paths[0].value.clone().into_native()
    else {
        panic!("the outer match should remain symbolic");
    };
    let MachineTerm::AlgebraicMatch { .. } = &arms[1].body else {
        panic!("the nested binder should lower to the inner symbolic match");
    };
}

#[test]
fn algebraic_result_match_on_symbolic_value_remains_one_term() {
    let algebraic_type = maybe_type();
    let expression = SpecAlgebraicExpression {
        algebraic_type: algebraic_type.clone(),
        node: SpecAlgebraicExpressionNode::Match {
            scrutinee: Box::new(SpecAlgebraicExpression {
                algebraic_type: algebraic_type.clone(),
                node: SpecAlgebraicExpressionNode::Variable(Variable(52)),
            }),
            arms: vec![
                SpecAlgebraicResultMatchArm {
                    variant: "None".to_string(),
                    bindings: Vec::new(),
                    binding_types: Vec::new(),
                    binding_variables: vec![],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: algebraic_type.clone(),
                        node: SpecAlgebraicExpressionNode::Constructor {
                            variant: "None".to_string(),
                            fields: Vec::new(),
                        },
                    }),
                },
                SpecAlgebraicResultMatchArm {
                    variant: "Some".to_string(),
                    bindings: vec!["value".to_string()],
                    binding_types: vec![AlgebraicValueType::Program(ProgramType::Int32)],
                    binding_variables: vec![None],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: algebraic_type.clone(),
                        node: SpecAlgebraicExpressionNode::Constructor {
                            variant: "Some".to_string(),
                            fields: vec![SpecAlgebraicValue::Program(
                                SpecExpression::ProgramExpression(ProgramExpression::Variable(
                                    "value".to_string(),
                                )),
                            )],
                        },
                    }),
                },
            ],
        },
    };
    let paths = evaluate_spec_algebraic_at_state_in(
        &ExecutionState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("an algebraic-valued match should stay symbolic");

    assert_eq!(paths.len(), 1);
    assert!(matches!(
        &paths[0].value,
        AlgebraicResult::Shared(root) if matches!(root.node(), crate::kernel::KernelTermNode::Match(_))
    ));
    assert!(paths[0].value.clone().into_native_compat().is_well_formed());
}

#[test]
fn match_on_known_constructor_reduces_to_selected_arm() {
    let algebraic_type = maybe_type();
    let expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type: algebraic_type.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Some".to_string(),
            fields: vec![SpecAlgebraicValue::Program(SpecExpression::Value(int32(7)))],
        },
    });
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &ExecutionState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("a match on a checked constructor should reduce");

    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].value.clone().into_native(), int32(7));
}

#[test]
fn pure_pointer_result_preserves_type_and_unsupported_results_are_explicit() {
    for result_type in [
        ProgramType::Int32Pointer,
        ProgramType::VoidPointer,
        ProgramType::Void,
    ] {
        let expression = SpecExpression::PureFunctionApplication {
            name: "select".into(),
            arguments: vec![],
            result_type,
            pointer_result: None,
            result_object_class: Some(crate::kernel::effective_type::CAccessClass::Struct(
                crate::kernel::effective_type::CStructClass::opaque("node"),
            )),
            projection: None,
        };
        let result = evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        );
        if result_type == ProgramType::Void {
            assert!(matches!(
                result,
                Err(ExecutionLimit::UnsupportedPureFunctionResult(
                    ProgramType::Void
                ))
            ));
        } else {
            let paths = result.expect("a pointer-valued pure call has one opaque result");
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].value.program_type(), result_type);
            // The declared return type's class reaches the pointer result.
            let crate::kernel::ProgramValue::Pointer(pointer) =
                &paths[0].value.clone().into_native()
            else {
                panic!("a pointer result");
            };
            assert_eq!(
                pointer.object_class().map(|class| class.spelling()),
                Some("struct node".to_string())
            );
            let ProgramValue::Pointer(pointer) = &paths[0].value.clone().into_native() else {
                panic!("lost pointer sort")
            };
            assert!(matches!(
                pointer.block,
                PointerBlock::PureFunctionApplication(_)
            ));
            assert!(paths[0].facts.is_empty());
            assert!(paths[0].obligations.is_empty());
        }
    }
}

#[test]
fn pure_function_application_is_not_eagerly_evaluated() {
    let expression = SpecExpression::PureFunctionApplication {
        name: "increment".to_string(),
        arguments: vec![SpecPureFunctionArgument::Value(SpecExpression::Value(
            int32(41),
        ))],
        result_type: ProgramType::Int32,
        pointer_result: None,
        result_object_class: None,
        projection: None,
    };
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &ExecutionState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("pure calls should lower to logical applications");

    assert_eq!(paths.len(), 1);
    assert_eq!(
        KernelTermExport::default()
            .argument(match &paths[0].value {
                SpecValue::Shared(root) => root,
                _ => panic!("common integer call result"),
            })
            .unwrap(),
        PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::ClickFunctionApplication {
            name: "increment".to_string(),
            arguments: vec![PureFunctionArgument::Value(int32(41))],
        }))
    );
}

#[test]
fn pure_function_application_retains_symbolic_algebraic_argument() {
    let algebraic_type = maybe_type();
    let expression = SpecExpression::PureFunctionApplication {
        name: "tag".to_string(),
        arguments: vec![SpecPureFunctionArgument::Algebraic(
            SpecAlgebraicExpression {
                algebraic_type: algebraic_type.clone(),
                node: SpecAlgebraicExpressionNode::Variable(Variable(61)),
            },
        )],
        result_type: ProgramType::Int32,
        pointer_result: None,
        result_object_class: None,
        projection: None,
    };
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &ExecutionState::new(),
        &expression,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .expect("an ADT argument should remain one typed term");

    assert_eq!(paths.len(), 1);
    let ProgramValue::Int32(MachineTerm::ClickFunctionApplication { arguments, .. }) =
        &paths[0].value.clone().into_native()
    else {
        panic!("pure call should remain an application");
    };
    assert_eq!(
        arguments,
        &[PureFunctionArgument::Algebraic(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(61)),
        })]
    );
}

#[test]
fn malformed_symbolic_match_is_rejected_before_term_construction() {
    let algebraic_type = maybe_type();
    let mut expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type,
        node: SpecAlgebraicExpressionNode::Variable(Variable(70)),
    });
    let SpecExpression::AlgebraicMatch { arms, .. } = &mut expression else {
        unreachable!()
    };
    arms.pop();

    assert!(
        evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .is_err()
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/algebraic_term_tests.rs");
}

#[test]
fn nominal_pointer_constructor_matches_preserve_the_checked_payload() {
    use crate::kernel::effective_type::{CAccessClass, CStructClass};
    use std::sync::Arc;
    let class = CAccessClass::Struct(CStructClass::opaque("node"));
    let field_type = AlgebraicValueType::ObjectPointer(ProgramType::Int32Pointer, class.clone());
    let arguments = vec![field_type.clone()];
    let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "At".to_string(),
        fields: arguments.clone(),
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "Ref".to_string(),
        arguments: arguments.clone(),
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Ref".to_string(),
                arguments,
            },
            variants,
        )]))),
    };
    for actual_class in [
        Some(class.clone()),
        Some(CAccessClass::Struct(CStructClass::opaque("other"))),
        None,
    ] {
        let valid = actual_class.as_ref() == Some(&class);
        let payload =
            ProgramValue::typed_pointer(Pointer::symbolic(Variable(44)), ProgramType::Int32Pointer)
                .with_pointer_object_class(actual_class);
        let constructor = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Constructor {
                variant: "At".to_string(),
                fields: vec![SpecAlgebraicValue::Program(SpecExpression::Value(
                    payload.clone(),
                ))],
            },
        };
        let scalar_match = SpecExpression::AlgebraicMatch {
            scrutinee: Box::new(constructor.clone()),
            arms: vec![SpecAlgebraicMatchArm {
                variant: "At".to_string(),
                bindings: vec!["p".to_string()],
                binding_types: vec![field_type.clone()],
                body: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                    "p".to_string(),
                )),
            }],
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::new(),
            &scalar_match,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .expect("typed pointer match");
        assert_eq!(paths.len(), usize::from(valid));
        if valid {
            assert!(paths[0].value.shared().is_some());
            assert_eq!(paths[0].value.clone().into_native(), payload);
            let ProgramValue::Pointer(expected) = &payload else {
                unreachable!()
            };
            assert_eq!(
                paths[0].value.pointer().unwrap().object_origin_evidence(),
                expected.object_origin_evidence()
            );
        }
        let model_match = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Match {
                scrutinee: Box::new(constructor),
                arms: vec![SpecAlgebraicResultMatchArm {
                    variant: "At".to_string(),
                    bindings: vec!["p".to_string()],
                    binding_types: vec![field_type.clone()],
                    binding_variables: vec![None],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: ty.clone(),
                        node: SpecAlgebraicExpressionNode::Constructor {
                            variant: "At".to_string(),
                            fields: vec![SpecAlgebraicValue::Program(
                                SpecExpression::ProgramExpression(ProgramExpression::Variable(
                                    "p".to_string(),
                                )),
                            )],
                        },
                    }),
                }],
            },
        };
        let paths = evaluate_spec_algebraic_at_state_in(
            &ExecutionState::new(),
            &model_match,
            None,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .expect("typed model match");
        assert_eq!(paths.len(), usize::from(valid));
        if valid {
            assert!(paths[0].value.clone().into_native_compat().is_well_formed());
        }
    }
}

#[test]
fn model_argument_guard_query_does_not_materialize_stored_models() {
    let ty = maybe_type();
    let stored = SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::ResourceField(ResourceFieldProjection {
            identity: Variable(90_000),
            children: vec![],
            field_index: 0,
            at_entry: false,
        }),
    };
    let envelope = SpecAlgebraicExpression {
        algebraic_type: envelope_type(&ty),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Present".into(),
            fields: vec![SpecAlgebraicValue::Algebraic(stored.clone())],
        },
    };
    let state = ExecutionState::new();
    let assumptions = PureFactContext::new();
    for expression in [&stored, &envelope] {
        assert!(
            algebraic_argument_evaluation_guards(&state, expression, None, &assumptions)
                .unwrap()
                .is_empty()
        );
        // The query grants no value or ownership: capture still refuses the
        // missing instance. Guard selection must not read or clone its payload.
        assert!(capture_spec_algebraic_value(&state, expression, None, &assumptions).is_err());
    }
    let guarded = SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Some".into(),
            fields: vec![SpecAlgebraicValue::Program(SpecExpression::Subtract(
                Box::new(SpecExpression::Value(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(90_001)),
                ))),
                Box::new(SpecExpression::Value(int32(1))),
            ))],
        },
    };
    let expected =
        algebraic_argument_evaluation_guards(&state, &guarded, None, &assumptions).unwrap();
    assert!(!expected.is_empty());
    let application = SpecAlgebraicExpression {
        algebraic_type: ty,
        node: SpecAlgebraicExpressionNode::PureFunctionApplication {
            name: "choose_model".into(),
            arguments: vec![
                SpecPureFunctionArgument::Algebraic(stored),
                SpecPureFunctionArgument::Algebraic(guarded),
            ],
        },
    };
    assert_eq!(
        algebraic_argument_evaluation_guards(&state, &application, None, &assumptions).unwrap(),
        expected
    );
}

fn signed_value_or_match(variable: Variable) -> SpecExpression {
    let mut expression = value_or_match(SpecAlgebraicExpression {
        algebraic_type: maybe_type(),
        node: SpecAlgebraicExpressionNode::Variable(variable),
    });
    let SpecExpression::AlgebraicMatch { arms, .. } = &mut expression else {
        unreachable!()
    };
    arms[1].body = SpecExpression::Subtract(
        Box::new(SpecExpression::Value(int32(0))),
        Box::new(arms[1].body.clone()),
    );
    expression
}

fn maybe_variable(variable: Variable) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: maybe_type(),
        node: AlgebraicTermNode::Variable(variable),
    }
}

fn maybe_constructor(payload: Option<ProgramValue>) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: maybe_type(),
        node: AlgebraicTermNode::Constructor {
            variant: if payload.is_some() { "Some" } else { "None" }.into(),
            fields: payload.into_iter().map(AlgebraicValue::Program).collect(),
        },
    }
}

#[test]
fn signed_match_is_fact_stable_and_retains_guarded_definedness() {
    let variable = Variable(41);
    let lower = |assumptions: &PureFactContext| {
        let mut paths = evaluate_spec_expression_paths_with_loop_entry_in(
            &ExecutionState::new(),
            &signed_value_or_match(variable),
            None,
            assumptions,
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .expect("signed arithmetic remains one symbolic match");
        assert_eq!(paths.len(), 1);
        paths.pop().unwrap()
    };
    let original = lower(&PureFactContext::new());
    assert!(!original.obligations.is_empty());
    for payload in [None, Some(int32(7)), Some(int32(i32::MIN as u32))] {
        let context = PureFactContext::new().assume_proposition(Proposition::Equal(
            Term::Algebraic(maybe_variable(variable)),
            Term::Algebraic(maybe_constructor(payload)),
        ));
        let path = lower(&context);
        assert_eq!(
            path.value, original.value,
            "constructor facts must not change the lowered term"
        );
        assert_eq!(
            path.obligations, original.obligations,
            "even a known payload must retain its guarded overflow obligation"
        );
    }
    for obligation in &original.obligations {
        let Proposition::ForAll { body, .. } = obligation.proposition() else {
            panic!("arm payload must be bound")
        };
        let Proposition::Implies(guard, _) = body.as_ref() else {
            panic!("arm obligation must be conditional")
        };
        assert!(
            matches!(guard.as_ref(), Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) if left == &maybe_variable(variable) && matches!(&right.node, AlgebraicTermNode::Constructor { variant, .. } if variant == "Some"))
        );
    }
}

#[test]
fn common_constructor_projection_preserves_fields_and_refusals() {
    let pointer = PointerValue::new(
        Pointer::symbolic(Variable(999650)),
        ProgramType::Int32Pointer,
    )
    .with_pointee_constant(true);
    let mut native = KernelMatch::test_scrutinee(vec![
        AlgebraicValueType::Program(ProgramType::Int32),
        AlgebraicValueType::Program(ProgramType::Int32Pointer),
    ]);
    native.node = AlgebraicTermNode::Constructor {
        variant: "Arm".into(),
        fields: vec![
            AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::add(
                MachineTerm::Variable(Variable(999651)),
                MachineTerm::constant(1),
            ))),
            AlgebraicValue::Program(ProgramValue::Pointer(pointer.clone())),
        ],
    };
    let root = KernelTermImport::default().algebraic(&native);
    let shared = [SpecCallArgument::Shared(root.clone())];
    let native = [SpecCallArgument::Native(PureFunctionArgument::Algebraic(
        native,
    ))];
    let exports = KernelTermExport::algebraic_export_count();
    for (field, ty) in [(0, ProgramType::Int32), (1, ProgramType::Int32Pointer)] {
        let projection = PureProjection {
            argument: 0,
            variant: "Arm".into(),
            field,
        };
        let result = projected_field(&projection, &shared, ty, true).unwrap();
        let expected = projected_field(&projection, &native, ty, true).unwrap();
        assert_eq!(
            format!("{:?}", result.into_native()),
            format!("{:?}", expected.into_native())
        );
        assert_eq!(
            projected_field(&projection, &shared, ty, false)
                .unwrap()
                .into_native(),
            projected_field(&projection, &native, ty, false)
                .unwrap()
                .into_native()
        );
    }
    for (argument, variant, field, ty) in [
        (1, "Arm", 0, ProgramType::Int32),
        (0, "Other", 0, ProgramType::Int32),
        (0, "Arm", 2, ProgramType::Int32),
        (0, "Arm", 0, ProgramType::UInt32),
    ] {
        let projection = PureProjection {
            argument,
            variant: variant.into(),
            field,
        };
        assert!(projected_field(&projection, &shared, ty, true).is_none());
        assert!(projected_field(&projection, &native, ty, true).is_none());
    }
    assert_eq!(KernelTermExport::algebraic_export_count(), exports);
}

#[test]
fn algebraic_read_result_preserves_native_state_and_type() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = TypeParameterName::intern("SpecReadT").algebraic_type();
    let native = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::MemoryLoad {
            memory: intern_memory(Memory::new()),
            pointer: Box::new(Pointer::symbolic(Variable(999749))),
        },
    };
    let expression = SpecAlgebraicExpression {
        algebraic_type: ty,
        node: SpecAlgebraicExpressionNode::ProgramValue(Box::new(SpecExpression::Value(
            ProgramValue::Parameter(Box::new(native.clone())),
        ))),
    };
    for disabled in [false, true] {
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        budget.machine_result_production_disabled = disabled;
        let paths = evaluate_spec_algebraic_at_state_in(
            &ExecutionState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut budget,
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(
            matches!(&paths[0].value, AlgebraicResult::Shared(root) if matches!(root.node(), KernelTermNode::AlgebraicRead(_))),
            !disabled
        );
        assert_eq!(paths[0].value.clone().into_native_compat(), native);
        assert!(paths[0].obligations.is_empty());
        assert!(!paths[0].facts.has_path_conditions());
    }
}

#[test]
fn algebraic_handoffs_keep_constructor_fields_and_binding_roots() {
    let _session = crate::kernel::VerificationSession::enter();
    let inner = maybe_type();
    let outer = envelope_type(&inner);
    let root = KernelTerm::variable(KernelType::Algebraic(inner.clone()), Variable(999760));
    let mut values = crate::persistent::PersistentMap::default();
    values.insert("seed".into(), root.clone());
    let constructed = SpecAlgebraicExpression {
        algebraic_type: outer.clone(),
        node: SpecAlgebraicExpressionNode::Constructor {
            variant: "Present".into(),
            fields: vec![SpecAlgebraicValue::Algebraic(SpecAlgebraicExpression {
                algebraic_type: inner.clone(),
                node: SpecAlgebraicExpressionNode::Binding("seed".into()),
            })],
        },
    };
    let expression = SpecAlgebraicExpression {
        algebraic_type: inner.clone(),
        node: SpecAlgebraicExpressionNode::Match {
            scrutinee: Box::new(constructed.clone()),
            arms: vec![
                SpecAlgebraicResultMatchArm {
                    variant: "Missing".into(),
                    bindings: vec![],
                    binding_types: vec![],
                    binding_variables: vec![],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: inner.clone(),
                        node: SpecAlgebraicExpressionNode::Variable(Variable(999761)),
                    }),
                },
                SpecAlgebraicResultMatchArm {
                    variant: "Present".into(),
                    bindings: vec!["selected".into()],
                    binding_types: vec![inner.value_type()],
                    binding_variables: vec![None],
                    body: Box::new(SpecAlgebraicExpression {
                        algebraic_type: inner.clone(),
                        node: SpecAlgebraicExpressionNode::Binding("selected".into()),
                    }),
                },
            ],
        },
    };
    let state = ExecutionState::new();
    let scope = SpecScope {
        values: Some(&values),
        ..SpecScope::unbound(&state, None)
    };
    let exports = KernelTermExport::algebraic_export_count();
    let mut budget = ExecutionBudget::new();
    let paths = evaluate_spec_algebraic_at_state_with_bindings_in(
        scope,
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut budget),
    )
    .unwrap();
    assert_eq!(paths[0].value, AlgebraicResult::Shared(root.clone()));
    assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    assert!(paths[0].facts.is_empty());
    assert!(paths[0].obligations.is_empty());
    let mut budget = ExecutionBudget::new();
    let mut native_budget = SpecEvaluation::logical(&mut budget);
    native_budget.machine_result_production_disabled = true;
    let native = evaluate_spec_algebraic_at_state_with_bindings_in(
        scope,
        &expression,
        &PureFactContext::new(),
        &mut native_budget,
    )
    .unwrap();
    assert_eq!(
        paths[0].value.clone().into_native_compat(),
        native[0].value.clone().into_native_compat()
    );
}

#[test]
fn algebraic_runtime_enum_handoffs_preserve_selected_roots_and_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    let inner = maybe_type();
    let outer = envelope_type(&inner);
    let root = KernelTerm::variable(KernelType::Algebraic(inner.clone()), Variable(999762));
    let mut state = ExecutionState::new();
    state.locals.set_retained_typed_with_all_qualifiers(
        "seed",
        SpecValue::Shared(root.clone()),
        ProgramType::Parameter(TypeParameterName::of(&inner)),
        false,
        false,
        false,
        false,
    );
    let expression = ProgramExpression::EnumConstruct {
        enum_type: TypeParameterName::of(&outer),
        variant: "Present".into(),
        fields: vec![ProgramExpression::Variable("seed".into())],
    };
    let exports = KernelTermExport::algebraic_export_count();
    let paths = crate::kernel::eval::evaluate_expression_value_paths(
        &state,
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("constructor");
    };
    let KernelTermNode::Constructor(constructor) = value.shared().unwrap().node() else {
        panic!("common constructor");
    };
    assert_eq!(constructor.fields, vec![root.clone()]);
    for (variant, index, succeeds) in [
        ("Present", 0, true),
        ("Present", 1, false),
        ("Missing", 0, false),
    ] {
        let projection = ProgramExpression::EnumField {
            value: Box::new(expression.clone()),
            variant: variant.into(),
            index,
        };
        let paths = crate::kernel::eval::evaluate_expression_value_paths(
            &state,
            &projection,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        if succeeds {
            assert!(
                matches!(&paths[0].outcome, ExpressionOutcome::Value(value) if value.shared() == Some(&root))
            );
        } else {
            assert!(matches!(
                paths[0].outcome,
                ExpressionOutcome::RuntimeError(_)
            ));
        }
    }
    assert_eq!(KernelTermExport::algebraic_export_count(), exports);
}

#[test]
fn algebraic_program_conditionals_preserve_existing_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = maybe_type();
    let left = SpecValue::Shared(KernelTerm::variable(
        KernelType::Algebraic(ty.clone()),
        Variable(999766),
    ));
    let right = SpecValue::Shared(KernelTerm::variable(
        KernelType::Algebraic(ty),
        Variable(999767),
    ));
    let guard = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    // Program-carried algebraic values only join when equal. The separate
    // logical algebraic evaluator owns algebraic If construction.
    for retain in [true, false] {
        assert!(
            SpecValue::conditional(&guard, &left, &right, retain)
                .unwrap()
                .is_none()
        );
    }
    let native = SpecValue::Native(left.clone().into_native());
    assert_eq!(
        SpecValue::conditional(&guard, &left, &native, true)
            .unwrap()
            .unwrap()
            .shared(),
        left.shared()
    );
}

#[test]
fn algebraic_program_call_results_retain_shared_arguments() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = maybe_type();
    let root = KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(999768));
    let mut values = crate::persistent::PersistentMap::default();
    values.insert("seed".into(), root.clone());
    let expression = SpecExpression::PureFunctionApplication {
        name: "algebraic_program_result".into(),
        arguments: vec![SpecPureFunctionArgument::Algebraic(
            SpecAlgebraicExpression {
                algebraic_type: ty.clone(),
                node: SpecAlgebraicExpressionNode::Binding("seed".into()),
            },
        )],
        result_type: ProgramType::Parameter(TypeParameterName::of(&ty)),
        pointer_result: None,
        result_object_class: None,
        projection: None,
    };
    let state = ExecutionState::new();
    let scope = SpecScope {
        values: Some(&values),
        ..SpecScope::unbound(&state, None)
    };
    let exports = KernelTermExport::algebraic_export_count();
    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .unwrap();
    let KernelTermNode::AlgebraicCall(call) = paths[0].value.shared().unwrap().node() else {
        panic!("common call result");
    };
    assert_eq!(call.arguments, vec![root]);
    assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    let mut execution = ExecutionBudget::new();
    let mut budget = SpecEvaluation::logical(&mut execution);
    budget.machine_result_production_disabled = true;
    let native = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        &expression,
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap();
    assert_eq!(
        paths[0].value.clone().into_native(),
        native[0].value.clone().into_native()
    );
}
