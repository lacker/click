//! Constructor exhaustion binds fields existentially in their own disjunct.
//! It does not select a case, introduce free witnesses, or grant ownership.

use super::*;

/// Checked constructor exhaustion for a well-formed symbolic algebraic value.
/// For `m: Maybe<int>`, this yields `m = None || exists x: int. m = Some(x)`.
/// Rigid type parameters cannot be inspected as enum declarations.
/// Payloads currently support signed 32/64-bit integers, pointers, and ADTs.
pub fn algebraic_constructor_cases(value: &AlgebraicTerm) -> Option<Theorem> {
    if value.algebraic_type.rigid || !value.is_well_formed() {
        return None;
    }
    let equality = |constructor| {
        Proposition::Equal(Term::Algebraic(value.clone()), Term::Algebraic(constructor))
    };
    let mut variables =
        KernelVariableGenerator::fresh_for(0, proposition_variables(&equality(value.clone())));
    let mut alternatives = Vec::with_capacity(value.algebraic_type.variants.len());
    let mut seen = BTreeSet::new();
    for variant in value.algebraic_type.variants.iter() {
        if !seen.insert(&variant.name) {
            return None;
        }
        let mut fields = Vec::with_capacity(variant.fields.len());
        let mut binders = Vec::with_capacity(variant.fields.len());
        for field_type in &variant.fields {
            let variable = variables.next();
            let (sort, field) = match field_type {
                AlgebraicValueType::C(c_type) => {
                    let sort = match c_type {
                        CType::Int32 => Sort::CInt32,
                        CType::Int64 => Sort::CInt64,
                        ty if ty.is_pointer() => Sort::CPointer(*ty),
                        _ => return None,
                    };
                    (
                        sort,
                        AlgebraicValue::C(symbolic_call_result(*c_type, variable)),
                    )
                }
                AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_) => {
                    let algebraic_type = value.algebraic_type.resolve_nested_type(field_type)?;
                    if !algebraic_type.has_consistent_root_schema() {
                        return None;
                    }
                    let sort = Sort::Algebraic(algebraic_type.clone());
                    (
                        sort,
                        AlgebraicValue::Algebraic(AlgebraicTerm {
                            algebraic_type,
                            node: AlgebraicTermNode::Variable(variable),
                        }),
                    )
                }
            };
            fields.push(field);
            binders.push((variable, sort));
        }
        let constructor = AlgebraicTerm {
            algebraic_type: value.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: variant.name.clone(),
                fields,
            },
        };
        // The fields were constructed directly from this exact variant's
        // schema. Do not search the whole constructor family again per arm.
        let mut alternative = equality(constructor);
        for (variable, sort) in binders.into_iter().rev() {
            alternative = Proposition::Exists {
                name: format!("case_field_{}", variable.0),
                var: variable,
                sort,
                body: Box::new(alternative),
            };
        }
        alternatives.push(alternative);
    }
    // Refuse an empty family rather than manufacturing a theorem of false.
    let mut alternatives = alternatives.into_iter().rev();
    let last = alternatives.next()?;
    Some(Theorem::new(alternatives.fold(last, |right, left| {
        Proposition::Or(Box::new(left), Box::new(right))
    })))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn datatype(name: &str, variants: Vec<AlgebraicVariantType>) -> AlgebraicType {
        let key = AlgebraicValueType::Algebraic {
            name: name.into(),
            arguments: vec![],
        };
        let variants: Arc<[AlgebraicVariantType]> = variants.into();
        AlgebraicType {
            rigid: false,
            name: name.into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
        }
    }

    fn tree_type() -> AlgebraicType {
        let recursive = AlgebraicValueType::Algebraic {
            name: "Tree".into(),
            arguments: vec![],
        };
        datatype(
            "Tree",
            vec![
                AlgebraicVariantType {
                    name: "Empty".into(),
                    fields: vec![],
                },
                AlgebraicVariantType {
                    name: "Node".into(),
                    fields: vec![
                        AlgebraicValueType::C(CType::Int32Pointer),
                        AlgebraicValueType::C(CType::Int32),
                        AlgebraicValueType::Parameter("T".into()),
                        recursive.clone(),
                        recursive,
                    ],
                },
            ],
        )
    }

    fn arbitrary(algebraic_type: AlgebraicType) -> AlgebraicTerm {
        AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(0)),
        }
    }

    #[test]
    fn constructor_cases_bind_typed_recursive_fields_without_capturing_scrutinee() {
        let value = arbitrary(tree_type());
        let theorem = algebraic_constructor_cases(&value).unwrap();
        let Proposition::Or(empty, node) = theorem.proposition() else {
            panic!("two constructors")
        };
        assert!(
            matches!(empty.as_ref(), Proposition::Equal(_, Term::Algebraic(AlgebraicTerm { node: AlgebraicTermNode::Constructor { variant, fields }, .. })) if variant == "Empty" && fields.is_empty())
        );
        let mut body = node.as_ref();
        let mut binders = BTreeSet::new();
        let mut ordered_binders = Vec::new();
        let expected_sorts = [
            Sort::CPointer(CType::Int32Pointer),
            Sort::CInt32,
            Sort::Algebraic(AlgebraicType::parameter("T".into())),
            Sort::Algebraic(value.algebraic_type.clone()),
            Sort::Algebraic(value.algebraic_type.clone()),
        ];
        for expected in expected_sorts {
            let Proposition::Exists {
                var,
                sort,
                body: inner,
                ..
            } = body
            else {
                panic!("field witness")
            };
            assert_eq!(sort, &expected);
            assert_ne!(*var, Variable(0));
            assert!(binders.insert(*var));
            ordered_binders.push(*var);
            body = inner.as_ref();
        }
        let Proposition::Equal(Term::Algebraic(scrutinee), Term::Algebraic(constructor)) = body
        else {
            panic!("constructor equation")
        };
        assert_eq!(scrutinee, &value);
        assert!(constructor.checked_constructor_fields().is_some());
        assert_eq!(
            constructor.checked_constructor_fields().unwrap(),
            &[
                AlgebraicValue::C(symbolic_call_result(
                    CType::Int32Pointer,
                    ordered_binders[0]
                )),
                AlgebraicValue::C(symbolic_call_result(CType::Int32, ordered_binders[1])),
                AlgebraicValue::Algebraic(AlgebraicTerm {
                    algebraic_type: AlgebraicType::parameter("T".into()),
                    node: AlgebraicTermNode::Variable(ordered_binders[2])
                }),
                AlgebraicValue::Algebraic(AlgebraicTerm {
                    algebraic_type: value.algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(ordered_binders[3])
                }),
                AlgebraicValue::Algebraic(AlgebraicTerm {
                    algebraic_type: value.algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(ordered_binders[4])
                }),
            ]
        );
        assert_eq!(
            proposition_variables(body),
            binders
                .union(&BTreeSet::from([Variable(0)]))
                .copied()
                .collect()
        );
    }

    #[test]
    fn constructor_cases_reserve_variables_inside_symbolic_matches_and_calls() {
        let ty = datatype(
            "Maybe",
            vec![
                AlgebraicVariantType {
                    name: "None".into(),
                    fields: vec![],
                },
                AlgebraicVariantType {
                    name: "Some".into(),
                    fields: vec![AlgebraicValueType::C(CType::Int32)],
                },
            ],
        );
        let variable = |id| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(id)),
        };
        let value = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(variable(0)),
                arms: vec![
                    AlgebraicResultMatchArm {
                        variant: "None".into(),
                        bindings: vec![],
                        body: variable(1),
                    },
                    AlgebraicResultMatchArm {
                        variant: "Some".into(),
                        bindings: vec![AlgebraicValue::C(symbolic_call_result(
                            CType::Int32,
                            Variable(2),
                        ))],
                        body: AlgebraicTerm {
                            algebraic_type: ty.clone(),
                            node: AlgebraicTermNode::PureFunctionApplication {
                                name: "opaque".into(),
                                arguments: vec![
                                    PureFunctionArgument::Algebraic(variable(3)),
                                    PureFunctionArgument::Value(symbolic_call_result(
                                        CType::Int32Pointer,
                                        Variable(4),
                                    )),
                                    PureFunctionArgument::Value(symbolic_call_result(
                                        CType::Int32,
                                        Variable(5),
                                    )),
                                ],
                            },
                        },
                    },
                ],
            },
        };
        let equality = Proposition::Equal(
            Term::Algebraic(value.clone()),
            Term::Algebraic(value.clone()),
        );
        assert_eq!(
            proposition_variables(&equality),
            (0..6).map(Variable).collect()
        );
        let theorem = algebraic_constructor_cases(&value).unwrap();
        let Proposition::Or(_, some) = theorem.proposition() else {
            panic!("two cases")
        };
        let Proposition::Exists { var, body, .. } = some.as_ref() else {
            panic!("bound payload")
        };
        assert_eq!(*var, Variable(6));
        let Proposition::Equal(Term::Algebraic(original), _) = body.as_ref() else {
            panic!("equation")
        };
        // Exhaustion preserves the expression, including its unknown match.
        assert_eq!(original, &value);
        let mut incomplete_match = value.clone();
        let AlgebraicTermNode::Match { arms, .. } = &mut incomplete_match.node else {
            unreachable!()
        };
        arms.pop();
        assert!(algebraic_constructor_cases(&incomplete_match).is_none());
    }

    #[test]
    fn constructor_cases_reject_rigid_types_and_malformed_terms() {
        assert!(
            algebraic_constructor_cases(&arbitrary(AlgebraicType::parameter("T".into()))).is_none()
        );
        let malformed = AlgebraicTerm {
            algebraic_type: tree_type(),
            node: AlgebraicTermNode::Constructor {
                variant: "Node".into(),
                fields: vec![],
            },
        };
        assert!(algebraic_constructor_cases(&malformed).is_none());
        let mut inconsistent = tree_type();
        inconsistent.variants = vec![AlgebraicVariantType {
            name: "Forged".into(),
            fields: vec![],
        }]
        .into();
        assert!(algebraic_constructor_cases(&arbitrary(inconsistent)).is_none());
        // Keeping a legitimate constructor but dropping another reachable
        // constructor must not manufacture an exhaustive singleton theorem.
        let mut truncated = tree_type();
        truncated.variants = vec![truncated.variants[0].clone()].into();
        assert!(algebraic_constructor_cases(&arbitrary(truncated)).is_none());
    }

    #[test]
    fn constructor_cases_reject_empty_duplicate_and_unsupported_schemas() {
        let variant = AlgebraicVariantType {
            name: "Unit".into(),
            fields: vec![],
        };
        for ty in [
            datatype("Empty", vec![]),
            datatype("Duplicate", vec![variant.clone(), variant]),
            datatype(
                "Unsupported",
                vec![AlgebraicVariantType {
                    name: "Value".into(),
                    fields: vec![AlgebraicValueType::C(CType::Void)],
                }],
            ),
        ] {
            assert!(algebraic_constructor_cases(&arbitrary(ty)).is_none());
        }
    }

    #[test]
    fn constructor_cases_reject_unresolved_and_ungrounded_recursive_fields() {
        let reference = |name: &str| AlgebraicValueType::Algebraic {
            name: name.into(),
            arguments: vec![],
        };
        let missing = datatype(
            "Bad",
            vec![
                AlgebraicVariantType {
                    name: "Empty".into(),
                    fields: vec![],
                },
                AlgebraicVariantType {
                    name: "Node".into(),
                    fields: vec![reference("Missing")],
                },
            ],
        );
        assert!(algebraic_constructor_cases(&arbitrary(missing)).is_none());
        let infinite = datatype(
            "Infinite",
            vec![AlgebraicVariantType {
                name: "Again".into(),
                fields: vec![reference("Infinite")],
            }],
        );
        assert!(algebraic_constructor_cases(&arbitrary(infinite)).is_none());
    }

    #[test]
    fn constructor_cases_reject_wrong_payload_types_and_foreign_constructors() {
        let ty = datatype(
            "Cell",
            vec![AlgebraicVariantType {
                name: "Cell".into(),
                fields: vec![AlgebraicValueType::C(CType::Int32)],
            }],
        );
        for (variant, fields) in [
            (
                "Cell",
                vec![AlgebraicValue::C(symbolic_call_result(
                    CType::Int32Pointer,
                    Variable(0),
                ))],
            ),
            ("Other", vec![AlgebraicValue::C(int32(0))]),
            (
                "Cell",
                vec![AlgebraicValue::C(int32(0)), AlgebraicValue::C(int32(1))],
            ),
        ] {
            assert!(
                algebraic_constructor_cases(&AlgebraicTerm {
                    algebraic_type: ty.clone(),
                    node: AlgebraicTermNode::Constructor {
                        variant: variant.into(),
                        fields
                    }
                })
                .is_none()
            );
        }
    }

    #[test]
    fn constructor_cases_cover_the_entire_declared_family() {
        for width in [1, 3, 16, 64] {
            let ty = datatype(
                "Wide",
                (0..width)
                    .map(|i| AlgebraicVariantType {
                        name: format!("V{i}"),
                        fields: vec![],
                    })
                    .collect(),
            );
            let theorem = algebraic_constructor_cases(&arbitrary(ty)).unwrap();
            let mut remaining = theorem.proposition();
            for i in 0..width {
                let arm = if i + 1 == width {
                    remaining
                } else {
                    let Proposition::Or(left, right) = remaining else {
                        panic!("missing alternative")
                    };
                    remaining = right;
                    left
                };
                assert!(
                    matches!(arm, Proposition::Equal(_, Term::Algebraic(AlgebraicTerm { node: AlgebraicTermNode::Constructor { variant, fields }, .. })) if variant == &format!("V{i}") && fields.is_empty())
                );
            }
        }
    }

    #[test]
    fn constructor_cases_preserve_generic_instantiation_in_recursive_tails() {
        for item in [
            AlgebraicValueType::Parameter("T".into()),
            AlgebraicValueType::C(CType::Int32),
            AlgebraicValueType::C(CType::Int64),
            AlgebraicValueType::C(CType::VoidPointer),
        ] {
            let key = AlgebraicValueType::Algebraic {
                name: "List".into(),
                arguments: vec![item.clone()],
            };
            let variants: Arc<[AlgebraicVariantType]> = vec![
                AlgebraicVariantType {
                    name: "Nil".into(),
                    fields: vec![],
                },
                AlgebraicVariantType {
                    name: "Cons".into(),
                    fields: vec![item.clone(), key.clone()],
                },
            ]
            .into();
            let ty = AlgebraicType {
                rigid: false,
                name: "List".into(),
                arguments: vec![item.clone()],
                variants: variants.clone(),
                schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
            };
            let value = arbitrary(ty);
            let theorem = algebraic_constructor_cases(&value).unwrap();
            assert_eq!(theorem, algebraic_constructor_cases(&value).unwrap());
            let Proposition::Or(_, cons) = theorem.proposition() else {
                panic!("list constructors")
            };
            let Proposition::Exists {
                sort: head_sort,
                body,
                ..
            } = cons.as_ref()
            else {
                panic!("head")
            };
            let expected = match item {
                AlgebraicValueType::Parameter(name) => {
                    Sort::Algebraic(AlgebraicType::parameter(name))
                }
                AlgebraicValueType::C(CType::Int32) => Sort::CInt32,
                AlgebraicValueType::C(CType::Int64) => Sort::CInt64,
                AlgebraicValueType::C(CType::VoidPointer) => Sort::CPointer(CType::VoidPointer),
                _ => unreachable!(),
            };
            assert_eq!(head_sort, &expected);
            let Proposition::Exists {
                sort: tail_sort,
                body,
                ..
            } = body.as_ref()
            else {
                panic!("tail")
            };
            assert_eq!(tail_sort, &Sort::Algebraic(value.algebraic_type.clone()));
            let Proposition::Equal(_, Term::Algebraic(constructor)) = body.as_ref() else {
                panic!("constructor")
            };
            assert!(constructor.checked_constructor_fields().is_some());
        }
    }
}
