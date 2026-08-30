use super::*;

pub(in crate::surface) fn array_refs_with_memory(
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
) -> ClickArrayRefs {
    array_refs
        .iter()
        .map(|(name, array_ref)| {
            (
                name.clone(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: array_ref.pointer.clone(),
                    element_type: array_ref.element_type,
                },
            )
        })
        .collect()
}

pub(in crate::surface) fn contract_environment_at_state(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
) -> (BTreeMap<String, CValue>, ClickArrayRefs) {
    let mut values = parameter_values.clone();
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );

    let mut state_array_refs = array_refs_with_memory(array_refs, state.memory());
    for (name, value, element_type) in state.locals().array_object_values() {
        let CValue::Pointer(pointer) = value.clone() else {
            unreachable!("local array values are pointers")
        };
        values.insert(name.to_string(), value);
        state_array_refs.insert(
            name.to_string(),
            ClickArrayRef {
                memory: state.memory().clone(),
                pointer,
                element_type,
            },
        );
    }
    (values, state_array_refs)
}

pub(in crate::surface) fn selected_snapshot_state<'a>(
    selector: &SnapshotSelector,
    function_entry_state: &'a CState,
    recorded_snapshots: &'a RecordedSnapshots,
) -> Result<&'a CState, String> {
    match selector {
        SnapshotSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }) => Ok(function_entry_state),
        SnapshotSelector::Mark(name) => recorded_snapshots.get(selector).ok_or_else(|| {
            format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )
        }),
        SnapshotSelector::ProgramPoint(point @ ProgramPointRef {
            region:
                CodeRegionRef::Statement(_)
                | CodeRegionRef::Loop(_)
                | CodeRegionRef::Label(_),
            ..
        }) => recorded_snapshots.get(selector).ok_or_else(|| {
            format!(
                "no state snapshot was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                describe_program_point_ref(point)
            )
        }),
        SnapshotSelector::ProgramPoint(point) => Err(format!(
            "`at({}, ...)` is not supported in concrete evaluation yet",
            describe_program_point_ref(point)
        )),
    }
}

pub(in crate::surface) fn evaluate_click_function_call(
    click_function_environment: &ClickFunctionEnvironment,
    name: &str,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    recorded_snapshots: &RecordedSnapshots,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    let definition = click_function_environment
        .get(name)
        .ok_or_else(|| format!("unknown function `{name}`"))?;
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "function `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    let recursive_reentry = active_functions.contains(name);
    if recursive_reentry && definition.decreases().is_none() {
        return Err(format!(
            "recursive function call `{name}` has no decreases measure"
        ));
    }

    let mut function_values = BTreeMap::new();
    let mut function_array_refs = BTreeMap::new();
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        let value = if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "function `{}` parameter `{}` is not an array-ref parameter",
                        definition.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "function `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    definition.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            let pointer = array_ref.pointer.clone();
            function_array_refs.insert(parameter.name().to_string(), array_ref);
            CValue::Pointer(pointer)
        } else {
            evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?
        };
        function_values.insert(parameter.name().to_string(), value);
    }

    if recursive_reentry {
        let symbolic_arguments = definition
            .parameters()
            .iter()
            .map(|parameter| match function_values.get(parameter.name()) {
                Some(CValue::Int32(value)) => Ok(value.clone()),
                _ => Err(format!(
                    "recursive function `{name}` currently supports only int32 arguments"
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;
        if symbolic_arguments
            .iter()
            .any(|argument| !matches!(argument, Bitvector32Term::Constant(_)))
        {
            return Ok(CValue::Int32(Bitvector32Term::PureFunctionApplication {
                name: name.to_string(),
                arguments: symbolic_arguments,
            }));
        }
    }

    let inserted = active_functions.insert(name.to_string());

    let value = evaluate_contract_expression_with_environment(
        &function_values,
        &function_array_refs,
        post_state,
        post_state,
        None,
        assumptions,
        definition.body(),
        predicate_environment,
        click_function_environment,
        recorded_snapshots,
        active_functions,
    )?;
    if inserted {
        active_functions.remove(name);
    }

    if !c_value_matches_click_type(&value, definition.return_type()) {
        return Err(format!(
            "function `{}` returned {value:?}, which does not match {:?}",
            definition.name(),
            definition.return_type()
        ));
    }
    Ok(value)
}

pub(in crate::surface) fn evaluate_contract_array_ref_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
    active_functions: &mut BTreeSet<String>,
) -> Result<ClickArrayRef, String> {
    match expression {
        ContractExpression::Old(expression) => {
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                pre_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `old(...)` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            let element_type =
                contract_array_ref_element_type(array_refs, expression).unwrap_or(CType::Int32);
            Ok(ClickArrayRef {
                memory: pre_state.memory().clone(),
                pointer,
                element_type,
            })
        }
        ContractExpression::At {
            selector,
            expression,
        } => {
            let snapshot_state = selected_snapshot_state(selector, pre_state, recorded_snapshots)?;
            let (snapshot_values, snapshot_array_refs) =
                contract_environment_at_state(parameter_values, array_refs, snapshot_state);
            let pointer_value = evaluate_contract_expression_with_environment(
                &snapshot_values,
                &snapshot_array_refs,
                pre_state,
                snapshot_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `at({}, ...)` did not evaluate to a pointer: `{pointer_value:?}`",
                    describe_snapshot_selector(selector)
                ));
            };
            let element_type =
                contract_array_ref_element_type(array_refs, expression).unwrap_or(CType::Int32);
            Ok(ClickArrayRef {
                memory: snapshot_state.memory().clone(),
                pointer,
                element_type,
            })
        }
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => {
            if let Some(array_ref) = array_refs.get(name) {
                return Ok(array_ref.clone());
            }
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference `{name}` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            Ok(ClickArrayRef {
                memory: post_state.memory().clone(),
                pointer,
                element_type: CType::Int32,
            })
        }
        ContractExpression::Add(left, right) => {
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    right,
                    predicate_environment,
                    click_function_environment,
                    recorded_snapshots,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        offset,
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    left,
                    predicate_environment,
                    click_function_environment,
                    recorded_snapshots,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        offset,
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            evaluate_pointer_expression_as_current_array_ref(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )
        }
        ContractExpression::Subtract(left, right) => {
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    right,
                    predicate_environment,
                    click_function_environment,
                    recorded_snapshots,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        bitvector32_subtract(Bitvector32Term::Constant(0), offset),
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            evaluate_pointer_expression_as_current_array_ref(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )
        }
        _ => evaluate_pointer_expression_as_current_array_ref(
            parameter_values,
            array_refs,
            pre_state,
            post_state,
            result,
            assumptions,
            expression,
            predicate_environment,
            click_function_environment,
            recorded_snapshots,
            active_functions,
        ),
    }
}

pub(in crate::surface) fn contract_array_ref_element_type(
    array_refs: &ClickArrayRefs,
    expression: &ContractExpression,
) -> Option<CType> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => {
            array_refs.get(name).map(|array_ref| array_ref.element_type)
        }
        ContractExpression::Old(expression) => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::At { expression, .. } => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::Add(left, right) => contract_array_ref_element_type(array_refs, left)
            .or_else(|| contract_array_ref_element_type(array_refs, right)),
        ContractExpression::Subtract(left, _) => contract_array_ref_element_type(array_refs, left),
        _ => None,
    }
}

pub(in crate::surface) fn evaluate_pointer_expression_as_current_array_ref(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
    active_functions: &mut BTreeSet<String>,
) -> Result<ClickArrayRef, String> {
    let pointer_value = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        post_state,
        result,
        assumptions,
        expression,
        predicate_environment,
        click_function_environment,
        recorded_snapshots,
        active_functions,
    )?;
    let CValue::Pointer(pointer) = pointer_value else {
        return Err(format!(
            "array reference expression did not evaluate to a pointer: `{pointer_value:?}`"
        ));
    };
    Ok(ClickArrayRef {
        memory: post_state.memory().clone(),
        pointer,
        element_type: CType::Int32,
    })
}

pub(in crate::surface) fn lower_predicate_call_arguments_with_environment(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
    active_functions: &mut BTreeSet<String>,
) -> Result<Vec<Term>, String> {
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "predicate `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }

    // Only a predicate that can observe `count(...)` includes the logical
    // resource-state snapshot in its identity. Giving every predicate that
    // hidden dependency makes an ordinary memory predicate change form
    // after an unrelated resource transition. C memory and locals remain
    // explicit through the predicate's ordinary arguments.
    let resource_state = if predicate_observes_resource_state(
        definition,
        predicate_environment,
        &mut BTreeSet::new(),
    ) {
        post_state.resource_state_snapshot()
    } else {
        CState::new()
    };
    let mut lowered_arguments = vec![Term::CState(resource_state)];
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "predicate `{}` parameter `{}` is not an array-ref parameter",
                        definition.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "predicate `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    definition.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            lowered_arguments.push(Term::CMemory(array_ref.memory));
            lowered_arguments.push(Term::CValue(CValue::Pointer(array_ref.pointer)));
        } else {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                recorded_snapshots,
                active_functions,
            )?;
            lowered_arguments.push(Term::CValue(value));
        }
    }
    Ok(lowered_arguments)
}

fn predicate_observes_resource_state(
    definition: &PredicateDefinition,
    predicate_environment: &PredicateEnvironment,
    visiting: &mut BTreeSet<String>,
) -> bool {
    if proposition_contains_resource_count(definition.body()) {
        return true;
    }
    if !visiting.insert(definition.name().to_string()) {
        return false;
    }
    let result = nested_predicate_names(definition.body())
        .into_iter()
        .any(|name| {
            predicate_environment.get(name).is_some_and(|nested| {
                predicate_observes_resource_state(nested, predicate_environment, visiting)
            })
        });
    visiting.remove(definition.name());
    result
}

fn nested_predicate_names(proposition: &ClickProposition) -> Vec<&str> {
    let mut names = Vec::new();
    fn collect<'a>(proposition: &'a ClickProposition, names: &mut Vec<&'a str>) {
        match proposition {
            ClickProposition::PredicateCall { name, .. } => names.push(name),
            ClickProposition::At { proposition, .. }
            | ClickProposition::Not(proposition)
            | ClickProposition::ForAll {
                body: proposition, ..
            }
            | ClickProposition::Exists {
                body: proposition, ..
            }
            | ClickProposition::RangeAll {
                body: proposition, ..
            }
            | ClickProposition::RangeAny {
                body: proposition, ..
            } => collect(proposition, names),
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                collect(left, names);
                collect(right, names);
            }
            ClickProposition::Comparison { .. }
            | ClickProposition::Defined { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => {}
        }
    }
    collect(proposition, &mut names);
    names
}

pub(in crate::surface) fn c_value_matches_click_type(value: &CValue, c_type: C0Type) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), C0Type::Int32)
            | (CValue::UInt8(_), C0Type::UInt8)
            | (CValue::Pointer(_), C0Type::Int32Pointer)
            | (CValue::Pointer(_), C0Type::UInt8Pointer)
    )
}

pub(in crate::surface) fn checked_contract_let_value(
    value: CValue,
    c_type: Option<C0Type>,
    name: &str,
) -> Result<CValue, String> {
    let Some(c_type) = c_type else {
        return Ok(value);
    };
    if c_value_matches_click_type(&value, c_type) {
        Ok(value)
    } else {
        Err(format!(
            "let binding `{name}` evaluated to {value:?}, which does not match {c_type:?}"
        ))
    }
}
