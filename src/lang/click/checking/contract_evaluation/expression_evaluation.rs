use super::*;

pub(in crate::lang::click) fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    match expression {
        ContractExpression::CFragment(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => evaluate_c_contract_expression(
            parameter_values,
            post_state,
            result,
            assumptions,
            expression,
        ),
        ContractExpression::CBinding(name) => post_state
            .locals()
            .object_values()
            .find_map(|(local_name, value)| (local_name == name).then(|| value.clone()))
            .or_else(|| parameter_values.get(name).cloned())
            .ok_or_else(|| format!("C binding `{name}` is not in scope")),
        ContractExpression::ResourceCount(resource) => {
            let ResourceClause::Declared {
                name, arguments, ..
            } = resource.as_ref()
            else {
                return Err("`count(...)` expects a declared resource".to_string());
            };
            let mut values = Vec::with_capacity(arguments.len());
            for argument in arguments {
                values.push(match argument {
                    ContractExpression::ResourceWildcard => None,
                    argument => Some(evaluate_contract_expression_with_environment(
                        parameter_values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        assumptions,
                        argument,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    )?),
                });
            }
            Ok(CValue::Int32(post_state.counted_population_sum(
                name,
                &values,
                assumptions,
            )))
        }
        ContractExpression::ResourceWildcard => {
            Err("`_` is only valid inside a `count(...)` resource pattern".to_string())
        }
        ContractExpression::Old(expression) => evaluate_contract_expression_with_environment(
            parameter_values,
            &array_refs_with_memory(array_refs, pre_state.memory()),
            pre_state,
            pre_state,
            None,
            assumptions,
            expression,
            predicate_environment,
            click_function_environment,
            program_point_states,
            active_functions,
        ),
        ContractExpression::At {
            selector,
            expression,
        } => {
            let snapshot_state =
                concrete_program_point_state(selector, pre_state, program_point_states)?;
            let (snapshot_values, snapshot_array_refs) =
                contract_environment_at_state(parameter_values, array_refs, snapshot_state);
            evaluate_contract_expression_with_environment(
                &snapshot_values,
                &snapshot_array_refs,
                pre_state,
                snapshot_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ContractExpression::Add(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_add(left, right)
        }
        ContractExpression::Subtract(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        ContractExpression::Multiply(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        ContractExpression::Divide(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        ContractExpression::Remainder(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        ContractExpression::ShiftRight(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        ContractExpression::BitwiseOr(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        ContractExpression::BitwiseXor(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        ContractExpression::BitwiseNot(expression) => {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        ContractExpression::Index(base, index) => {
            let surface_base = contract_expression_to_c_fragment(base);
            let surface_index = contract_expression_to_c_fragment(index);
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                base,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let index = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                index,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let CValue::Int32(index) = index else {
                return Err(format!(
                    "array index did not evaluate to int32: `{index:?}`"
                ));
            };
            let element_type = array_ref.element_type;
            let pointer =
                offset_pointer_by_elements(array_ref.pointer, index, element_type.byte_width());
            let value = evaluate_contract_memory_load_from_memory(
                &array_ref.memory,
                pointer.clone(),
                element_type,
                assumptions,
            )?;
            if let (Some(base), Some(index)) = (surface_base, surface_index) {
                record_surface_loadability_segment(
                    &array_ref.memory,
                    &pointer,
                    element_type,
                    CExpression::Add(Box::new(base), Box::new(index)),
                    CExpression::Value(int32(0)),
                    CExpression::Value(int32(1)),
                );
            }
            Ok(value)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut values = parameter_values.clone();
            let mut next_variable = 2_000_000;
            let condition = lower_outcome_proposition_with_environment(
                &mut values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                condition,
                &mut next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            if assumptions.proves(&condition) {
                return evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    then_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }
            if assumptions_prove_proposition_false(assumptions, &condition) {
                return evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    else_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }

            let then_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                then_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let else_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                else_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            conditional_contract_value(&condition, then_value, else_value)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold start",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold end",
            )?;
            let mut value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                initial,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match (
                concrete_bound_from_term(&start, "fold", "start"),
                concrete_bound_from_term(&end, "fold", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    for index in concrete_fold_range(start, end)? {
                        let mut fold_values = parameter_values.clone();
                        fold_values.insert(accumulator.clone(), value);
                        fold_values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        value = evaluate_contract_expression_with_environment(
                            &fold_values,
                            array_refs,
                            pre_state,
                            post_state,
                            result,
                            assumptions,
                            body,
                            predicate_environment,
                            click_function_environment,
                            program_point_states,
                            active_functions,
                        )?;
                    }
                    Ok(value)
                }
                _ => {
                    let mut fold_values = parameter_values.clone();
                    fold_values.insert(
                        accumulator.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                            accumulator,
                            0,
                        ))),
                    );
                    fold_values.insert(
                        item.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                    );
                    let body_value = evaluate_contract_expression_with_environment(
                        &fold_values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        assumptions,
                        body,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    )?;
                    symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                }
            }
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                value,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let value = checked_contract_let_value(value, *c_type, name)?;
            let mut let_values = parameter_values.clone();
            let_values.insert(name.clone(), value);
            evaluate_contract_expression_with_environment(
                &let_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ContractExpression::Call { name, arguments } => evaluate_click_function_call(
            click_function_environment,
            name,
            arguments,
            parameter_values,
            array_refs,
            pre_state,
            post_state,
            result,
            assumptions,
            predicate_environment,
            program_point_states,
            active_functions,
        ),
    }
}
