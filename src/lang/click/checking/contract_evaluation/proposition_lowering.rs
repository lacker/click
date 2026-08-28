use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn evaluate_contract_expression_with_program_points(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<CValue, String> {
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut active_functions = BTreeSet::new();
    evaluate_contract_expression_with_environment(
        &parameter_values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        expression,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn lower_outcome_proposition(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let program_point_states = ProgramPointStates::new();
    lower_outcome_proposition_with_program_points(
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        available_pure_facts,
        proposition,
        predicate_environment,
        click_function_environment,
        &program_point_states,
    )
}

/// Lowers an outcome proposition against an already-indexed assumption
/// context. Proof-object transitions use this entry point so one simple step
/// does not rebuild the complete ambient fact context merely to lower its
/// explicit surface proposition.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn lower_outcome_proposition_with_assumptions(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &ProgramPointStates::new(),
        &mut active_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn lower_outcome_proposition_with_program_points(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<Proposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

/// Lowers a proposition while retaining symbolic external-memory loads even
/// when the selected snapshot already materializes their values.
///
/// Fact transport needs this form for propositions such as
/// `at(mark, field == 11)`: reducing the marked load to `11 == 11` proves the
/// source but erases the memory identity needed to frame it to a later state.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn lower_outcome_proposition_symbolically_with_program_points(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<Proposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts)
        .allow_symbolic_contract_loads()
        .force_symbolic_external_loads();
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

pub(in crate::lang::click) fn lower_outcome_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    next_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_contract_expression_with_environment(
                values,
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
                values,
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
            comparison_proposition(left, *operator, right).map_err(|error| error.message)
        }
        ClickProposition::Separate { left, right } => {
            let left = evaluate_resource_subject_with_environment(
                values,
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
            let right = evaluate_resource_subject_with_environment(
                values,
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
            Ok(Proposition::CResourceSeparate { left, right })
        }
        ClickProposition::Contains { parent, child } => {
            let parent = evaluate_resource_subject_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                parent,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let child = evaluate_resource_subject_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                child,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::CResourceContains { parent, child })
        }
        ClickProposition::Loadable { segment } => {
            let segment = evaluate_contract_segment_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                segment,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let element_width =
                contract_segment_element_width_from_array_refs(array_refs, &segment.source)
                    .unwrap_or(4);
            let memory = match segment.source.state {
                ContractSegmentState::Current => post_state.memory(),
                ContractSegmentState::Old => pre_state.memory(),
            };
            loadable_segment_prop(memory, segment, element_width).map_err(|error| error.message)
        }
        ClickProposition::Defined { expression } => {
            let expression = contract_expression_to_c_fragment(expression).ok_or_else(|| {
                "`defined(...)` currently requires an expression without `old`, `at`, folds, lets, or Click function calls".to_string()
            })?;
            let mut state = post_state.clone();
            for (name, value) in values.iter() {
                state = state.with_local(name.clone(), value.clone());
            }
            if let Some(result) = result {
                state = state.with_local("result", result.clone());
            }
            c_expression_definedness_proposition(&state, &expression).map_err(|limit| {
                format!("`defined(...)` elaboration hit execution limit {limit:?}")
            })
        }
        ClickProposition::At {
            selector,
            proposition,
        } => {
            let snapshot_state =
                concrete_program_point_state(selector, pre_state, program_point_states)?;
            let (mut snapshot_values, snapshot_array_refs) =
                contract_environment_at_state(values, array_refs, snapshot_state);
            lower_outcome_proposition_with_environment(
                &mut snapshot_values,
                &snapshot_array_refs,
                pre_state,
                snapshot_state,
                None,
                assumptions,
                proposition,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(negate_lowered_proposition(
            lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?,
        )),
        ClickProposition::Implies(left, right) => {
            let left = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            // At a concrete outcome, a result guard can already be false.
            // Its consequent is unreachable in this point judgment, so do
            // not lower memory expressions that the implication cannot use.
            // Retaining the implication shape lets an explicit
            // `intro(); contradiction(...)` certificate check normally.
            if matches!(
                &left,
                Proposition::ConditionIs(ConditionTerm::Constant(actual), expected)
                    if actual != expected
            ) {
                return Ok(Proposition::Implies(
                    Box::new(left),
                    Box::new(true_proposition()),
                ));
            }
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                &right_assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        ClickProposition::ForAll { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `forall (...: int32)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::ForAll {
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `exists (...: int32)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::Exists {
                name: name.clone(),
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
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
                "range `all` start bound",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
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
                "range `all` end bound",
            )?;
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let item_bits = Bitvector32Term::Variable(variable);
            let item_value = CValue::Int32(item_bits.clone());
            let outer_values = values.clone();
            values.insert(item.clone(), item_value.clone());
            let body_assumptions =
                assumptions
                    .clone()
                    .assume_proposition(range_membership_proposition(
                        start.clone(),
                        item_bits.clone(),
                        end.clone(),
                    ));
            let body = match lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                &body_assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            ) {
                Ok(body) => body,
                Err(error) => {
                    *values = outer_values;
                    return Err(error);
                }
            };
            *values = outer_values;
            Ok(bounded_forall_int32(variable, start, item_bits, end, body))
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
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
                "range `any` start bound",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
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
                "range `any` end bound",
            )?;
            let outer_values = values.clone();
            match (
                concrete_bound_from_term(&start, "any", "start"),
                concrete_bound_from_term(&end, "any", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    let mut proposition = false_proposition();
                    for index in concrete_fold_range(start, end)? {
                        *values = outer_values.clone();
                        values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        let body = match lower_outcome_proposition_with_environment(
                            values,
                            array_refs,
                            pre_state,
                            post_state,
                            result,
                            assumptions,
                            body,
                            next_variable,
                            predicate_environment,
                            click_function_environment,
                            program_point_states,
                            active_functions,
                        ) {
                            Ok(body) => body,
                            Err(error) => {
                                *values = outer_values;
                                return Err(error);
                            }
                        };
                        proposition = disjunction(proposition, body);
                    }
                    *values = outer_values;
                    Ok(proposition)
                }
                _ => {
                    let variable = Variable(*next_variable);
                    *next_variable += 1;
                    let item_bits = Bitvector32Term::Variable(variable);
                    let item_value = CValue::Int32(item_bits.clone());
                    values.insert(item.clone(), item_value.clone());
                    let body_assumptions =
                        assumptions
                            .clone()
                            .assume_proposition(range_membership_proposition(
                                start.clone(),
                                item_bits.clone(),
                                end.clone(),
                            ));
                    let body = match lower_outcome_proposition_with_environment(
                        values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        &body_assumptions,
                        body,
                        next_variable,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    ) {
                        Ok(body) => body,
                        Err(error) => {
                            *values = outer_values;
                            return Err(error);
                        }
                    };
                    *values = outer_values;
                    Ok(bounded_exists_int32(
                        item.clone(),
                        variable,
                        start,
                        item_bits,
                        end,
                        body,
                    ))
                }
            }
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let lowered_arguments = if let Some(definition) = predicate_environment.get(name) {
                lower_predicate_call_arguments_with_environment(
                    definition,
                    arguments,
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?
            } else {
                let mut lowered_arguments = vec![Term::CMemory(post_state.memory().clone())];
                lowered_arguments.extend(
                    arguments
                        .iter()
                        .map(|argument| {
                            evaluate_contract_expression_with_environment(
                                values,
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
                            )
                            .map(Term::CValue)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                );
                lowered_arguments
            };
            Ok(Proposition::Predicate {
                name: name.clone(),
                arguments: lowered_arguments,
            })
        }
    }
}

fn evaluate_contract_segment_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    segment: &ContractSegment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<EvaluatedContractSegment, String> {
    let evaluation_post_state = match segment.state {
        ContractSegmentState::Current => post_state,
        ContractSegmentState::Old => pre_state,
    };
    let base = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        evaluation_post_state,
        result,
        assumptions,
        &ContractExpression::CFragment(segment.base.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        evaluation_post_state,
        result,
        assumptions,
        &ContractExpression::CFragment(segment.start.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        evaluation_post_state,
        result,
        assumptions,
        &ContractExpression::CFragment(segment.end.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Int32(end) = end else {
        return Err("segment end did not evaluate to int32".to_string());
    };

    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base,
        start,
        end,
    })
}

fn evaluate_resource_subject_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    resource: &ResourceSubject,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CResource, String> {
    match resource {
        ResourceSubject::Memory(segment) => {
            let segment = evaluate_contract_segment_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                segment,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(CResource::Memory(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            )))
        }
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            if arguments.len() != parameter_types.len() {
                return Err(format!(
                    "resource `{name}` has malformed argument type metadata"
                ));
            }
            let mut values = Vec::new();
            for (index, (argument, parameter_type)) in
                arguments.iter().zip(parameter_types).enumerate()
            {
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
                    program_point_states,
                    active_functions,
                )?;
                if !c_value_matches_click_type(&value, *parameter_type) {
                    return Err(format!(
                        "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                        parameter_type
                    ));
                }
                values.push(value);
            }
            Ok(match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: values,
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: values,
                },
            })
        }
    }
}
