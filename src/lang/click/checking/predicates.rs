use super::*;

pub(in crate::lang::click) fn unfold_available_predicate_facts(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    available_pure_facts: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    if unfolded_predicates.is_empty() {
        return Ok(available_pure_facts.to_vec());
    }

    // SourceProof contexts can contain large execution propositions whose trees do
    // not mention a Click predicate at all. Rebuilding every one of those
    // trees for each `unfold` made this otherwise structural tactic scale with
    // the entire execution history. Predicate applications only occur at the
    // proposition level, so select the small relevant subset first.
    let to_unfold = available_pure_facts
        .iter()
        .filter(|proposition| {
            proposition_contains_named_predicate(proposition, unfolded_predicates)
        })
        .collect::<Vec<_>>();
    if to_unfold.is_empty() {
        return Ok(available_pure_facts.to_vec());
    }

    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut propositions = available_pure_facts.to_vec();
    for proposition in to_unfold {
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            proposition,
            &assumptions,
        )?;
        if &unfolded != proposition && !propositions.contains(&unfolded) {
            propositions.push(unfolded);
        }
    }
    Ok(propositions)
}

fn proposition_contains_named_predicate(proposition: &Proposition, names: &[String]) -> bool {
    match proposition {
        Proposition::Predicate { name, .. } => names.iter().any(|candidate| candidate == name),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_contains_named_predicate(left, names)
                || proposition_contains_named_predicate(right, names)
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => proposition_contains_named_predicate(body, names),
        _ => false,
    }
}

pub(in crate::lang::click) fn unfold_predicates_in_proposition(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Result<Proposition, String> {
    let mut active = BTreeSet::new();
    unfold_predicates_in_proposition_with_active(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        proposition,
        assumptions,
        &mut active,
    )
}

pub(in crate::lang::click) fn unfold_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &PureFactContext,
    active: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        Proposition::Predicate { name, arguments }
            if unfolded_predicates
                .iter()
                .any(|predicate| predicate == name) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_predicate_definition(
                definition,
                arguments,
                assumptions,
                predicate_environment,
                click_function_environment,
            )?;
            let unfolded = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &unfolded,
                assumptions,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        Proposition::And(left, right) => Ok(Proposition::And(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Not(body) => Ok(Proposition::Not(Box::new(
            unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?,
        ))),
        Proposition::Implies(left, right) => {
            let left = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                &right_assumptions,
                active,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        Proposition::ForAll { var, sort, body } => Ok(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Ok(Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        _ => Ok(proposition.clone()),
    }
}

pub(in crate::lang::click) fn instantiate_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[Term],
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let (state, mut values, array_refs) = decode_predicate_arguments(definition, arguments)?;

    let mut next_variable = 2_500_000;
    let mut active_functions = BTreeSet::new();
    let program_point_states = ProgramPointStates::new();
    lower_predicate_body_proposition_with_environment(
        &mut values,
        &array_refs,
        &state,
        assumptions,
        definition.body(),
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &program_point_states,
        &mut active_functions,
    )
}

pub(in crate::lang::click) fn decode_predicate_arguments(
    definition: &PredicateDefinition,
    arguments: &[Term],
) -> Result<(CState, BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let expanded_len = 1 + definition
        .parameters()
        .iter()
        .map(|parameter| {
            if parameter_is_click_array_ref(parameter) {
                2
            } else {
                1
            }
        })
        .sum::<usize>();

    if arguments.len() == expanded_len {
        let Some(Term::CState(state)) = arguments.first() else {
            return Err(format!(
                "predicate `{}` is missing its resource-state snapshot",
                definition.name()
            ));
        };
        let mut values = BTreeMap::new();
        let mut array_refs = BTreeMap::new();
        let mut default_memory = None;
        let mut index = 1;
        for parameter in definition.parameters() {
            if parameter_is_click_array_ref(parameter) {
                let Some(Term::CMemory(memory)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref memory",
                        definition.name(),
                        parameter.name()
                    ));
                };
                let Some(Term::CValue(CValue::Pointer(pointer))) = arguments.get(index + 1) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                default_memory.get_or_insert_with(|| memory.clone());
                values.insert(
                    parameter.name().to_string(),
                    CValue::Pointer(pointer.clone()),
                );
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        memory: memory.clone(),
                        pointer: pointer.clone(),
                        element_type: click_array_element_type(parameter.c_type()).ok_or_else(
                            || {
                                format!(
                                    "predicate `{}` argument `{}` is not an array-ref parameter",
                                    definition.name(),
                                    parameter.name()
                                )
                            },
                        )?,
                    },
                );
                index += 2;
            } else {
                let Some(Term::CValue(value)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` did not lower to a C value",
                        definition.name(),
                        parameter.name()
                    ));
                };
                values.insert(parameter.name().to_string(), value.clone());
                index += 1;
            }
        }
        return Ok((
            state
                .clone()
                .with_memory(default_memory.unwrap_or_default()),
            values,
            array_refs,
        ));
    }

    Err(format!(
        "predicate `{}` has malformed lowered argument count: expected {} expanded argument term(s), got {}",
        definition.name(),
        expanded_len,
        arguments.len()
    ))
}

pub(in crate::lang::click) fn lower_predicate_body_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    next_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    let memory = state;
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
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
            let parent = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
                assumptions,
                parent,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let child = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
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
            let segment = evaluate_predicate_contract_segment(
                values,
                array_refs,
                memory,
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
            loadable_segment_prop(state.memory(), segment, element_width)
                .map_err(|error| error.message)
        }
        ClickProposition::Defined { expression } => {
            let expression = contract_expression_to_c_fragment(expression).ok_or_else(|| {
                "`defined(...)` currently requires an expression without `old`, `at`, folds, lets, or Click function calls".to_string()
            })?;
            let expression_state = values.iter().fold(state.clone(), |state, (name, value)| {
                state.with_local(name.clone(), value.clone())
            });
            c_expression_definedness_proposition(&expression_state, &expression).map_err(|limit| {
                format!("`defined(...)` elaboration hit execution limit {limit:?}")
            })
        }
        ClickProposition::At { .. } => {
            Err("`at(...)` is not available in predicate definitions".to_string())
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
            lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
            let left = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
            let body = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
            let body = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
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
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
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
            let body = match lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
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
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
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
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
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
                        let body = match lower_predicate_body_proposition_with_environment(
                            values,
                            array_refs,
                            memory,
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
                    let body = match lower_predicate_body_proposition_with_environment(
                        values,
                        array_refs,
                        memory,
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
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let lowered_arguments = lower_predicate_call_arguments_with_environment(
                definition,
                arguments,
                values,
                array_refs,
                state,
                state,
                None,
                assumptions,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::Predicate {
                name: name.clone(),
                arguments: lowered_arguments,
            })
        }
    }
}

fn evaluate_predicate_contract_segment(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    assumptions: &PureFactContext,
    segment: &ContractSegment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<EvaluatedContractSegment, String> {
    let memory = state;
    if segment.state != ContractSegmentState::Current {
        return Err("`old(...)` is not available in memory resource subjects".to_string());
    }
    let base = evaluate_predicate_contract_expression(
        values,
        array_refs,
        memory,
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
    let start = evaluate_predicate_contract_expression(
        values,
        array_refs,
        memory,
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
    let end = evaluate_predicate_contract_expression(
        values,
        array_refs,
        memory,
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

fn evaluate_predicate_resource_subject(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    assumptions: &PureFactContext,
    resource: &ResourceSubject,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CResource, String> {
    let memory = state;
    match resource {
        ResourceSubject::Memory(segment) => {
            let segment = evaluate_predicate_contract_segment(
                values,
                array_refs,
                memory,
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
            let mut values_out = Vec::new();
            for (index, (argument, parameter_type)) in
                arguments.iter().zip(parameter_types).enumerate()
            {
                let value = evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
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
                values_out.push(value);
            }
            Ok(match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: values_out,
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: values_out,
                },
            })
        }
    }
}

pub(in crate::lang::click) fn evaluate_predicate_contract_expression(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    assumptions: &PureFactContext,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    let memory = state;
    match expression {
        ContractExpression::CFragment(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => evaluate_c_contract_expression(values, state, None, assumptions, expression),
        ContractExpression::CBinding(name) => Err(format!(
            "`c({name})` is not available in predicate definitions"
        )),
        ContractExpression::ResourceCount(resource) => {
            let ResourceClause::Declared {
                name, arguments, ..
            } = resource.as_ref()
            else {
                return Err("`count(...)` expects a declared resource".to_string());
            };
            let mut resource_arguments = Vec::with_capacity(arguments.len());
            for argument in arguments {
                resource_arguments.push(match argument {
                    ContractExpression::ResourceWildcard => None,
                    argument => Some(evaluate_predicate_contract_expression(
                        values,
                        array_refs,
                        state,
                        assumptions,
                        argument,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    )?),
                });
            }
            Ok(CValue::Int32(state.counted_population_sum(
                name,
                &resource_arguments,
                assumptions,
            )))
        }
        ContractExpression::ResourceWildcard => {
            Err("`_` is only valid inside a `count(...)` resource pattern".to_string())
        }
        ContractExpression::Old(_) => {
            Err("`old(...)` is not available in predicate definitions".to_string())
        }
        ContractExpression::At { .. } => {
            Err("`at(...)` is not available in predicate definitions".to_string())
        }
        ContractExpression::Add(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            let value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
            if contains_old_expression(base) {
                return Err("`old(...)` is not available in predicate definitions".to_string());
            }
            if contains_at_expression(base) {
                return Err("`at(...)` is not available in predicate definitions".to_string());
            }
            let array_ref = evaluate_contract_array_ref_with_environment(
                values,
                array_refs,
                &state,
                &state,
                None,
                assumptions,
                base,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let index = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
                pointer,
                element_type,
                assumptions,
            )?;
            Ok(value)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut condition_values = values.clone();
            let mut next_variable = 2_500_000;
            let condition = lower_predicate_body_proposition_with_environment(
                &mut condition_values,
                array_refs,
                memory,
                assumptions,
                condition,
                &mut next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            if assumptions.proves(&condition) {
                return evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    then_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }
            if assumptions_prove_proposition_false(assumptions, &condition) {
                return evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    else_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }

            let then_value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                then_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let else_value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
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
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold end",
            )?;
            let mut value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
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
                        let mut fold_values = values.clone();
                        fold_values.insert(accumulator.clone(), value);
                        fold_values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        value = evaluate_predicate_contract_expression(
                            &fold_values,
                            array_refs,
                            memory,
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
                    let mut fold_values = values.clone();
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
                    let body_value = evaluate_predicate_contract_expression(
                        &fold_values,
                        array_refs,
                        memory,
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
            let value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                value,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let value = checked_contract_let_value(value, *c_type, name)?;
            let mut let_values = values.clone();
            let_values.insert(name.clone(), value);
            evaluate_predicate_contract_expression(
                &let_values,
                array_refs,
                memory,
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
            values,
            array_refs,
            &state,
            &state,
            None,
            assumptions,
            predicate_environment,
            program_point_states,
            active_functions,
        ),
    }
}
