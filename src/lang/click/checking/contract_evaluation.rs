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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lang::click) struct LoweredOutcomeProposition {
    pub(in crate::lang::click) proposition: Proposition,
    pub(in crate::lang::click) loadability_obligations: Vec<SurfaceLoadabilityObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lang::click) struct SurfaceLoadabilityObligation {
    pub(in crate::lang::click) proposition: Proposition,
    pub(in crate::lang::click) segment: Option<ContractSegment>,
}

thread_local! {
    static SURFACE_LOADABILITY_OBLIGATIONS:
        std::cell::RefCell<Option<Vec<SurfaceLoadabilityObligation>>> =
        const { std::cell::RefCell::new(None) };
}

struct SurfaceLoadabilityObligationGuard;

impl SurfaceLoadabilityObligationGuard {
    fn enter() -> Result<Self, String> {
        SURFACE_LOADABILITY_OBLIGATIONS.with(|obligations| {
            let mut obligations = obligations.borrow_mut();
            if obligations.is_some() {
                return Err("nested surface loadability certification".to_string());
            }
            *obligations = Some(Vec::new());
            Ok(Self)
        })
    }

    fn finish(self) -> Vec<SurfaceLoadabilityObligation> {
        let obligations = SURFACE_LOADABILITY_OBLIGATIONS
            .with(|obligations| obligations.borrow_mut().take().unwrap_or_default());
        std::mem::forget(self);
        obligations
    }
}

impl Drop for SurfaceLoadabilityObligationGuard {
    fn drop(&mut self) {
        SURFACE_LOADABILITY_OBLIGATIONS.with(|obligations| {
            obligations.borrow_mut().take();
        });
    }
}

fn record_surface_loadability_obligation(proposition: &Proposition) {
    SURFACE_LOADABILITY_OBLIGATIONS.with(|obligations| {
        let mut obligations = obligations.borrow_mut();
        let Some(obligations) = obligations.as_mut() else {
            return;
        };
        if !obligations
            .iter()
            .any(|obligation| obligation.proposition == *proposition)
        {
            obligations.push(SurfaceLoadabilityObligation {
                proposition: proposition.clone(),
                segment: None,
            });
        }
    });
}

pub(in crate::lang::click) fn record_surface_loadability_segment(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    base: CExpression,
    start: CExpression,
    end: CExpression,
) {
    let proposition = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(value_type.byte_width()),
    };
    SURFACE_LOADABILITY_OBLIGATIONS.with(|obligations| {
        let mut obligations = obligations.borrow_mut();
        let Some(obligations) = obligations.as_mut() else {
            return;
        };
        let Some(obligation) = obligations
            .iter_mut()
            .find(|obligation| obligation.proposition == proposition)
        else {
            return;
        };
        obligation.segment = Some(ContractSegment {
            state: ContractSegmentState::Current,
            base: base.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::CFragment(base),
                start: ContractExpression::CFragment(start),
                end: ContractExpression::CFragment(end),
            },
        });
    });
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn lower_outcome_proposition_with_obligations(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<LoweredOutcomeProposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions =
        assumptions_from_propositions(available_pure_facts).allow_symbolic_contract_loads();
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    let guard = SurfaceLoadabilityObligationGuard::enter()?;
    let proposition = lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        result,
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )?;
    Ok(LoweredOutcomeProposition {
        proposition,
        loadability_obligations: guard.finish(),
    })
}

pub(in crate::lang::click) fn lower_outcome_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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

pub(in crate::lang::click) fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
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

pub(in crate::lang::click) fn array_refs_with_memory(
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

pub(in crate::lang::click) fn contract_environment_at_state(
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

fn concrete_program_point_state<'a>(
    selector: &VisitSelector,
    function_entry_state: &'a CState,
    program_point_states: &'a ProgramPointStates,
) -> Result<&'a CState, String> {
    match selector {
        VisitSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }) => Ok(function_entry_state),
        VisitSelector::ProgramPoint(point @ ProgramPointRef {
            region: CodeRegionRef::Mark(name),
            ..
        }) => program_point_states.get(point).ok_or_else(|| {
            format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )
        }),
        VisitSelector::ProgramPoint(point @ ProgramPointRef {
            region:
                CodeRegionRef::Statement(_)
                | CodeRegionRef::Loop(_)
                | CodeRegionRef::Label(_),
            ..
        }) => program_point_states.get(point).ok_or_else(|| {
            format!(
                "no state snapshot was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                describe_program_point_ref(point)
            )
        }),
        VisitSelector::ProgramPoint(point) => Err(format!(
            "`at({}, ...)` is not supported in concrete evaluation yet",
            describe_program_point_ref(point)
        )),
    }
}

pub(in crate::lang::click) fn evaluate_click_function_call(
    click_function_environment: &ClickFunctionEnvironment,
    name: &str,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    program_point_states: &ProgramPointStates,
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
                program_point_states,
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
                program_point_states,
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
        program_point_states,
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

pub(in crate::lang::click) fn evaluate_contract_array_ref_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
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
                program_point_states,
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
            let snapshot_state =
                concrete_program_point_state(selector, pre_state, program_point_states)?;
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
                program_point_states,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `at({}, ...)` did not evaluate to a pointer: `{pointer_value:?}`",
                    describe_visit_selector(selector)
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
                program_point_states,
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
                program_point_states,
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
                    program_point_states,
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
                program_point_states,
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
                    program_point_states,
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
                program_point_states,
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
                program_point_states,
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
                    program_point_states,
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
                program_point_states,
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
            program_point_states,
            active_functions,
        ),
    }
}

pub(in crate::lang::click) fn contract_array_ref_element_type(
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

pub(in crate::lang::click) fn evaluate_pointer_expression_as_current_array_ref(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
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
        program_point_states,
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

pub(in crate::lang::click) fn lower_predicate_call_arguments_with_environment(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
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

    let mut lowered_arguments = Vec::new();
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
                program_point_states,
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
                program_point_states,
                active_functions,
            )?;
            lowered_arguments.push(Term::CValue(value));
        }
    }
    Ok(lowered_arguments)
}

pub(in crate::lang::click) fn c_value_matches_click_type(value: &CValue, c_type: C0Type) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), C0Type::Int32)
            | (CValue::UInt8(_), C0Type::UInt8)
            | (CValue::Pointer(_), C0Type::Int32Pointer)
            | (CValue::Pointer(_), C0Type::UInt8Pointer)
    )
}

pub(in crate::lang::click) fn checked_contract_let_value(
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

pub(in crate::lang::click) fn evaluate_c_contract_expression(
    parameter_values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &CExpression,
) -> Result<CValue, String> {
    match expression {
        CExpression::Value(value) => Ok(value.clone()),
        CExpression::Variable(name) if name == "result" => result
            .cloned()
            .ok_or_else(|| "`result` is not available inside `old(...)`".to_string()),
        CExpression::Variable(name) => parameter_values
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown contract variable `{name}`")),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("byte-offset base is not a pointer".to_string());
            };
            Ok(CValue::Pointer(pointer.offset_by_bytes(*bytes)))
        }
        CExpression::Add(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_add(left, right)
        }
        CExpression::Subtract(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        CExpression::Multiply(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        CExpression::Divide(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        CExpression::Remainder(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        CExpression::ShiftLeft(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        CExpression::ShiftRight(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        CExpression::BitwiseAnd(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        CExpression::BitwiseOr(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        CExpression::BitwiseXor(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        CExpression::BitwiseNot(expression) => {
            let value = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                expression,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        CExpression::Load(pointer) => {
            let surface_pointer = pointer.as_ref().clone();
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            let value =
                evaluate_contract_memory_load(state, pointer.clone(), CType::Int32, assumptions)?;
            record_surface_loadability_segment(
                state.memory(),
                &pointer,
                CType::Int32,
                surface_pointer,
                CExpression::Value(int32(0)),
                CExpression::Value(int32(1)),
            );
            Ok(value)
        }
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => {
            let surface_pointer = pointer.as_ref().clone();
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            let value =
                evaluate_contract_memory_load(state, pointer.clone(), *value_type, assumptions)?;
            if value_type.byte_width() == 4 {
                record_surface_loadability_segment(
                    state.memory(),
                    &pointer,
                    *value_type,
                    surface_pointer,
                    CExpression::Value(int32(0)),
                    CExpression::Value(int32(1)),
                );
            }
            Ok(value)
        }
        CExpression::Index(base, index) => {
            let surface_base = base.as_ref().clone();
            let surface_index = index.as_ref().clone();
            let base =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, base)?;
            let index = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            let value =
                evaluate_contract_memory_load(state, pointer.clone(), CType::Int32, assumptions)?;
            record_surface_loadability_segment(
                state.memory(),
                &pointer,
                CType::Int32,
                CExpression::Add(Box::new(surface_base), Box::new(surface_index)),
                CExpression::Value(int32(0)),
                CExpression::Value(int32(1)),
            );
            Ok(value)
        }
        _ => Err(format!(
            "unsupported postcondition expression `{expression:?}`"
        )),
    }
}

pub(in crate::lang::click) fn evaluate_contract_memory_load(
    state: &CState,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    evaluate_contract_memory_load_from_memory(state.memory(), pointer, value_type, assumptions)
}

pub(in crate::lang::click) fn evaluate_contract_memory_load_from_memory(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    let required = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(value_type.byte_width()),
    };
    let outcome = memory.load(&pointer);
    if assumptions.should_allow_symbolic_contract_loads()
        && matches!(outcome, crate::kernel::CExpressionOutcome::Value(_))
        && !assumptions.proves(&required)
    {
        record_surface_loadability_obligation(&required);
    }
    match outcome {
        crate::kernel::CExpressionOutcome::Value(value)
            if c_value_matches_kernel_type(&value, value_type) =>
        {
            Ok(value)
        }
        crate::kernel::CExpressionOutcome::Value(CValue::Int32(
            bits @ Bitvector32Term::MemoryLoad(_, _),
        )) if matches!(value_type, CType::Int32Pointer | CType::UInt8Pointer) => {
            symbolic_pointer_contract_memory_load(pointer, bits, value_type)
        }
        crate::kernel::CExpressionOutcome::Value(value) => Err(format!(
            "load from {pointer:?} produced {value:?}, not {value_type:?}"
        )),
        outcome => {
            if assumptions.should_allow_symbolic_contract_loads() {
                if !assumptions.proves(&required) {
                    record_surface_loadability_obligation(&required);
                }
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            if value_type == CType::Int32
                && assumptions
                    .pure_facts()
                    .iter()
                    .any(|fact| proposition_certifies_contract_load(fact, memory, &pointer))
            {
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            let is_loadable = if assumptions.should_defer_non_exact_loadability_obligations() {
                assumptions.proves_memory_loadable_for_memory_resolution(
                    memory,
                    &pointer,
                    &Bitvector32Term::Constant(value_type.byte_width()),
                )
            } else {
                assumptions.proves(&required)
            };
            if is_loadable {
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            let pure_facts = assumptions.pure_facts();
            Err(format!(
                "{}\n  load from {pointer:?} as {value_type:?} produced {outcome:?}",
                describe_missing_pure_fact(&required, &pure_facts, &[], &[], &[], &[])
            ))
        }
    }
}

fn proposition_certifies_contract_load(
    proposition: &Proposition,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    let Proposition::ConditionIs(condition, _) = proposition else {
        return false;
    };
    condition_contains_contract_load(condition, memory, pointer)
}

fn condition_contains_contract_load(
    condition: &ConditionTerm,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            bitvector_contains_contract_load(left, memory, pointer)
                || bitvector_contains_contract_load(right, memory, pointer)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            pointer_offset_contains_contract_load(left, memory, pointer)
                || pointer_offset_contains_contract_load(right, memory, pointer)
        }
        ConditionTerm::PointerEqual(left, right) => {
            pointer_offset_contains_contract_load(&left.offset, memory, pointer)
                || pointer_offset_contains_contract_load(&right.offset, memory, pointer)
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
    }
}

fn pointer_offset_contains_contract_load(
    term: &PointerOffsetTerm,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    match term {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        PointerOffsetTerm::Add(left, right) => {
            pointer_offset_contains_contract_load(left, memory, pointer)
                || pointer_offset_contains_contract_load(right, memory, pointer)
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            bitvector_contains_contract_load(value, memory, pointer)
        }
    }
}

fn bitvector_contains_contract_load(
    term: &Bitvector32Term,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
        Bitvector32Term::MemoryLoad(load_memory, load_pointer) => {
            load_memory.has_same_snapshot_markers(memory)
                && load_pointer.block == pointer.block
                && normalize_direct_atomic_pointer_offset_loads(&load_pointer.offset)
                    == normalize_direct_atomic_pointer_offset_loads(&pointer.offset)
                || pointer_offset_contains_contract_load(&load_pointer.offset, memory, pointer)
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            bitvector_contains_contract_load(left, memory, pointer)
                || bitvector_contains_contract_load(right, memory, pointer)
        }
        Bitvector32Term::BitwiseNot(value) => {
            bitvector_contains_contract_load(value, memory, pointer)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            condition_contains_contract_load(condition, memory, pointer)
                || bitvector_contains_contract_load(then_term, memory, pointer)
                || bitvector_contains_contract_load(else_term, memory, pointer)
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            bitvector_contains_contract_load(start, memory, pointer)
                || bitvector_contains_contract_load(end, memory, pointer)
                || bitvector_contains_contract_load(initial, memory, pointer)
                || bitvector_contains_contract_load(body, memory, pointer)
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .any(|argument| bitvector_contains_contract_load(argument, memory, pointer)),
    }
}

pub(in crate::lang::click) fn c_value_matches_kernel_type(value: &CValue, c_type: CType) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), CType::Int32)
            | (CValue::UInt8(_), CType::UInt8)
            | (
                CValue::Pointer(_),
                CType::Int32Pointer | CType::UInt8Pointer
            )
    )
}

pub(in crate::lang::click) fn symbolic_contract_memory_load(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
) -> Result<CValue, String> {
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
    );
    match value_type {
        CType::Void => Err("cannot symbolically load void".to_string()),
        CType::Int32 => Ok(CValue::Int32(load)),
        CType::UInt8 => Ok(CValue::UInt8(load)),
        CType::Int32Pointer | CType::UInt8Pointer => {
            symbolic_pointer_contract_memory_load(pointer, load, value_type)
        }
        CType::Int32Array(_) | CType::UInt8Array(_) => {
            Err(format!("cannot symbolically load {value_type:?}"))
        }
    }
}

fn symbolic_pointer_contract_memory_load(
    pointer: Pointer,
    bits: Bitvector32Term,
    value_type: CType,
) -> Result<CValue, String> {
    let pointee_byte_width = match value_type {
        CType::Int32Pointer => 4,
        CType::UInt8Pointer => 1,
        _ => {
            return Err(format!(
                "cannot symbolically load {value_type:?} as pointer"
            ));
        }
    };
    Ok(CValue::Pointer(Pointer {
        block: pointer.block,
        offset: scale_int32_offset(bits, i64::from(pointee_byte_width)),
    }))
}

pub(in crate::lang::click) fn evaluate_postcondition_add(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_add(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add pointer and `{offset:?}`")),
        (offset, CValue::Pointer(pointer)) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add `{offset:?}` and pointer")),
        (left, right) => Err(format!("cannot add `{left:?}` and `{right:?}`")),
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_sub(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_subtract(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => {
            let Some(index) = promoted_int32_term(&offset) else {
                return Err(format!("cannot subtract `{offset:?}` from pointer"));
            };
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(format!("cannot subtract `{right:?}` from `{left:?}`")),
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_multiply(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(bitvector32_multiply(left_term, right_term)))
    } else {
        Err(format!("cannot multiply `{left:?}` and `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_divide(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_divide(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot divide `{left:?}` by `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_remainder(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_remainder(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot compute `{left:?}` % `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_shift_left(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_left(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `<<` to `{left:?}` and `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_shift_right(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_right(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `>>` to `{left:?}` and `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_bitwise_binary(
    left: CValue,
    right: CValue,
    operator: &str,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(apply(left_term, right_term)))
    } else {
        Err(format!(
            "cannot apply `{operator}` to `{left:?}` and `{right:?}`"
        ))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_bitwise_not(
    value: CValue,
) -> Result<CValue, String> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(format!("cannot apply `~` to `{value:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_pointer_add(
    left: CValue,
    right: CValue,
) -> Result<Pointer, String> {
    match evaluate_postcondition_add(left, right)? {
        CValue::Pointer(pointer) => Ok(pointer),
        value => Err(format!(
            "index base did not evaluate to a pointer: `{value:?}`"
        )),
    }
}

pub(in crate::lang::click) fn offset_pointer_by_int32_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

pub(in crate::lang::click) fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
    element_width: u32,
) -> Pointer {
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(
            pointer.offset,
            scale_int32_offset(elements, i64::from(element_width)),
        ),
    }
}

pub(in crate::lang::click) fn add_pointer_offset(
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

pub(in crate::lang::click) fn scale_int32_offset(
    value: Bitvector32Term,
    byte_width: i64,
) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}
