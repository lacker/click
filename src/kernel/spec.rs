use super::prelude::*;

type EvaluatedSpecResource = (CResource, Vec<ExecutionPureFact>, Vec<ProofObligation>);
type SpecResourceBuilder = Box<dyn Fn(Vec<CValue>) -> Option<CResource>>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SpecPropositionPath {
    pub(super) proposition: Proposition,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SpecExpressionPath {
    pub(super) value: CValue,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

pub(super) fn lower_spec_proposition_at_state_with_loop_entry(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    match proposition {
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => lower_spec_comparison_proposition_at_state(
            state,
            left,
            *operator,
            right,
            loop_entry_state,
            assumptions,
            budget,
        ),
        SpecProposition::And(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_spec_proposition_at_state_with_loop_entry(
                state,
                left,
                loop_entry_state,
                assumptions,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in lower_spec_proposition_at_state_with_loop_entry(
                    state,
                    right,
                    loop_entry_state,
                    &right_assumptions,
                    budget,
                )? {
                    if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &left_path.facts,
                        &left_path.obligations,
                        &right_path.facts,
                        &right_path.obligations,
                        assumptions,
                    ) {
                        paths.push(SpecPropositionPath {
                            proposition: Proposition::And(
                                Box::new(left_path.proposition.clone()),
                                Box::new(right_path.proposition),
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
            }
            Ok(paths)
        }
        SpecProposition::Or(left, right) => lower_spec_binary_proposition_at_state(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right| Proposition::Or(Box::new(left), Box::new(right)),
        ),
        SpecProposition::Not(body) => Ok(lower_spec_proposition_at_state_with_loop_entry(
            state,
            body,
            loop_entry_state,
            assumptions,
            budget,
        )?
        .into_iter()
        .map(|path| SpecPropositionPath {
            proposition: Proposition::Not(Box::new(path.proposition)),
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect()),
        SpecProposition::Implies(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_spec_proposition_at_state_with_loop_entry(
                state,
                left,
                loop_entry_state,
                assumptions,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                )
                .assume_proposition(left_path.proposition.clone());
                for right_path in lower_spec_proposition_at_state_with_loop_entry(
                    state,
                    right,
                    loop_entry_state,
                    &right_assumptions,
                    budget,
                )? {
                    let guarded_right_obligations = right_path
                        .obligations
                        .iter()
                        .cloned()
                        .map(|obligation| {
                            let antecedent = left_path.proposition.clone();
                            obligation.map_proposition(|proposition| {
                                Proposition::Implies(Box::new(antecedent), Box::new(proposition))
                            })
                        })
                        .collect::<Vec<_>>();
                    if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &left_path.facts,
                        &left_path.obligations,
                        &right_path.facts,
                        &guarded_right_obligations,
                        assumptions,
                    ) {
                        paths.push(SpecPropositionPath {
                            proposition: Proposition::Implies(
                                Box::new(left_path.proposition.clone()),
                                Box::new(right_path.proposition),
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
            }
            Ok(paths)
        }
        SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } => {
            let mut state = state.clone();
            state
                .locals
                .set(name.clone(), int32(Bitvector32Term::Variable(*variable)));
            Ok(lower_spec_proposition_at_state_with_loop_entry(
                &state,
                body,
                loop_entry_state,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPropositionPath {
                proposition: Proposition::ForAll {
                    var: *variable,
                    sort: Sort::CInt32,
                    body: Box::new(wrap_path_context(path.proposition, &path.facts, &[])),
                },
                // Path facts may mention the bound variable. They are guards
                // on this quantified path, not facts in the surrounding
                // context.
                facts: Vec::new(),
                obligations: path
                    .obligations
                    .into_iter()
                    .map(|obligation| {
                        obligation.map_proposition(|proposition| Proposition::ForAll {
                            var: *variable,
                            sort: Sort::CInt32,
                            body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                        })
                    })
                    .collect(),
            })
            .collect())
        }
        SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } => {
            let mut state = state.clone();
            state
                .locals
                .set(name.clone(), int32(Bitvector32Term::Variable(*variable)));
            Ok(lower_spec_proposition_at_state_with_loop_entry(
                &state,
                body,
                loop_entry_state,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPropositionPath {
                proposition: Proposition::Exists {
                    name: name.clone(),
                    var: *variable,
                    sort: Sort::CInt32,
                    body: Box::new(path.proposition),
                },
                facts: path.facts,
                obligations: path
                    .obligations
                    .into_iter()
                    .map(|obligation| {
                        obligation.map_proposition(|proposition| Proposition::Exists {
                            name: name.clone(),
                            var: *variable,
                            sort: Sort::CInt32,
                            body: Box::new(proposition),
                        })
                    })
                    .collect(),
            })
            .collect())
        }
        SpecProposition::Predicate { name, arguments } => {
            lower_spec_predicate_proposition_at_state(
                state,
                name,
                arguments,
                loop_entry_state,
                assumptions,
                budget,
            )
        }
        SpecProposition::ResourceSeparate { left, right } => lower_spec_resource_relation_at_state(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right| Proposition::CResourceSeparate { left, right },
        ),
        SpecProposition::ResourceContains { parent, child } => {
            lower_spec_resource_relation_at_state(
                state,
                parent,
                child,
                loop_entry_state,
                assumptions,
                budget,
                |parent, child| Proposition::CResourceContains { parent, child },
            )
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            element_width,
        } => lower_spec_memory_loadable_at_state(
            state,
            memory,
            base,
            start,
            end,
            *element_width,
            loop_entry_state,
            assumptions,
            budget,
        ),
        SpecProposition::Defined(expression) => {
            let paths = evaluate_spec_expression_paths_with_loop_entry(
                state,
                expression,
                loop_entry_state,
                &Assumptions::new(),
                budget,
            )?;
            let mut normal_paths = paths.into_iter().map(|path| {
                proposition_and_all(
                    path.facts
                        .into_iter()
                        .map(|fact| fact.proposition().clone())
                        .chain(
                            path.obligations
                                .into_iter()
                                .map(|obligation| obligation.proposition().clone()),
                        )
                        .collect(),
                )
            });
            let proposition = normal_paths.next().map_or_else(
                || Proposition::ConditionIs(ConditionTerm::Constant(false), true),
                |first| {
                    normal_paths.fold(first, |left, right| {
                        Proposition::Or(Box::new(left), Box::new(right))
                    })
                },
            );
            Ok(vec![SpecPropositionPath {
                proposition,
                facts: Vec::new(),
                obligations: Vec::new(),
            }])
        }
    }
}

#[derive(Clone)]
struct SpecValuesPath {
    values: Vec<CValue>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

fn evaluate_spec_values_at_state(
    state: &CState,
    expressions: &[SpecExpression],
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecValuesPath>> {
    let mut paths = vec![SpecValuesPath {
        values: Vec::new(),
        facts: Vec::new(),
        obligations: Vec::new(),
    }];
    for expression in expressions {
        let mut next_paths = Vec::new();
        for prefix in paths {
            let path_assumptions =
                assumptions_with_path_context(assumptions, &prefix.facts, &prefix.obligations);
            for value_path in evaluate_spec_expression_paths_with_loop_entry(
                state,
                expression,
                loop_entry_state,
                &path_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &prefix.facts,
                    &prefix.obligations,
                    &value_path.facts,
                    &value_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                let mut values = prefix.values.clone();
                values.push(value_path.value);
                next_paths.push(SpecValuesPath {
                    values,
                    facts,
                    obligations,
                });
            }
        }
        paths = next_paths;
    }
    Ok(paths)
}

fn evaluate_spec_resource_at_state(
    state: &CState,
    resource: &SpecResource,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<EvaluatedSpecResource>> {
    let (expressions, build): (Vec<SpecExpression>, SpecResourceBuilder) = match resource {
        SpecResource::Memory { base, start, end } => (
            vec![base.clone(), start.clone(), end.clone()],
            Box::new(|values| match values.as_slice() {
                [
                    CValue::Pointer(base),
                    CValue::Int32(start),
                    CValue::Int32(end),
                ] => Some(CResource::Memory(CMemoryRange::new(
                    base.clone(),
                    start.clone(),
                    end.clone(),
                ))),
                _ => None,
            }),
        ),
        SpecResource::Composite { name, arguments } => {
            let name = name.clone();
            (
                arguments.clone(),
                Box::new(move |arguments| {
                    Some(CResource::Composite {
                        name: name.clone(),
                        arguments,
                    })
                }),
            )
        }
        SpecResource::Token { name, arguments } => {
            let name = name.clone();
            (
                arguments.clone(),
                Box::new(move |arguments| {
                    Some(CResource::Token {
                        name: name.clone(),
                        arguments,
                    })
                }),
            )
        }
    };
    Ok(
        evaluate_spec_values_at_state(state, &expressions, loop_entry_state, assumptions, budget)?
            .into_iter()
            .filter_map(|path| {
                build(path.values).map(|resource| (resource, path.facts, path.obligations))
            })
            .collect(),
    )
}

fn lower_spec_resource_relation_at_state(
    state: &CState,
    left: &SpecResource,
    right: &SpecResource,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    relation: impl Fn(CResource, CResource) -> Proposition,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for (left, left_facts, left_obligations) in
        evaluate_spec_resource_at_state(state, left, loop_entry_state, assumptions, budget)?
    {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for (right, right_facts, right_obligations) in evaluate_spec_resource_at_state(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_facts,
                &right_obligations,
                assumptions,
            ) else {
                continue;
            };
            paths.push(SpecPropositionPath {
                proposition: relation(left.clone(), right),
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

#[allow(clippy::too_many_arguments)]
fn lower_spec_memory_loadable_at_state(
    state: &CState,
    memory: &SpecMemory,
    base: &SpecExpression,
    start: &SpecExpression,
    end: &SpecExpression,
    element_width: u32,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let memory = match memory {
        SpecMemory::Current => state.memory(),
        SpecMemory::FunctionEntry | SpecMemory::LoopEntry => match loop_entry_state {
            Some(entry) => entry.memory(),
            None => return Ok(Vec::new()),
        },
        SpecMemory::Fixed(memory) => memory,
    };
    Ok(evaluate_spec_values_at_state(
        state,
        &[base.clone(), start.clone(), end.clone()],
        loop_entry_state,
        assumptions,
        budget,
    )?
    .into_iter()
    .filter_map(|path| match path.values.as_slice() {
        [
            CValue::Pointer(base),
            CValue::Int32(start),
            CValue::Int32(end),
        ] => {
            let elements =
                Bitvector32Term::Subtract(Box::new(end.clone()), Box::new(start.clone()));
            let base = Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Add(
                    Box::new(base.offset.clone()),
                    Box::new(PointerOffsetTerm::Int32Scaled {
                        value: Box::new(start.clone()),
                        byte_width: i64::from(element_width),
                    }),
                ),
            };
            Some(SpecPropositionPath {
                proposition: Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base,
                    bytes: Bitvector32Term::Multiply(
                        Box::new(elements),
                        Box::new(Bitvector32Term::Constant(element_width)),
                    ),
                },
                facts: path.facts,
                obligations: path.obligations,
            })
        }
        _ => None,
    })
    .collect())
}

pub(super) fn lower_spec_binary_proposition_at_state(
    state: &CState,
    left: &SpecProposition,
    right: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    combine: impl Fn(Proposition, Proposition) -> Proposition,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in lower_spec_proposition_at_state_with_loop_entry(
        state,
        left,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in lower_spec_proposition_at_state_with_loop_entry(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            budget,
        )? {
            if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) {
                paths.push(SpecPropositionPath {
                    proposition: combine(left_path.proposition.clone(), right_path.proposition),
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

pub(super) fn lower_spec_comparison_proposition_at_state(
    state: &CState,
    left: &SpecExpression,
    operator: CComparisonOperator,
    right: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_spec_expression_paths_with_loop_entry(
        state,
        left,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_expression_paths_with_loop_entry(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            if let Some(proposition) =
                c_value_comparison_proposition(&left_path.value, operator, &right_path.value)
            {
                paths.push(SpecPropositionPath {
                    proposition,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

pub(super) fn lower_spec_predicate_proposition_at_state(
    state: &CState,
    name: &str,
    arguments: &[SpecPredicateArgument],
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = vec![SpecPropositionPath {
        proposition: Proposition::Predicate {
            name: name.to_string(),
            arguments: Vec::new(),
        },
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let (expression, memory) = match argument {
            SpecPredicateArgument::Value(expression) => (expression, None),
            SpecPredicateArgument::ArrayRef { memory, pointer } => (pointer, Some(memory)),
        };
        let argument_paths = evaluate_spec_expression_paths_with_loop_entry(
            state,
            expression,
            loop_entry_state,
            assumptions,
            budget,
        )?;
        let mut next_paths = Vec::new();
        for prefix_path in paths {
            let path_assumptions = assumptions_with_path_context(
                assumptions,
                &prefix_path.facts,
                &prefix_path.obligations,
            );
            for argument_path in &argument_paths {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &prefix_path.facts,
                    &prefix_path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    &path_assumptions,
                ) else {
                    continue;
                };
                let Proposition::Predicate {
                    name,
                    mut arguments,
                } = prefix_path.proposition.clone()
                else {
                    unreachable!("predicate lowering should carry predicate propositions")
                };
                if let Some(memory) = memory {
                    let memory = match memory {
                        SpecMemory::Current => state.memory(),
                        SpecMemory::FunctionEntry | SpecMemory::LoopEntry => {
                            let Some(entry_state) = loop_entry_state else {
                                continue;
                            };
                            entry_state.memory()
                        }
                        SpecMemory::Fixed(memory) => memory,
                    };
                    arguments.push(Term::CMemory(memory.clone()));
                }
                arguments.push(Term::CValue(argument_path.value.clone()));
                next_paths.push(SpecPropositionPath {
                    proposition: Proposition::Predicate { name, arguments },
                    facts,
                    obligations,
                });
            }
        }
        paths = next_paths;
    }

    Ok(paths)
}

pub(super) fn evaluate_spec_expression_paths_with_loop_entry(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        SpecExpression::Value(value) => vec![SpecExpressionPath {
            value: value.clone(),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        SpecExpression::CExpression(expression) => {
            evaluate_c_expression_paths(state, expression, assumptions, budget)?
                .into_iter()
                .filter_map(c_expression_path_value)
                .collect()
        }
        SpecExpression::Add(left, right) => {
            evaluate_spec_add_paths(state, left, right, loop_entry_state, assumptions, budget)?
        }
        SpecExpression::Subtract(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_subtract(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::Multiply(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_multiply(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::Divide(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_divide(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::Remainder(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_remainder(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::ShiftLeft(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::ShiftRight(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::BitwiseAnd(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_total_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    Bitvector32Term::bitwise_and,
                )
            },
        )?,
        SpecExpression::BitwiseOr(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_total_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    Bitvector32Term::bitwise_or,
                )
            },
        )?,
        SpecExpression::BitwiseXor(left, right) => evaluate_spec_int32_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_total_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    Bitvector32Term::bitwise_xor,
                )
            },
        )?,
        SpecExpression::BitwiseNot(expression) => evaluate_spec_int32_unary_paths(
            state,
            expression,
            loop_entry_state,
            assumptions,
            budget,
            Bitvector32Term::bitwise_not,
        )?,
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => evaluate_spec_if_paths(
            state,
            condition,
            then_branch,
            else_branch,
            loop_entry_state,
            assumptions,
            budget,
        )?,
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => evaluate_spec_range_fold_paths(
            state,
            start,
            end,
            initial,
            accumulator,
            item,
            body,
            loop_entry_state,
            assumptions,
            budget,
        )?,
        SpecExpression::Let { name, value, body } => {
            let mut paths = Vec::new();
            for value_path in evaluate_spec_expression_paths_with_loop_entry(
                state,
                value,
                loop_entry_state,
                assumptions,
                budget,
            )? {
                let mut body_state = state.clone();
                body_state
                    .locals
                    .set(name.clone(), value_path.value.clone());
                let body_assumptions = assumptions_with_path_context(
                    assumptions,
                    &value_path.facts,
                    &value_path.obligations,
                );
                for body_path in evaluate_spec_expression_paths_with_loop_entry(
                    &body_state,
                    body,
                    loop_entry_state,
                    &body_assumptions,
                    budget,
                )? {
                    if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &value_path.facts,
                        &value_path.obligations,
                        &body_path.facts,
                        &body_path.obligations,
                        assumptions,
                    ) {
                        paths.push(SpecExpressionPath {
                            value: body_path.value,
                            facts,
                            obligations,
                        });
                    }
                }
            }
            paths
        }
        SpecExpression::LoopEntrySnapshot(expression) => {
            if let Some(loop_entry_state) = loop_entry_state {
                evaluate_spec_expression_paths_with_loop_entry(
                    loop_entry_state,
                    expression,
                    Some(loop_entry_state),
                    assumptions,
                    budget,
                )?
            } else {
                Vec::new()
            }
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => evaluate_spec_pointer_offset_paths(
            state,
            pointer,
            elements,
            *byte_width,
            loop_entry_state,
            assumptions,
            budget,
        )?,
        SpecExpression::MemoryLoad {
            memory,
            pointer,
            value_type,
        } => {
            let mut paths = Vec::new();
            for pointer_path in evaluate_spec_expression_paths_with_loop_entry(
                state,
                pointer,
                loop_entry_state,
                assumptions,
                budget,
            )? {
                let CValue::Pointer(pointer) = pointer_path.value else {
                    continue;
                };
                let memory = match memory {
                    SpecMemory::Current => state.memory(),
                    SpecMemory::FunctionEntry => match loop_entry_state {
                        Some(entry_state) => entry_state.memory(),
                        None => continue,
                    },
                    SpecMemory::LoopEntry => match loop_entry_state {
                        Some(loop_entry_state) => loop_entry_state.memory(),
                        None => continue,
                    },
                    SpecMemory::Fixed(memory) => memory,
                };
                let value = memory
                    .known_value(&pointer)
                    .and_then(|stored| {
                        symbolic_pointer_value_from_int_cell(&pointer, &stored, *value_type)
                            .or_else(|| value_type.accepts(&stored).then_some(stored))
                    })
                    .or_else(|| symbolic_load_value(memory, &pointer, *value_type));
                let Some(value) = value else {
                    continue;
                };
                let mut obligations = pointer_path.obligations;
                if !memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
                    let loadable = Proposition::CMemoryLoadable {
                        memory: memory.clone(),
                        base: pointer,
                        bytes: Bitvector32Term::Constant(value_type.byte_width()),
                    };
                    if add_proof_obligation(&mut obligations, assumptions, loadable).is_none() {
                        continue;
                    }
                }
                paths.push(SpecExpressionPath {
                    value,
                    facts: pointer_path.facts,
                    obligations,
                });
            }
            paths
        }
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn evaluate_spec_pointer_offset_paths(
    state: &CState,
    pointer: &SpecExpression,
    elements: &SpecExpression,
    byte_width: u32,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for pointer_path in evaluate_spec_expression_paths_with_loop_entry(
        state,
        pointer,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let CValue::Pointer(pointer) = pointer_path.value else {
            continue;
        };
        let element_assumptions = assumptions_with_path_context(
            assumptions,
            &pointer_path.facts,
            &pointer_path.obligations,
        );
        for element_path in evaluate_spec_expression_paths_with_loop_entry(
            state,
            elements,
            loop_entry_state,
            &element_assumptions,
            budget,
        )? {
            let CValue::Int32(elements) = element_path.value else {
                continue;
            };
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &pointer_path.facts,
                &pointer_path.obligations,
                &element_path.facts,
                &element_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            paths.push(SpecExpressionPath {
                value: CValue::Pointer(pointer.offset_by_elements(elements, byte_width)),
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

pub(super) fn c_expression_path_value(path: CExpressionPath) -> Option<SpecExpressionPath> {
    let CExpressionOutcome::Value(value) = path.outcome else {
        return None;
    };
    Some(SpecExpressionPath {
        value,
        facts: path.facts,
        obligations: path.obligations,
    })
}

pub(super) fn evaluate_spec_add_paths(
    state: &CState,
    left: &SpecExpression,
    right: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_spec_expression_paths_with_loop_entry(
        state,
        left,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_expression_paths_with_loop_entry(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            paths.extend(
                apply_c_add(
                    left_path.value.clone(),
                    right_path.value,
                    None,
                    None,
                    facts,
                    obligations,
                    assumptions,
                )
                .into_iter()
                .filter_map(c_expression_path_value),
            );
        }
    }
    Ok(paths)
}

pub(super) fn evaluate_spec_int32_binary_paths(
    state: &CState,
    left: &SpecExpression,
    right: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    apply: impl Fn(
        Bitvector32Term,
        Bitvector32Term,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    ) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_spec_expression_paths_with_loop_entry(
        state,
        left,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let mut left_facts = left_path.facts;
        let Some(left) = promote_c_int32_path_value(left_path.value, &mut left_facts, assumptions)
        else {
            continue;
        };
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_path.obligations);
        for right_path in evaluate_spec_expression_paths_with_loop_entry(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let mut facts = facts;
            let Some(right) = promote_c_int32_path_value(right_path.value, &mut facts, assumptions)
            else {
                continue;
            };
            paths.extend(
                apply(left.clone(), right, facts, obligations)
                    .into_iter()
                    .filter_map(c_expression_path_value),
            );
        }
    }
    Ok(paths)
}

pub(super) fn evaluate_spec_int32_unary_paths(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    apply: fn(Bitvector32Term) -> Bitvector32Term,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_spec_expression_paths_with_loop_entry(
        state,
        expression,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let mut facts = path.facts;
        let Some(value) = promote_c_int32_path_value(path.value, &mut facts, assumptions) else {
            continue;
        };
        paths.push(SpecExpressionPath {
            value: int32(apply(value)),
            facts,
            obligations: path.obligations,
        });
    }
    Ok(paths)
}

pub(super) fn evaluate_spec_if_paths(
    state: &CState,
    condition: &SpecProposition,
    then_branch: &SpecExpression,
    else_branch: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for condition_path in lower_spec_proposition_at_state_with_loop_entry(
        state,
        condition,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let branch_assumptions = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        let condition_truth = if branch_assumptions.proves(&condition_path.proposition) {
            Some(true)
        } else if assumptions_prove_proposition_false(
            &branch_assumptions,
            &condition_path.proposition,
        ) {
            Some(false)
        } else {
            None
        };

        let branch_paths = match condition_truth {
            Some(true) => evaluate_spec_expression_paths_with_loop_entry(
                state,
                then_branch,
                loop_entry_state,
                &branch_assumptions,
                budget,
            )?,
            Some(false) => evaluate_spec_expression_paths_with_loop_entry(
                state,
                else_branch,
                loop_entry_state,
                &branch_assumptions,
                budget,
            )?,
            None => {
                let then_paths = evaluate_spec_expression_paths_with_loop_entry(
                    state,
                    then_branch,
                    loop_entry_state,
                    &branch_assumptions,
                    budget,
                )?;
                let else_paths = evaluate_spec_expression_paths_with_loop_entry(
                    state,
                    else_branch,
                    loop_entry_state,
                    &branch_assumptions,
                    budget,
                )?;
                let mut branch_paths = Vec::new();
                for then_path in then_paths {
                    for else_path in &else_paths {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &then_path.facts,
                            &then_path.obligations,
                            &else_path.facts,
                            &else_path.obligations,
                            &branch_assumptions,
                        ) else {
                            continue;
                        };
                        let Some(value) = conditional_spec_value(
                            &condition_path.proposition,
                            then_path.value.clone(),
                            else_path.value.clone(),
                        ) else {
                            continue;
                        };
                        branch_paths.push(SpecExpressionPath {
                            value,
                            facts,
                            obligations,
                        });
                    }
                }
                branch_paths
            }
        };

        for branch_path in branch_paths {
            if let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &condition_path.facts,
                &condition_path.obligations,
                &branch_path.facts,
                &branch_path.obligations,
                assumptions,
            ) {
                paths.push(SpecExpressionPath {
                    value: branch_path.value,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

pub(super) fn evaluate_spec_range_fold_paths(
    state: &CState,
    start: &SpecExpression,
    end: &SpecExpression,
    initial: &SpecExpression,
    accumulator: &str,
    item: &str,
    body: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for start_path in evaluate_spec_expression_paths_with_loop_entry(
        state,
        start,
        loop_entry_state,
        assumptions,
        budget,
    )? {
        let CValue::Int32(start) = start_path.value else {
            continue;
        };
        let start_assumptions =
            assumptions_with_path_context(assumptions, &start_path.facts, &start_path.obligations);
        for end_path in evaluate_spec_expression_paths_with_loop_entry(
            state,
            end,
            loop_entry_state,
            &start_assumptions,
            budget,
        )? {
            let CValue::Int32(end) = end_path.value else {
                continue;
            };
            let Some((bound_facts, bound_obligations)) = merge_execution_pure_facts_and_obligations(
                &start_path.facts,
                &start_path.obligations,
                &end_path.facts,
                &end_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let bound_assumptions =
                assumptions_with_path_context(assumptions, &bound_facts, &bound_obligations);
            for initial_path in evaluate_spec_expression_paths_with_loop_entry(
                state,
                initial,
                loop_entry_state,
                &bound_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &bound_facts,
                    &bound_obligations,
                    &initial_path.facts,
                    &initial_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                let Some(path) = evaluate_spec_range_fold_body_path(
                    state,
                    start.clone(),
                    end.clone(),
                    initial_path.value,
                    accumulator,
                    item,
                    body,
                    facts,
                    obligations,
                    loop_entry_state,
                    assumptions,
                    budget,
                )?
                else {
                    continue;
                };
                paths.push(path);
            }
        }
    }
    Ok(paths)
}

pub(super) fn evaluate_spec_range_fold_body_path(
    state: &CState,
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body: &SpecExpression,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    loop_entry_state: Option<&CState>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<SpecExpressionPath>> {
    match (start.as_const(), end.as_const()) {
        (Some(start), Some(end)) => {
            let mut value = initial;
            let mut facts = facts;
            let mut obligations = obligations;
            for index in concrete_spec_fold_range(start as i32, end as i32) {
                let mut body_state = state.clone();
                body_state.locals.set(accumulator.to_string(), value);
                body_state.locals.set(item.to_string(), int32(index as u32));
                let body_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let mut body_paths = evaluate_spec_expression_paths_with_loop_entry(
                    &body_state,
                    body,
                    loop_entry_state,
                    &body_assumptions,
                    budget,
                )?;
                let Some(body_path) = body_paths.pop() else {
                    return Ok(None);
                };
                if !body_paths.is_empty() {
                    return Ok(None);
                }
                let Some((next_facts, next_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &body_path.facts,
                        &body_path.obligations,
                        assumptions,
                    )
                else {
                    return Ok(None);
                };
                value = body_path.value;
                facts = next_facts;
                obligations = next_obligations;
            }
            Ok(Some(SpecExpressionPath {
                value,
                facts,
                obligations,
            }))
        }
        _ => {
            let mut body_state = state.clone();
            body_state.locals.set(
                accumulator.to_string(),
                int32(Bitvector32Term::Variable(spec_fold_bound_variable(
                    accumulator,
                    0,
                ))),
            );
            body_state.locals.set(
                item.to_string(),
                int32(Bitvector32Term::Variable(spec_fold_bound_variable(item, 1))),
            );
            let body_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            let mut body_paths = evaluate_spec_expression_paths_with_loop_entry(
                &body_state,
                body,
                loop_entry_state,
                &body_assumptions,
                budget,
            )?;
            let Some(body_path) = body_paths.pop() else {
                return Ok(None);
            };
            if !body_paths.is_empty() {
                return Ok(None);
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &facts,
                &obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                return Ok(None);
            };
            let Some(value) = symbolic_spec_range_fold_value(
                start,
                end,
                initial,
                accumulator,
                item,
                body_path.value,
            ) else {
                return Ok(None);
            };
            Ok(Some(SpecExpressionPath {
                value,
                facts,
                obligations,
            }))
        }
    }
}

pub(super) fn concrete_spec_fold_range(start: i32, end: i32) -> std::ops::Range<i32> {
    if start <= end {
        start..end
    } else {
        start..start
    }
}

pub(super) fn spec_fold_bound_variable(name: &str, salt: u64) -> Variable {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ salt;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x1000_0000_01b3);
    }
    Variable(3_000_000 + (hash % 1_000_000_000))
}

pub(super) fn symbolic_spec_range_fold_value(
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body_value: CValue,
) -> Option<CValue> {
    let CValue::Int32(initial) = initial else {
        return None;
    };
    let CValue::Int32(body) = body_value else {
        return None;
    };
    Some(CValue::Int32(Bitvector32Term::range_fold(
        start,
        end,
        initial,
        spec_fold_bound_variable(accumulator, 0),
        spec_fold_bound_variable(item, 1),
        body,
    )))
}

pub(super) fn conditional_spec_value(
    proposition: &Proposition,
    then_value: CValue,
    else_value: CValue,
) -> Option<CValue> {
    if then_value == else_value {
        return Some(then_value);
    }
    let (condition, expected) = proposition_as_single_condition(proposition)?;
    let (CValue::Int32(then_term), CValue::Int32(else_term)) = (then_value, else_value) else {
        return None;
    };
    let (then_term, else_term) = if expected {
        (then_term, else_term)
    } else {
        (else_term, then_term)
    };
    Some(CValue::Int32(Bitvector32Term::if_then_else(
        condition, then_term, else_term,
    )))
}

pub(super) fn proposition_as_single_condition(
    proposition: &Proposition,
) -> Option<(ConditionTerm, bool)> {
    match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Not(body) => {
            let Proposition::ConditionIs(condition, value) = body.as_ref() else {
                return None;
            };
            Some((condition.clone(), !*value))
        }
        _ => None,
    }
}

pub(super) fn assumptions_prove_proposition_false(
    assumptions: &Assumptions,
    proposition: &Proposition,
) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !*value))
        }
        _ => assumptions.proves(&Proposition::Not(Box::new(proposition.clone()))),
    }
}

pub(super) fn c_value_comparison_proposition(
    left: &CValue,
    operator: CComparisonOperator,
    right: &CValue,
) -> Option<Proposition> {
    let pointer_condition = match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            Some(pointer_equality_condition(left.clone(), right.clone()))
        }
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            Some(pointer_is_null_condition(pointer.clone()))
        }
        _ => None,
    };
    if let Some(condition) = pointer_condition {
        return match operator {
            CComparisonOperator::Equal => Some(Proposition::ConditionIs(condition, true)),
            CComparisonOperator::NotEqual => Some(Proposition::ConditionIs(condition, false)),
            CComparisonOperator::LessThan
            | CComparisonOperator::LessEqual
            | CComparisonOperator::GreaterThan
            | CComparisonOperator::GreaterEqual => None,
        };
    }

    let left = c_value_int32_term(left)?;
    let right = c_value_int32_term(right)?;
    let (condition, value) = match operator {
        CComparisonOperator::Equal => (ConditionTerm::equal(left, right), true),
        CComparisonOperator::NotEqual => (ConditionTerm::equal(left, right), false),
        CComparisonOperator::LessThan => (ConditionTerm::signed_less_than(left, right), true),
        CComparisonOperator::LessEqual => (ConditionTerm::signed_less_equal(left, right), true),
        CComparisonOperator::GreaterThan => (ConditionTerm::signed_greater_than(left, right), true),
        CComparisonOperator::GreaterEqual => {
            (ConditionTerm::signed_greater_equal(left, right), true)
        }
    };
    Some(Proposition::ConditionIs(condition, value))
}

fn c_value_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(value) | CValue::UInt8(value) => Some(value.clone()),
        CValue::Pointer(_) => None,
    }
}
