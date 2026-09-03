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
    assumptions: &PureFactContext,
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
            // A negated condition is the condition with the other value,
            // as an execution spells the branch it did not take.
            proposition: match path.proposition {
                Proposition::ConditionIs(condition, value) => {
                    Proposition::ConditionIs(condition, !value)
                }
                proposition => Proposition::Not(Box::new(proposition)),
            },
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
                &PureFactContext::new(),
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<EvaluatedSpecResource>> {
    let (expressions, build): (Vec<SpecExpression>, SpecResourceBuilder) = match resource {
        SpecResource::Memory {
            base,
            start,
            end,
            element_width,
        } => {
            let element_width = *element_width;
            (
                vec![base.clone(), start.clone(), end.clone()],
                Box::new(move |values| match values.as_slice() {
                    [
                        CValue::Pointer(base),
                        CValue::Int32(start),
                        CValue::Int32(end),
                    ] => Some(CResource::Memory(CMemoryRange::new_with_element_width(
                        base.clone(),
                        start.clone(),
                        end.clone(),
                        element_width,
                    ))),
                    _ => None,
                }),
            )
        }
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
            // Terms are canonical at creation: the same segment lowered
            // anywhere is one proposition.
            let elements = canonical_subtract(end.clone(), start.clone());
            let mut discarded_facts = Vec::new();
            let start =
                crate::kernel::canonicalized_offset_index_term(start.clone(), &mut discarded_facts);
            let base = Pointer {
                block: base.block.clone(),
                offset: canonical_offset_sum(
                    base.offset.clone(),
                    canonical_scaled_offset(start, i64::from(element_width)),
                ),
            };
            Some(SpecPropositionPath {
                proposition: Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base,
                    bytes: canonical_multiply(elements, Bitvector32Term::Constant(element_width)),
                },
                facts: path.facts,
                obligations: path.obligations,
            })
        }
        _ => None,
    })
    .collect())
}

/// `left - right` with constants folded, a zero subtrahend dropped, equal
/// terms cancelled, and shared addends of two sums cancelled.
fn canonical_subtract(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        _ if left == right => Bitvector32Term::Constant(0),
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            canonical_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
    }
}

/// `left * right` with constants folded and unit and zero factors applied.
fn canonical_multiply(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_mul(*right))
        }
        (_, Bitvector32Term::Constant(1)) => left,
        (Bitvector32Term::Constant(1), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ => Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
    }
}

/// An element index scaled to bytes, folded when the index is a constant.
fn canonical_scaled_offset(value: Bitvector32Term, byte_width: i64) -> PointerOffsetTerm {
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

/// `left + right` on offsets with constants folded and zero addends dropped.
fn canonical_offset_sum(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

pub(super) fn lower_spec_binary_proposition_at_state(
    state: &CState,
    left: &SpecProposition,
    right: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    let left_paths = evaluate_spec_expression_paths_with_loop_entry(
        state,
        left,
        loop_entry_state,
        assumptions,
        budget,
    )?;
    let left_path_count = left_paths.len();
    let mut right_path_count = 0usize;
    let mut merge_failure_count = 0usize;
    for left_path in left_paths {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        let right_paths = evaluate_spec_expression_paths_with_loop_entry(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            budget,
        )?;
        right_path_count = right_path_count.saturating_add(right_paths.len());
        for right_path in right_paths {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                merge_failure_count = merge_failure_count.saturating_add(1);
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
    if paths.is_empty() && crate::instrumentation::enabled() {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
            format!(
                "spec comparison produced no paths: {left_path_count} left paths, {right_path_count} right paths, {merge_failure_count} inconsistent merges"
            ),
        ));
    }
    Ok(paths)
}

pub(super) fn lower_spec_predicate_proposition_at_state(
    state: &CState,
    name: &str,
    arguments: &[SpecPredicateArgument],
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = vec![SpecPropositionPath {
        proposition: Proposition::Predicate {
            name: name.to_string(),
            arguments: vec![Term::CState(state.resource_state_snapshot())],
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
    assumptions: &PureFactContext,
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
        SpecExpression::CountedResourceCount { name, arguments } => {
            let mut argument_paths = vec![(Vec::<Option<CValue>>::new(), Vec::new(), Vec::new())];
            for argument in arguments {
                let mut next = Vec::new();
                for (values, facts, obligations) in argument_paths {
                    let Some(argument) = argument else {
                        let mut next_values = values;
                        next_values.push(None);
                        next.push((next_values, facts, obligations));
                        continue;
                    };
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for argument_path in evaluate_spec_expression_paths_with_loop_entry(
                        state,
                        argument,
                        loop_entry_state,
                        &path_assumptions,
                        budget,
                    )? {
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &facts,
                                &obligations,
                                &argument_path.facts,
                                &argument_path.obligations,
                                assumptions,
                            )
                        else {
                            continue;
                        };
                        let mut next_values = values.clone();
                        next_values.push(Some(argument_path.value));
                        next.push((next_values, merged_facts, merged_obligations));
                    }
                }
                argument_paths = next;
            }
            argument_paths
                .into_iter()
                .map(|(arguments, facts, mut obligations)| {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    let mut total: Option<Bitvector32Term> = None;
                    for population in state.counted_populations().filter(|population| {
                        population.name == *name
                            && population.arguments.len() == arguments.len()
                            && population.arguments.iter().zip(&arguments).all(
                                |(actual, pattern)| {
                                    pattern.as_ref().is_none_or(|expected| {
                                        c_values_proven_equal_for_memory_resolution(
                                            actual,
                                            expected,
                                            &path_assumptions,
                                        )
                                    })
                                },
                            )
                    }) {
                        total = Some(if let Some(current) = total {
                            let overflow = ConditionTerm::signed_add_overflows(
                                current.clone(),
                                population.count.clone(),
                            );
                            let no_overflow = Proposition::ConditionIs(overflow, false);
                            if !path_assumptions.proves(&no_overflow) {
                                obligations.push(
                                    ProofObligation::verification_condition(no_overflow)
                                        .with_context("resource pattern count fits in int32"),
                                );
                            }
                            Bitvector32Term::add(current, population.count.clone())
                        } else {
                            population.count.clone()
                        });
                    }
                    SpecExpressionPath {
                        value: CValue::Int32(total.unwrap_or(Bitvector32Term::Constant(0))),
                        facts,
                        obligations,
                    }
                })
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
        SpecExpression::PureFunctionApplication { name, arguments } => {
            evaluate_spec_pure_function_application_paths(
                state,
                name,
                arguments,
                loop_entry_state,
                assumptions,
                budget,
            )?
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
                let mut facts = pointer_path.facts;
                let mut value = None;
                if let Some(stored) = memory.known_value(&pointer) {
                    value = canonicalized_pointer_value_from_int_cell(
                        &pointer,
                        &stored,
                        *value_type,
                        &mut budget.next_kernel_variable,
                        &mut facts,
                        assumptions,
                    )
                    .or_else(|| value_type.accepts(&stored).then_some(stored));
                }
                if value.is_none() {
                    value = canonicalized_symbolic_load_value(
                        memory,
                        &pointer,
                        *value_type,
                        &mut budget.next_kernel_variable,
                        &mut facts,
                        assumptions,
                    );
                }
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
                    facts,
                    obligations,
                });
            }
            paths
        }
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_spec_pure_function_application_paths(
    state: &CState,
    name: &str,
    arguments: &[SpecExpression],
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = vec![(Vec::new(), Vec::new(), Vec::new())];
    for argument in arguments {
        let mut next = Vec::new();
        for (values, facts, obligations) in paths {
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            for argument_path in evaluate_spec_expression_paths_with_loop_entry(
                state,
                argument,
                loop_entry_state,
                &path_assumptions,
                budget,
            )? {
                let CValue::Int32(value) = argument_path.value else {
                    continue;
                };
                if let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &argument_path.facts,
                        &argument_path.obligations,
                        assumptions,
                    )
                {
                    let mut merged_values = values.clone();
                    merged_values.push(value);
                    next.push((merged_values, merged_facts, merged_obligations));
                }
            }
        }
        paths = next;
    }
    Ok(paths
        .into_iter()
        .map(|(arguments, facts, obligations)| SpecExpressionPath {
            value: CValue::Int32(Bitvector32Term::PureFunctionApplication {
                name: name.to_string(),
                arguments,
            }),
            facts,
            obligations,
        })
        .collect())
}

pub(super) fn evaluate_spec_pointer_offset_paths(
    state: &CState,
    pointer: &SpecExpression,
    elements: &SpecExpression,
    byte_width: u32,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
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
            let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &pointer_path.facts,
                &pointer_path.obligations,
                &element_path.facts,
                &element_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let elements = canonicalized_offset_index_term(elements, &mut facts);
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    let left_step_width = spec_expression_pointer_step_width(state, left);
    let right_step_width = spec_expression_pointer_step_width(state, right);
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
                    state,
                    left_path.value.clone(),
                    right_path.value,
                    left_step_width,
                    right_step_width,
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

fn spec_expression_pointer_step_width(state: &CState, expression: &SpecExpression) -> Option<u32> {
    match expression {
        SpecExpression::CExpression(expression) => {
            c_expression_pointer_step_width(state, expression)
        }
        SpecExpression::PointerOffset { byte_width, .. } => Some(*byte_width),
        SpecExpression::Add(left, right) => spec_expression_pointer_step_width(state, left)
            .or_else(|| spec_expression_pointer_step_width(state, right)),
        SpecExpression::Subtract(left, _) => spec_expression_pointer_step_width(state, left),
        _ => None,
    }
}

pub(super) fn evaluate_spec_int32_binary_paths(
    state: &CState,
    left: &SpecExpression,
    right: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
        (CValue::Pointer(left), CValue::Pointer(right)) => match operator {
            CComparisonOperator::Equal => Some((
                pointer_equality_condition(left.clone(), right.clone()),
                true,
            )),
            CComparisonOperator::NotEqual => Some((
                pointer_equality_condition(left.clone(), right.clone()),
                false,
            )),
            CComparisonOperator::LessThan
            | CComparisonOperator::LessEqual
            | CComparisonOperator::GreaterThan
            | CComparisonOperator::GreaterEqual
                if left.block == right.block =>
            {
                let left = byte_offset_from_pointer_offset(&left.offset)?;
                let right = byte_offset_from_pointer_offset(&right.offset)?;
                Some((pointer_order_condition(left, right, operator), true))
            }
            CComparisonOperator::LessThan
            | CComparisonOperator::LessEqual
            | CComparisonOperator::GreaterThan
            | CComparisonOperator::GreaterEqual => None,
        },
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            match operator {
                CComparisonOperator::Equal => {
                    Some((pointer_is_null_condition(pointer.clone()), true))
                }
                CComparisonOperator::NotEqual => {
                    Some((pointer_is_null_condition(pointer.clone()), false))
                }
                CComparisonOperator::LessThan
                | CComparisonOperator::LessEqual
                | CComparisonOperator::GreaterThan
                | CComparisonOperator::GreaterEqual => None,
            }
        }
        _ => None,
    };
    if let Some((condition, value)) = pointer_condition {
        return Some(Proposition::ConditionIs(condition, value));
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
        CValue::Void | CValue::Pointer(_) => None,
    }
}
