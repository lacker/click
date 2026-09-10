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

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecSequencePath {
    value: SequenceTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecAlgebraicPath {
    value: AlgebraicTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

/// Capture a symbolic ADT value without admitting case assumptions or
/// unresolved memory reads into a resource initializer.
pub(crate) fn capture_spec_algebraic_value(
    state: &CState,
    expression: &SpecAlgebraicExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<AlgebraicTerm, String> {
    let paths = evaluate_spec_algebraic_at_state_with_bindings(
        state,
        expression,
        entry_state,
        assumptions,
        &BTreeMap::new(),
        &mut ExecutionBudget::default(),
    )
    .map_err(|limit| format!("algebraic initializer evaluation hit {limit:?}"))?;
    let [path] = paths.as_slice() else {
        return Err("algebraic initializer must denote one symbolic value".into());
    };
    if !path.facts.is_empty()
        || path
            .obligations
            .iter()
            .any(|o| !assumptions.proves(o.proposition()))
    {
        return Err("algebraic initializer has unproved evaluation obligations".into());
    }
    Ok(path.value.clone())
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecAlgebraicCasePath {
    variant: String,
    fields: Vec<AlgebraicValue>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecAlgebraicValuePath {
    value: AlgebraicValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecPureFunctionArgumentPath {
    value: PureFunctionArgument,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

pub(super) fn lower_spec_proposition_at_state_with_loop_entry(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    lower_spec_proposition_at_state_with_algebraic_bindings(
        state,
        proposition,
        loop_entry_state,
        assumptions,
        &BTreeMap::new(),
        budget,
    )
}

pub(in crate::kernel) fn lower_spec_proposition_at_state_without_range_guards(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    // Composite-resource population setup uses loadability as an opaque
    // symbolic summary. Public contract requirements and ensures use the
    // ordinary lowering path below, which attaches the range validity
    // obligations before the resulting bytes term can be consumed.
    let SpecProposition::MemoryLoadable {
        memory,
        base,
        start,
        end,
        element_width,
    } = proposition
    else {
        return lower_spec_proposition_at_state_with_algebraic_bindings(
            state,
            proposition,
            loop_entry_state,
            assumptions,
            &BTreeMap::new(),
            budget,
        );
    };
    lower_spec_memory_loadable_at_state(
        state,
        memory,
        base,
        start,
        end,
        *element_width,
        loop_entry_state,
        assumptions,
        &BTreeMap::new(),
        budget,
        false,
    )
}

pub(in crate::kernel) fn lower_spec_proposition_at_state_with_algebraic_bindings(
    state: &CState,
    proposition: &SpecProposition,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    match proposition {
        SpecProposition::IntegerComparison {
            left,
            operator,
            right,
        } => {
            let left = lower_spec_integer_expression(left, budget)?;
            let right = lower_spec_integer_expression(right, budget)?;
            let condition = match operator {
                IntegerComparisonOperator::Equal => ConditionTerm::integer_equal(left, right),
                IntegerComparisonOperator::NotEqual => {
                    ConditionTerm::integer_not_equal(left, right)
                }
                IntegerComparisonOperator::LessThan => {
                    ConditionTerm::integer_less_than(left, right)
                }
                IntegerComparisonOperator::LessEqual => {
                    ConditionTerm::integer_less_equal(left, right)
                }
                IntegerComparisonOperator::GreaterThan => {
                    ConditionTerm::integer_greater_than(left, right)
                }
                IntegerComparisonOperator::GreaterEqual => {
                    ConditionTerm::integer_greater_equal(left, right)
                }
            };
            Ok(vec![SpecPropositionPath {
                proposition: Proposition::ConditionIs(condition, true),
                facts: Vec::new(),
                obligations: Vec::new(),
            }])
        }
        SpecProposition::AlgebraicComparison { left, equal, right } => {
            lower_spec_algebraic_comparison_at_state(
                state,
                left,
                *equal,
                right,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            lower_spec_sequence_membership_at_state(
                state,
                element,
                sequence,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )
        }
        SpecProposition::SequenceComparison { left, equal, right } => {
            lower_spec_sequence_comparison_at_state(
                state,
                left,
                *equal,
                right,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )
        }
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
            algebraic_bindings,
            budget,
        ),
        SpecProposition::FloatClassification {
            expression,
            classification,
        } => lower_spec_float_classification_proposition_at_state(
            state,
            expression,
            *classification,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
        ),
        SpecProposition::And(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_spec_proposition_at_state_with_algebraic_bindings(
                state,
                left,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in lower_spec_proposition_at_state_with_algebraic_bindings(
                    state,
                    right,
                    loop_entry_state,
                    &right_assumptions,
                    algebraic_bindings,
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
            algebraic_bindings,
            budget,
            |left, right| Proposition::Or(Box::new(left), Box::new(right)),
        ),
        SpecProposition::Not(body) => Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
            state,
            body,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
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
            for left_path in lower_spec_proposition_at_state_with_algebraic_bindings(
                state,
                left,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                )
                .assume_proposition(left_path.proposition.clone());
                for right_path in lower_spec_proposition_at_state_with_algebraic_bindings(
                    state,
                    right,
                    loop_entry_state,
                    &right_assumptions,
                    algebraic_bindings,
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
            Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
                &state,
                body,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
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
        SpecProposition::ForAllInteger {
            name: _,
            variable,
            body,
        } => Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
            state,
            body,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
        )?
        .into_iter()
        .map(|path| SpecPropositionPath {
            proposition: Proposition::ForAll {
                var: *variable,
                sort: Sort::Integer,
                body: Box::new(wrap_path_context(path.proposition, &path.facts, &[])),
            },
            facts: Vec::new(),
            obligations: path
                .obligations
                .into_iter()
                .map(|obligation| {
                    obligation.map_proposition(|proposition| Proposition::ForAll {
                        var: *variable,
                        sort: Sort::Integer,
                        body: Box::new(wrap_path_context(proposition, &path.facts, &[])),
                    })
                })
                .collect(),
        })
        .collect()),
        SpecProposition::ForAllPointer {
            name,
            variable,
            c_type,
            body,
        } => {
            let mut state = state.clone();
            let value = if matches!(c_type, CType::FunctionPointer(_)) {
                CValue::typed_pointer(Pointer::symbolic_function(*variable), *c_type)
            } else {
                CValue::typed_pointer(Pointer::symbolic(*variable), *c_type)
            };
            state.locals.set_typed(name.clone(), value, *c_type);
            Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
                &state,
                body,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPropositionPath {
                proposition: Proposition::ForAll {
                    var: *variable,
                    sort: Sort::CPointer(*c_type),
                    body: Box::new(wrap_path_context(path.proposition, &path.facts, &[])),
                },
                facts: Vec::new(),
                obligations: path
                    .obligations
                    .into_iter()
                    .map(|obligation| {
                        obligation.map_proposition(|proposition| Proposition::ForAll {
                            var: *variable,
                            sort: Sort::CPointer(*c_type),
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
            Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
                &state,
                body,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
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
        SpecProposition::ExistsInteger {
            name,
            variable,
            body,
        } => Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
            state,
            body,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
        )?
        .into_iter()
        .map(|path| {
            // An existential witness cannot soundly absorb path guards or
            // evaluation obligations: existentially quantifying an
            // implication would make a false guard vacuously prove the body.
            // The pure Integer fragment currently accepts only total bodies.
            if !path.facts.is_empty() || !path.obligations.is_empty() {
                return Err(ExecutionLimit::UnsupportedIntegerExistentialBody);
            }
            Ok(SpecPropositionPath {
                proposition: Proposition::Exists {
                    name: name.clone(),
                    var: *variable,
                    sort: Sort::Integer,
                    body: Box::new(path.proposition),
                },
                facts: Vec::new(),
                obligations: Vec::new(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?),
        SpecProposition::ExistsPointer {
            name,
            variable,
            c_type,
            body,
        } => {
            let mut state = state.clone();
            let value = if matches!(c_type, CType::FunctionPointer(_)) {
                CValue::typed_pointer(Pointer::symbolic_function(*variable), *c_type)
            } else {
                CValue::typed_pointer(Pointer::symbolic(*variable), *c_type)
            };
            state.locals.set_typed(name.clone(), value, *c_type);
            Ok(lower_spec_proposition_at_state_with_algebraic_bindings(
                &state,
                body,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPropositionPath {
                proposition: Proposition::Exists {
                    name: name.clone(),
                    var: *variable,
                    sort: Sort::CPointer(*c_type),
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
                            sort: Sort::CPointer(*c_type),
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
                algebraic_bindings,
                budget,
            )
        }
        SpecProposition::ResourceSeparate { left, right } => lower_spec_resource_relation_at_state(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
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
                algebraic_bindings,
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
            algebraic_bindings,
            budget,
            true,
        ),
        SpecProposition::Defined(expression) => {
            let paths = evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                expression,
                loop_entry_state,
                &PureFactContext::new(),
                algebraic_bindings,
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

fn lower_spec_integer_expression(
    expression: &SpecIntegerExpression,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<IntegerTerm> {
    budget.consume_expression_step()?;
    let SpecIntegerExpression::Term(term) = expression;
    let work = term.as_const().map_or(1, |value| {
        usize::try_from(value.bits())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    });
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        return Err(ExecutionLimit::Deadline);
    }
    Ok(term.clone())
}

#[allow(clippy::too_many_arguments)]
fn lower_spec_algebraic_comparison_at_state(
    state: &CState,
    left: &SpecAlgebraicExpression,
    equal: bool,
    right: &SpecAlgebraicExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    if super::functions::spec_algebraic_expression_is_state_independent(left)
        && super::functions::spec_algebraic_expression_is_state_independent(right)
        && (left == right
            || algebraic_match_reconstructs(left, right)
            || algebraic_match_reconstructs(right, left))
    {
        return Ok(vec![SpecPropositionPath {
            proposition: Proposition::ConditionIs(ConditionTerm::Constant(equal), true),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }
    let mut paths = Vec::new();
    for left_path in evaluate_spec_algebraic_at_state_with_bindings(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_algebraic_at_state_with_bindings(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
            budget,
        )? {
            if left_path.value.algebraic_type != right_path.value.algebraic_type {
                continue;
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            // State-dependent projections must be resolved (and their ownership
            // checked) before reflexivity can close a symbolic application.
            let equality = if left_path.value == right_path.value {
                Proposition::ConditionIs(ConditionTerm::Constant(true), true)
            } else {
                Proposition::Equal(
                    Term::Algebraic(left_path.value.clone()),
                    Term::Algebraic(right_path.value),
                )
            };
            paths.push(SpecPropositionPath {
                proposition: if equal {
                    equality
                } else {
                    Proposition::Not(Box::new(equality))
                },
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

fn algebraic_match_reconstructs(
    expression: &SpecAlgebraicExpression,
    scrutinee: &SpecAlgebraicExpression,
) -> bool {
    let SpecAlgebraicExpressionNode::Match {
        scrutinee: matched,
        arms,
    } = &expression.node
    else {
        return false;
    };
    if matched.as_ref() != scrutinee || expression.algebraic_type != scrutinee.algebraic_type {
        return false;
    }
    let arm_variants = arms
        .iter()
        .map(|arm| arm.variant.as_str())
        .collect::<BTreeSet<_>>();
    !scrutinee.algebraic_type.rigid
        && arms.len() == scrutinee.algebraic_type.variants.len()
        && arm_variants.len() == arms.len()
        && arms.iter().all(|arm| {
            let Some(schema) = scrutinee
                .algebraic_type
                .variants
                .iter()
                .find(|variant| variant.name == arm.variant)
            else {
                return false;
            };
            let SpecAlgebraicExpressionNode::Constructor { variant, fields } = &arm.body.node
            else {
                return false;
            };
            arm.body.algebraic_type == scrutinee.algebraic_type
                && variant == &arm.variant
                && arm.binding_types == schema.fields
                && fields.len() == arm.bindings.len()
                && fields.iter().zip(&schema.fields).zip(&arm.bindings).all(
                    |((field, field_type), binding)| match (field, field_type) {
                        (
                            SpecAlgebraicValue::C(SpecExpression::CExpression(
                                CExpression::Variable(name),
                            )),
                            AlgebraicValueType::C(_),
                        ) => name == binding,
                        (
                            SpecAlgebraicValue::Algebraic(SpecAlgebraicExpression {
                                node: SpecAlgebraicExpressionNode::Binding(name),
                                ..
                            }),
                            AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_),
                        ) => name == binding,
                        _ => false,
                    },
                )
        })
}

#[cfg(test)]
fn evaluate_spec_algebraic_at_state(
    state: &CState,
    expression: &SpecAlgebraicExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecAlgebraicPath>> {
    evaluate_spec_algebraic_at_state_with_bindings(
        state,
        expression,
        loop_entry_state,
        assumptions,
        &BTreeMap::new(),
        budget,
    )
}

fn evaluate_spec_algebraic_at_state_with_bindings(
    state: &CState,
    expression: &SpecAlgebraicExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecAlgebraicPath>> {
    budget.consume_expression_step()?;
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(projection) => {
            let snapshot = if projection.at_entry {
                loop_entry_state.ok_or(ExecutionLimit::Paths)?
            } else {
                state
            };
            let Some(AlgebraicValue::Algebraic(value)) = snapshot
                .resource_instance_at_path(projection.identity, &projection.children)
                .and_then(|instance| instance.fields().get(projection.field_index))
            else {
                return Err(ExecutionLimit::Paths);
            };
            if value.algebraic_type != expression.algebraic_type {
                return Err(ExecutionLimit::Paths);
            }
            Ok(vec![SpecAlgebraicPath {
                value: value.clone(),
                facts: vec![],
                obligations: vec![],
            }])
        }
        SpecAlgebraicExpressionNode::Variable(variable) => Ok(vec![SpecAlgebraicPath {
            value: AlgebraicTerm {
                algebraic_type: expression.algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(*variable),
            },
            facts: Vec::new(),
            obligations: Vec::new(),
        }]),
        SpecAlgebraicExpressionNode::Binding(name) => {
            let Some(value) = algebraic_bindings.get(name) else {
                return Err(ExecutionLimit::Paths);
            };
            if value.algebraic_type != expression.algebraic_type {
                return Err(ExecutionLimit::Paths);
            }
            Ok(vec![SpecAlgebraicPath {
                value: value.clone(),
                facts: Vec::new(),
                obligations: Vec::new(),
            }])
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            if !spec_algebraic_result_match_arms_are_well_formed(&scrutinee.algebraic_type, arms) {
                return Err(ExecutionLimit::Paths);
            }
            let mut result = Vec::new();
            for scrutinee_path in evaluate_spec_algebraic_at_state_with_bindings(
                state,
                scrutinee,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )? {
                if !matches!(
                    scrutinee_path.value.node,
                    AlgebraicTermNode::Constructor { .. }
                ) {
                    let mut lowered_arms = Vec::with_capacity(arms.len());
                    let mut facts = scrutinee_path.facts.clone();
                    let mut obligations = scrutinee_path.obligations.clone();
                    for arm in arms {
                        let Some(schema) = scrutinee_path
                            .value
                            .algebraic_type
                            .variants
                            .iter()
                            .find(|variant| variant.name == arm.variant)
                        else {
                            return Err(ExecutionLimit::Paths);
                        };
                        let bindings = symbolic_algebraic_bindings(
                            &scrutinee_path.value.algebraic_type,
                            schema,
                            budget,
                        )?;
                        let mut body_state = state.clone();
                        let mut body_algebraic_bindings = algebraic_bindings.clone();
                        for (binding, value) in arm.bindings.iter().zip(&bindings) {
                            match value {
                                AlgebraicValue::C(value) => {
                                    body_state.locals.set(binding.clone(), value.clone());
                                }
                                AlgebraicValue::Algebraic(value) => {
                                    body_algebraic_bindings.insert(binding.clone(), value.clone());
                                }
                            }
                        }
                        let body_assumptions =
                            assumptions_with_path_context(assumptions, &facts, &obligations);
                        let mut body_paths = evaluate_spec_algebraic_at_state_with_bindings(
                            &body_state,
                            &arm.body,
                            loop_entry_state,
                            &body_assumptions,
                            &body_algebraic_bindings,
                            budget,
                        )?;
                        let Some(body_path) = body_paths.pop() else {
                            return Err(ExecutionLimit::Paths);
                        };
                        if !body_paths.is_empty() {
                            return Err(ExecutionLimit::Paths);
                        }
                        // Arm-local facts and obligations are valid only when this
                        // constructor is selected. A symbolic match must not leak
                        // them into its unconditional enclosing path.
                        if !body_path.facts.is_empty() || !body_path.obligations.is_empty() {
                            return Err(ExecutionLimit::Paths);
                        }
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &facts,
                                &obligations,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                            )
                        else {
                            return Err(ExecutionLimit::Paths);
                        };
                        facts = merged_facts;
                        obligations = merged_obligations;
                        lowered_arms.push(AlgebraicResultMatchArm {
                            variant: arm.variant.clone(),
                            bindings,
                            body: body_path.value,
                        });
                    }
                    result.push(SpecAlgebraicPath {
                        value: AlgebraicTerm {
                            algebraic_type: expression.algebraic_type.clone(),
                            node: AlgebraicTermNode::Match {
                                scrutinee: Box::new(scrutinee_path.value),
                                arms: lowered_arms,
                            },
                        },
                        facts,
                        obligations,
                    });
                    continue;
                }
                for case in algebraic_case_paths(&scrutinee_path.value, budget)? {
                    let Some(arm) = arms.iter().find(|arm| arm.variant == case.variant) else {
                        return Err(ExecutionLimit::Paths);
                    };
                    if arm.bindings.len() != case.fields.len()
                        || arm.binding_types
                            != case
                                .fields
                                .iter()
                                .map(AlgebraicValue::value_type)
                                .collect::<Vec<_>>()
                    {
                        return Err(ExecutionLimit::Paths);
                    }
                    let mut body_state = state.clone();
                    let mut body_algebraic_bindings = algebraic_bindings.clone();
                    for (binding, field) in arm.bindings.iter().zip(&case.fields) {
                        match field {
                            AlgebraicValue::C(field) => {
                                body_state.locals.set(binding.clone(), field.clone());
                            }
                            AlgebraicValue::Algebraic(field) => {
                                body_algebraic_bindings.insert(binding.clone(), field.clone());
                            }
                        }
                    }
                    let Some((case_facts, case_obligations)) =
                        merge_execution_pure_facts_and_obligations(
                            &scrutinee_path.facts,
                            &scrutinee_path.obligations,
                            &case.facts,
                            &case.obligations,
                            assumptions,
                        )
                    else {
                        continue;
                    };
                    let body_assumptions =
                        assumptions_with_path_context(assumptions, &case_facts, &case_obligations);
                    for body_path in evaluate_spec_algebraic_at_state_with_bindings(
                        &body_state,
                        &arm.body,
                        loop_entry_state,
                        &body_assumptions,
                        &body_algebraic_bindings,
                        budget,
                    )? {
                        if let Some((facts, obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &case_facts,
                                &case_obligations,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                            )
                        {
                            result.push(SpecAlgebraicPath {
                                value: body_path.value,
                                facts,
                                obligations,
                            });
                        }
                    }
                }
            }
            budget.check_path_width(result.len())?;
            Ok(result)
        }
        SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
            let Some(schema) = expression
                .algebraic_type
                .variants
                .iter()
                .find(|schema| schema.name == *variant)
            else {
                return Err(ExecutionLimit::Paths);
            };
            if schema.fields.len() != fields.len() {
                return Err(ExecutionLimit::Paths);
            }
            let mut paths = vec![(Vec::new(), Vec::new(), Vec::new())];
            for field in fields {
                let mut next = Vec::new();
                for (values, facts, obligations) in paths {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for field_path in evaluate_spec_algebraic_value_at_state(
                        state,
                        field,
                        loop_entry_state,
                        &path_assumptions,
                        algebraic_bindings,
                        budget,
                    )? {
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &facts,
                                &obligations,
                                &field_path.facts,
                                &field_path.obligations,
                                assumptions,
                            )
                        else {
                            continue;
                        };
                        let mut next_values = values.clone();
                        next_values.push(field_path.value);
                        next.push((next_values, merged_facts, merged_obligations));
                    }
                }
                paths = next;
            }
            let paths = paths
                .into_iter()
                .filter(|(fields, _, _)| {
                    fields
                        .iter()
                        .map(AlgebraicValue::value_type)
                        .eq(schema.fields.iter().cloned())
                })
                .map(|(fields, facts, obligations)| SpecAlgebraicPath {
                    value: AlgebraicTerm {
                        algebraic_type: expression.algebraic_type.clone(),
                        node: AlgebraicTermNode::Constructor {
                            variant: variant.clone(),
                            fields,
                        },
                    },
                    facts,
                    obligations,
                })
                .collect::<Vec<_>>();
            budget.check_path_width(paths.len())?;
            Ok(paths)
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            let mut paths = vec![(Vec::new(), Vec::new(), Vec::new())];
            for argument in arguments {
                let mut next = Vec::new();
                for (values, facts, obligations) in paths {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for argument_path in evaluate_spec_pure_function_argument_paths(
                        state,
                        argument,
                        loop_entry_state,
                        &path_assumptions,
                        algebraic_bindings,
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
                        let mut values = values.clone();
                        values.push(argument_path.value);
                        next.push((values, merged_facts, merged_obligations));
                    }
                }
                paths = next;
            }
            Ok(paths
                .into_iter()
                .map(|(arguments, facts, obligations)| SpecAlgebraicPath {
                    value: AlgebraicTerm {
                        algebraic_type: expression.algebraic_type.clone(),
                        node: AlgebraicTermNode::PureFunctionApplication {
                            name: name.clone(),
                            arguments,
                        },
                    },
                    facts,
                    obligations,
                })
                .collect())
        }
    }
}

fn symbolic_algebraic_bindings(
    algebraic_type: &AlgebraicType,
    variant: &AlgebraicVariantType,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<AlgebraicValue>> {
    variant
        .fields
        .iter()
        .map(|value_type| {
            let variable = Variable(budget.next_kernel_variable);
            budget.next_kernel_variable += 1;
            match value_type {
                AlgebraicValueType::C(c_type) => {
                    Ok(AlgebraicValue::C(symbolic_call_result(*c_type, variable)))
                }
                AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_) => {
                    algebraic_type
                        .resolve_nested_type(value_type)
                        .map(|nested_type| {
                            AlgebraicValue::Algebraic(AlgebraicTerm {
                                algebraic_type: nested_type,
                                node: AlgebraicTermNode::Variable(variable),
                            })
                        })
                        .ok_or(ExecutionLimit::Paths)
                }
            }
        })
        .collect()
}

fn evaluate_spec_algebraic_value_at_state(
    state: &CState,
    value: &SpecAlgebraicValue,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecAlgebraicValuePath>> {
    match value {
        SpecAlgebraicValue::C(expression) => {
            Ok(evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                expression,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecAlgebraicValuePath {
                value: AlgebraicValue::C(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
        SpecAlgebraicValue::Algebraic(expression) => {
            Ok(evaluate_spec_algebraic_at_state_with_bindings(
                state,
                expression,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecAlgebraicValuePath {
                value: AlgebraicValue::Algebraic(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
    }
}

fn spec_algebraic_result_match_arms_are_well_formed(
    algebraic_type: &AlgebraicType,
    arms: &[SpecAlgebraicResultMatchArm],
) -> bool {
    !algebraic_type.rigid
        && arms.len() == algebraic_type.variants.len()
        && algebraic_type.variants.iter().all(|variant| {
            arms.iter()
                .filter(|arm| arm.variant == variant.name)
                .count()
                == 1
                && arms
                    .iter()
                    .find(|arm| arm.variant == variant.name)
                    .is_some_and(|arm| {
                        arm.bindings.len() == variant.fields.len()
                            && arm.binding_types == variant.fields
                    })
        })
}

fn spec_scalar_match_arms_are_well_formed(
    algebraic_type: &AlgebraicType,
    arms: &[SpecAlgebraicMatchArm],
) -> bool {
    !algebraic_type.rigid
        && arms.len() == algebraic_type.variants.len()
        && algebraic_type.variants.iter().all(|variant| {
            arms.iter()
                .filter(|arm| arm.variant == variant.name)
                .count()
                == 1
                && arms
                    .iter()
                    .find(|arm| arm.variant == variant.name)
                    .is_some_and(|arm| {
                        arm.bindings.len() == variant.fields.len()
                            && arm.binding_types == variant.fields
                    })
        })
}

fn algebraic_case_paths(
    term: &AlgebraicTerm,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecAlgebraicCasePath>> {
    match &term.node {
        AlgebraicTermNode::Constructor { variant, fields } => Ok(vec![SpecAlgebraicCasePath {
            variant: variant.clone(),
            fields: fields.clone(),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]),
        AlgebraicTermNode::Variable(_)
        | AlgebraicTermNode::Match { .. }
        | AlgebraicTermNode::PureFunctionApplication { .. } => {
            let mut paths = Vec::with_capacity(term.algebraic_type.variants.len());
            for variant in term.algebraic_type.variants.iter() {
                let fields = symbolic_algebraic_bindings(&term.algebraic_type, variant, budget)?;
                let constructor = AlgebraicTerm {
                    algebraic_type: term.algebraic_type.clone(),
                    node: AlgebraicTermNode::Constructor {
                        variant: variant.name.clone(),
                        fields: fields.clone(),
                    },
                };
                paths.push(SpecAlgebraicCasePath {
                    variant: variant.name.clone(),
                    fields,
                    facts: vec![ExecutionPureFact::new(Proposition::Equal(
                        Term::Algebraic(term.clone()),
                        Term::Algebraic(constructor),
                    ))],
                    obligations: Vec::new(),
                });
            }
            budget.check_path_width(paths.len())?;
            Ok(paths)
        }
    }
}

fn lower_spec_sequence_membership_at_state(
    state: &CState,
    element: &SpecExpression,
    sequence: &SpecSequenceExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for element_path in evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        element,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let sequence_assumptions = assumptions_with_path_context(
            assumptions,
            &element_path.facts,
            &element_path.obligations,
        );
        for sequence_path in evaluate_spec_sequence_at_state(
            state,
            sequence,
            loop_entry_state,
            &sequence_assumptions,
            algebraic_bindings,
            budget,
        )? {
            if sequence_path
                .value
                .element_type
                .is_some_and(|element_type| element_type != element_path.value.c_type())
            {
                continue;
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &element_path.facts,
                &element_path.obligations,
                &sequence_path.facts,
                &sequence_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let comparisons = sequence_elements(&sequence_path.value)
                .filter_map(|member| {
                    c_value_comparison_proposition(
                        &element_path.value,
                        CComparisonOperator::Equal,
                        member,
                    )
                })
                .collect::<Vec<_>>();
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            let comparison_truth = |comparison: &Proposition| {
                proposition_as_single_condition(comparison).and_then(|(condition, expected)| {
                    path_assumptions
                        .decide(&condition)
                        .map(|actual| actual == expected)
                })
            };
            let proposition = if comparisons
                .iter()
                .any(|comparison| comparison_truth(comparison) == Some(true))
            {
                Proposition::ConditionIs(ConditionTerm::Constant(true), true)
            } else if comparisons
                .iter()
                .all(|comparison| comparison_truth(comparison) == Some(false))
            {
                Proposition::ConditionIs(ConditionTerm::Constant(false), true)
            } else {
                comparisons
                    .into_iter()
                    .reduce(|left, right| Proposition::Or(Box::new(left), Box::new(right)))
                    .unwrap_or(Proposition::ConditionIs(
                        ConditionTerm::Constant(false),
                        true,
                    ))
            };
            paths.push(SpecPropositionPath {
                proposition,
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

pub(super) fn sequence_elements(sequence: &SequenceTerm) -> SequenceElements<'_> {
    SequenceElements {
        pending: vec![sequence],
        current: None,
    }
}

pub(super) struct SequenceElements<'a> {
    pending: Vec<&'a SequenceTerm>,
    current: Option<std::slice::Iter<'a, CValue>>,
}

impl<'a> Iterator for SequenceElements<'a> {
    type Item = &'a CValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(values) = &mut self.current {
                if let Some(value) = values.next() {
                    return Some(value);
                }
                self.current = None;
            }
            match self.pending.pop()?.node.as_ref() {
                SequenceTermNode::Literal(values) => self.current = Some(values.iter()),
                SequenceTermNode::Concat(left, right) => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_spec_sequence_comparison_at_state(
    state: &CState,
    left: &SpecSequenceExpression,
    equal: bool,
    right: &SpecSequenceExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_spec_sequence_at_state(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_sequence_at_state(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
            budget,
        )? {
            if !sequence_element_types_compatible(
                left_path.value.element_type,
                right_path.value.element_type,
            ) {
                continue;
            }
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let equality = finite_sequence_equality(&left_path.value, &right_path.value);
            paths.push(SpecPropositionPath {
                proposition: if equal {
                    equality
                } else {
                    Proposition::Not(Box::new(equality))
                },
                facts,
                obligations,
            });
        }
    }
    Ok(paths)
}

/// Finite integer sequences have ordinary elementwise equality. Expose that
/// logical structure once during elaboration, so every proof context can use
/// the same introduction, extraction, and equality rules. Other element types
/// retain logical sequence equality (not C floating or address comparison).
fn finite_sequence_equality(left: &SequenceTerm, right: &SequenceTerm) -> Proposition {
    let fallback =
        || Proposition::Equal(Term::Sequence(left.clone()), Term::Sequence(right.clone()));
    let mut left = sequence_elements(left);
    let mut right = sequence_elements(right);
    let mut equalities = Vec::new();
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) => {
                let Some(equality) = integer_sequence_element_equality(left, right) else {
                    return fallback();
                };
                equalities.push(equality);
            }
            (None, None) => break,
            _ => return Proposition::ConditionIs(ConditionTerm::Constant(false), true),
        }
    }
    if equalities.is_empty() {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    }
    while equalities.len() > 1 {
        let mut next = Vec::with_capacity(equalities.len().div_ceil(2));
        let mut values = equalities.into_iter();
        while let Some(left) = values.next() {
            next.push(match values.next() {
                Some(right) => Proposition::And(Box::new(left), Box::new(right)),
                None => left,
            });
        }
        equalities = next;
    }
    equalities.pop().expect("nonempty equality tree")
}

pub(super) fn integer_sequence_element_equality(
    left: &CValue,
    right: &CValue,
) -> Option<Proposition> {
    if left.c_type() != right.c_type()
        || !matches!(
            left,
            CValue::Int16(_)
                | CValue::Int32(_)
                | CValue::UInt8(_)
                | CValue::UInt16(_)
                | CValue::UInt32(_)
                | CValue::Int64(_)
                | CValue::UInt64(_)
        )
    {
        return None;
    }
    c_value_comparison_proposition(left, CComparisonOperator::Equal, right)
}

fn evaluate_spec_sequence_at_state(
    state: &CState,
    expression: &SpecSequenceExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecSequencePath>> {
    budget.consume_expression_step()?;
    match expression {
        SpecSequenceExpression::Literal(elements) => {
            let mut paths = vec![(Vec::new(), Vec::new(), Vec::new())];
            for element in elements {
                let mut next = Vec::new();
                for (values, facts, obligations) in paths {
                    let path_assumptions =
                        assumptions_with_path_context(assumptions, &facts, &obligations);
                    for element_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                        state,
                        element,
                        loop_entry_state,
                        &path_assumptions,
                        algebraic_bindings,
                        budget,
                    )? {
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &facts,
                                &obligations,
                                &element_path.facts,
                                &element_path.obligations,
                                assumptions,
                            )
                        else {
                            continue;
                        };
                        let mut next_values = values.clone();
                        next_values.push(element_path.value);
                        next.push((next_values, merged_facts, merged_obligations));
                    }
                }
                paths = next;
            }
            Ok(paths
                .into_iter()
                .filter_map(|(values, facts, obligations)| {
                    let element_type = values.first().map(CValue::c_type);
                    values
                        .iter()
                        .all(|value| Some(value.c_type()) == element_type)
                        .then(|| SpecSequencePath {
                            value: SequenceTerm {
                                element_type,
                                node: std::sync::Arc::new(SequenceTermNode::Literal(values.into())),
                            },
                            facts,
                            obligations,
                        })
                })
                .collect())
        }
        SpecSequenceExpression::Concat(left, right) => {
            let mut paths = Vec::new();
            for left_path in evaluate_spec_sequence_at_state(
                state,
                left,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in evaluate_spec_sequence_at_state(
                    state,
                    right,
                    loop_entry_state,
                    &right_assumptions,
                    algebraic_bindings,
                    budget,
                )? {
                    if !sequence_element_types_compatible(
                        left_path.value.element_type,
                        right_path.value.element_type,
                    ) {
                        continue;
                    }
                    let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &left_path.facts,
                        &left_path.obligations,
                        &right_path.facts,
                        &right_path.obligations,
                        assumptions,
                    ) else {
                        continue;
                    };
                    paths.push(SpecSequencePath {
                        value: concatenate_sequence_terms(
                            left_path.value.clone(),
                            right_path.value,
                        ),
                        facts,
                        obligations,
                    });
                }
            }
            Ok(paths)
        }
    }
}

fn sequence_element_types_compatible(left: Option<CType>, right: Option<CType>) -> bool {
    left.is_none() || right.is_none() || left == right
}

fn concatenate_sequence_terms(left: SequenceTerm, right: SequenceTerm) -> SequenceTerm {
    if matches!(left.node.as_ref(), SequenceTermNode::Literal(values) if values.is_empty()) {
        return right;
    }
    if matches!(right.node.as_ref(), SequenceTermNode::Literal(values) if values.is_empty()) {
        return left;
    }
    SequenceTerm {
        element_type: left.element_type.or(right.element_type),
        node: std::sync::Arc::new(SequenceTermNode::Concat(left, right)),
    }
}

#[cfg(test)]
mod sequence_term_tests {
    use super::*;

    fn singleton(value: u32) -> SequenceTerm {
        SequenceTerm {
            element_type: Some(CType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Literal(vec![int32(value)].into())),
        }
    }

    #[test]
    fn integer_sequence_equality_has_linear_size_and_logarithmic_depth() {
        for size in [8usize, 32, 128, 512] {
            let mut left = singleton(0);
            for value in 1..size {
                left = concatenate_sequence_terms(left, singleton(value as u32));
            }
            let right = SequenceTerm {
                element_type: Some(CType::Int32),
                node: std::sync::Arc::new(SequenceTermNode::Literal(
                    (0..size)
                        .map(|n| int32(n as u32))
                        .collect::<Vec<_>>()
                        .into(),
                )),
            };
            let equality = finite_sequence_equality(&left, &right);
            let mut pending = vec![(&equality, 0)];
            let mut nodes = 0;
            let mut depth = 0;
            while let Some((proposition, current_depth)) = pending.pop() {
                nodes += 1;
                depth = depth.max(current_depth);
                if let Proposition::And(left, right) = proposition {
                    pending.push((left, current_depth + 1));
                    pending.push((right, current_depth + 1));
                }
            }
            assert_eq!(nodes, 2 * size - 1);
            assert_eq!(depth, size.ilog2());
        }
    }

    #[test]
    fn repeated_concatenation_shares_the_existing_root() {
        for size in [8usize, 64, 512] {
            let mut sequence = singleton(0);
            for value in 1..size {
                let previous_root = sequence.node.clone();
                sequence = concatenate_sequence_terms(sequence, singleton(value as u32));
                let SequenceTermNode::Concat(left, _) = sequence.node.as_ref() else {
                    panic!("nonempty concatenation should retain a rope node");
                };
                assert!(
                    std::sync::Arc::ptr_eq(&left.node, &previous_root),
                    "concatenating size {value} copied the existing sequence"
                );
            }
        }
    }

    #[test]
    fn empty_concatenation_reuses_the_nonempty_root() {
        let empty = SequenceTerm {
            element_type: None,
            node: std::sync::Arc::new(SequenceTermNode::Literal(Vec::new().into())),
        };
        let value = singleton(7);
        let root = value.node.clone();

        assert!(std::sync::Arc::ptr_eq(
            &concatenate_sequence_terms(empty.clone(), value.clone()).node,
            &root,
        ));
        assert!(std::sync::Arc::ptr_eq(
            &concatenate_sequence_terms(value, empty).node,
            &root,
        ));
    }
}

#[cfg(test)]
mod algebraic_term_tests {
    use super::*;

    fn maybe_type() -> AlgebraicType {
        let arguments = vec![AlgebraicValueType::C(CType::Int32)];
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "None".to_string(),
                fields: Vec::new(),
            },
            AlgebraicVariantType {
                name: "Some".to_string(),
                fields: vec![AlgebraicValueType::C(CType::Int32)],
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
                    binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                    body: SpecExpression::CExpression(CExpression::Variable("value".to_string())),
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
            arguments: vec![AlgebraicValueType::C(CType::Int32)],
        };
        let mut schemas = maybe_type.schemas.definitions().clone();
        schemas.insert(value_type, variants.clone());
        AlgebraicType {
            rigid: false,
            name: "Envelope".to_string(),
            arguments: vec![AlgebraicValueType::C(CType::Int32)],
            variants,
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(schemas)),
        }
    }

    fn recursive_list_type() -> AlgebraicType {
        let arguments = vec![AlgebraicValueType::C(CType::Int32)];
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
                fields: vec![AlgebraicValueType::C(CType::Int32), value_type.clone()],
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
        let arguments = vec![AlgebraicValueType::C(CType::Int32)];
        let variants: std::sync::Arc<[AlgebraicVariantType]> = (0..variant_count)
            .map(|index| AlgebraicVariantType {
                name: format!("V{index}"),
                fields: vec![AlgebraicValueType::C(CType::Int32)],
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
                &CState::new(),
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
            let captured =
                capture_spec_algebraic_value(&CState::new(), &call, None, &PureFactContext::new())
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
            let mut budget = ExecutionBudget::new();
            let next_variable = budget.next_kernel_variable;
            let paths = evaluate_spec_algebraic_at_state(
                &CState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut budget,
            )
            .expect("a logical ADT variable lowers without case analysis");

            assert_eq!(paths.len(), 1);
            assert_eq!(budget.next_kernel_variable, next_variable);
            assert_eq!(
                paths[0].value,
                AlgebraicTerm {
                    algebraic_type,
                    node: AlgebraicTermNode::Variable(Variable(41)),
                }
            );
        }
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
                fields: vec![AlgebraicValue::C(int32(9))],
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
                fields: vec![AlgebraicValue::C(int32(7)), AlgebraicValue::Algebraic(tail)],
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
        let paths = evaluate_spec_expression_paths_with_loop_entry(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .expect("a pure match is a symbolic expression, not a path split");

        assert_eq!(paths.len(), 1);
        assert!(paths[0].facts.is_empty());
        assert!(paths[0].obligations.is_empty());
        let CValue::Int32(Bitvector32Term::AlgebraicMatch { scrutinee, arms }) = &paths[0].value
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

        let paths = evaluate_spec_expression_paths_with_loop_entry(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .expect("a nested algebraic binder should remain available to the arm body");

        assert_eq!(paths.len(), 1);
        let CValue::Int32(Bitvector32Term::AlgebraicMatch { arms, .. }) = &paths[0].value else {
            panic!("the outer match should remain symbolic");
        };
        let Bitvector32Term::AlgebraicMatch { .. } = &arms[1].body else {
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
                        binding_types: vec![AlgebraicValueType::C(CType::Int32)],
                        body: Box::new(SpecAlgebraicExpression {
                            algebraic_type: algebraic_type.clone(),
                            node: SpecAlgebraicExpressionNode::Constructor {
                                variant: "Some".to_string(),
                                fields: vec![SpecAlgebraicValue::C(SpecExpression::CExpression(
                                    CExpression::Variable("value".to_string()),
                                ))],
                            },
                        }),
                    },
                ],
            },
        };
        let paths = evaluate_spec_algebraic_at_state(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .expect("an algebraic-valued match should stay symbolic");

        assert_eq!(paths.len(), 1);
        assert!(matches!(
            paths[0].value.node,
            AlgebraicTermNode::Match { .. }
        ));
        assert!(paths[0].value.is_well_formed());
    }

    #[test]
    fn match_on_known_constructor_reduces_to_selected_arm() {
        let algebraic_type = maybe_type();
        let expression = value_or_match(SpecAlgebraicExpression {
            algebraic_type: algebraic_type.clone(),
            node: SpecAlgebraicExpressionNode::Constructor {
                variant: "Some".to_string(),
                fields: vec![SpecAlgebraicValue::C(SpecExpression::Value(int32(7)))],
            },
        });
        let paths = evaluate_spec_expression_paths_with_loop_entry(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .expect("a match on a checked constructor should reduce");

        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value, int32(7));
    }

    #[test]
    fn pure_function_application_is_not_eagerly_evaluated() {
        let expression = SpecExpression::PureFunctionApplication {
            name: "increment".to_string(),
            arguments: vec![SpecPureFunctionArgument::Value(SpecExpression::Value(
                int32(41),
            ))],
            result_type: CType::Int32,
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .expect("pure calls should lower to logical applications");

        assert_eq!(paths.len(), 1);
        assert_eq!(
            paths[0].value,
            CValue::Int32(Bitvector32Term::ClickFunctionApplication {
                name: "increment".to_string(),
                arguments: vec![PureFunctionArgument::Value(int32(41))],
            })
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
            result_type: CType::Int32,
        };
        let paths = evaluate_spec_expression_paths_with_loop_entry(
            &CState::new(),
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .expect("an ADT argument should remain one typed term");

        assert_eq!(paths.len(), 1);
        let CValue::Int32(Bitvector32Term::ClickFunctionApplication { arguments, .. }) =
            &paths[0].value
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
            evaluate_spec_expression_paths_with_loop_entry(
                &CState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .is_err()
        );
    }
}

fn lower_spec_float_classification_proposition_at_state(
    state: &CState,
    expression: &SpecExpression,
    classification: CFloatClassification,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    Ok(evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        expression,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )?
    .into_iter()
    .filter_map(|path| {
        let condition = match path.value {
            CValue::Float32(value) => ConditionTerm::float32_classification(value, classification),
            CValue::Float64(value) => ConditionTerm::float64_classification(value, classification),
            _ => return None,
        };
        Some(SpecPropositionPath {
            proposition: Proposition::ConditionIs(condition, true),
            facts: path.facts,
            obligations: path.obligations,
        })
    })
    .collect())
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
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
            for value_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                expression,
                loop_entry_state,
                &path_assumptions,
                algebraic_bindings,
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
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
                        base.pointer().clone(),
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
                        arguments: arguments.into_iter().map(AlgebraicValue::C).collect(),
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
                        arguments: arguments.into_iter().map(AlgebraicValue::C).collect(),
                    })
                }),
            )
        }
    };
    Ok(evaluate_spec_values_at_state(
        state,
        &expressions,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )?
    .into_iter()
    .filter_map(|path| build(path.values).map(|resource| (resource, path.facts, path.obligations)))
    .collect())
}

fn lower_spec_resource_relation_at_state(
    state: &CState,
    left: &SpecResource,
    right: &SpecResource,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
    relation: impl Fn(CResource, CResource) -> Proposition,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for (left, left_facts, left_obligations) in evaluate_spec_resource_at_state(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for (right, right_facts, right_obligations) in evaluate_spec_resource_at_state(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
    enforce_range_guards: bool,
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
        algebraic_bindings,
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
            let range_start = start.clone();
            let range_end = end.clone();
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
            let mut obligations = path.obligations;
            if enforce_range_guards {
                for guard in crate::kernel::memory_range_byte_count_guards(
                    range_start.clone(),
                    range_end.clone(),
                    element_width,
                ) {
                    add_proof_obligation(&mut obligations, assumptions, guard)?;
                }
            }
            Some(SpecPropositionPath {
                proposition: Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base,
                    bytes: crate::kernel::memory_range_byte_count(
                        range_start,
                        range_end,
                        element_width,
                    ),
                },
                facts: path.facts,
                obligations,
            })
        }
        _ => None,
    })
    .collect())
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
    combine: impl Fn(Proposition, Proposition) -> Proposition,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in lower_spec_proposition_at_state_with_algebraic_bindings(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in lower_spec_proposition_at_state_with_algebraic_bindings(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    if matches!(left, SpecExpression::AlgebraicMatch { .. })
        && left == right
        && matches!(
            operator,
            CComparisonOperator::Equal | CComparisonOperator::NotEqual
        )
    {
        return Ok(vec![SpecPropositionPath {
            proposition: Proposition::ConditionIs(
                ConditionTerm::Constant(operator == CComparisonOperator::Equal),
                true,
            ),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }
    let mut paths = Vec::new();
    let left_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )?;
    let left_path_count = left_paths.len();
    let mut right_path_count = 0usize;
    let mut merge_failure_count = 0usize;
    for left_path in left_paths {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        let right_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    // A function-contract fact describes the behavior of its pointer value;
    // it is independent of the caller's current resource-population snapshot.
    // Keeping the uniform predicate state argument canonical lets a closed
    // pure theorem establish the same fact at every later application site.
    let predicate_state = if CFunctionContract::surface_name_from_predicate(name).is_some() {
        CState::new()
    } else {
        state.resource_state_snapshot()
    };
    let mut paths = vec![SpecPropositionPath {
        proposition: Proposition::Predicate {
            name: name.to_string(),
            arguments: vec![Term::CState(predicate_state)],
        },
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let (expression, memory) = match argument {
            SpecPredicateArgument::Value(expression) => (expression, None),
            SpecPredicateArgument::ArrayRef { memory, pointer } => (pointer, Some(memory)),
        };
        let argument_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
            state,
            expression,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
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
    evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        expression,
        loop_entry_state,
        assumptions,
        &BTreeMap::new(),
        budget,
    )
}

fn evaluate_spec_expression_paths_with_algebraic_bindings(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        SpecExpression::ResourceField { projection, c_type } => {
            let snapshot = if projection.at_entry {
                loop_entry_state.ok_or(ExecutionLimit::Paths)?
            } else {
                state
            };
            let Some(AlgebraicValue::C(value)) = snapshot
                .resource_instance_at_path(projection.identity, &projection.children)
                .and_then(|instance| instance.fields().get(projection.field_index))
            else {
                return Err(ExecutionLimit::Paths);
            };
            if value.c_type() != *c_type {
                return Err(ExecutionLimit::Paths);
            }
            vec![SpecExpressionPath {
                value: value.clone(),
                facts: vec![],
                obligations: vec![],
            }]
        }
        SpecExpression::Value(value) => vec![SpecExpressionPath {
            value: value.clone(),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            if !spec_scalar_match_arms_are_well_formed(&scrutinee.algebraic_type, arms) {
                return Err(ExecutionLimit::Paths);
            }
            let mut paths = Vec::new();
            for scrutinee_path in evaluate_spec_algebraic_at_state_with_bindings(
                state,
                scrutinee,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )? {
                if !matches!(
                    scrutinee_path.value.node,
                    AlgebraicTermNode::Constructor { .. }
                ) {
                    let mut lowered_arms = Vec::with_capacity(arms.len());
                    let mut result_type = None;
                    let mut facts = scrutinee_path.facts.clone();
                    let mut obligations = scrutinee_path.obligations.clone();
                    for arm in arms {
                        let Some(schema) = scrutinee_path
                            .value
                            .algebraic_type
                            .variants
                            .iter()
                            .find(|variant| variant.name == arm.variant)
                        else {
                            return Err(ExecutionLimit::Paths);
                        };
                        let bindings = symbolic_algebraic_bindings(
                            &scrutinee_path.value.algebraic_type,
                            schema,
                            budget,
                        )?;
                        let mut body_state = state.clone();
                        let mut body_algebraic_bindings = algebraic_bindings.clone();
                        for (binding, value) in arm.bindings.iter().zip(&bindings) {
                            match value {
                                AlgebraicValue::C(value) => {
                                    body_state.locals.set(binding.clone(), value.clone());
                                }
                                AlgebraicValue::Algebraic(value) => {
                                    body_algebraic_bindings.insert(binding.clone(), value.clone());
                                }
                            }
                        }
                        let body_assumptions =
                            assumptions_with_path_context(assumptions, &facts, &obligations);
                        let mut body_paths =
                            evaluate_spec_expression_paths_with_algebraic_bindings(
                                &body_state,
                                &arm.body,
                                loop_entry_state,
                                &body_assumptions,
                                &body_algebraic_bindings,
                                budget,
                            )?;
                        let Some(body_path) = body_paths.pop() else {
                            return Err(ExecutionLimit::Paths);
                        };
                        if !body_paths.is_empty() {
                            return Err(ExecutionLimit::Paths);
                        }
                        // These side conditions would need to be guarded by the
                        // arm's constructor test. Reject instead of asserting them
                        // unconditionally beside the symbolic match term.
                        if !body_path.facts.is_empty() || !body_path.obligations.is_empty() {
                            return Err(ExecutionLimit::Paths);
                        }
                        let body_type = body_path.value.c_type();
                        if result_type.is_some_and(|expected| expected != body_type) {
                            return Err(ExecutionLimit::Paths);
                        }
                        result_type = Some(body_type);
                        let Some(body) = c_value_bitvector_term(&body_path.value) else {
                            return Err(ExecutionLimit::Paths);
                        };
                        let Some((merged_facts, merged_obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &facts,
                                &obligations,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                            )
                        else {
                            return Err(ExecutionLimit::Paths);
                        };
                        facts = merged_facts;
                        obligations = merged_obligations;
                        lowered_arms.push(AlgebraicBitvectorMatchArm {
                            variant: arm.variant.clone(),
                            bindings,
                            body,
                        });
                    }
                    let Some(result_type) = result_type else {
                        return Err(ExecutionLimit::Paths);
                    };
                    let Some(value) = c_value_from_bitvector_term(
                        result_type,
                        Bitvector32Term::AlgebraicMatch {
                            scrutinee: Box::new(scrutinee_path.value),
                            arms: lowered_arms,
                        },
                    ) else {
                        return Err(ExecutionLimit::Paths);
                    };
                    paths.push(SpecExpressionPath {
                        value,
                        facts,
                        obligations,
                    });
                    continue;
                }
                for case in algebraic_case_paths(&scrutinee_path.value, budget)? {
                    let Some(arm) = arms.iter().find(|arm| arm.variant == case.variant) else {
                        return Err(ExecutionLimit::Paths);
                    };
                    if arm.bindings.len() != case.fields.len()
                        || arm.binding_types
                            != case
                                .fields
                                .iter()
                                .map(AlgebraicValue::value_type)
                                .collect::<Vec<_>>()
                    {
                        return Err(ExecutionLimit::Paths);
                    }
                    let mut body_state = state.clone();
                    let mut body_algebraic_bindings = algebraic_bindings.clone();
                    for (binding, field) in arm.bindings.iter().zip(&case.fields) {
                        match field {
                            AlgebraicValue::C(field) => {
                                body_state.locals.set(binding.clone(), field.clone());
                            }
                            AlgebraicValue::Algebraic(field) => {
                                body_algebraic_bindings.insert(binding.clone(), field.clone());
                            }
                        }
                    }
                    let Some((case_facts, case_obligations)) =
                        merge_execution_pure_facts_and_obligations(
                            &scrutinee_path.facts,
                            &scrutinee_path.obligations,
                            &case.facts,
                            &case.obligations,
                            assumptions,
                        )
                    else {
                        continue;
                    };
                    let body_assumptions =
                        assumptions_with_path_context(assumptions, &case_facts, &case_obligations);
                    for body_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                        &body_state,
                        &arm.body,
                        loop_entry_state,
                        &body_assumptions,
                        &body_algebraic_bindings,
                        budget,
                    )? {
                        if let Some((facts, obligations)) =
                            merge_execution_pure_facts_and_obligations(
                                &case_facts,
                                &case_obligations,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                            )
                        {
                            paths.push(SpecExpressionPath {
                                value: body_path.value,
                                facts,
                                obligations,
                            });
                        }
                    }
                }
            }
            paths
        }
        SpecExpression::CExpression(expression) => {
            evaluate_c_expression_paths(state, expression, assumptions, budget)?
                .into_iter()
                .filter_map(c_expression_path_value)
                .collect()
        }
        SpecExpression::CountedResourceCount { name, arguments } => {
            let mut argument_paths =
                vec![(Vec::<Option<AlgebraicValue>>::new(), Vec::new(), Vec::new())];
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
                    for argument_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                        state,
                        argument,
                        loop_entry_state,
                        &path_assumptions,
                        algebraic_bindings,
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
                        next_values.push(Some(AlgebraicValue::C(argument_path.value)));
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
                                        crate::kernel::resource_arguments_proven_equal(
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
        SpecExpression::Add(left, right) => evaluate_spec_add_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
        )?,
        SpecExpression::Subtract(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_scalar_subtract(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::Multiply(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_multiply(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::Divide(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_divide(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::Remainder(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_remainder(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::ShiftLeft(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::ShiftRight(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        SpecExpression::BitwiseAnd(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::And,
                )
            },
        )?,
        SpecExpression::BitwiseOr(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Or,
                )
            },
        )?,
        SpecExpression::BitwiseXor(left, right) => evaluate_spec_scalar_binary_paths(
            state,
            left,
            right,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Xor,
                )
            },
        )?,
        SpecExpression::Cast(expression, target_type) => evaluate_spec_scalar_unary_paths(
            state,
            expression,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |value, facts, mut obligations| {
                let outcome =
                    cast_c_value_to_type(value, *target_type, &mut obligations, assumptions)
                        .map(CExpressionOutcome::Value)
                        .unwrap_or_else(CExpressionOutcome::RuntimeError);
                vec![CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                }]
            },
        )?,
        SpecExpression::BitwiseNot(expression) => evaluate_spec_scalar_unary_paths(
            state,
            expression,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
            |value, facts, obligations| apply_c_bitwise_not(value, facts, obligations, assumptions),
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
            algebraic_bindings,
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
            algebraic_bindings,
            budget,
        )?,
        SpecExpression::Let { name, value, body } => {
            let mut paths = Vec::new();
            for value_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                value,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
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
                for body_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                    &body_state,
                    body,
                    loop_entry_state,
                    &body_assumptions,
                    algebraic_bindings,
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
        SpecExpression::PureFunctionApplication {
            name,
            arguments,
            result_type,
        } => evaluate_spec_pure_function_application_paths(
            state,
            name,
            arguments,
            *result_type,
            loop_entry_state,
            assumptions,
            algebraic_bindings,
            budget,
        )?,
        SpecExpression::LoopEntrySnapshot(expression) => {
            if let Some(loop_entry_state) = loop_entry_state {
                evaluate_spec_expression_paths_with_algebraic_bindings(
                    loop_entry_state,
                    expression,
                    Some(loop_entry_state),
                    assumptions,
                    algebraic_bindings,
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
            algebraic_bindings,
            budget,
        )?,
        SpecExpression::MemoryLoad {
            memory,
            pointer,
            value_type,
        } => {
            let mut paths = Vec::new();
            for pointer_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                pointer,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )? {
                let CValue::Pointer(pointer) = pointer_path.value else {
                    continue;
                };
                let pointer = pointer.into_pointer();
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
                if assumptions.should_keep_spec_loads_symbolic() {
                    paths.extend(
                        evaluate_spec_memory_load_paths(
                            memory,
                            pointer,
                            *value_type,
                            pointer_path.facts,
                            pointer_path.obligations,
                            assumptions,
                            &mut budget.next_kernel_variable,
                        )
                        .into_iter()
                        .filter_map(c_expression_path_value),
                    );
                    continue;
                }

                // Executable contract and invariant checking preserves the
                // historical one-term spec semantics. It must not branch over
                // the current C heap's unresolved aliases: those branches are
                // C execution choices, while this expression denotes a pure
                // load from one specified snapshot.
                let mut facts = pointer_path.facts;
                let mut value = None;
                if let Some(stored) = memory.known_union_value(&pointer, *value_type) {
                    value = value_type.accepts(&stored).then_some(stored);
                }
                if value.is_none()
                    && let Some(stored) = memory.known_value(&pointer)
                {
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
                        base: pointer.clone(),
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
    arguments: &[SpecPureFunctionArgument],
    result_type: CType,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = vec![(Vec::new(), Vec::new(), Vec::new())];
    for argument in arguments {
        let mut next = Vec::new();
        for (values, facts, obligations) in paths {
            let path_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            for argument_path in evaluate_spec_pure_function_argument_paths(
                state,
                argument,
                loop_entry_state,
                &path_assumptions,
                algebraic_bindings,
                budget,
            )? {
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
                    merged_values.push(argument_path.value);
                    next.push((merged_values, merged_facts, merged_obligations));
                }
            }
        }
        paths = next;
    }
    let mut results = Vec::new();
    for (arguments, facts, obligations) in paths {
        let Some(value) = c_value_from_bitvector_term(
            result_type,
            Bitvector32Term::ClickFunctionApplication {
                name: name.to_string(),
                arguments,
            },
        ) else {
            continue;
        };
        results.push(SpecExpressionPath {
            value,
            facts,
            obligations,
        });
    }
    Ok(results)
}

fn evaluate_spec_pure_function_argument_paths(
    state: &CState,
    argument: &SpecPureFunctionArgument,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecPureFunctionArgumentPath>> {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            Ok(evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                expression,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPureFunctionArgumentPath {
                value: PureFunctionArgument::Value(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            Ok(evaluate_spec_algebraic_at_state_with_bindings(
                state,
                expression,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPureFunctionArgumentPath {
                value: PureFunctionArgument::Algebraic(path.value),
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
        SpecPureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => {
            let memory = match memory {
                SpecMemory::Current => state.memory(),
                SpecMemory::FunctionEntry | SpecMemory::LoopEntry => {
                    let Some(entry) = loop_entry_state else {
                        return Ok(Vec::new());
                    };
                    entry.memory()
                }
                SpecMemory::Fixed(memory) => memory,
            };
            Ok(evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                pointer,
                loop_entry_state,
                assumptions,
                algebraic_bindings,
                budget,
            )?
            .into_iter()
            .map(|path| SpecPureFunctionArgumentPath {
                value: PureFunctionArgument::ArrayRef {
                    memory: memory.clone(),
                    pointer: path.value,
                    element_type: *element_type,
                },
                facts: path.facts,
                obligations: path.obligations,
            })
            .collect())
        }
    }
}

fn c_value_bitvector_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Bool(term) => Some(term.clone()),
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => Some(term.clone()),
        CValue::Void | CValue::Pointer(_) => None,
    }
}

fn c_value_from_bitvector_term(c_type: CType, term: Bitvector32Term) -> Option<CValue> {
    Some(match c_type {
        CType::Int16 => CValue::Int16(term),
        CType::Int32 => CValue::Int32(term),
        CType::UInt8 => CValue::UInt8(term),
        CType::UInt16 => CValue::UInt16(term),
        CType::UInt32 => CValue::UInt32(term),
        CType::Int64 => CValue::Int64(term),
        CType::UInt64 => CValue::UInt64(term),
        CType::Float32 => CValue::Float32(term),
        CType::Float64 => CValue::Float64(term),
        _ => return None,
    })
}

pub(super) fn evaluate_spec_pointer_offset_paths(
    state: &CState,
    pointer: &SpecExpression,
    elements: &SpecExpression,
    byte_width: u32,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for pointer_path in evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        pointer,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let CValue::Pointer(pointer) = pointer_path.value else {
            continue;
        };
        let pointer_type = pointer.c_type();
        let pointer = pointer.into_pointer();
        let element_assumptions = assumptions_with_path_context(
            assumptions,
            &pointer_path.facts,
            &pointer_path.obligations,
        );
        for element_path in evaluate_spec_expression_paths_with_algebraic_bindings(
            state,
            elements,
            loop_entry_state,
            &element_assumptions,
            algebraic_bindings,
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
                value: CValue::typed_pointer(
                    pointer.offset_by_elements(elements, byte_width),
                    pointer_type,
                ),
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    let left_step_width = spec_expression_pointer_step_width(state, left);
    let right_step_width = spec_expression_pointer_step_width(state, right);
    for left_path in evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_expression_paths_with_algebraic_bindings(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
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

pub(super) fn evaluate_spec_scalar_binary_paths(
    state: &CState,
    left: &SpecExpression,
    right: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
    apply: impl Fn(CValue, CValue, Vec<ExecutionPureFact>, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        left,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_spec_expression_paths_with_algebraic_bindings(
            state,
            right,
            loop_entry_state,
            &right_assumptions,
            algebraic_bindings,
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
                apply(
                    left_path.value.clone(),
                    right_path.value,
                    facts,
                    obligations,
                )
                .into_iter()
                .filter_map(c_expression_path_value),
            );
        }
    }
    Ok(paths)
}

pub(super) fn evaluate_spec_scalar_unary_paths(
    state: &CState,
    expression: &SpecExpression,
    loop_entry_state: Option<&CState>,
    assumptions: &PureFactContext,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
    apply: impl Fn(CValue, Vec<ExecutionPureFact>, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        expression,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        paths.extend(
            apply(path.value, path.facts, path.obligations)
                .into_iter()
                .filter_map(c_expression_path_value),
        );
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for condition_path in lower_spec_proposition_at_state_with_algebraic_bindings(
        state,
        condition,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let branch_assumptions = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        // Logical expressions must have the same shape at declaration and
        // application sites. Ambient proof facts justify explicit reductions,
        // not a different expression during lowering.
        let context_free = PureFactContext::new();
        let condition_truth = if context_free.proves(&condition_path.proposition) {
            Some(true)
        } else if assumptions_prove_proposition_false(&context_free, &condition_path.proposition) {
            Some(false)
        } else {
            None
        };

        let branch_paths = match condition_truth {
            Some(true) => evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                then_branch,
                loop_entry_state,
                &branch_assumptions,
                algebraic_bindings,
                budget,
            )?,
            Some(false) => evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                else_branch,
                loop_entry_state,
                &branch_assumptions,
                algebraic_bindings,
                budget,
            )?,
            None => {
                let then_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
                    state,
                    then_branch,
                    loop_entry_state,
                    &branch_assumptions,
                    algebraic_bindings,
                    budget,
                )?;
                let else_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
                    state,
                    else_branch,
                    loop_entry_state,
                    &branch_assumptions,
                    algebraic_bindings,
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<SpecExpressionPath>> {
    let mut paths = Vec::new();
    for start_path in evaluate_spec_expression_paths_with_algebraic_bindings(
        state,
        start,
        loop_entry_state,
        assumptions,
        algebraic_bindings,
        budget,
    )? {
        let CValue::Int32(start) = start_path.value else {
            continue;
        };
        let start_assumptions =
            assumptions_with_path_context(assumptions, &start_path.facts, &start_path.obligations);
        for end_path in evaluate_spec_expression_paths_with_algebraic_bindings(
            state,
            end,
            loop_entry_state,
            &start_assumptions,
            algebraic_bindings,
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
            for initial_path in evaluate_spec_expression_paths_with_algebraic_bindings(
                state,
                initial,
                loop_entry_state,
                &bound_assumptions,
                algebraic_bindings,
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
                    algebraic_bindings,
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
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
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
                let mut body_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
                    &body_state,
                    body,
                    loop_entry_state,
                    &body_assumptions,
                    algebraic_bindings,
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
            let mut body_paths = evaluate_spec_expression_paths_with_algebraic_bindings(
                &body_state,
                body,
                loop_entry_state,
                &body_assumptions,
                algebraic_bindings,
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
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => Some((
            ConditionTerm::AlgebraicEqual(Box::new(left.clone()), Box::new(right.clone())),
            true,
        )),
        Proposition::Not(body) => {
            let (condition, value) = proposition_as_single_condition(body)?;
            Some((condition, !value))
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
        (CValue::Pointer(left), CValue::Pointer(right))
            if left.c_type().pointer_types_compatible(right.c_type())
                || left.is_null()
                || right.is_null() =>
        {
            match operator {
                CComparisonOperator::Equal => Some((
                    pointer_equality_condition(left.pointer().clone(), right.pointer().clone()),
                    true,
                )),
                CComparisonOperator::NotEqual => Some((
                    pointer_equality_condition(left.pointer().clone(), right.pointer().clone()),
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
            }
        }
        (CValue::Pointer(_), CValue::Pointer(_)) => None,
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            match operator {
                CComparisonOperator::Equal => {
                    Some((pointer_is_null_condition(pointer.pointer().clone()), true))
                }
                CComparisonOperator::NotEqual => {
                    Some((pointer_is_null_condition(pointer.pointer().clone()), false))
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

    let target_type = if matches!(left, CValue::Float64(_)) || matches!(right, CValue::Float64(_)) {
        Some(CType::Float64)
    } else if matches!(left, CValue::Float32(_)) || matches!(right, CValue::Float32(_)) {
        Some(CType::Float32)
    } else {
        None
    };
    if let Some(target_type) = target_type {
        let mut obligations = Vec::new();
        let left = coerce_c_value_to_type(
            left.clone(),
            target_type,
            &mut obligations,
            &PureFactContext::new(),
        )?;
        let right = coerce_c_value_to_type(
            right.clone(),
            target_type,
            &mut obligations,
            &PureFactContext::new(),
        )?;
        if !obligations.is_empty() {
            return None;
        }
        let condition = match (target_type, left, right) {
            (CType::Float32, CValue::Float32(left), CValue::Float32(right)) => {
                ConditionTerm::float32_compare(left, right, operator)
            }
            (CType::Float64, CValue::Float64(left), CValue::Float64(right)) => {
                ConditionTerm::float64_compare(left, right, operator)
            }
            _ => return None,
        };
        return Some(Proposition::ConditionIs(
            condition,
            !matches!(operator, CComparisonOperator::NotEqual),
        ));
    }

    if matches!(left, CValue::UInt64(_)) || matches!(right, CValue::UInt64(_)) {
        let left = c_value_uint64_term(left)?;
        let right = c_value_uint64_term(right)?;
        let condition = match operator {
            CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
                ConditionTerm::uint64_equal(left, right)
            }
            CComparisonOperator::LessThan => ConditionTerm::uint64_less_than(left, right),
            CComparisonOperator::LessEqual => ConditionTerm::uint64_less_equal(left, right),
            CComparisonOperator::GreaterThan => ConditionTerm::uint64_greater_than(left, right),
            CComparisonOperator::GreaterEqual => ConditionTerm::uint64_greater_equal(left, right),
        };
        return Some(Proposition::ConditionIs(
            condition,
            !matches!(operator, CComparisonOperator::NotEqual),
        ));
    }
    if matches!(left, CValue::Int64(_)) || matches!(right, CValue::Int64(_)) {
        let left = c_value_int64_term(left)?;
        let right = c_value_int64_term(right)?;
        let condition = match operator {
            CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
                ConditionTerm::int64_equal(left, right)
            }
            CComparisonOperator::LessThan => ConditionTerm::int64_signed_less_than(left, right),
            CComparisonOperator::LessEqual => ConditionTerm::int64_signed_less_equal(left, right),
            CComparisonOperator::GreaterThan => {
                ConditionTerm::int64_signed_greater_than(left, right)
            }
            CComparisonOperator::GreaterEqual => {
                ConditionTerm::int64_signed_greater_equal(left, right)
            }
        };
        return Some(Proposition::ConditionIs(
            condition,
            !matches!(operator, CComparisonOperator::NotEqual),
        ));
    }

    let unsigned = matches!(left, CValue::UInt32(_)) || matches!(right, CValue::UInt32(_));
    let left = c_value_int32_term(left)?;
    let right = c_value_int32_term(right)?;
    let (condition, value) = match operator {
        CComparisonOperator::Equal => (ConditionTerm::equal(left, right), true),
        CComparisonOperator::NotEqual => (ConditionTerm::equal(left, right), false),
        CComparisonOperator::LessThan => (
            if unsigned {
                ConditionTerm::unsigned_less_than(left, right)
            } else {
                ConditionTerm::signed_less_than(left, right)
            },
            true,
        ),
        CComparisonOperator::LessEqual => (
            if unsigned {
                ConditionTerm::unsigned_less_equal(left, right)
            } else {
                ConditionTerm::signed_less_equal(left, right)
            },
            true,
        ),
        CComparisonOperator::GreaterThan => (
            if unsigned {
                ConditionTerm::unsigned_greater_than(left, right)
            } else {
                ConditionTerm::signed_greater_than(left, right)
            },
            true,
        ),
        CComparisonOperator::GreaterEqual => (
            if unsigned {
                ConditionTerm::unsigned_greater_equal(left, right)
            } else {
                ConditionTerm::signed_greater_equal(left, right)
            },
            true,
        ),
    };
    Some(Proposition::ConditionIs(condition, value))
}

fn c_value_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Bool(value)
        | CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value)
        | CValue::UInt32(value) => Some(value.clone()),
        CValue::Void
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn c_value_int64_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int64(value) => Some(value.clone()),
        CValue::Bool(value) => Some(Bitvector32Term::int64_from_32(value.clone())),
        CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value) => Some(Bitvector32Term::int64_from_32(value.clone())),
        CValue::UInt32(value) => Some(Bitvector32Term::int64_from_uint32(value.clone())),
        CValue::Void
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn c_value_uint64_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::UInt64(value) => Some(value.clone()),
        CValue::Bool(value) => Some(Bitvector32Term::uint64_from_32(value.clone())),
        CValue::Int64(value) => Some(Bitvector32Term::uint64_from_int64(value.clone())),
        CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value) => Some(Bitvector32Term::uint64_from_int32(value.clone())),
        CValue::UInt32(value) => Some(Bitvector32Term::uint64_from_32(value.clone())),
        CValue::Void | CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => None,
    }
}

#[cfg(test)]
mod integer_quantifier_tests {
    use super::*;
    use crate::kernel::reasoning::substitute_integer_variable_in_pure_proposition;

    fn integer_comparison(variable: Variable) -> SpecProposition {
        SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(IntegerTerm::var(variable)),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
        }
    }

    #[test]
    fn integer_quantifiers_lower_to_sorted_kernel_quantifiers() {
        let variable = Variable(700);
        let state = CState::new();
        let assumptions = PureFactContext::new();
        for (quantifier, expected_sort) in [(true, Sort::Integer), (false, Sort::Integer)] {
            let proposition = if quantifier {
                SpecProposition::ForAllInteger {
                    name: "z".into(),
                    variable,
                    body: Box::new(integer_comparison(variable)),
                }
            } else {
                SpecProposition::ExistsInteger {
                    name: "z".into(),
                    variable,
                    body: Box::new(integer_comparison(variable)),
                }
            };
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                &state,
                &proposition,
                None,
                &assumptions,
                &mut ExecutionBudget::default(),
            )
            .expect("Integer quantifier should lower");
            assert_eq!(paths.len(), 1);
            assert!(paths[0].facts.is_empty());
            assert!(paths[0].obligations.is_empty());
            match &paths[0].proposition {
                Proposition::ForAll { sort, var, .. } | Proposition::Exists { sort, var, .. } => {
                    assert_eq!(*sort, expected_sort);
                    assert_eq!(*var, variable);
                }
                other => panic!("unexpected lowered proposition: {other:?}"),
            }
        }
    }

    #[test]
    fn integer_substitution_is_capture_avoiding_through_nested_binders() {
        let source = Proposition::ForAll {
            var: Variable(1),
            sort: Sort::Integer,
            body: Box::new(Proposition::Exists {
                name: "inner".into(),
                var: Variable(2),
                sort: Sort::Integer,
                body: Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(Variable(9))),
                    Term::Integer(IntegerTerm::var(Variable(2))),
                )),
            }),
        };
        let substituted = substitute_integer_variable_in_pure_proposition(
            &source,
            Variable(9),
            &IntegerTerm::var(Variable(1)),
        )
        .expect("pure Integer substitution should accept nested binders");
        let Proposition::ForAll { var, body, .. } = substituted else {
            panic!("substitution changed the outer quantifier carrier");
        };
        assert_ne!(
            var,
            Variable(1),
            "replacement variable must not be captured"
        );
        let Proposition::Exists {
            var: inner, body, ..
        } = *body
        else {
            panic!("substitution changed the inner quantifier carrier");
        };
        assert_eq!(inner, Variable(2));
        let Proposition::Equal(Term::Integer(left), Term::Integer(right)) = *body else {
            panic!("substitution changed the pure Integer proposition");
        };
        assert_eq!(left, IntegerTerm::var(Variable(1)));
        assert_eq!(right, IntegerTerm::var(Variable(2)));
    }

    #[test]
    fn integer_existential_rejects_conditional_path_facts() {
        let mut state = CState::new();
        state
            .locals
            .set("flag", int32(Bitvector32Term::Variable(Variable(900))));
        let proposition = SpecProposition::ExistsInteger {
            name: "z".into(),
            variable: Variable(901),
            body: Box::new(SpecProposition::Comparison {
                left: SpecExpression::CExpression(CExpression::Conditional {
                    condition: Box::new(CExpression::Variable("flag".into())),
                    then_branch: Box::new(CExpression::Divide(
                        Box::new(CExpression::Value(int32(Bitvector32Term::constant(
                            0x8000_0000,
                        )))),
                        Box::new(CExpression::Value(int32(Bitvector32Term::constant(
                            u32::MAX,
                        )))),
                    )),
                    else_branch: Box::new(CExpression::Value(int32(Bitvector32Term::constant(0)))),
                }),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(Bitvector32Term::constant(1))),
            }),
        };
        let result = lower_spec_proposition_at_state_with_loop_entry(
            &state,
            &proposition,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        );
        assert_eq!(
            result,
            Err(ExecutionLimit::UnsupportedIntegerExistentialBody)
        );
    }
}
