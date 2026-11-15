use super::*;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{bits32_constant, constant_u32};
use crate::surface::planning::solve::plan_context_free_closer;
use crate::surface::planning::solve::plan_explicit_equality_rewrites_from;

pub(super) fn surface_logical_children(
    goal: &ClickProposition,
    conjunction: bool,
) -> Option<(ClickProposition, ClickProposition)> {
    match goal {
        ClickProposition::And(left, right) if conjunction => {
            Some((left.as_ref().clone(), right.as_ref().clone()))
        }
        ClickProposition::Or(left, right) if !conjunction => {
            Some((left.as_ref().clone(), right.as_ref().clone()))
        }
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } if conjunction => {
            let left = written_sequence_elements(left)?;
            let right = written_sequence_elements(right)?;
            if left.len() != right.len() || left.len() < 2 {
                return None;
            }
            // Match finite_sequence_equality's pairwise balanced tree. The
            // written comparison names the whole tree; its children retain
            // element spellings, including each operand's state.
            let mut level = left
                .into_iter()
                .zip(right)
                .map(|(left, right)| ClickProposition::Comparison {
                    left,
                    operator: ComparisonOperator::Equal,
                    right,
                })
                .collect::<Vec<_>>();
            while level.len() > 2 {
                let mut next = Vec::with_capacity(level.len().div_ceil(2));
                let mut values = level.into_iter();
                while let Some(left) = values.next() {
                    crate::instrumentation::record_deterministic_work(1);
                    next.push(match values.next() {
                        Some(right) => ClickProposition::And(Box::new(left), Box::new(right)),
                        None => left,
                    });
                }
                level = next;
            }
            let right = level.pop()?;
            Some((level.pop()?, right))
        }
        ClickProposition::At {
            selector,
            proposition,
        } => {
            let (left, right) = surface_logical_children(proposition, conjunction)?;
            Some((
                ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(left),
                },
                ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(right),
                },
            ))
        }
        _ => None,
    }
}

/// Flatten only explicit sequence syntax. Memory state wrappers apply to each
/// element; no value evaluation or fact-dependent simplification participates.
fn written_sequence_elements(expression: &ContractExpression) -> Option<Vec<ContractExpression>> {
    let mut pending = vec![(expression, Vec::<Option<ProgramPointSelector>>::new())];
    let mut elements = Vec::new();
    while let Some((expression, selectors)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            ContractExpression::SequenceConcat(left, right) => {
                pending.push((right, selectors.clone()));
                pending.push((left, selectors));
            }
            ContractExpression::SequenceLiteral(values) => {
                for value in values {
                    crate::instrumentation::record_deterministic_work(1 + selectors.len());
                    let mut value = value.clone();
                    for selector in selectors.iter().rev() {
                        value = match selector {
                            Some(selector) => ContractExpression::At {
                                selector: selector.clone(),
                                expression: Box::new(value),
                            },
                            None => ContractExpression::Old(Box::new(value)),
                        };
                    }
                    elements.push(value);
                }
            }
            ContractExpression::Old(inner) => {
                let mut selectors = selectors;
                selectors.push(None);
                pending.push((inner, selectors));
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                let mut selectors = selectors;
                selectors.push(Some(selector.clone()));
                pending.push((expression, selectors));
            }
            _ => return None,
        }
    }
    Some(elements)
}

#[cfg(test)]
mod sequence_scaling_tests {
    include!("../../scaling_tests/surface/proof/surface_certificates.rs");
}

/// How one written universal's body continues under the binder.
///
/// The kernel form of a range quantifier is the binder followed by the range
/// membership guard; the guard's consequent is the written body. A written
/// implication instead has both parts written.
pub(super) enum WrittenAntecedent {
    Implication {
        antecedent: ClickProposition,
        consequent: ClickProposition,
    },
    RangeGuard {
        body: ClickProposition,
    },
}

/// Refines the written goal a recorded written implication introduces.
///
/// Only the recorded head chain decides that this kernel node is a written
/// connective; this function then reads which written form carries it.
pub(super) fn written_implication_consequent(goal: &ClickProposition) -> Option<WrittenAntecedent> {
    match goal {
        ClickProposition::Implies(antecedent, consequent) => Some(WrittenAntecedent::Implication {
            antecedent: antecedent.as_ref().clone(),
            consequent: consequent.as_ref().clone(),
        }),
        ClickProposition::RangeAll { body, .. } => Some(WrittenAntecedent::RangeGuard {
            body: body.as_ref().clone(),
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => match written_implication_consequent(proposition)? {
            WrittenAntecedent::Implication {
                antecedent,
                consequent,
            } => Some(WrittenAntecedent::Implication {
                antecedent: ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(antecedent),
                },
                consequent: ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(consequent),
                },
            }),
            WrittenAntecedent::RangeGuard { body } => Some(WrittenAntecedent::RangeGuard {
                body: ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(body),
                },
            }),
        },
        _ => None,
    }
}

/// Refines the written goal a recorded written universal introduces.
///
/// A `forall` writes its body directly. A range quantifier keeps its written
/// form focused: its range guard is the next introduction, and that guard
/// exposes the written body.
pub(super) fn written_universal_body(goal: &ClickProposition) -> Option<ClickProposition> {
    match goal {
        ClickProposition::ForAll { body, .. } => Some(body.as_ref().clone()),
        ClickProposition::RangeAll { .. } => Some(goal.clone()),
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(written_universal_body(proposition)?),
        }),
        _ => None,
    }
}

/// Select just the antecedent without copying the unselected consequent.
pub(super) fn surface_implication_antecedent(goal: &ClickProposition) -> Option<ClickProposition> {
    match goal {
        ClickProposition::Implies(antecedent, _) => Some(antecedent.as_ref().clone()),
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_implication_antecedent(proposition)?),
        }),
        _ => None,
    }
}

pub(super) fn surface_implication_parts(
    goal: &ClickProposition,
) -> Option<(ClickProposition, ClickProposition)> {
    match goal {
        ClickProposition::Implies(antecedent, consequent) => {
            Some((antecedent.as_ref().clone(), consequent.as_ref().clone()))
        }
        ClickProposition::At {
            selector,
            proposition,
        } => {
            let (antecedent, consequent) = surface_implication_parts(proposition)?;
            Some((
                ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(antecedent),
                },
                ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(consequent),
                },
            ))
        }
        _ => None,
    }
}

fn contract_expression_for_instantiation_value(value: &MachineTerm) -> Option<ContractExpression> {
    let bits32_constant!(bits) = value else {
        return None;
    };
    Some(ContractExpression::ProgramExpression(
        ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(constant_u32(
            *bits,
        )))),
    ))
}

/// Plans an explicit universal-instantiation certificate: one listed
/// universal premise, specialized at an explicit constant, proves the goal
/// after its guards discharge from the remaining listed premises. The named
/// `instantiate ... using` step adds the specialized fact and `known`
/// closes the exact goal, matching independent proof-step check.
pub(super) fn plan_explicit_forall_instantiation(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let Proposition::ForAll {
            var, sort, body, ..
        } = kernel
        else {
            continue;
        };
        if *sort != Sort::ProgramInt32 {
            continue;
        }
        let other_kernels = premise_pairs
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != index)
            .map(|(_, (kernel, _))| kernel.clone())
            .collect::<Vec<_>>();
        let other_surfaces = premise_pairs
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != index)
            .map(|(_, (_, surface))| surface.clone())
            .collect::<Vec<_>>();
        for value in crate::kernel::forall_instantiation_candidate_values(kernel, goal) {
            let Some(argument) = contract_expression_for_instantiation_value(&value) else {
                continue;
            };
            let instantiated = substitute_int32_variable_in_proposition(body, *var, value.clone());
            let Ok((_, conclusion)) = discharge_instantiated_guards(instantiated, &other_kernels)
            else {
                continue;
            };
            // The closer is `known`, so the instantiated conclusion must
            // match the goal by exactly the equivalence `known` checks.
            if conclusion != *goal {
                continue;
            }
            let tactics = vec![
                ProofTactic::InstantiateUsing {
                    quantified: surface.clone(),
                    argument,
                    premises: Some(other_surfaces.clone()),
                },
                ProofTactic::Known,
            ];
            return Some(tactics);
        }
    }
    None
}

pub(super) fn plan_explicit_forall_instantiation_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    extra_arguments: &[(MachineTerm, ContractExpression)],
    conclusion_gate: &dyn Fn(&Proposition) -> bool,
) -> Option<Vec<ProofTactic>> {
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let Proposition::ForAll { sort, .. } = kernel else {
            continue;
        };
        if *sort != Sort::ProgramInt32 {
            continue;
        }
        let discharge_kernels = premise_pairs
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != index)
            .map(|(_, (kernel, _))| kernel.clone())
            .collect::<Vec<_>>();
        let using_surfaces = premise_pairs
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != index)
            .map(|(_, (_, surface))| surface.clone())
            .collect::<Vec<_>>();
        let mut arguments = extra_arguments.to_vec();
        arguments.extend(
            crate::kernel::forall_instantiation_candidate_values(kernel, goal)
                .into_iter()
                .filter_map(|value| {
                    contract_expression_for_instantiation_value(&value)
                        .map(|argument| (value, argument))
                }),
        );
        for (value, argument) in arguments {
            if let Some(tactics) = plan_explicit_universal_conclusion_discharge(
                kernel,
                surface,
                value,
                &argument,
                goal,
                surface_goal,
                &discharge_kernels,
                &using_surfaces,
                Some(conclusion_gate),
            ) {
                return Some(tactics);
            }
        }
    }
    None
}

/// Plans an explicit certificate for a universal goal: introduce the binder
/// (and implication antecedent), then specialize one listed universal premise
/// at the introduced binder. Instantiation adds the specialized fact; an
/// optional transport adds its target, and `known` closes the exact goal.
/// The instantiated guards discharge from the introduced antecedent plus the
/// remaining listed premises.
#[allow(clippy::too_many_arguments)]
fn plan_explicit_universal_conclusion_discharge(
    premise_kernel: &Proposition,
    premise_surface: &ClickProposition,
    argument_term: MachineTerm,
    argument_expression: &ContractExpression,
    goal_conclusion: &Proposition,
    surface_goal_conclusion: &ClickProposition,
    discharge_kernels: &[Proposition],
    using_surfaces: &[ClickProposition],
    conclusion_gate: Option<&dyn Fn(&Proposition) -> bool>,
) -> Option<Vec<ProofTactic>> {
    let Proposition::ForAll {
        var: premise_var,
        sort: Sort::ProgramInt32,
        body: premise_body,
        ..
    } = premise_kernel
    else {
        return None;
    };
    let instantiated =
        substitute_int32_variable_in_proposition(premise_body, *premise_var, argument_term);
    let (_, conclusion) = discharge_instantiated_guards(instantiated, discharge_kernels).ok()?;
    let closes_by_known =
        conclusion == *goal_conclusion || conclusion.clone() == goal_conclusion.clone();
    // Constant-argument instances offer several instantiation candidates, so
    // the caller may insist the instantiated conclusion provably reaches the
    // goal before accepting a transport that check would reject.
    if !closes_by_known
        && let Some(gate) = conclusion_gate
        && !gate(&conclusion)
    {
        return None;
    }
    // A residual form difference (for example a loop counter the listed
    // order facts pin to a constant) crosses through an explicit transport
    // from the instantiated conclusion instead. The transported closure is
    // validated by the caller's immediate certificate validation, so no weaker
    // equivalence pre-check runs here.
    let transport_closure = if closes_by_known {
        None
    } else {
        // A loop-exit universal invariant fact is written through an
        // `at(point, ...)` wrapper; peel it here and restore it on the
        // substituted transport source so the source lowers at the same
        // state the premise denotes.
        let (premise_selector, premise_forall) = match premise_surface {
            ClickProposition::At {
                selector,
                proposition,
            } => (Some(selector), proposition.as_ref()),
            other => (None, other),
        };
        let ClickProposition::ForAll {
            name: premise_binder,
            body: premise_surface_body,
            ..
        } = premise_forall
        else {
            return None;
        };
        let premise_surface_conclusion = match premise_surface_body.as_ref() {
            ClickProposition::Implies(_, conclusion) => conclusion.as_ref(),
            body => body,
        };
        let substitutions = std::iter::once((premise_binder.clone(), argument_expression.clone()))
            .collect::<BTreeMap<_, _>>();
        let source =
            substitute_click_proposition(premise_surface_conclusion, &substitutions).ok()?;
        let source = match premise_selector {
            Some(selector) => ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(source),
            },
            None => source,
        };
        Some((source, surface_goal_conclusion.clone()))
    };
    let mut tactics = vec![ProofTactic::InstantiateUsing {
        quantified: premise_surface.clone(),
        argument: argument_expression.clone(),
        premises: Some(using_surfaces.to_vec()),
    }];
    if let Some((source, target)) = transport_closure {
        if let Some((historical, current)) = comparison_state_expression_pair(&source, &target) {
            let reflexive = ClickProposition::Comparison {
                left: historical.clone(),
                operator: ComparisonOperator::Equal,
                right: historical.clone(),
            };
            let forward = ClickProposition::Comparison {
                left: historical.clone(),
                operator: ComparisonOperator::Equal,
                right: current.clone(),
            };
            let reverse = ClickProposition::Comparison {
                left: current,
                operator: ComparisonOperator::Equal,
                right: historical,
            };
            let mut bridge_premises = vec![reflexive.clone()];
            bridge_premises.extend(using_surfaces.iter().cloned());
            tactics.push(ProofTactic::Have(ProofHave {
                proposition: forward.clone(),
                proof: SourceProof::Script(vec![ProofTactic::TransportUsing {
                    source: reflexive,
                    target: forward.clone(),
                    premises: bridge_premises,
                }]),
            }));
            tactics.push(ProofTactic::Have(ProofHave {
                proposition: reverse.clone(),
                proof: SourceProof::Script(vec![ProofTactic::Rewrite(forward), ProofTactic::Known]),
            }));
            tactics.push(ProofTactic::Rewrite(reverse));
        } else {
            let mut transport_premises = vec![source.clone()];
            transport_premises.extend(using_surfaces.iter().cloned());
            tactics.push(ProofTactic::TransportUsing {
                source,
                target,
                premises: transport_premises,
            });
        }
    }
    tactics.push(ProofTactic::Known);
    Some(tactics)
}

/// Finds the comparison operand written as the same expression at a named
/// state and at the current state. An equality bridge for that operand can
/// then carry the surrounding comparison by an ordinary checked rewrite.
fn comparison_state_expression_pair(
    source: &ClickProposition,
    target: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    let (
        ClickProposition::Comparison {
            left: source_left,
            operator: source_operator,
            right: source_right,
        },
        ClickProposition::Comparison {
            left: target_left,
            operator: target_operator,
            right: target_right,
        },
    ) = (source, target)
    else {
        return None;
    };
    if source_operator != target_operator {
        return None;
    }
    [
        (source_left, target_left, source_right, target_right),
        (source_right, target_right, source_left, target_left),
    ]
    .into_iter()
    .find_map(
        |(historical, current, source_other, target_other)| match historical {
            ContractExpression::At { expression, .. }
                if expression.as_ref() == current && source_other == target_other =>
            {
                Some((historical.clone(), current.clone()))
            }
            _ => None,
        },
    )
}

pub(super) fn plan_explicit_forall_goal_from_premises(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ForAll {
        var: goal_var,
        sort: Sort::ProgramInt32,
        body: goal_body,
        ..
    } = goal
    else {
        return None;
    };
    let ClickProposition::ForAll {
        name: binder_name,
        body: surface_body,
        ..
    } = surface_goal
    else {
        return None;
    };
    let (antecedent, goal_conclusion, surface_antecedent) =
        match (goal_body.as_ref(), surface_body.as_ref()) {
            (
                Proposition::Implies(antecedent, conclusion),
                ClickProposition::Implies(surface_antecedent, _),
            ) => (
                Some(antecedent.as_ref().clone()),
                conclusion.as_ref(),
                Some(surface_antecedent.as_ref().clone()),
            ),
            (body, _) => (None, body, None),
        };
    let surface_goal_conclusion = match surface_body.as_ref() {
        ClickProposition::Implies(_, conclusion) => conclusion.as_ref(),
        body => body,
    };
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let mut discharge_kernels = antecedent.iter().cloned().collect::<Vec<_>>();
        let mut using_surfaces = surface_antecedent.iter().cloned().collect::<Vec<_>>();
        for (other, (other_kernel, other_surface)) in premise_pairs.iter().enumerate() {
            if other == index {
                continue;
            }
            discharge_kernels.push(other_kernel.clone());
            using_surfaces.push(other_surface.clone());
        }
        let Some(mut body_tactics) = plan_explicit_universal_conclusion_discharge(
            kernel,
            surface,
            MachineTerm::Variable(*goal_var),
            &ContractExpression::ProgramExpression(ProgramExpression::Variable(
                binder_name.clone(),
            )),
            goal_conclusion,
            surface_goal_conclusion,
            &discharge_kernels,
            &using_surfaces,
            None,
        ) else {
            continue;
        };
        let mut tactics = vec![ProofTactic::Intro];
        if antecedent.is_some() {
            tactics.push(ProofTactic::Intro);
        }
        tactics.append(&mut body_tactics);
        return Some(tactics);
    }
    None
}

pub(super) fn plan_explicit_named_signed_rule(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    plan_explicit_implies_refuted_antecedent(goal, premise_pairs)
        .or_else(|| plan_explicit_signed_antisymmetry(goal, premise_pairs))
        .or_else(|| plan_explicit_discharged_implication_consequent(goal, premise_pairs))
        .or_else(|| plan_explicit_one_plus_strictly_increases(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_strictly_increases(goal, premise_pairs))
        .or_else(|| plan_explicit_successor_le_implies_lt(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_preserves_order(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_lower_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_upper_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_positive_is_nonnegative(goal, premise_pairs))
        .or_else(|| plan_explicit_le_transitive_constant_lower(goal, premise_pairs))
        .or_else(|| plan_explicit_strict_implies_nonstrict(goal, premise_pairs))
        .or_else(|| plan_explicit_greater_equal_to_reversed_less_equal(goal, premise_pairs))
        .or_else(|| plan_explicit_not_strict_implies_greater_equal(goal, premise_pairs))
        .or_else(|| plan_explicit_greater_equal_transitive(goal, premise_pairs))
        .or_else(|| plan_explicit_negated_strict_successor_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_greater_equal_lower_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_strict_greater_lower_bound(goal, premise_pairs))
        .or_else(|| {
            SIGNED_TRANSITIVE_CHAINS
                .into_iter()
                .find_map(|chain| plan_explicit_transitive(goal, premise_pairs, chain))
        })
        .or_else(|| plan_explicit_constant_lower_bound_weakening(goal, premise_pairs))
        .or_else(|| plan_explicit_constant_strict_upper_bound_weakening(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_constant_upper_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_below_max_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_one_plus_below_max_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_nonnegative_add_within_max_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_nonnegative_subtract_within_value_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_positive_predecessor_is_nonnegative(goal, premise_pairs))
        .or_else(|| plan_explicit_predecessor_upper_bound(goal, premise_pairs, false))
        .or_else(|| plan_explicit_one_le_predecessor(goal, premise_pairs))
        .or_else(|| plan_explicit_positive_predecessor_strictly_decreases(goal, premise_pairs))
        .or_else(|| plan_explicit_le_and_neq_implies_lt(goal, premise_pairs))
        .or_else(|| plan_explicit_le_and_not_lt_implies_eq(goal, premise_pairs))
        .or_else(|| plan_explicit_ge_and_not_gt_implies_eq(goal, premise_pairs))
}

fn plan_explicit_signed_antisymmetry(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let forward = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel)
            .is_some_and(|(a, b)| a == left.as_ref() && b == right.as_ref())
    })?;
    let reverse = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel)
            .is_some_and(|(a, b)| a == right.as_ref() && b == left.as_ref())
    })?;
    crate::surface::checking::plan_arithmetic(
        crate::surface::checking::ArithmeticEngine::SignedInt32,
        goal,
        &[forward.0.clone(), reverse.0.clone()],
    )
    .and_then(crate::surface::checking::ArithmeticPlan::signed_int32)?;
    let (goal_left, goal_right) = match &forward.1 {
        ClickProposition::Comparison { left, right, .. } => (left.clone(), right.clone()),
        _ => return None,
    };
    Some(vec![ProofTactic::ArithmeticCertificate(
        ArithmeticCertificate {
            family: ArithmeticCertificateFamily::SignedInt32(SignedInt32Certificate {
                nodes: vec![
                    SignedArithmeticStep::Premise {
                        index: 0,
                        proposition: forward.1.clone(),
                        result: forward.1.clone(),
                    },
                    SignedArithmeticStep::Premise {
                        index: 1,
                        proposition: reverse.1.clone(),
                        result: reverse.1.clone(),
                    },
                    SignedArithmeticStep::EqualityFromBounds {
                        lower: 0,
                        upper: 1,
                        result: ClickProposition::Comparison {
                            left: goal_left,
                            operator: ComparisonOperator::Equal,
                            right: goal_right,
                        },
                    },
                ],
                conclusion: 2,
            }),
        },
    )])
}

pub(super) fn plan_explicit_le_and_neq_implies_lt(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (left, right) = goal_exact_less_than_parts(goal)?;
    for (le_kernel, le_surface) in premise_pairs {
        let Some((le_left, le_right)) = signed_nonstrict_parts(le_kernel) else {
            continue;
        };
        if le_left != left || le_right != right {
            continue;
        }
        for (neq_kernel, neq_surface) in premise_pairs {
            let matches_neq = match neq_kernel {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left: neq_left,
                        right: neq_right,
                    },
                    false,
                ) => neq_left.as_ref() == left && neq_right.as_ref() == right,
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left: neq_left, right: neq_right },
                        true,
                    ) if neq_left.as_ref() == left && neq_right.as_ref() == right
                ),
                _ => false,
            };
            if !matches_neq {
                continue;
            }
            surface_nonstrict_parts(le_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                le_surface.clone(),
                neq_surface.clone(),
            ])]);
        }
    }
    None
}

/// Select the written separation for a single named statement's read equality.
/// Selection is syntactic and bounded by the explicit premises. The driver
/// checks the selected footprint's landing state before invoking preserve.
pub(super) fn single_statement_preservation_premise(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<ClickProposition> {
    let (region, _) = preservation_read(source, target)?;
    let separation = premises.iter().find(|premise| matches!(premise,
        ClickProposition::Separate { left: ResourceSubject::Footprint(selected), .. } if selected == &region
    ))?;
    // The only other admitted citation is the reflexive source. Preserve
    // establishes its observation's definedness along with the equality.
    if !premises
        .iter()
        .all(|premise| premise == separation || premise == source)
    {
        return None;
    }
    Some(separation.clone())
}

/// The explicit old/current observation shared by preservation expansions.
fn preservation_read(
    source: &ClickProposition,
    target: &ClickProposition,
) -> Option<(CodeRegionRef, ContractExpression)> {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = source
    else {
        return None;
    };
    if left != right {
        return None;
    }
    let (historical, current) = comparison_state_expression_pair(source, target)?;
    // Preserve is the read-observation axiom. Constant equalities and
    // arithmetic expressions use their existing ordinary reasoning routes.
    if !matches!(current, ContractExpression::ResourceField(_))
        && !matches!(
            contract_expression_as_program_expression(&current),
            Some(
                ProgramExpression::Load(_)
                    | ProgramExpression::TypedLoad { .. }
                    | ProgramExpression::Index(_, _)
            )
        )
    {
        return None;
    }
    let ContractExpression::At {
        selector:
            ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region,
                kind: ProgramPointKind::Entry,
            }),
        ..
    } = historical
    else {
        return None;
    };
    if !matches!(region, CodeRegionRef::Region(_) | CodeRegionRef::Path(_)) {
        return None;
    }
    Some((region, current))
}

/// Expand a written list of footprint separations into independent preservation
/// equalities. Endpoint connectivity is ordinary equality reasoning; this reads
/// no execution history and discovers no missing footprint or premise.
pub(super) fn statement_preservation_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<ProofStep>> {
    let (start, read) = preservation_read(source, target)?;
    let mut steps = Vec::new();
    let mut includes_start = false;
    for premise in premises {
        if premise == source {
            continue;
        }
        let ClickProposition::Separate {
            left: ResourceSubject::Footprint(region),
            ..
        } = premise
        else {
            return None;
        };
        if !matches!(region, CodeRegionRef::Region(_) | CodeRegionRef::Path(_)) {
            return None;
        }
        includes_start |= region == &start;
        let at = |kind| ContractExpression::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region.clone(),
                kind,
            }),
            expression: Box::new(read.clone()),
        };
        steps.push(ProofStep::Have {
            proposition: ClickProposition::Comparison {
                left: at(ProgramPointKind::Exit),
                operator: ComparisonOperator::Equal,
                right: at(ProgramPointKind::Entry),
            },
            proof: Box::new(
                ProofCertificate::from_steps(vec![ProofStep::Preserve(premise.clone())])
                    .expect("preserve is an ordinary certificate step"),
            ),
        });
    }
    if !includes_start {
        return None;
    }
    steps.push(ProofStep::Known);
    Some(steps)
}

/// Carry a comparison whose read operands change state. All selected
/// footprints remain ordinary preservation steps; no ambient premise discovery.
pub(super) fn comparison_preservation_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<ProofStep>> {
    let pairs = comparison_preservation_reads(source, target)?;
    read_preservation_rewrite_steps(source, pairs, premises)
}

/// Preserve matching logical trees under an implication. Walk only the written
/// trees, deduplicate exact read pairs, and let equality closure connect the
/// whole fact after preservation. Rewriting the whole goal once per read would
/// make replay quadratic in the number of distinct reads.
pub(super) fn implication_preservation_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<ProofStep>> {
    if !matches!(target, ClickProposition::Implies(..)) {
        return None;
    }
    let mut pending = vec![(source, target, None)];
    let mut seen = std::collections::HashSet::new();
    let mut pairs = Vec::new();
    while let Some((source, target, retained_state)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match (source, target) {
            (
                ClickProposition::At {
                    selector,
                    proposition,
                },
                _,
            ) if retained_state.is_none() => {
                pending.push((proposition.as_ref(), target, Some(selector)));
            }
            (ClickProposition::And(sl, sr), ClickProposition::And(tl, tr))
            | (ClickProposition::Or(sl, sr), ClickProposition::Or(tl, tr))
            | (ClickProposition::Implies(sl, sr), ClickProposition::Implies(tl, tr)) => {
                pending.push((sr.as_ref(), tr.as_ref(), retained_state));
                pending.push((sl.as_ref(), tl.as_ref(), retained_state));
            }
            (ClickProposition::Not(source), ClickProposition::Not(target)) => {
                pending.push((source.as_ref(), target.as_ref(), retained_state));
            }
            (ClickProposition::Comparison { .. }, ClickProposition::Comparison { .. }) => {
                let historical = match retained_state {
                    Some(selector) => ClickProposition::At {
                        selector: selector.clone(),
                        proposition: Box::new(source.clone()),
                    },
                    None => source.clone(),
                };
                for pair in comparison_preservation_reads(&historical, target)? {
                    if seen.insert(pair.clone()) {
                        pairs.push(pair);
                    }
                }
            }
            _ => return None,
        }
    }
    let (mut steps, _) = read_preservation_steps(source, pairs, premises)?;
    steps.push(ProofStep::Known);
    Some(steps)
}

fn read_preservation_rewrite_steps(
    source: &ClickProposition,
    pairs: Vec<(ContractExpression, ContractExpression)>,
    premises: &[ClickProposition],
) -> Option<Vec<ProofStep>> {
    let (mut steps, equalities) = read_preservation_steps(source, pairs, premises)?;
    steps.extend(equalities.into_iter().map(ProofStep::Rewrite));
    steps.push(ProofStep::Known);
    Some(steps)
}

/// Construct the ordinary read equalities. Premise selection is indexed by
/// written subject, so many logical leaves do not rescan all separations.
fn read_preservation_steps(
    source: &ClickProposition,
    pairs: Vec<(ContractExpression, ContractExpression)>,
    premises: &[ClickProposition],
) -> Option<(Vec<ProofStep>, Vec<ClickProposition>)> {
    let separations = premises
        .iter()
        .filter(|p| *p != source)
        .cloned()
        .collect::<Vec<_>>();
    let selected = if pairs.len() == 1 {
        vec![separations]
    } else {
        let mut selected = vec![Vec::new(); pairs.len()];
        let mut by_subject = std::collections::HashMap::<TransportReadSubject, Vec<usize>>::new();
        for (index, (_, read)) in pairs.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            by_subject
                .entry(transport_read_subject(read)?)
                .or_default()
                .push(index);
        }
        for premise in separations {
            crate::instrumentation::record_deterministic_work(1);
            let ClickProposition::Separate {
                left: ResourceSubject::Footprint(_),
                right,
            } = &premise
            else {
                return None;
            };
            let indices = by_subject.get(&transport_separation_subject(right)?)?;
            // Each visit emits this explicitly supplied preservation in a
            // selected read proof, including several fields of one resource.
            for &index in indices {
                crate::instrumentation::record_deterministic_work(1);
                selected[index].push(premise.clone());
            }
        }
        selected
    };
    let have = |proposition, steps| ProofStep::Have {
        proposition,
        proof: Box::new(ProofCertificate::from_steps(steps).expect("ordinary preservation proof")),
    };
    // The written source is a premise, not a new assumption. Each written
    // separation is used by at least one preservation proof and checked there.
    let mut steps = vec![have(source.clone(), vec![ProofStep::Known])];
    let mut equalities = Vec::new();
    for ((historical, current), separations) in pairs.into_iter().zip(selected) {
        let reflexive = ClickProposition::Comparison {
            left: historical.clone(),
            operator: ComparisonOperator::Equal,
            right: historical.clone(),
        };
        let bridge = ClickProposition::Comparison {
            left: current,
            operator: ComparisonOperator::Equal,
            right: historical,
        };
        let equality_steps = statement_preservation_steps(&reflexive, &bridge, &separations)?;
        steps.push(have(bridge.clone(), equality_steps));
        equalities.push(bridge);
    }
    Some((steps, equalities))
}

/// Read bridges selected by the written comparison only.
fn comparison_preservation_reads(
    source: &ClickProposition,
    target: &ClickProposition,
) -> Option<Vec<(ContractExpression, ContractExpression)>> {
    // Distribute only a comparison's written state. Literal integers are
    // state-independent; every other operand keeps its explicit state.
    // Retain the original source below, so ordinary `known` checks connect
    // the written fact to the rewritten goal without a new trusted rule.
    let distributed;
    let comparison = if let ClickProposition::At {
        selector,
        proposition,
    } = source
    {
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = proposition.as_ref()
        else {
            return None;
        };
        let at = |expression: &ContractExpression| {
            if matches!(expression, ContractExpression::IntegerLiteral(_)) {
                expression.clone()
            } else {
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(expression.clone()),
                }
            }
        };
        distributed = ClickProposition::Comparison {
            left: at(left),
            operator: *operator,
            right: at(right),
        };
        &distributed
    } else {
        source
    };
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = comparison
    else {
        return None;
    };
    if *operator == ComparisonOperator::Equal && left == right {
        return None;
    }
    if !matches!(
        operator,
        ComparisonOperator::Equal
            | ComparisonOperator::LessThan
            | ComparisonOperator::LessEqual
            | ComparisonOperator::GreaterThan
            | ComparisonOperator::GreaterEqual
            | ComparisonOperator::NotEqual
    ) {
        return None;
    }
    let pairs = if let Some(pair) = comparison_state_expression_pair(comparison, target) {
        vec![pair]
    } else {
        let ClickProposition::Comparison {
            left: target_left,
            operator: target_operator,
            right: target_right,
        } = target
        else {
            return None;
        };
        if operator != target_operator {
            return None;
        }
        [(left, target_left), (right, target_right)]
            .into_iter()
            .map(|(historical, current)| match historical {
                ContractExpression::At { expression, .. } if expression.as_ref() == current => {
                    Some((historical.clone(), current.clone()))
                }
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?
    };
    scalar_preservation_read_leaves(pairs)
}

/// Decompose only the written scalar expression. Each read is preserved once;
/// ordinary equality reasoning distributes those equalities through arithmetic.
/// Unknown expression forms stay on the existing explicit transport route.
fn scalar_preservation_read_leaves(
    pairs: Vec<(ContractExpression, ContractExpression)>,
) -> Option<Vec<(ContractExpression, ContractExpression)>> {
    let mut reads = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for (historical, current) in &pairs {
        let ContractExpression::At { selector, .. } = historical else {
            return None;
        };
        let mut pending = vec![current];
        while let Some(expression) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match expression {
                ContractExpression::IntegerLiteral(_) => {}
                ContractExpression::Add(left, right)
                | ContractExpression::Subtract(left, right)
                | ContractExpression::Multiply(left, right)
                | ContractExpression::BitwiseAnd(left, right)
                | ContractExpression::BitwiseOr(left, right)
                | ContractExpression::BitwiseXor(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                ContractExpression::Negate(value) | ContractExpression::BitwiseNot(value) => {
                    pending.push(value);
                }
                ContractExpression::Call { name, arguments }
                    if name == "to_integer" && arguments.len() == 1 =>
                {
                    pending.push(&arguments[0]);
                }
                _ => {
                    if !matches!(expression, ContractExpression::ResourceField(_))
                        && !matches!(
                            contract_expression_as_program_expression(expression),
                            Some(
                                ProgramExpression::Load(_)
                                    | ProgramExpression::TypedLoad { .. }
                                    | ProgramExpression::Index(_, _)
                            )
                        )
                    {
                        return None;
                    }
                    let pair = (
                        ContractExpression::At {
                            selector: selector.clone(),
                            expression: Box::new(expression.clone()),
                        },
                        expression.clone(),
                    );
                    if seen.insert(pair.clone()) {
                        reads.push(pair);
                    }
                }
            }
        }
    }
    (!reads.is_empty()).then_some(reads)
}

/// Select scalar leaves from the written historical conjunction. Index the
/// leaf spellings once: neither ambient facts nor candidate histories are read.
pub(super) fn conjunction_projection_preservation_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<ProofStep>> {
    if !matches!(
        target,
        ClickProposition::Comparison { .. } | ClickProposition::And(..)
    ) {
        return None;
    }
    let mut pending = vec![(source, None)];
    let mut leaves = std::collections::HashMap::new();
    let mut conjunction = false;
    while let Some((proposition, retained_state)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match proposition {
            ClickProposition::And(left, right) => {
                conjunction = true;
                pending.push((right.as_ref(), retained_state));
                pending.push((left.as_ref(), retained_state));
            }
            ClickProposition::At {
                selector,
                proposition,
            } if retained_state.is_none() => {
                pending.push((proposition.as_ref(), Some(selector)));
            }
            ClickProposition::Comparison { .. } => {
                if let Some(retained_state) = retained_state {
                    // One selected witness. Failure of its ordinary proof does
                    // not retry another state or discover extra premises.
                    leaves.entry(proposition).or_insert(retained_state);
                }
            }
            _ => {}
        }
    }
    if !conjunction {
        return None;
    }
    let mut pending = vec![Some(target)];
    let mut selected = Vec::new();
    let mut shape = Vec::new();
    while let Some(node) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match node {
            Some(ClickProposition::And(left, right)) => {
                pending.push(None);
                pending.push(Some(right));
                pending.push(Some(left));
            }
            Some(target @ ClickProposition::Comparison { .. }) => {
                let retained_state = leaves.get(target)?;
                let source = ClickProposition::At {
                    selector: (*retained_state).clone(),
                    proposition: Box::new(target.clone()),
                };
                shape.push(Some(selected.len()));
                selected.push((source, target));
            }
            None => shape.push(None),
            _ => return None,
        }
    }
    conjunction_leaf_preservation_steps(source, premises, selected, shape)
}

/// Preserve a written conjunction tree without rescanning its premises at each
/// branch. Only scalar leaves are copied; the tree is traversed by reference.
pub(super) fn conjunction_preservation_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<ProofStep>> {
    if !matches!(target, ClickProposition::And(..)) {
        return None;
    }
    enum Task<'a> {
        Visit(
            &'a ClickProposition,
            &'a ClickProposition,
            Option<&'a ProgramPointSelector>,
        ),
        Join,
    }
    let mut pending = vec![Task::Visit(source, target, None)];
    let mut leaves = Vec::new();
    let mut shape = Vec::new();
    while let Some(task) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        let Task::Visit(source, target, retained_state) = task else {
            shape.push(None);
            continue;
        };
        if let ClickProposition::At {
            selector,
            proposition,
        } = source
        {
            if retained_state.is_some() {
                return None;
            }
            pending.push(Task::Visit(proposition, target, Some(selector)));
        } else if let (ClickProposition::And(sl, sr), ClickProposition::And(tl, tr)) =
            (source, target)
        {
            pending.push(Task::Join);
            pending.push(Task::Visit(sr, tr, retained_state));
            pending.push(Task::Visit(sl, tl, retained_state));
        } else {
            let source = match retained_state {
                Some(selector) => ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(source.clone()),
                },
                None => source.clone(),
            };
            shape.push(Some(leaves.len()));
            leaves.push((source, target));
        }
    }
    conjunction_leaf_preservation_steps(source, premises, leaves, shape)
}

/// Both matching trees and selected/regrouped trees use one premise index and
/// the same ordinary scalar proofs. `shape` is the target's postorder tree.
fn conjunction_leaf_preservation_steps(
    source: &ClickProposition,
    premises: &[ClickProposition],
    leaves: Vec<(ClickProposition, &ClickProposition)>,
    shape: Vec<Option<usize>>,
) -> Option<Vec<ProofStep>> {
    use std::collections::{HashMap, HashSet};
    // Hash each explicit source once, rather than compare the whole conjunction
    // with every premise. Each leaf is still proved by ordinary `known`.
    let mut sources = leaves
        .iter()
        .map(|(source, _)| source)
        .collect::<HashSet<_>>();
    sources.insert(source);
    let mut by_subject = HashMap::<TransportReadSubject, Vec<usize>>::new();
    let mut used = vec![false; premises.len()];
    for (index, premise) in premises.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        if sources.contains(premise) {
            used[index] = true;
            continue;
        }
        let ClickProposition::Separate {
            left: ResourceSubject::Footprint(_),
            right,
        } = premise
        else {
            return None;
        };
        by_subject
            .entry(transport_separation_subject(right)?)
            .or_default()
            .push(index);
    }
    let mut proofs = Vec::with_capacity(leaves.len());
    for (source, target) in &leaves {
        let reads = comparison_preservation_reads(source, target)?;
        let mut selected = Vec::new();
        let mut previous = None;
        for (_, read) in &reads {
            let key = transport_read_subject(read)?;
            // Two operands can read the same subject; cite its evidence once.
            if previous.as_ref() == Some(&key) {
                continue;
            }
            if let Some(indices) = by_subject.get(&key) {
                for &index in indices {
                    crate::instrumentation::record_deterministic_work(1);
                    used[index] = true;
                    selected.push(premises[index].clone());
                }
            }
            previous = Some(key);
        }
        proofs.push(Some(comparison_preservation_steps(
            source, target, &selected,
        )?));
    }
    if used.iter().any(|used| !used) {
        return None;
    }
    let mut built = Vec::new();
    for node in shape {
        if let Some(index) = node {
            built.push(proofs[index].take()?);
        } else {
            let right = built.pop()?;
            let left = built.pop()?;
            // Children were constructed above from ordinary steps. Do not walk
            // their entire certificate trees again at every enclosing `both`.
            let certificate = |steps| {
                Box::new(
                    ProofCertificate::from_steps_checking_arithmetic_later(steps)
                        .expect("ordinary conjunction proof"),
                )
            };
            built.push(vec![ProofStep::Both {
                left_proof: certificate(left),
                right_proof: certificate(right),
            }]);
        }
    }
    built.pop()
}

#[derive(Eq, PartialEq, Hash)]
enum TransportReadSubject {
    Cell(ProgramExpression),
    Resource(crate::kernel::Variable),
}

fn transport_read_subject(read: &ContractExpression) -> Option<TransportReadSubject> {
    if let ContractExpression::ResourceField(field) = read {
        return field
            .children
            .is_empty()
            .then_some(TransportReadSubject::Resource(field.identity));
    }
    match contract_expression_as_program_expression(read)? {
        ProgramExpression::Load(pointer) | ProgramExpression::TypedLoad { pointer, .. } => {
            Some(TransportReadSubject::Cell(*pointer))
        }
        // The parser names a single indexed cell by the address of that
        // written place. Select that same subject; preserve checks the law.
        read @ ProgramExpression::Index(_, _) => Some(TransportReadSubject::Cell(
            ProgramExpression::AddressOf(Box::new(read)),
        )),
        _ => None,
    }
}

fn transport_separation_subject(subject: &ResourceSubject) -> Option<TransportReadSubject> {
    match subject {
        ResourceSubject::Instance {
            identity, at: None, ..
        } => Some(TransportReadSubject::Resource(*identity)),
        // An instance named at an earlier state is not held now, so it is
        // not a subject whose field a transport reads.
        ResourceSubject::Instance { at: Some(_), .. } => None,
        ResourceSubject::Memory(segment)
            if segment.state == ContractSegmentState::Current
                && segment.start == ProgramExpression::Value(crate::kernel::int32(0))
                && segment.end == ProgramExpression::Value(crate::kernel::int32(1)) =>
        {
            Some(TransportReadSubject::Cell(segment.base.clone()))
        }
        _ => None,
    }
}

/// Equalities of the bases and endpoints written in two memory descriptors.
/// The planner proposes them; ordinary rewrite checks each equality. No
/// semantic descriptor normalization or ambient fact search happens here.
pub(super) fn resource_descriptor_rewrite_steps(
    target: &ClickProposition,
    source: &ClickProposition,
) -> Option<Vec<ProofStep>> {
    let (
        ClickProposition::Separate { left, right },
        ClickProposition::Separate {
            left: source_left,
            right: source_right,
        },
    ) = (target, source)
    else {
        return None;
    };
    let parts = |resource: &ResourceSubject| match resource {
        ResourceSubject::Memory(ContractSegment {
            surface:
                ContractSegmentSurface::Range { base, start, end }
                | ContractSegmentSurface::StructRange {
                    base, start, end, ..
                },
            ..
        }) => Some([base.clone(), start.clone(), end.clone()]),
        _ => None,
    };
    let mut steps = Vec::new();
    for (target, source) in [(left, source_left), (right, source_right)] {
        if target == source {
            continue;
        }
        for (left, right) in parts(target)?.into_iter().zip(parts(source)?) {
            if left == right
                || contract_expression_as_program_expression(&left)
                    .zip(contract_expression_as_program_expression(&right))
                    .is_some_and(|(a, b)| a == b)
            {
                continue;
            }
            steps.push(ProofStep::Rewrite(ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            }));
        }
    }
    if steps.is_empty() {
        return None;
    }
    steps.push(ProofStep::Known);
    Some(steps)
}

fn viewability_resource(proposition: &ClickProposition) -> Option<ResourceSubject> {
    match proposition {
        ClickProposition::Loadable { segment }
            if segment.state == ContractSegmentState::Current =>
        {
            Some(ResourceSubject::Memory(segment.clone()))
        }
        ClickProposition::ResourceViewable { resource } => Some(resource.clone()),
        _ => None,
    }
}

/// Ordinary proof of a selected viewability restriction. This visits only
/// written descriptors and premises; no state, history, or ambient facts.
pub(super) fn viewability_restriction_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<(Vec<ProofStep>, bool)> {
    if source == target || !premises.contains(source) {
        return None;
    }
    let parent = viewability_resource(source)?;
    let child = viewability_resource(target)?;
    if let (ResourceSubject::Memory(parent_segment), ResourceSubject::Memory(child_segment)) =
        (&parent, &child)
    {
        let range_base = |segment: &ContractSegment| match &segment.surface {
            ContractSegmentSurface::Range { base, .. }
            | ContractSegmentSurface::StructRange { base, .. } => Some(base.clone()),
            _ => None,
        };
        if let (Some(parent_base), Some(child_base)) =
            (range_base(parent_segment), range_base(child_segment))
            && parent_base != child_base
        {
            let equality = ClickProposition::Comparison {
                left: child_base,
                operator: ComparisonOperator::Equal,
                right: parent_base.clone(),
            };
            if !premises.contains(&equality) {
                return None;
            }
            let mut segment = child_segment.clone();
            segment.base = parent_segment.base.clone();
            match &mut segment.surface {
                ContractSegmentSurface::Range { base, .. }
                | ContractSegmentSurface::StructRange { base, .. } => *base = parent_base,
                _ => unreachable!(),
            }
            let intermediate = ClickProposition::Loadable { segment };
            let (steps, narrow_range) =
                viewability_restriction_steps(source, &intermediate, premises)?;
            return Some((
                vec![
                    ProofStep::Have {
                        proposition: intermediate,
                        proof: Box::new(
                            ProofCertificate::from_steps(steps).expect("ordinary view restriction"),
                        ),
                    },
                    ProofStep::Rewrite(equality),
                    ProofStep::Known,
                ],
                narrow_range,
            ));
        }
    }
    let containment = ClickProposition::Contains {
        parent: parent.clone(),
        child: child.clone(),
    };
    let mut steps = Vec::new();
    let mut narrow_range = false;
    if !premises.contains(&containment) {
        let (ResourceSubject::Memory(parent), ResourceSubject::Memory(child)) = (&parent, &child)
        else {
            return None;
        };
        if parent.state != child.state {
            return None;
        }
        fn endpoints(
            segment: &ContractSegment,
        ) -> Option<(
            &ContractExpression,
            &ContractExpression,
            &ContractExpression,
        )> {
            match &segment.surface {
                ContractSegmentSurface::Range { base, start, end }
                | ContractSegmentSurface::StructRange {
                    base, start, end, ..
                } => Some((base, start, end)),
                _ => None,
            }
        }
        let (base, lo, hi) = endpoints(parent)?;
        let (child_base, inner_lo, inner_hi) = endpoints(child)?;
        // Different rows of a global array can share a lowered base while
        // their offsets live in the lowered bounds. The subrange application
        // below uses written endpoints, so it must also use one written base.
        if base != child_base {
            return None;
        }
        let bounds = [(lo, inner_lo), (inner_lo, inner_hi), (inner_hi, hi)].map(|(left, right)| {
            ClickProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::LessEqual,
                right: right.clone(),
            }
        });
        // Constant endpoint comparisons close by computation with `known`.
        // Nonconstant bounds still have to be explicitly selected by planning.
        for bound in &bounds {
            if premises.contains(bound) {
                continue;
            }
            let ClickProposition::Comparison { left, right, .. } = bound else {
                unreachable!()
            };
            let literal = |value: &ContractExpression| {
                matches!(
                    value,
                    ContractExpression::IntegerLiteral(_)
                        | ContractExpression::ProgramExpression(ProgramExpression::Value(_))
                )
            };
            if !literal(left) || !literal(right) {
                return None;
            }
            steps.push(ProofStep::Have {
                proposition: bound.clone(),
                proof: Box::new(
                    ProofCertificate::from_steps(vec![ProofStep::Known])
                        .expect("constant comparison is an ordinary known step"),
                ),
            });
        }
        narrow_range = true;
        steps.push(ProofStep::Have {
            proposition: containment.clone(),
            proof: Box::new(
                ProofCertificate::from_steps(vec![ProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "click::separation::contains_subrange".into(),
                        arguments: [base, lo, hi, inner_lo, inner_hi]
                            .into_iter()
                            .cloned()
                            .collect(),
                    },
                    premises: bounds.to_vec(),
                }])
                .expect("ordinary theorem application is a certificate step"),
            ),
        });
    }
    let mut cited = premises.to_vec();
    if !cited.contains(&containment) {
        cited.push(containment);
    }
    steps.push(ProofStep::ApplyTheoremUsing {
        application: TheoremApplication {
            name: "click::separation::viewable_restrict".into(),
            arguments: vec![
                ContractExpression::Resource(Box::new(parent)),
                ContractExpression::Resource(Box::new(child)),
            ],
        },
        premises: cited,
    });
    Some((steps, narrow_range))
}

/// A displaced view is first restricted to the offset, then rebased, then
/// restricted to its requested length. Every link is an ordinary library law.
pub(super) fn rebased_viewability_restriction_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<(ClickProposition, Vec<ProofStep>)>> {
    let parent = viewability_resource(source)?;
    let child = viewability_resource(target)?;
    let (ResourceSubject::Memory(parent_segment), ResourceSubject::Memory(child_segment)) =
        (&parent, &child)
    else {
        return None;
    };
    if parent_segment.state != child_segment.state {
        return None;
    }
    let (base, lo, hi) = parent_segment.surface_range()?;
    let (child_base, zero, requested) = child_segment.surface_range()?;
    let ProgramExpression::Add(pointer, offset) =
        contract_expression_as_program_expression(child_base)?
    else {
        return None;
    };
    if contract_expression_as_program_expression(base).as_ref() != Some(pointer.as_ref()) {
        return None;
    }
    let is_zero = |value: &ContractExpression| {
        matches!(
            contract_expression_as_program_expression(value),
            Some(ProgramExpression::Value(ProgramValue::Int32(value)
                | ProgramValue::UInt64(value))) if matches!(value, MachineTerm::Constant { bits: 0, .. })
        )
    };
    if !is_zero(zero) {
        return None;
    }
    let offset = ContractExpression::ProgramExpression(*offset);
    let remaining = ContractExpression::ProgramExpression(ProgramExpression::Subtract(
        Box::new(contract_expression_as_program_expression(hi)?),
        Box::new(contract_expression_as_program_expression(&offset)?),
    ));
    let range =
        |template: &ContractSegment, start: &ContractExpression, end: &ContractExpression| {
            let mut segment = template.clone();
            segment.start = contract_expression_as_program_expression(start)?;
            segment.end = contract_expression_as_program_expression(end)?;
            let ContractSegmentSurface::Range {
                start: written_start,
                end: written_end,
                ..
            } = &mut segment.surface
            else {
                return None;
            };
            *written_start = start.clone();
            *written_end = end.clone();
            Some(ResourceSubject::Memory(segment))
        };
    let tail = range(parent_segment, &offset, hi)?;
    let rebased = range(child_segment, zero, &remaining)?;
    let contains = |a: &ResourceSubject, b: &ResourceSubject| ClickProposition::Contains {
        parent: a.clone(),
        child: b.clone(),
    };
    let viewable = |a: &ResourceSubject| {
        let ResourceSubject::Memory(segment) = a else {
            unreachable!()
        };
        ClickProposition::Loadable {
            segment: segment.clone(),
        }
    };
    // Keep computed machine endpoints inside an explicit observation. A bare
    // subtraction in a comparison parses as mathematical integer arithmetic.
    let observe = |value: &ContractExpression| ContractExpression::Call {
        name: "to_integer".into(),
        arguments: vec![value.clone()],
    };
    let bound =
        |left: &ContractExpression, right: &ContractExpression| ClickProposition::Comparison {
            left: observe(left),
            operator: ComparisonOperator::LessEqual,
            right: observe(right),
        };
    let apply = |name: &str, arguments, premises| {
        vec![ProofStep::ApplyTheoremUsing {
            application: TheoremApplication {
                name: format!("click::separation::{name}"),
                arguments,
            },
            premises,
        }]
    };
    let arg = |resource: &ResourceSubject| ContractExpression::Resource(Box::new(resource.clone()));
    let mut cited = premises.to_vec();
    let mut goals = Vec::new();
    for goal in [
        bound(lo, &offset),
        bound(&offset, hi),
        bound(hi, hi),
        bound(zero, &offset),
        bound(zero, zero),
        bound(zero, requested),
        bound(requested, &remaining),
    ] {
        if !cited.contains(&goal) {
            goals.push((
                goal.clone(),
                vec![ProofStep::ArithmeticUsing(cited.clone())],
            ));
            cited.push(goal);
        }
    }
    for (a, b, steps) in [
        (
            &parent,
            &tail,
            apply(
                "contains_subrange",
                vec![
                    base.clone(),
                    lo.clone(),
                    hi.clone(),
                    offset.clone(),
                    hi.clone(),
                ],
                cited.clone(),
            ),
        ),
        (
            &tail,
            &rebased,
            apply(
                "contains_rebase",
                vec![base.clone(), offset, hi.clone()],
                cited.clone(),
            ),
        ),
        (
            &rebased,
            &child,
            apply(
                "contains_subrange",
                vec![
                    child_base.clone(),
                    zero.clone(),
                    remaining,
                    zero.clone(),
                    requested.clone(),
                ],
                cited.clone(),
            ),
        ),
    ] {
        let containment = contains(a, b);
        goals.push((containment.clone(), steps));
        goals.push((
            viewable(b),
            apply(
                "viewable_restrict",
                vec![arg(a), arg(b)],
                vec![viewable(a), containment],
            ),
        ));
    }
    Some(goals)
}

/// Plan an element-range restriction whose kernel view has a native byte
/// count. The ordinary resource laws perform the element-width scaling;
/// planning only proves the written endpoint bounds.
pub(super) fn native_viewability_restriction_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<(ClickProposition, Vec<ProofStep>)>> {
    let requirements = viewability_restriction_requirements(source, target)?;
    let mut cited = premises.to_vec();
    let mut goals = Vec::new();
    for requirement in requirements {
        if cited.contains(&requirement) {
            continue;
        }
        let step = if matches!(
            &requirement,
            ClickProposition::Comparison {
                operator: ComparisonOperator::Equal,
                ..
            }
        ) {
            ProofStep::Known
        } else {
            ProofStep::ArithmeticUsing(cited.clone())
        };
        goals.push((requirement.clone(), vec![step]));
        cited.push(requirement);
    }
    let (steps, _) = viewability_restriction_steps(source, target, &cited)?;
    goals.push((target.clone(), steps));
    Some(goals)
}

/// Plan a narrow range with one computed upper endpoint through the explicit
/// signed operation identity. Search applies these steps under its budget;
/// replay retains the resulting arithmetic certificates and library steps.
pub(super) fn computed_viewability_restriction_steps(
    source: &ClickProposition,
    target: &ClickProposition,
    premises: &[ClickProposition],
) -> Option<Vec<(ClickProposition, Vec<ProofStep>)>> {
    let parent = viewability_resource(source)?;
    let child = viewability_resource(target)?;
    let (ResourceSubject::Memory(parent_segment), ResourceSubject::Memory(child_segment)) =
        (&parent, &child)
    else {
        return None;
    };
    let (
        ContractSegmentSurface::Range {
            base,
            start: lo,
            end: hi,
        },
        ContractSegmentSurface::Range {
            base: child_base,
            start: inner_lo,
            end: inner_hi,
        },
    ) = (&parent_segment.surface, &child_segment.surface)
    else {
        return None;
    };
    if base != child_base || parent_segment.state != child_segment.state {
        return None;
    }
    let expression = contract_expression_as_program_expression(inner_hi)?;
    let (left, right, law) = match expression {
        ProgramExpression::Add(left, right) => {
            (left, right, "click::integer::int32_add_to_integer")
        }
        ProgramExpression::Subtract(left, right) => {
            (left, right, "click::integer::int32_subtract_to_integer")
        }
        _ => return None,
    };
    let observe = |value: ContractExpression| ContractExpression::Call {
        name: "to_integer".into(),
        arguments: vec![value],
    };
    let exact_left = Box::new(observe(ContractExpression::ProgramExpression(
        (*left).clone(),
    )));
    let exact_right = Box::new(observe(ContractExpression::ProgramExpression(
        (*right).clone(),
    )));
    let exact = if law == "click::integer::int32_add_to_integer" {
        ContractExpression::Add(exact_left, exact_right)
    } else {
        ContractExpression::Subtract(exact_left, exact_right)
    };
    let compare = |left, operator, right| ClickProposition::Comparison {
        left,
        operator,
        right,
    };
    let have = |proposition, steps| (proposition, steps);
    let mut cited = premises.to_vec();
    let mut steps = Vec::new();
    for (left, right) in [
        (observe(lo.clone()), observe(inner_lo.clone())),
        (observe(inner_lo.clone()), exact.clone()),
        (exact.clone(), observe(hi.clone())),
        (
            ContractExpression::Negate(Box::new(ContractExpression::IntegerLiteral(
                "2147483648".into(),
            ))),
            exact.clone(),
        ),
        (
            exact.clone(),
            ContractExpression::IntegerLiteral("2147483647".into()),
        ),
    ] {
        let bound = compare(left.clone(), ComparisonOperator::LessEqual, right.clone());
        steps.push(have(
            bound.clone(),
            vec![ProofStep::ArithmeticUsing(cited.clone())],
        ));
        cited.push(bound);
    }
    let defined = ClickProposition::Defined {
        expression: inner_hi.clone(),
    };
    steps.push(have(defined.clone(), vec![ProofStep::Known]));
    cited.push(defined.clone());
    let identity = compare(observe(inner_hi.clone()), ComparisonOperator::Equal, exact);
    steps.push(have(
        identity.clone(),
        vec![ProofStep::ApplyTheoremUsing {
            application: TheoremApplication {
                name: law.into(),
                arguments: vec![
                    ContractExpression::ProgramExpression(*left),
                    ContractExpression::ProgramExpression(*right),
                ],
            },
            premises: vec![defined],
        }],
    ));
    cited.push(identity.clone());
    for (left, right) in [
        (observe(inner_lo.clone()), observe(inner_hi.clone())),
        (observe(inner_hi.clone()), observe(hi.clone())),
    ] {
        let bound = compare(left, ComparisonOperator::LessEqual, right);
        steps.push(have(
            bound.clone(),
            vec![ProofStep::Rewrite(identity.clone()), ProofStep::Known],
        ));
        cited.push(bound);
    }
    let containment = ClickProposition::Contains {
        parent: parent.clone(),
        child: child.clone(),
    };
    steps.push(have(
        containment.clone(),
        vec![ProofStep::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "click::separation::contains_subrange".into(),
                arguments: [base, lo, hi, inner_lo, inner_hi]
                    .into_iter()
                    .cloned()
                    .collect(),
            },
            premises: cited.clone(),
        }],
    ));
    cited.push(containment);
    steps.push(have(
        target.clone(),
        vec![ProofStep::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "click::separation::viewable_restrict".into(),
                arguments: vec![
                    ContractExpression::Resource(Box::new(parent)),
                    ContractExpression::Resource(Box::new(child)),
                ],
            },
            premises: cited,
        }],
    ));
    Some(steps)
}

/// The explicit alias and endpoint facts needed by the ordinary subrange law.
/// Planning proves these; the driver only consumes the selected facts.
pub(super) fn viewability_restriction_requirements(
    source: &ClickProposition,
    target: &ClickProposition,
) -> Option<Vec<ClickProposition>> {
    if source == target {
        return None;
    }
    let ResourceSubject::Memory(parent) = viewability_resource(source)? else {
        return None;
    };
    let ResourceSubject::Memory(child) = viewability_resource(target)? else {
        return None;
    };
    if parent.state != child.state {
        return None;
    }
    let endpoints = |segment: ContractSegment| match segment.surface {
        ContractSegmentSurface::Range { base, start, end }
        | ContractSegmentSurface::StructRange {
            base, start, end, ..
        } => Some((base, start, end)),
        _ => None,
    };
    let (base, lo, hi) = endpoints(parent)?;
    let (child_base, inner_lo, inner_hi) = endpoints(child)?;
    // Computed endpoints have mathematical Integer semantics in a range,
    // while a machine-typed theorem argument can denote a wrapping operation.
    // Those need an explicit operation-identity bridge, not just order bounds.
    let direct = |bound: &ContractExpression| {
        matches!(
            bound,
            ContractExpression::IntegerLiteral(_)
                | ContractExpression::Binding(_)
                | ContractExpression::Field { .. }
                | ContractExpression::ArrayIndex { .. }
                | ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(_)
                        | ProgramExpression::Value(_)
                        | ProgramExpression::Load(_)
                        | ProgramExpression::TypedLoad { .. }
                        | ProgramExpression::Index(..)
                )
        )
    };
    if ![&lo, &hi, &inner_lo, &inner_hi].into_iter().all(direct) {
        return None;
    }
    let mut requirements = Vec::new();
    if base != child_base {
        requirements.push(ClickProposition::Comparison {
            left: child_base,
            operator: ComparisonOperator::Equal,
            right: base,
        });
    }
    for (left, right) in [
        (lo, inner_lo.clone()),
        (inner_lo, inner_hi.clone()),
        (inner_hi, hi),
    ] {
        requirements.push(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        });
    }
    Some(requirements)
}

pub(super) fn plan_explicit_loadability_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let goal_width;
    let goal_bytes = match goal {
        Proposition::MemoryLoadable { bytes, .. } => bytes,
        Proposition::MemoryReadDefined { value_type, .. } => {
            goal_width = MachineTerm::constant(value_type.byte_width());
            &goal_width
        }
        _ => return None,
    };
    let mut sources = premise_pairs
        .iter()
        .filter(|(kernel, _)| {
            matches!(
                kernel,
                Proposition::MemoryLoadable { .. } | Proposition::MemoryReadDefined { .. }
            )
        })
        .collect::<Vec<_>>();
    let surface_is_range = |surface: &ClickProposition| match surface {
        ClickProposition::At { proposition, .. } => {
            matches!(
                proposition.as_ref(),
                ClickProposition::Loadable { segment }
                    if matches!(segment.surface, ContractSegmentSurface::Range { .. } | ContractSegmentSurface::StructRange { .. })
            )
        }
        ClickProposition::Loadable { segment } => {
            matches!(
                segment.surface,
                ContractSegmentSurface::Range { .. } | ContractSegmentSurface::StructRange { .. }
            )
        }
        _ => false,
    };
    sources.sort_by_key(|(kernel, surface)| match kernel {
        Proposition::MemoryLoadable { bytes, .. } => (
            (!surface_is_range(surface)) as u8,
            (bytes == goal_bytes) as u8,
        ),
        Proposition::MemoryReadDefined { .. } => (0, 0),
        _ => unreachable!(),
    });
    if sources.is_empty() {
        super::attempt::record_search_note(
            "solve view transport planning",
            format!(
                "no memory-view premise has a checked source spelling ({} resolved premises)",
                premise_pairs.len()
            ),
        );
    }
    for (source, surface_source) in sources {
        let mut selected = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::MemoryLoadable { .. }
                        | Proposition::MemoryReadDefined { .. }
                        | Proposition::ConditionIs(_, _)
                )
            })
            .collect::<Vec<_>>();
        let proves_goal = |pairs: &[&(Proposition, ClickProposition)]| {
            let propositions = pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            crate::kernel::search::ProofSearch::derive_solve_proposition(
                &(assumptions_from_propositions(&propositions)),
                goal,
            )
            .is_some()
        };
        if !proves_goal(&selected) {
            super::attempt::record_search_note(
                "solve view transport planning",
                format!(
                    "the resolved memory-view and condition premises do not produce a retained-premise derivation of the requested view ({} resolved transport premises)",
                    selected.len()
                ),
            );
            continue;
        }
        let mut index = 0;
        while index < selected.len() {
            if selected[index].0 == *source {
                index += 1;
                continue;
            }
            let mut reduced = selected.clone();
            reduced.remove(index);
            if proves_goal(&reduced) {
                selected = reduced;
            } else {
                index += 1;
            }
        }
        // Selection starts with a successful search and changes only after
        // another success. Do not repeat bounded search as an assertion: its
        // budget can now be exhausted. The emitted transport still goes
        // through the ordinary checked operation before it can prove anything.
        let mut premises = selected
            .into_iter()
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        let mut tactics = Vec::new();
        // Native byte-count views can use scaled bounds or displaced bases.
        // Their existing transport is not an element-subrange certificate.
        if !matches!(goal, Proposition::MemoryLoadable { wide: true, .. })
            && let Some(requirements) =
                viewability_restriction_requirements(surface_source, surface_goal)
        {
            for requirement in requirements {
                if premises.contains(&requirement) {
                    continue;
                }
                let proof = if matches!(
                    &requirement,
                    ClickProposition::Comparison {
                        operator: ComparisonOperator::Equal,
                        ..
                    }
                ) {
                    ProofTactic::Known
                } else {
                    ProofTactic::ArithmeticUsing(premises.clone())
                };
                tactics.push(ProofTactic::Have(ProofHave {
                    proposition: requirement.clone(),
                    proof: SourceProof::Script(vec![proof]),
                }));
                premises.push(requirement);
            }
        }
        tactics.push(ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_goal.clone(),
            premises,
        });
        tactics.push(ProofTactic::Known);
        return Some(tactics);
    }
    None
}

pub(super) fn signed_strict_parts(
    proposition: &Proposition,
) -> Option<(&MachineTerm, &MachineTerm)> {
    match proposition {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            },
            true,
        ) => Some((left, right)),
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            },
            true,
        ) => Some((right, left)),
        _ => None,
    }
}

pub(super) fn signed_nonstrict_parts(
    proposition: &Proposition,
) -> Option<(&MachineTerm, &MachineTerm)> {
    match proposition {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            },
            true,
        ) => Some((left, right)),
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            true,
        ) => Some((right, left)),
        _ => None,
    }
}

/// The operands of a negated signed order, written `Not(order)` or as the
/// order's condition being false, ordered as [`signed_strict_parts`] and
/// [`signed_nonstrict_parts`] order them, and whether the negated order is
/// strict.
fn negated_signed_order_parts(
    proposition: &Proposition,
) -> Option<(&MachineTerm, &MachineTerm, bool)> {
    let condition = match proposition {
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, true) => condition,
            _ => return None,
        },
        Proposition::ConditionIs(condition, false) => condition,
        _ => return None,
    };
    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => Some((left, right, true)),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => Some((right, left, true)),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => Some((left, right, false)),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => Some((right, left, false)),
        _ => None,
    }
}

/// A signed `int32` order, equality, or `+`/`-` definedness goal spelled from
/// the operands of `premise_pairs`: each operand the premises compare is
/// written as they write it, a constant as a literal, and a sum or
/// difference of those term by term. `None` when an operand has no spelling.
pub(super) fn spell_signed_goal(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<ClickProposition> {
    use crate::kernel::{MachineBinaryOp, MachineOperandView, SignedDefinedWidth};
    let mut operands: Vec<(&MachineTerm, ContractExpression)> = Vec::new();
    for (kernel, surface) in premise_pairs {
        let parts = signed_strict_parts(kernel)
            .zip(surface_strict_parts(surface))
            .or_else(|| signed_nonstrict_parts(kernel).zip(surface_nonstrict_parts(surface)));
        // A negated order, `not (x < 2)`, names its operands as an order
        // does.
        let parts = parts.or_else(|| {
            let (left, right, strict) = negated_signed_order_parts(kernel)?;
            let ClickProposition::Not(inner) = surface else {
                return None;
            };
            let surface_parts = if strict {
                surface_strict_parts(inner)
            } else {
                surface_nonstrict_parts(inner)
            };
            Some((left, right)).zip(surface_parts)
        });
        if let Some(((left, right), (surface_left, surface_right))) = parts {
            operands.push((left, surface_left));
            operands.push((right, surface_right));
        }
    }
    fn spell(
        term: MachineOperandView<'_>,
        operands: &[(&MachineTerm, ContractExpression)],
    ) -> Option<ContractExpression> {
        if let Some(value) = term.word32_constant() {
            return Some(ContractExpression::ProgramExpression(
                ProgramExpression::Value(int32(value)),
            ));
        }
        if let Some((_, surface)) = operands
            .iter()
            .find(|(operand, _)| same_written_int32_operand(term, operand))
        {
            return Some(surface.clone());
        }
        match term.binary() {
            Some((MachineIntegerType::Int32, MachineBinaryOp::Add, [left, right])) => {
                Some(ContractExpression::Add(
                    Box::new(spell(left, operands)?),
                    Box::new(spell(right, operands)?),
                ))
            }
            Some((MachineIntegerType::Int32, MachineBinaryOp::Subtract, [left, right])) => {
                Some(ContractExpression::Subtract(
                    Box::new(spell(left, operands)?),
                    Box::new(spell(right, operands)?),
                ))
            }
            _ => None,
        }
    }
    let compare = |left: &MachineTerm, operator, right: &MachineTerm| {
        Some(ClickProposition::Comparison {
            left: spell(MachineOperandView::Legacy(left), &operands)?,
            operator,
            right: spell(MachineOperandView::Legacy(right), &operands)?,
        })
    };
    if let Some((SignedDefinedWidth::Int32, values, subtract)) =
        crate::kernel::proof::arithmetic_special::signed_definedness_query(goal)
    {
        let left = Box::new(spell(values[0].operand_view(), &operands)?);
        let right = Box::new(spell(values[1].operand_view(), &operands)?);
        return Some(ClickProposition::Defined {
            expression: if subtract {
                ContractExpression::Subtract(left, right)
            } else {
                ContractExpression::Add(left, right)
            },
        });
    }
    match goal {
        Proposition::ConditionIs(condition, true) => match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } => compare(left, ComparisonOperator::LessThan, right),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => compare(left, ComparisonOperator::LessEqual, right),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            } => compare(left, ComparisonOperator::GreaterThan, right),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => compare(left, ComparisonOperator::GreaterEqual, right),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => compare(left, ComparisonOperator::Equal, right),
            _ => None,
        },
        _ => None,
    }
}

/// The source premises of one kernel-selected signed-order path, in chain
/// order.
pub(super) fn recorded_signed_order_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation.signed_order_path().and_then(|path| {
        path.iter()
            .map(|step| {
                premise_pairs
                    .iter()
                    .find(|(kernel, _)| kernel == step.premise())
            })
            .collect::<Option<Vec<_>>>()
            .map(|pairs| pairs.into_iter().cloned().collect::<Vec<_>>())
    })
}

/// The source premises of an atomic 64-bit order decision's recorded chain,
/// in chain order.
pub(super) fn recorded_wide_order_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (_, path) = derivation.wide_order_path()?;
    let pairs = path
        .iter()
        .map(|step| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == step.premise())
                .cloned()
        })
        .collect::<Option<Vec<_>>>()?;
    Some(pairs)
}

/// A recorded 64-bit order chain closed by Integer arithmetic over its
/// links: `arithmetic() using` the chain's premises, which expands to the
/// explicit arithmetic certificate. A link whose source premise is not
/// written as `<`, `<=`, `>` or `>=` (a negated order, say) is left to other
/// routes.
pub(super) fn plan_recorded_wide_order_path(
    path: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    if path.len() < 2 {
        return None;
    }
    let premises = path
        .iter()
        .map(|(_, surface)| {
            surface_strict_parts(surface)
                .or_else(|| surface_nonstrict_parts(surface))
                .map(|_| surface.clone())
        })
        .collect::<Option<Vec<_>>>()?;
    Some(vec![ProofTactic::ArithmeticUsing(premises)])
}

/// The listed premise pairs that state each of `premises`, in order, or
/// `None` when one is missing. With `polarity`, a condition stated with the
/// opposite polarity also matches.
pub(super) fn recorded_premise_pairs<'a>(
    premises: impl IntoIterator<Item = &'a Proposition>,
    premise_pairs: &[(Proposition, ClickProposition)],
    polarity: bool,
) -> Option<Vec<(Proposition, ClickProposition)>> {
    premises
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| {
                    kernel == premise
                        || (polarity && condition_polarity_equivalent(kernel, premise))
                })
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_one_le_predecessor_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_one_le_predecessor_is_nonnegative_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_one_le_predecessor_strictly_decreases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_one_le_predecessor_strictly_decreases_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .int32_equal_one_predecessor_is_nonnegative_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
}

pub(super) fn recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .int32_equal_one_predecessor_strictly_decreases_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
}

pub(super) fn recorded_int32_equal_one_predecessor_is_zero_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .int32_equal_one_predecessor_is_zero_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
}

pub(super) fn plan_recorded_int32_equal_one_predecessor(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let path = derivation
        .int32_equal_one_predecessor_is_nonnegative_path()
        .or_else(|| derivation.int32_equal_one_predecessor_strictly_decreases_path())?;
    let value = one_le_predecessor_value(goal)?;
    let one_le_kernel = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(MachineTerm::constant(1)),
            right: Box::new(value.clone()),
        },
        true,
    );
    let first = path.first()?;
    let (_, first_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == first.premise())?;
    let first_oriented = orient_surface_bitvector_equality(first, first_surface)?;
    let one_le_surface = surface_one_le_equality_source(&first_oriented)?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = one_le_kernel.clone();
    let mut equality_tactics = Vec::with_capacity(path.len() + 1);
    for step in path {
        let (_, surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == step.premise())?;
        let oriented_surface = orient_surface_bitvector_equality(step, surface)?;
        let oriented_kernel = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(step.source().clone()),
                right: Box::new(step.target().clone()),
            },
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        equality_tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    equality_tactics.push(plan_context_free_closer(&current)?);

    let mut predecessor_tactics =
        plan_explicit_one_le_predecessor(goal, &[(one_le_kernel, one_le_surface.clone())])?;
    let mut tactics = Vec::with_capacity(predecessor_tactics.len() + 1);
    tactics.push(ProofTactic::Have(ProofHave {
        proposition: one_le_surface,
        proof: SourceProof::Script(equality_tactics),
    }));
    tactics.append(&mut predecessor_tactics);
    Some(tactics)
}

pub(super) fn plan_recorded_int32_equal_one_predecessor_is_zero(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let path = derivation.int32_equal_one_predecessor_is_zero_path()?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = goal.clone();
    let mut tactics = Vec::with_capacity(path.len() + 1);
    for step in path {
        let (_, surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == step.premise())?;
        let oriented_surface = orient_surface_bitvector_equality(step, surface)?;
        let oriented_kernel = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(step.source().clone()),
                right: Box::new(step.target().clone()),
            },
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    tactics.push(plan_context_free_closer(&current)?);
    Some(tactics)
}

/// A recorded 32-bit order chain closed by Integer arithmetic over its
/// links, once its last link composes into the goal as a two-premise rule
/// does.
pub(super) fn plan_recorded_signed_order_path(
    goal: &Proposition,
    path: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    if path.len() < 2 {
        return plan_explicit_named_signed_rule(goal, path);
    }
    let mut current = path[0].clone();
    for next in &path[1..path.len() - 1] {
        let (current_lower, current_upper, current_strict) =
            if let Some((lower, upper)) = signed_strict_parts(&current.0) {
                (lower.clone(), upper.clone(), true)
            } else {
                let (lower, upper) = signed_nonstrict_parts(&current.0)?;
                (lower.clone(), upper.clone(), false)
            };
        let (next_lower, next_upper, next_strict) =
            if let Some((lower, upper)) = signed_strict_parts(&next.0) {
                (lower.clone(), upper.clone(), true)
            } else {
                let (lower, upper) = signed_nonstrict_parts(&next.0)?;
                (lower.clone(), upper.clone(), false)
            };
        if current_upper != next_lower {
            return None;
        }
        let (surface_lower, _) = if current_strict {
            surface_strict_parts(&current.1)?
        } else {
            surface_nonstrict_parts(&current.1)?
        };
        let (_, surface_upper) = if next_strict {
            surface_strict_parts(&next.1)?
        } else {
            surface_nonstrict_parts(&next.1)?
        };
        let strict = current_strict || next_strict;
        let surface_target = ClickProposition::Comparison {
            left: surface_lower.clone(),
            operator: if strict {
                ComparisonOperator::LessThan
            } else {
                ComparisonOperator::LessEqual
            },
            right: surface_upper.clone(),
        };
        let kernel_target = Proposition::ConditionIs(
            if strict {
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(current_lower),
                    right: Box::new(next_upper),
                }
            } else {
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(current_lower),
                    right: Box::new(next_upper),
                }
            },
            true,
        );
        current = (kernel_target, surface_target);
    }
    // The chain's last link must compose into the goal as a two-premise
    // rule does; the whole chain is then one Integer arithmetic step over
    // its written premises.
    let final_edge = path.last()?.clone();
    plan_explicit_named_signed_rule(goal, &[current, final_edge])?;
    Some(vec![ProofTactic::ArithmeticUsing(
        path.iter().map(|(_, surface)| surface.clone()).collect(),
    )])
}

fn orient_surface_bitvector_equality(
    step: &BitvectorEqualityDerivationStep,
    surface: &ClickProposition,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(condition, true) = step.premise() else {
        return None;
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
    if view.negated
        || view.relation != CompareRelation::Equal
        || !matches!(
            view.format,
            MachineIntegerType::Int32 | MachineIntegerType::UInt32
        )
    {
        return None;
    }
    let [left, right] = view
        .operands
        .each_ref()
        .map(|operand| operand.operand_view().retain(MachineIntegerType::Int32));
    let source = step.source_view().retain(MachineIntegerType::Int32);
    let target = step.target_view().retain(MachineIntegerType::Int32);
    let reverse = source == right && target == left;
    if !(reverse || source == left && target == right) {
        return None;
    }
    fn oriented(surface: &ClickProposition, reverse: bool) -> Option<ClickProposition> {
        match surface {
            ClickProposition::At {
                selector,
                proposition,
            } => Some(ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(oriented(proposition, reverse)?),
            }),
            ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } => Some(ClickProposition::Comparison {
                left: if reverse { right.clone() } else { left.clone() },
                operator: ComparisonOperator::Equal,
                right: if reverse { left.clone() } else { right.clone() },
            }),
            _ => None,
        }
    }
    oriented(surface, reverse)
}

fn recorded_bitvector_equality_path_pairs(
    path: &[BitvectorEqualityDerivationStep],
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    path.iter()
        .map(|step| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == step.premise())
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_load_address_congruence_path_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<Vec<(Proposition, ClickProposition)>>> {
    derivation
        .load_address_congruence_paths()?
        .iter()
        .map(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
        .collect()
}

/// Transcribe the exact equality path retained by the kernel. Each edge is
/// oriented in the direction selected by the path, even when its source
/// premise was written in reverse. Rewriting the goal along every edge must
/// end in a context-free reflexive proposition.
pub(super) fn plan_recorded_bitvector_equality_path(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let path = derivation.bitvector_equality_path()?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = goal.clone();
    let mut tactics = Vec::with_capacity(path.len() + 1);
    for step in path {
        let (_, surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == step.premise())?;
        let oriented_surface = orient_surface_bitvector_equality(step, surface)?;
        let oriented_kernel = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(step.source().clone()),
                right: Box::new(step.target().clone()),
            },
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    tactics.push(plan_context_free_closer(&current)?);
    Some(tactics)
}

/// A pointer-word equality decision is certified by a checked special
/// certificate naming every retained fact, or by a goal-local closer when it
/// used none.
pub(super) fn plan_recorded_pointer_word(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
) -> Option<Vec<ProofTactic>> {
    let premises = derivation.pointer_word_premises()?;
    let surfaces = premises
        .iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .map(|(_, surface)| surface.clone())
        })
        .collect::<Option<Vec<_>>>()?;
    let kernels = premises.to_vec();
    let plan = crate::surface::checking::plan_arithmetic(
        crate::surface::checking::ArithmeticEngine::Special,
        goal,
        &kernels,
    )
    .and_then(crate::surface::checking::ArithmeticPlan::special)?;
    Some(vec![ProofTactic::ArithmeticCertificate(
        crate::surface::checking::special_plan_to_surface_certificate(
            &plan,
            &surfaces,
            surface_goal,
        ),
    )])
}

/// A pointer-alignment decision is certified by a checked special certificate
/// naming its retained base fact, or with no premise for intrinsic heap
/// alignment. Both cases use the explicit alignment certificate rule.
pub(super) fn plan_recorded_pointer_alignment(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
) -> Option<Vec<ProofTactic>> {
    let premise = derivation.pointer_alignment_premise()?;
    let kernels = premise.into_iter().cloned().collect::<Vec<_>>();
    let surfaces = premise
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .map(|(_, surface)| surface.clone())
        })
        .collect::<Option<Vec<_>>>()?;
    let plan = crate::surface::checking::plan_arithmetic(
        crate::surface::checking::ArithmeticEngine::Special,
        goal,
        &kernels,
    )
    .and_then(crate::surface::checking::ArithmeticPlan::special)?;
    Some(vec![ProofTactic::ArithmeticCertificate(
        crate::surface::checking::special_plan_to_surface_certificate(
            &plan,
            &surfaces,
            surface_goal,
        ),
    )])
}

/// Expand registered-load address congruence into the ordinary exact
/// equality rewrites that establish it. `rewrite` descends through the
/// registered load origins, while `known` checks that the resulting
/// memory version and complete pointer are identical.
pub(super) fn plan_recorded_load_address_congruence(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_paths: &[Vec<(Proposition, ClickProposition)>],
) -> Option<Vec<ProofTactic>> {
    let paths = derivation.load_address_congruence_paths()?;
    if paths.len() != premise_paths.len() {
        return None;
    }
    let available = premise_paths
        .iter()
        .flatten()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = goal.clone();
    let mut tactics = Vec::new();
    for (path, pairs) in paths.iter().zip(premise_paths) {
        if path.len() != pairs.len() {
            return None;
        }
        for (step, (_, surface)) in path.iter().zip(pairs) {
            let oriented_surface = orient_surface_bitvector_equality(step, surface)?;
            let oriented_kernel = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(step.source().clone()),
                    right: Box::new(step.target().clone()),
                },
                true,
            );
            current = rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available)
                .ok()?;
            tactics.push(ProofTactic::Rewrite(oriented_surface));
        }
    }
    tactics.push(plan_context_free_closer(&current)?);
    Some(tactics)
}

/// The goal-side counterpart of [`signed_strict_parts`]: a goal written
/// `<`, not its reversed (`>`) spelling, which other rules recognize.
fn goal_exact_less_than_parts(goal: &Proposition) -> Option<(&MachineTerm, &MachineTerm)> {
    match goal {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            },
            true,
        ) => Some((left, right)),
        _ => None,
    }
}

/// The goal-side counterpart of [`signed_nonstrict_parts`]; see
/// [`goal_exact_less_than_parts`].
fn goal_exact_less_equal_parts(goal: &Proposition) -> Option<(&MachineTerm, &MachineTerm)> {
    match goal {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            },
            true,
        ) => Some((left, right)),
        _ => None,
    }
}

fn increment_base(term: &MachineTerm) -> Option<&MachineTerm> {
    let binary_term!(Int32, Add, left, right) = term else {
        return None;
    };
    if right.as_ref() == &MachineTerm::constant(1) {
        Some(left)
    } else if left.as_ref() == &MachineTerm::constant(1) {
        Some(right)
    } else {
        None
    }
}

/// The operands of a comparison as the native comparison reads them. A
/// comparison of exact observations, `to_integer(a) < to_integer(b)` or
/// `to_integer(a) < 7`, is the native comparison of `a` and `b`, so a lemma
/// over machine values takes `a` and `b` as its arguments.
fn native_operands(
    left: &ContractExpression,
    right: &ContractExpression,
) -> (ContractExpression, ContractExpression) {
    fn observed(operand: &ContractExpression) -> Option<&ContractExpression> {
        match operand {
            ContractExpression::Call { name, arguments } if name == "to_integer" => {
                match arguments.as_slice() {
                    [argument] => Some(argument),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    fn literal(operand: &ContractExpression) -> bool {
        match operand {
            ContractExpression::IntegerLiteral(_) => true,
            ContractExpression::Negate(inner) => {
                matches!(inner.as_ref(), ContractExpression::IntegerLiteral(_))
            }
            _ => false,
        }
    }
    match (observed(left), observed(right)) {
        (Some(left), Some(right)) => (left.clone(), right.clone()),
        (Some(left), None) if literal(right) => (left.clone(), right.clone()),
        (None, Some(right)) if literal(left) => (left.clone(), right.clone()),
        _ => (left.clone(), right.clone()),
    }
}

pub(super) fn surface_strict_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    if let ClickProposition::At {
        selector,
        proposition,
    } = proposition
    {
        let (left, right) = surface_strict_parts(proposition)?;
        let at = |expression| ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression),
        };
        return Some((at(left), at(right)));
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let (left, right) = native_operands(left, right);
    match operator {
        ComparisonOperator::LessThan => Some((left, right)),
        ComparisonOperator::GreaterThan => Some((right, left)),
        _ => None,
    }
}

pub(super) fn surface_nonstrict_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    if let ClickProposition::At {
        selector,
        proposition,
    } = proposition
    {
        let (left, right) = surface_nonstrict_parts(proposition)?;
        let at = |expression| ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression),
        };
        return Some((at(left), at(right)));
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let (left, right) = native_operands(left, right);
    match operator {
        ComparisonOperator::LessEqual => Some((left, right)),
        ComparisonOperator::GreaterEqual => Some((right, left)),
        _ => None,
    }
}

pub(super) fn plan_explicit_increment_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (incremented, goal_upper) = goal_exact_less_equal_parts(goal)?;
    let base = increment_base(incremented)?;

    for (kernel, surface) in premise_pairs {
        let Some((premise_base, premise_upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_base != base || premise_upper != goal_upper {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_positive_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // `0 <= value` and `value >= 0` are one order; arithmetic closes either
    // spelling.
    let (goal_lower, goal_value) = signed_nonstrict_parts(goal)?;
    if goal_lower != &MachineTerm::constant(0) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &MachineTerm::constant(0) || premise_value != goal_value {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_le_transitive_constant_lower(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: goal_lower,
            right: goal_value,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let bits32_constant!(goal_lower_bits) = goal_lower.as_ref() else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        let bits32_constant!(premise_lower_bits) = premise_lower else {
            continue;
        };
        if premise_value != goal_value.as_ref()
            || (constant_u32(*goal_lower_bits) as i32) >= (constant_u32(*premise_lower_bits) as i32)
        {
            continue;
        }
        let constant_leg = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(goal_lower.as_ref().clone()),
                right: Box::new(premise_lower.clone()),
            },
            true,
        );
        if !normalizes_context_free(&constant_leg) {
            continue;
        }
        surface_nonstrict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

fn plan_explicit_strict_implies_nonstrict(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_left, goal_right) = signed_nonstrict_parts(goal)?;
    for (kernel, surface) in premise_pairs {
        let Some((premise_left, premise_right)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_left != goal_left || premise_right != goal_right {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

/// Plans a vacuous-implication certificate: an implication chain whose
/// antecedent at some depth is refuted by a listed premise closes by
/// introducing antecedents down to the refuted one, then naming the
/// contradiction. Check pushes each introduced antecedent exactly as the
/// goal writes it, so the refuting premise must be that form's exact
/// opposite (flipped condition polarity or a stripped `not`); anything looser
/// would not survive the `contradiction` tactic's exact-match check.
fn plan_explicit_implies_refuted_antecedent(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let mut tactics = Vec::new();
    let mut current = goal;
    while let Proposition::Implies(antecedent, consequent) = current {
        tactics.push(ProofTactic::Intro);
        let refutation = premise_pairs
            .iter()
            .find(|(kernel, _)| match antecedent.as_ref() {
                Proposition::ConditionIs(condition, expected) => {
                    kernel == &Proposition::ConditionIs(condition.clone(), !expected)
                }
                Proposition::Not(inner) => kernel == inner.as_ref(),
                _ => false,
            });
        if let Some((_, surface)) = refutation {
            tactics.push(ProofTactic::Contradiction(surface.clone()));
            return Some(tactics);
        }
        current = consequent;
    }
    None
}

/// Modus ponens over a listed implication premise: walk a (possibly chained)
/// implication whose antecedents are each listed premises, and close the goal
/// when a consequent along the walk is the goal. The emitted `extract` names
/// the consequent's surface form, so the checker revalidates the same bounded
/// rule; `known` then closes the goal from the extracted fact.
fn plan_explicit_discharged_implication_consequent(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let antecedent_listed = |antecedent: &Proposition| {
        premise_pairs.iter().any(|(kernel, _)| {
            kernel == antecedent || condition_polarity_equivalent(kernel, antecedent)
        })
    };
    for (kernel, surface) in premise_pairs {
        let mut current = (kernel, surface);
        while let (
            Proposition::Implies(antecedent, consequent),
            ClickProposition::Implies(_, surface_consequent),
        ) = (current.0, current.1)
        {
            if !antecedent_listed(antecedent) {
                break;
            }
            if consequent.as_ref() == goal || condition_polarity_equivalent(consequent, goal) {
                return Some(vec![
                    ProofTactic::Extract(surface_consequent.as_ref().clone()),
                    ProofTactic::Known,
                ]);
            }
            current = (consequent, surface_consequent);
        }
    }
    None
}

fn plan_explicit_greater_equal_to_reversed_less_equal(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: goal_lower,
            right: goal_greater,
        },
        true,
    ) = goal
    else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: greater,
                right: lower,
            },
            true,
        ) = kernel
        else {
            continue;
        };
        if greater != goal_greater || lower != goal_lower {
            continue;
        }
        surface_nonstrict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

fn plan_explicit_not_strict_implies_greater_equal(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_left, goal_right) = match goal {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            true,
        ) => (left, right),
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: lower,
                right: greater,
            },
            true,
        ) => (greater, lower),
        _ => return None,
    };
    for (kernel, surface) in premise_pairs {
        let matches = match kernel {
            Proposition::Not(body) => matches!(
                body.as_ref(),
                Proposition::ConditionIs(
                    ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left, right },
                    true,
                ) if left == goal_left && right == goal_right
            ),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left,
                    right,
                },
                false,
            ) => left == goal_left && right == goal_right,
            _ => false,
        };
        if !matches {
            continue;
        }
        let ClickProposition::Not(inner) = surface else {
            continue;
        };
        surface_strict_parts(inner)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

fn plan_explicit_greater_equal_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: goal_last,
            right: goal_first,
        },
        true,
    ) = goal
    else {
        return None;
    };
    for (first_kernel, first_surface) in premise_pairs {
        let Some((first, middle)) = signed_nonstrict_parts(first_kernel) else {
            continue;
        };
        if first != goal_first.as_ref() {
            continue;
        }
        for (second_kernel, second_surface) in premise_pairs {
            let Some((second_middle, last)) = signed_nonstrict_parts(second_kernel) else {
                continue;
            };
            if second_middle != middle || last != goal_last.as_ref() {
                continue;
            }
            surface_nonstrict_parts(first_surface)?;
            surface_nonstrict_parts(second_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                second_surface.clone(),
                first_surface.clone(),
            ])]);
        }
    }
    None
}

pub(super) fn plan_explicit_negated_strict_successor_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: goal_value,
            right: goal_lower,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let bits32_constant!(lower) = goal_lower.as_ref() else {
        return None;
    };
    let upper = (constant_u32(*lower) as i32).checked_add(1)? as u32;
    for (kernel, surface) in premise_pairs {
        let (premise_value, premise_upper) = match kernel {
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: value,
                        right: upper,
                    },
                    true,
                ) => (value.as_ref(), upper.as_ref()),
                _ => continue,
            },
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: value,
                    right: upper,
                },
                false,
            ) => (value.as_ref(), upper.as_ref()),
            _ => continue,
        };
        if premise_value != goal_value.as_ref() || premise_upper != &MachineTerm::constant(upper) {
            continue;
        }
        let ClickProposition::Not(inner) = surface else {
            continue;
        };
        surface_strict_parts(inner)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_increment_greater_equal_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: incremented,
            right: goal_lower,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower.as_ref() || lower_base != base {
            continue;
        }
        surface_nonstrict_parts(lower_surface)?;
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            surface_strict_parts(upper_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                lower_surface.clone(),
                upper_surface.clone(),
            ])]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_strict_greater_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: incremented,
            right: goal_lower,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower.as_ref() || lower_base != base {
            continue;
        }
        surface_nonstrict_parts(lower_surface)?;
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            surface_strict_parts(upper_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                lower_surface.clone(),
                upper_surface.clone(),
            ])]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_strict_greater_from_strict_lower(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: incremented,
            right: goal_lower,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    let [(lower_kernel, lower_surface), (upper_kernel, upper_surface)] = premise_pairs else {
        return None;
    };
    let (premise_lower, lower_base) = signed_strict_parts(lower_kernel)?;
    let (upper_base, _) = signed_strict_parts(upper_kernel)?;
    if premise_lower != goal_lower.as_ref() || lower_base != base || upper_base != base {
        return None;
    }
    let (_, surface_value) = surface_strict_parts(lower_surface)?;
    let (surface_upper_base, _) = surface_strict_parts(upper_surface)?;
    if surface_upper_base != surface_value {
        return None;
    }
    Some(vec![ProofTactic::ArithmeticUsing(vec![
        lower_surface.clone(),
        upper_surface.clone(),
    ])])
}

/// The order of one leg of a signed transitive chain.
#[derive(Clone, Copy)]
enum SignedOrder {
    NonStrict,
    Strict,
}

impl SignedOrder {
    fn kernel_parts(self, proposition: &Proposition) -> Option<(&MachineTerm, &MachineTerm)> {
        match self {
            Self::NonStrict => signed_nonstrict_parts(proposition),
            Self::Strict => signed_strict_parts(proposition),
        }
    }

    fn surface_parts(
        self,
        proposition: &ClickProposition,
    ) -> Option<(ContractExpression, ContractExpression)> {
        match self {
            Self::NonStrict => surface_nonstrict_parts(proposition),
            Self::Strict => surface_strict_parts(proposition),
        }
    }
}

/// The signed transitive chains the planner recognizes, tried in order: the
/// order of each leg. A chain is strict end to end when either leg is.
const SIGNED_TRANSITIVE_CHAINS: [(SignedOrder, SignedOrder); 4] = [
    (SignedOrder::Strict, SignedOrder::Strict),
    (SignedOrder::NonStrict, SignedOrder::NonStrict),
    (SignedOrder::NonStrict, SignedOrder::Strict),
    (SignedOrder::Strict, SignedOrder::NonStrict),
];

/// Listed `first ~ middle` and `middle ~ last` give the goal `first ~ last`
/// by Integer arithmetic over the two.
fn plan_explicit_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    (first_order, second_order): (SignedOrder, SignedOrder),
) -> Option<Vec<ProofTactic>> {
    let strict =
        matches!(first_order, SignedOrder::Strict) || matches!(second_order, SignedOrder::Strict);
    let (goal_first, goal_last) = match goal {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: goal_first,
                right: goal_last,
            },
            true,
        ) if strict => (goal_first, goal_last),
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: goal_first,
                right: goal_last,
            },
            true,
        ) if !strict => (goal_first, goal_last),
        _ => return None,
    };
    for (first_kernel, first_surface) in premise_pairs {
        let Some((first, middle)) = first_order.kernel_parts(first_kernel) else {
            continue;
        };
        if first != goal_first.as_ref() {
            continue;
        }
        for (second_kernel, second_surface) in premise_pairs {
            let Some((second_middle, last)) = second_order.kernel_parts(second_kernel) else {
                continue;
            };
            if second_middle != middle || last != goal_last.as_ref() {
                continue;
            }
            first_order.surface_parts(first_surface)?;
            second_order.surface_parts(second_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                first_surface.clone(),
                second_surface.clone(),
            ])]);
        }
    }
    None
}

/// A constant non-strict upper bound sharpens below any larger constant:
/// `x < c1` follows from a listed `x <= c2` when `c2 < c1`, through
/// Integer arithmetic over the premise.
fn plan_explicit_constant_strict_upper_bound_weakening(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: goal_value,
            right: goal_upper,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let bits32_constant!(goal_constant) = goal_upper.as_ref() else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let strict = signed_strict_parts(premise_kernel).is_some();
        let Some((premise_value, premise_upper)) =
            signed_nonstrict_parts(premise_kernel).or_else(|| signed_strict_parts(premise_kernel))
        else {
            continue;
        };
        if premise_value != goal_value.as_ref() {
            continue;
        }
        let bits32_constant!(premise_constant) = premise_upper else {
            continue;
        };
        if (constant_u32(*premise_constant) as i32) >= (constant_u32(*goal_constant) as i32) {
            continue;
        }
        if strict {
            surface_strict_parts(premise_surface)?;
        } else {
            surface_nonstrict_parts(premise_surface)?;
        }
        return Some(vec![ProofTactic::ArithmeticUsing(vec![
            premise_surface.clone(),
        ])]);
    }
    None
}

/// An increment stays under a constant bound that clears its base's constant
/// bound: `x + 1 <= c1` follows from a listed `x <= c2` when `c2 < c1`,
/// by Integer arithmetic over the premise.
pub(super) fn plan_explicit_increment_constant_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: incremented,
            right: goal_upper,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    let bits32_constant!(goal_constant) = goal_upper.as_ref() else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let Some((premise_value, premise_upper)) = signed_nonstrict_parts(premise_kernel) else {
            continue;
        };
        if premise_value != base {
            continue;
        }
        let bits32_constant!(premise_constant) = premise_upper else {
            continue;
        };
        if (constant_u32(*premise_constant) as i32) >= (constant_u32(*goal_constant) as i32) {
            continue;
        }
        surface_nonstrict_parts(premise_surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![
            premise_surface.clone(),
        ])]);
    }
    None
}

/// A constant lower bound relaxes to any smaller constant: `c1 <= x` follows
/// from a listed `x >= c2` (in either form) when `c1 <= c2`, by Integer
/// arithmetic over the premise.
fn plan_explicit_constant_lower_bound_weakening(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, goal_value) = signed_nonstrict_parts(goal)?;
    let bits32_constant!(goal_constant) = goal_lower else {
        return None;
    };
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        },
        true,
    ) = goal
    else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(premise_kernel) else {
            continue;
        };
        if premise_value != goal_value {
            continue;
        }
        let bits32_constant!(premise_constant) = premise_lower else {
            continue;
        };
        if (constant_u32(*goal_constant) as i32) > (constant_u32(*premise_constant) as i32)
            || constant_u32(*premise_constant) == constant_u32(*goal_constant)
        {
            continue;
        }
        surface_nonstrict_parts(premise_surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![
            premise_surface.clone(),
        ])]);
    }
    None
}

// Written operand identity for the explicit arithmetic rules below. The
// observation handle is an exact syntax key, not a value/equality-graph read.
fn same_written_int32_operand(
    operand: crate::kernel::MachineOperandView<'_>,
    written: &MachineTerm,
) -> bool {
    operand.retain(MachineIntegerType::Int32)
        == crate::kernel::SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            written.clone(),
        )
}

pub(super) fn plan_explicit_increment_below_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (crate::kernel::SignedDefinedWidth::Int32, operands, false) =
        crate::kernel::proof::arithmetic_special::signed_definedness_query(goal)?
    else {
        return None;
    };
    let [value, amount] = [&operands[0], &operands[1]].map(|operand| operand.operand_view());
    if amount.literal() != Some(MachineTerm::constant(1)) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if !same_written_int32_operand(value, premise_value)
            || upper != &MachineTerm::constant(i32::MAX as u32)
        {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_one_plus_below_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (crate::kernel::SignedDefinedWidth::Int32, operands, false) =
        crate::kernel::proof::arithmetic_special::signed_definedness_query(goal)?
    else {
        return None;
    };
    let [one, value] = [&operands[0], &operands[1]].map(|operand| operand.operand_view());
    if one.literal() != Some(MachineTerm::constant(1)) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if !same_written_int32_operand(value, premise_value)
            || upper != &MachineTerm::constant(i32::MAX as u32)
        {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_one_plus_strictly_increases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: value,
            right: sum,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let binary_term!(Int32, Add, one, added_value) = sum.as_ref() else {
        return None;
    };
    if one.as_ref() != &MachineTerm::constant(1) || added_value.as_ref() != value.as_ref() {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &MachineTerm::constant(i32::MAX as u32) {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_nonnegative_add_within_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (crate::kernel::SignedDefinedWidth::Int32, operands, false) =
        crate::kernel::proof::arithmetic_special::signed_definedness_query(goal)?
    else {
        return None;
    };
    let [value, amount] = [&operands[0], &operands[1]].map(|operand| operand.operand_view());
    let zero = MachineTerm::constant(0);
    let (_, nonnegative_surface) = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel)
            .is_some_and(|(left, right)| left == &zero && same_written_int32_operand(amount, right))
    })?;
    let (_, headroom_surface) = premise_pairs.iter().find(|(kernel, _)| {
        let Some((left, right)) = signed_nonstrict_parts(kernel) else {
            return false;
        };
        let binary_term!(Int32, Subtract, maximum, subtracted) = right else {
            return false;
        };
        same_written_int32_operand(value, left)
            && maximum.as_ref() == &MachineTerm::constant(i32::MAX as u32)
            && same_written_int32_operand(amount, subtracted)
    })?;
    surface_nonstrict_parts(nonnegative_surface)?;
    surface_nonstrict_parts(headroom_surface)?;
    let (_, surface_amount) = surface_nonstrict_parts(nonnegative_surface)?;
    let (surface_value, _) = surface_nonstrict_parts(headroom_surface)?;
    // The headroom `MAX - amount` is itself a machine difference, whose
    // observation the Integer bounds would first need as an in-range
    // identity; the named rule states the whole step.
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "click::integer::int32_nonnegative_add_within_max_is_defined".to_string(),
                arguments: vec![surface_value, surface_amount],
            },
            premises: vec![nonnegative_surface.clone(), headroom_surface.clone()],
        },
        ProofTactic::Known,
    ])
}

/// `defined(value - amount)` over `int32` by its two Integer bounds, which
/// together are the definedness fact: each bound of the exact value is
/// proved by Integer arithmetic from `premises` and the type-range bound of
/// `value` it needs, stated by its explicit certificate.
fn int32_definedness_by_integer_bounds(
    value: ContractExpression,
    amount: ContractExpression,
    subtract: bool,
    premises: Vec<ClickProposition>,
) -> Vec<ProofTactic> {
    let observe = |operand: ContractExpression| ContractExpression::Call {
        name: "to_integer".to_string(),
        arguments: vec![operand],
    };
    let literal = |text: &str| ContractExpression::IntegerLiteral(text.to_string());
    let less_equal = |left, right| ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::LessEqual,
        right,
    };
    let (left, right) = (Box::new(observe(value.clone())), Box::new(observe(amount)));
    let exact = if subtract {
        ContractExpression::Subtract(left, right)
    } else {
        ContractExpression::Add(left, right)
    };
    let minimum = ContractExpression::Negate(Box::new(literal("2147483648")));
    // A sum of a nonnegative amount reaches below the type only through
    // `value`'s lower range; a difference of one reaches above it only
    // through `value`'s upper range.
    let range = if subtract {
        less_equal(observe(value), literal("2147483647"))
    } else {
        less_equal(minimum.clone(), observe(value))
    };
    let mut listed = premises;
    listed.push(range.clone());
    let have = |proposition: ClickProposition, proof: Vec<ProofTactic>| {
        ProofTactic::Have(ProofHave {
            proposition,
            proof: SourceProof::Script(proof),
        })
    };
    vec![
        have(
            range.clone(),
            vec![ProofTactic::ArithmeticCertificate(
                ArithmeticCertificate::integer(IntegerCertificate {
                    nodes: vec![IntegerCertificateNode::TypeRange { result: range }],
                    conclusion: 0,
                }),
            )],
        ),
        have(
            less_equal(minimum, exact.clone()),
            vec![ProofTactic::ArithmeticUsing(listed.clone())],
        ),
        have(
            less_equal(exact, literal("2147483647")),
            vec![ProofTactic::ArithmeticUsing(listed)],
        ),
        ProofTactic::Known,
    ]
}

pub(super) fn plan_explicit_nonnegative_subtract_within_value_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (crate::kernel::SignedDefinedWidth::Int32, operands, true) =
        crate::kernel::proof::arithmetic_special::signed_definedness_query(goal)?
    else {
        return None;
    };
    let [value, amount] = [&operands[0], &operands[1]].map(|operand| operand.operand_view());
    let zero = MachineTerm::constant(0);
    let (_, nonnegative_surface) = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel)
            .is_some_and(|(left, right)| left == &zero && same_written_int32_operand(amount, right))
    })?;
    let (_, within_value_surface) = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel).is_some_and(|(left, right)| {
            same_written_int32_operand(amount, left) && same_written_int32_operand(value, right)
        })
    })?;
    let (_, surface_amount) = surface_nonstrict_parts(nonnegative_surface)?;
    let (_, surface_value) = surface_nonstrict_parts(within_value_surface)?;
    Some(int32_definedness_by_integer_bounds(
        surface_value,
        surface_amount,
        true,
        vec![nonnegative_surface.clone(), within_value_surface.clone()],
    ))
}

pub(super) fn plan_explicit_positive_predecessor_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, predecessor) = goal_exact_less_equal_parts(goal)?;
    if goal_lower != &MachineTerm::constant(0) {
        return None;
    }
    let binary_term!(Int32, Subtract, value, amount) = predecessor else {
        return None;
    };
    if amount.as_ref() != &MachineTerm::constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &MachineTerm::constant(0) || premise_value != value.as_ref() {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

/// From `0 <= value` and `value <= bound`, the predecessor keeps the bound:
/// `value - 1 <= bound` by Integer arithmetic over the two.
/// When the nonnegativity leg is not itself a selected premise and
/// `synthesize_missing_leg` is set, a nested `have` derives it from the same
/// premises with the explicit equality-rewrite search (closing by a listed
/// premise or context-free normalization), so the emitted certificate still
/// names every dependency. Only outcome contexts pass `synthesize_missing_leg`:
/// a pure theorem proof has no `have`, so its planner must not emit one.
pub(super) fn plan_explicit_predecessor_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    synthesize_missing_leg: bool,
) -> Option<Vec<ProofTactic>> {
    let (predecessor, goal_upper) = goal_exact_less_equal_parts(goal)?;
    let binary_term!(Int32, Subtract, value, amount) = predecessor else {
        return None;
    };
    if amount.as_ref() != &MachineTerm::constant(1) {
        return None;
    }
    for (bound_kernel, bound_surface) in premise_pairs {
        let Some((premise_value, premise_bound)) = signed_nonstrict_parts(bound_kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || premise_bound != goal_upper {
            continue;
        }
        let Some((surface_value, _)) = surface_nonstrict_parts(bound_surface) else {
            continue;
        };
        let nonnegative_kernel = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::constant(0)),
                right: value.clone(),
            },
            true,
        );
        let mut tactics = Vec::new();
        let nonnegative_surface = if let Some((_, surface)) =
            premise_pairs.iter().find(|(kernel, _)| {
                signed_nonstrict_parts(kernel).is_some_and(|(lower, bounded)| {
                    lower == &MachineTerm::constant(0) && bounded == value.as_ref()
                })
            }) {
            surface.clone()
        } else {
            if !synthesize_missing_leg {
                continue;
            }
            let kernel_premises = premise_pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            let Some(sub_tactics) = plan_explicit_equality_rewrites_from(
                &nonnegative_kernel,
                premise_pairs,
                &kernel_premises,
                &|current| {
                    kernel_premises
                        .iter()
                        .any(|fact| fact == current || condition_polarity_equivalent(fact, current))
                },
                &|_| None,
            ) else {
                continue;
            };
            let surface_zero =
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0)));
            let nonnegative = ClickProposition::Comparison {
                left: surface_zero,
                operator: ComparisonOperator::LessEqual,
                right: surface_value.clone(),
            };
            tactics.push(ProofTactic::Have(ProofHave {
                proposition: nonnegative.clone(),
                proof: SourceProof::Script(sub_tactics),
            }));
            nonnegative
        };
        tactics.push(ProofTactic::ArithmeticUsing(vec![
            nonnegative_surface,
            bound_surface.clone(),
        ]));
        return Some(tactics);
    }
    None
}

pub(super) fn plan_explicit_one_le_predecessor(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let value = if let Some((goal_lower, predecessor)) = goal_exact_less_equal_parts(goal) {
        if goal_lower != &MachineTerm::constant(0) {
            return None;
        }
        let binary_term!(Int32, Subtract, value, amount) = predecessor else {
            return None;
        };
        if amount.as_ref() != &MachineTerm::constant(1) {
            return None;
        }
        value.as_ref()
    } else {
        let (predecessor, value) = goal_exact_less_than_parts(goal)?;
        let binary_term!(Int32, Subtract, predecessor_value, amount) = predecessor else {
            return None;
        };
        if predecessor_value.as_ref() != value || amount.as_ref() != &MachineTerm::constant(1) {
            return None;
        }
        value
    };
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        if premise_lower != &MachineTerm::constant(1) || premise_value != value {
            continue;
        }
        surface_nonstrict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

fn one_le_predecessor_value(goal: &Proposition) -> Option<MachineTerm> {
    if let Some((goal_lower, predecessor)) = goal_exact_less_equal_parts(goal) {
        if goal_lower != &MachineTerm::constant(0) {
            return None;
        }
        let binary_term!(Int32, Subtract, value, amount) = predecessor else {
            return None;
        };
        (amount.as_ref() == &MachineTerm::constant(1)).then(|| value.as_ref().clone())
    } else {
        let (predecessor, value) = goal_exact_less_than_parts(goal)?;
        let binary_term!(Int32, Subtract, predecessor_value, amount) = predecessor else {
            return None;
        };
        (predecessor_value.as_ref() == value && amount.as_ref() == &MachineTerm::constant(1))
            .then(|| value.clone())
    }
}

fn surface_one_le_equality_source(surface: &ClickProposition) -> Option<ClickProposition> {
    match surface {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_one_le_equality_source(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            ..
        } => Some(ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            operator: ComparisonOperator::LessEqual,
            right: left.clone(),
        }),
        _ => None,
    }
}

pub(super) fn plan_explicit_positive_predecessor_strictly_decreases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (predecessor, value) = goal_exact_less_than_parts(goal)?;
    let binary_term!(Int32, Subtract, predecessor_value, amount) = predecessor else {
        return None;
    };
    if predecessor_value.as_ref() != value || amount.as_ref() != &MachineTerm::constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &MachineTerm::constant(0) || premise_value != value {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_le_and_not_lt_implies_eq(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = goal
    else {
        return None;
    };
    for (le_kernel, le_surface) in premise_pairs {
        let Some((le_left, le_right)) = signed_nonstrict_parts(le_kernel) else {
            continue;
        };
        if le_left != left.as_ref() || le_right != right.as_ref() {
            continue;
        }
        for (not_lt_kernel, not_lt_surface) in premise_pairs {
            let matches_not_lt = match not_lt_kernel {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: not_left,
                        right: not_right,
                    },
                    false,
                ) => not_left.as_ref() == left.as_ref() && not_right.as_ref() == right.as_ref(),
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left: not_left, right: not_right },
                        true,
                    ) if not_left.as_ref() == left.as_ref()
                        && not_right.as_ref() == right.as_ref()
                ),
                _ => false,
            };
            if !matches_not_lt {
                continue;
            }
            surface_nonstrict_parts(le_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                le_surface.clone(),
                not_lt_surface.clone(),
            ])]);
        }
    }
    None
}

/// Plans the small proof that commonly finishes a pointer/index loop:
/// rewrite the load through the loop invariant's pointer equality, then
/// rewrite the array index after proving that the loop counter equals the
/// bound. The kernel's general memory reasoning can establish this equality,
/// but the generated Surface proof must expose the same fact through checked
/// rewrites rather than carrying legacy derivation evidence across the
/// smart/simple boundary.
pub(super) fn plan_pointer_advanced_load_equality(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = goal
    else {
        return None;
    };
    let (left_pointer, right_pointer) = (
        registered_load_pointer(left.as_ref())?,
        registered_load_pointer(right.as_ref())?,
    );

    for (pointer_kernel, pointer_surface) in premise_pairs {
        let Proposition::ConditionIs(ConditionTerm::PointerEqual(fact_left, fact_right), true) =
            pointer_kernel
        else {
            continue;
        };
        let (pointer_surface, fact_array_pointer) = if fact_left.as_ref() == &left_pointer {
            (pointer_surface.clone(), fact_right.as_ref())
        } else if fact_right.as_ref() == &left_pointer {
            (
                reverse_surface_equality(pointer_surface)?,
                fact_left.as_ref(),
            )
        } else {
            continue;
        };
        if fact_array_pointer.block != right_pointer.block {
            continue;
        }
        let (source_index, target_index) =
            pointer_array_index_pair(&fact_array_pointer.offset, &right_pointer.offset)?;
        let index_goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(source_index.clone()),
                right: Box::new(target_index.clone()),
            },
            true,
        );
        let index_proof = plan_explicit_le_and_not_lt_implies_eq(&index_goal, premise_pairs)?;
        let (_, index_surface) = premise_pairs.iter().find(|(kernel, _)| {
            signed_nonstrict_parts(kernel)
                .is_some_and(|(left, right)| left == &source_index && right == &target_index)
        })?;
        let (index_left, index_right) = surface_nonstrict_parts(index_surface)?;
        let index_surface = ClickProposition::Comparison {
            left: index_left,
            operator: ComparisonOperator::Equal,
            right: index_right,
        };
        return Some(vec![
            ProofTactic::Have(ProofHave {
                proposition: index_surface.clone(),
                proof: SourceProof::Script(index_proof),
            }),
            ProofTactic::Rewrite(pointer_surface),
            ProofTactic::Rewrite(index_surface),
            ProofTactic::Known,
        ]);
    }
    None
}

fn registered_load_pointer(term: &MachineTerm) -> Option<Pointer> {
    crate::kernel::scalar_read_observation(crate::kernel::MachineOperandView::Legacy(term))
        .map(|read| read.pointer)
}

fn pointer_array_index_pair(
    source: &PointerOffsetTerm,
    target: &PointerOffsetTerm,
) -> Option<(MachineTerm, MachineTerm)> {
    let source = pointer_offset_addends(source)?;
    let target = pointer_offset_addends(target)?;
    if source.len() != 2 || target.len() != 2 {
        return None;
    }
    let common = source.iter().find(|addend| target.contains(addend))?;
    let source_index = source
        .iter()
        .find(|addend| **addend != *common)
        .and_then(pointer_int32_scaled_value)?;
    let target_index = target
        .iter()
        .find(|addend| **addend != *common)
        .and_then(pointer_int32_scaled_value)?;
    Some((source_index, target_index))
}

fn pointer_offset_addends(offset: &PointerOffsetTerm) -> Option<Vec<PointerOffsetTerm>> {
    match offset {
        PointerOffsetTerm::Constant(0) => Some(Vec::new()),
        PointerOffsetTerm::Add(left, right) => {
            let mut addends = pointer_offset_addends(left)?;
            addends.extend(pointer_offset_addends(right)?);
            Some(addends)
        }
        _ => Some(vec![offset.clone()]),
    }
}

fn pointer_int32_scaled_value(offset: &PointerOffsetTerm) -> Option<MachineTerm> {
    let PointerOffsetTerm::Int32Scaled { value, byte_width } = offset else {
        return None;
    };
    (*byte_width == 4).then(|| value.structural_value().clone())
}

pub(super) fn plan_explicit_ge_and_not_gt_implies_eq(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = goal
    else {
        return None;
    };
    for (ge_kernel, ge_surface) in premise_pairs {
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: ge_left,
                right: ge_right,
            },
            true,
        ) = ge_kernel
        else {
            continue;
        };
        if ge_left != left || ge_right != right {
            continue;
        }
        for (not_gt_kernel, not_gt_surface) in premise_pairs {
            let matches_not_gt = match not_gt_kernel {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: not_left,
                        right: not_right,
                    },
                    false,
                ) => not_left == left && not_right == right,
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::GreaterThan, left: not_left, right: not_right },
                        true,
                    ) if not_left == left && not_right == right
                ),
                _ => false,
            };
            if !matches_not_gt {
                continue;
            }
            surface_nonstrict_parts(ge_surface)?;
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                ge_surface.clone(),
                not_gt_surface.clone(),
            ])]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_strictly_increases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (base, incremented) = goal_exact_less_than_parts(goal)?;
    if increment_base(incremented)? != base {
        return None;
    }

    for (kernel, surface) in premise_pairs {
        let Some((premise_base, _)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_base != base {
            continue;
        }
        surface_strict_parts(surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
    }
    None
}

pub(super) fn plan_explicit_successor_le_implies_lt(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (lower, value) = match goal {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: lower,
                right: value,
            },
            true,
        )
        | Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: value,
                right: lower,
            },
            true,
        ) => (lower.as_ref(), value.as_ref()),
        _ => return None,
    };
    for (bound_kernel, bound_surface) in premise_pairs {
        let Some((successor, bound_value)) = signed_nonstrict_parts(bound_kernel) else {
            continue;
        };
        if bound_value != value
            || successor
                != &crate::kernel::canonical_term(&MachineTerm::add(
                    lower.clone(),
                    MachineTerm::constant(1),
                ))
        {
            continue;
        }
        let no_overflow = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(lower.clone()),
                right: Box::new(successor.clone()),
            },
            true,
        );
        if !normalizes_context_free(&no_overflow) {
            continue;
        }
        if !matches!(lower, bits32_constant!(_)) {
            continue;
        }
        surface_nonstrict_parts(bound_surface)?;
        return Some(vec![ProofTactic::ArithmeticUsing(vec![
            bound_surface.clone(),
        ])]);
    }
    None
}

pub(super) fn plan_explicit_increment_preserves_order(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    for (order_kernel, order_surface) in premise_pairs {
        let Some((lower, value)) = signed_nonstrict_parts(order_kernel) else {
            continue;
        };
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_value, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_value != value {
                continue;
            }
            let expected = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(MachineTerm::add(lower.clone(), MachineTerm::constant(1))),
                    right: Box::new(MachineTerm::add(value.clone(), MachineTerm::constant(1))),
                },
                true,
            );
            if &expected != goal {
                continue;
            }
            let Some(_) = surface_nonstrict_parts(order_surface) else {
                continue;
            };
            let Some(_) = surface_strict_parts(upper_surface) else {
                continue;
            };
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                order_surface.clone(),
                upper_surface.clone(),
            ])]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // A greater-equal goal form belongs to
    // `plan_explicit_increment_greater_equal_lower_bound`.
    let (goal_lower, incremented) = goal_exact_less_equal_parts(goal)?;
    let base = increment_base(incremented)?;

    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower || lower_base != base {
            continue;
        }
        let Some(_) = surface_nonstrict_parts(lower_surface) else {
            continue;
        };
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let Some(_) = surface_strict_parts(upper_surface) else {
                continue;
            };
            return Some(vec![ProofTactic::ArithmeticUsing(vec![
                lower_surface.clone(),
                upper_surface.clone(),
            ])]);
        }
    }
    None
}

pub(super) fn comparison_state_variants(
    proposition: &ClickProposition,
    selectors: &[ProgramPointSelector],
) -> Option<Vec<ClickProposition>> {
    if let ClickProposition::Not(body) = proposition {
        return Some(
            comparison_state_variants(body, selectors)?
                .into_iter()
                .map(|variant| ClickProposition::Not(Box::new(variant)))
                .collect(),
        );
    }
    if let ClickProposition::ForAll {
        click_type: interface_type,
        name,
        written_name,
        body,
    } = proposition
    {
        return Some(
            comparison_state_variants(body, selectors)?
                .into_iter()
                .map(|body| ClickProposition::ForAll {
                    click_type: interface_type.clone(),
                    name: name.clone(),
                    written_name: written_name.clone(),
                    body: Box::new(body),
                })
                .collect(),
        );
    }
    if let ClickProposition::Implies(left, right) = proposition {
        let mut variants = comparison_state_variants(right, selectors)?
            .into_iter()
            .map(|right| ClickProposition::Implies(left.clone(), Box::new(right)))
            .collect::<Vec<_>>();
        if let Some(left_variants) = comparison_state_variants(left, selectors) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::Implies(Box::new(left), right.clone())),
            );
        }
        return Some(variants);
    }
    if let ClickProposition::Or(left, right) = proposition {
        let left_variants = comparison_state_variants(left, selectors)?;
        let right_variants = comparison_state_variants(right, selectors)?;
        let mut variants = vec![proposition.clone()];
        let mut push = |left: ClickProposition, right: ClickProposition| {
            let candidate = ClickProposition::Or(Box::new(left), Box::new(right));
            if !variants.contains(&candidate) {
                variants.push(candidate);
            }
        };
        for left in &left_variants {
            push(left.clone(), right.as_ref().clone());
        }
        for right in &right_variants {
            push(left.as_ref().clone(), right.clone());
        }
        for (left, right) in left_variants.into_iter().zip(right_variants) {
            push(left, right);
        }
        return Some(variants);
    }
    if let ClickProposition::And(left, right) = proposition {
        let mut variants = Vec::new();
        if let Some(right_variants) = comparison_state_variants(right, selectors) {
            variants.extend(
                right_variants
                    .into_iter()
                    .map(|right| ClickProposition::And(left.clone(), Box::new(right))),
            );
        }
        if let Some(left_variants) = comparison_state_variants(left, selectors) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::And(Box::new(left), right.clone())),
            );
        }
        return (!variants.is_empty()).then_some(variants);
    }
    // A predicate call names its memory state only through its array-ref
    // arguments, so the state is selected by wrapping the arguments —
    // uniformly, the way the recorded-form search in
    // `checked_surface_fact_in_state_with_assumptions` already does. Wrapping
    // a value argument is harmless: it evaluates to the same value in every
    // selected state where it is synthesizable at, and a wrapping that
    // does not lower is discarded by the caller's `check`.
    if let ClickProposition::PredicateCall { name, arguments } = proposition {
        let call = |wrap: &dyn Fn(&ContractExpression) -> ContractExpression| {
            ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments.iter().map(wrap).collect(),
            }
        };
        let mut variants = vec![proposition.clone()];
        if !arguments
            .iter()
            .any(|argument| matches!(argument, ContractExpression::Old(_)))
        {
            variants.push(call(&|argument| {
                ContractExpression::Old(Box::new(argument.clone()))
            }));
        }
        for selector in selectors.iter().rev() {
            let candidate = call(&|argument| ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(argument.clone()),
            });
            if !variants.contains(&candidate) {
                variants.push(candidate);
            }
        }
        return Some(variants);
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let at_program_point =
        |expression: &ContractExpression, selector: &ProgramPointSelector| ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression.clone()),
        };
    let comparison = |left, right| ClickProposition::Comparison {
        left,
        operator: *operator,
        right,
    };
    let old_left = (!matches!(left, ContractExpression::Old(_)))
        .then(|| ContractExpression::Old(Box::new(left.clone())));
    let old_right = (!matches!(right, ContractExpression::Old(_)))
        .then(|| ContractExpression::Old(Box::new(right.clone())));
    let state_pairs = selectors
        .iter()
        .rev()
        .map(|selector| {
            (
                at_program_point(left, selector),
                at_program_point(right, selector),
            )
        })
        .collect::<Vec<_>>();
    let mut variants = Vec::new();
    let mut push = |left, right| {
        let candidate = comparison(left, right);
        if !variants.contains(&candidate) {
            variants.push(candidate);
        }
    };
    push(left.clone(), right.clone());
    if let Some(old_left) = &old_left {
        push(old_left.clone(), right.clone());
    }
    if let Some(old_right) = &old_right {
        push(left.clone(), old_right.clone());
    }
    if let (Some(old_left), Some(old_right)) = (&old_left, &old_right) {
        push(old_left.clone(), old_right.clone());
    }
    for (state_left, state_right) in &state_pairs {
        push(state_left.clone(), right.clone());
        push(left.clone(), state_right.clone());
        push(state_left.clone(), state_right.clone());
    }

    let mut left_variants = vec![left.clone()];
    let mut right_variants = vec![right.clone()];
    if let Some(old_left) = old_left {
        left_variants.push(old_left);
    }
    if let Some(old_right) = old_right {
        right_variants.push(old_right);
    }
    for (state_left, state_right) in state_pairs {
        left_variants.push(state_left);
        right_variants.push(state_right);
    }
    for left in left_variants {
        for right in &right_variants {
            push(left.clone(), right.clone());
        }
    }
    Some(variants)
}

pub(super) fn lower_surface_candidate_in_state_with_assumptions(
    view: ExecutionView<'_>,
    candidate: &ClickProposition,
    assumptions: &PureFactContext,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, ClickError> {
    check_verification_deadline()?;
    let values = parameter_values(parameter_binding)?;
    let array_refs =
        array_refs_for_parameters(parameter_binding.parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let assumptions = assumptions.clone().allow_symbolic_contract_loads();
    lower_fixed_state_proposition_through_kernel(
        candidate,
        &assumptions,
        ContractEnvironment::new(&values, &array_refs),
        FixedStateFrame::new(
            view.old_reference_state(state),
            state,
            None,
            view.recorded_states,
        ),
        spec_definitions,
    )
    .map_err(ClickError::new)
}

fn program_expression_mentions_program_local(
    expression: &ProgramExpression,
    parameter_names: &BTreeSet<&str>,
) -> bool {
    let mut names = BTreeSet::new();
    crate::surface::collect_program_expression_referenced_names(expression, &mut names);
    names
        .iter()
        .any(|name| !parameter_names.contains(name.as_str()))
}

pub(super) fn contract_expression_mentions_program_local(
    expression: &ContractExpression,
    parameter_names: &BTreeSet<&str>,
) -> bool {
    match expression {
        ContractExpression::Resource(subject) => {
            let mut names = BTreeSet::new();
            crate::surface::lowering::collect_resource_subject_referenced_names(
                subject, &mut names,
            );
            names
                .iter()
                .any(|name| !parameter_names.contains(name.as_str()))
        }
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => false,
        ContractExpression::IntegerLiteral(_) => false,
        ContractExpression::CUnary { operand: inner, .. } | ContractExpression::Negate(inner) => {
            contract_expression_mentions_program_local(inner, parameter_names)
        }
        ContractExpression::ResourceField(_) => false,
        ContractExpression::AlgebraicVariable { .. } => false,
        ContractExpression::Binding(name) => !parameter_names.contains(name.as_str()),
        ContractExpression::AlgebraicConstructor { arguments, .. } => arguments
            .iter()
            .any(|argument| contract_expression_mentions_program_local(argument, parameter_names)),
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            contract_expression_mentions_program_local(scrutinee, parameter_names)
                || arms.iter().any(|arm| {
                    let mut arm_names = parameter_names.clone();
                    arm_names.extend(arm.bindings.iter().map(String::as_str));
                    contract_expression_mentions_program_local(&arm.body, &arm_names)
                })
        }
        ContractExpression::SequenceLiteral(elements) => elements
            .iter()
            .any(|element| contract_expression_mentions_program_local(element, parameter_names)),
        ContractExpression::SequenceConcat(left, right) => {
            contract_expression_mentions_program_local(left, parameter_names)
                || contract_expression_mentions_program_local(right, parameter_names)
        }
        ContractExpression::CBinding(_) | ContractExpression::ResourceWildcard => false,
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => arguments.iter().any(|argument| {
                contract_expression_mentions_program_local(argument, parameter_names)
            }),
            _ => false,
        },
        ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) => {
            !parameter_names.contains(name.as_str())
        }
        ContractExpression::QualifiedC { .. } | ContractExpression::ProgramExpression(_) => false,
        ContractExpression::ArrayIndex {
            base,
            indexes,
            lowered,
            ..
        } => {
            contract_expression_mentions_program_local(base, parameter_names)
                || indexes
                    .iter()
                    .any(|index| contract_expression_mentions_program_local(index, parameter_names))
                || (!matches!(base.as_ref(), ContractExpression::QualifiedC { .. })
                    && program_expression_mentions_program_local(lowered, parameter_names))
        }
        ContractExpression::Field { base, .. }
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::BitwiseNot(base) => {
            contract_expression_mentions_program_local(base, parameter_names)
        }
        crate::surface::binary_contract_expression!(left, right) => {
            contract_expression_mentions_program_local(left, parameter_names)
                || contract_expression_mentions_program_local(right, parameter_names)
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            contract_expression_mentions_program_local(then_branch, parameter_names)
                || contract_expression_mentions_program_local(else_branch, parameter_names)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contract_expression_mentions_program_local(start, parameter_names)
                || contract_expression_mentions_program_local(end, parameter_names)
                || contract_expression_mentions_program_local(initial, parameter_names)
                || contract_expression_mentions_program_local(body, parameter_names)
        }
        ContractExpression::Let { value, body, .. } => {
            contract_expression_mentions_program_local(value, parameter_names)
                || contract_expression_mentions_program_local(body, parameter_names)
        }
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            contract_expression_mentions_program_local(receiver, parameter_names)
                || arguments.iter().any(|argument| {
                    contract_expression_mentions_program_local(argument, parameter_names)
                })
        }
        ContractExpression::Call { arguments, .. } => arguments
            .iter()
            .any(|argument| contract_expression_mentions_program_local(argument, parameter_names)),
    }
}

#[cfg(test)]
mod selected_premise_tests {
    use super::*;
    use crate::kernel::{PointerBlock, PointerOffsetTerm};

    #[test]
    fn loadability_planning_does_not_repeat_search_after_its_budget_is_spent() {
        use crate::instrumentation::{
            TacticEvent, TacticWorkLimits, VerificationEvent, emit, measure_deterministic_work,
            with_tactic_work_limits,
        };

        let goal = Proposition::MemoryLoadable {
            memory: Memory::new(),
            base: Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: MachineTerm::constant(4),
            wide: false,
        };
        let surface = ClickProposition::Loadable {
            segment: ContractSegment {
                uninitialized: false,
                state: ContractSegmentState::Current,
                base: ProgramExpression::Variable("p".into()),
                start: ProgramExpression::Value(int32(0)),
                end: ProgramExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        "p".into(),
                    )),
                    start: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(
                        0,
                    ))),
                    end: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
                },
            },
        };
        // Give planning exactly the work needed to establish its candidate.
        // Repeating that query in a debug assertion then exhausts the budget.
        let (derivation, work) = measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::derive_solve_proposition(
                &(assumptions_from_propositions(std::slice::from_ref(&goal))),
                &goal,
            )
        });
        assert!(derivation.is_some());
        assert!(work > 0);
        let tactic = TacticEvent {
            source_tactic_path: None,
            claim: "viewability".into(),
            tactic_index: 0,
            tactic_name: "solve".into(),
            class: "smart".into(),
            statement_index: 0,
            source_index: 0,
        };
        let candidate = with_tactic_work_limits(
            TacticWorkLimits {
                smart: work,
                ..TacticWorkLimits::default()
            },
            || {
                emit(VerificationEvent::TacticStarted(tactic.clone()));
                let candidate = plan_explicit_loadability_transport(
                    &goal,
                    &surface,
                    &[(goal.clone(), surface.clone())],
                );
                emit(VerificationEvent::TacticFailed(tactic));
                candidate
            },
        );
        assert_eq!(
            candidate,
            Some(vec![
                ProofTactic::TransportUsing {
                    source: surface.clone(),
                    target: surface.clone(),
                    premises: vec![surface],
                },
                ProofTactic::Known,
            ])
        );
    }
}

#[cfg(test)]
mod shared_goal_spelling_tests {
    use super::*;

    #[test]
    fn ordinary_signed_goal_spelling_does_not_export_operands() {
        use crate::kernel::{IntegerTerm, KernelTerm, KernelType, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(991705);
        let machine = SharedMachineIntegerTerm::from_shared(
            MachineIntegerType::Int32,
            KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::Add,
                [
                    KernelTerm::variable(
                        KernelType::Program(MachineIntegerType::Int32.program_type()),
                        variable,
                    ),
                    KernelTerm::variable(
                        KernelType::Program(MachineIntegerType::Int32.program_type()),
                        variable,
                    ),
                ],
            ),
        )
        .unwrap();
        let surface =
            ContractExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
        let one = ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1)));
        let pairs = vec![(
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(MachineTerm::constant(10)),
                },
                true,
            ),
            ClickProposition::Comparison {
                left: surface.clone(),
                operator: ComparisonOperator::LessEqual,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(10))),
            },
        )];
        let surface = ContractExpression::Add(Box::new(surface.clone()), Box::new(surface));
        for subtract in [false, true] {
            let left = IntegerTerm::Machine(machine.clone()).into();
            let right = IntegerTerm::constant(1.into()).into();
            let exact = if subtract {
                IntegerTerm::Subtract(left, right)
            } else {
                IntegerTerm::Add(left, right)
            };
            let upper = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    exact.clone().into(),
                    IntegerTerm::constant(i32::MAX.into()).into(),
                ),
                true,
            );
            let lower = Proposition::ConditionIs(
                ConditionTerm::IntegerGreaterEqual(
                    exact.into(),
                    IntegerTerm::constant(i32::MIN.into()).into(),
                ),
                true,
            );
            assert!(spell_signed_goal(&upper, &pairs).is_none());
            let domain = Proposition::And(Box::new(upper), Box::new(lower));
            let expected = ClickProposition::Defined {
                expression: if subtract {
                    ContractExpression::Subtract(Box::new(surface.clone()), Box::new(one.clone()))
                } else {
                    ContractExpression::Add(Box::new(surface.clone()), Box::new(one.clone()))
                },
            };
            assert_eq!(spell_signed_goal(&domain, &pairs), Some(expected));
            assert!(!machine.has_boxed_operand());
        }
    }
}
