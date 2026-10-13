use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

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

fn contract_expression_for_instantiation_value(
    value: &Bitvector32Term,
) -> Option<ContractExpression> {
    let Bitvector32Term::Constant(bits) = value else {
        return None;
    };
    Some(ContractExpression::CFragment(CExpression::Value(
        CValue::Int32(Bitvector32Term::Constant(*bits)),
    )))
}

/// Plans an explicit universal-instantiation certificate: one listed
/// universal premise, specialized at an explicit constant, proves the goal
/// after its guards discharge from the remaining listed premises. The named
/// `instantiate ... using` step adds the specialized fact and `assumption`
/// closes the exact goal, matching independent proof-step check.
pub(super) fn plan_explicit_forall_instantiation(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let Proposition::ForAll { var, sort, body } = kernel else {
            continue;
        };
        if *sort != Sort::CInt32 {
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
            // The closer is `assumption`, so the instantiated conclusion must
            // match the goal by exactly the equivalence assumption checks.
            if conclusion != *goal {
                continue;
            }
            let tactics = vec![
                ProofTactic::InstantiateUsing {
                    quantified: surface.clone(),
                    argument,
                    premises: Some(other_surfaces.clone()),
                },
                ProofTactic::Assumption,
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
    extra_arguments: &[(Bitvector32Term, ContractExpression)],
    conclusion_gate: &dyn Fn(&Proposition) -> bool,
) -> Option<Vec<ProofTactic>> {
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let Proposition::ForAll { sort, .. } = kernel else {
            continue;
        };
        if *sort != Sort::CInt32 {
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
/// optional transport adds its target, and `assumption` closes the exact goal.
/// The instantiated guards discharge from the introduced antecedent plus the
/// remaining listed premises.
#[allow(clippy::too_many_arguments)]
fn plan_explicit_universal_conclusion_discharge(
    premise_kernel: &Proposition,
    premise_surface: &ClickProposition,
    argument_term: Bitvector32Term,
    argument_expression: &ContractExpression,
    goal_conclusion: &Proposition,
    surface_goal_conclusion: &ClickProposition,
    discharge_kernels: &[Proposition],
    using_surfaces: &[ClickProposition],
    conclusion_gate: Option<&dyn Fn(&Proposition) -> bool>,
) -> Option<Vec<ProofTactic>> {
    let Proposition::ForAll {
        var: premise_var,
        sort: Sort::CInt32,
        body: premise_body,
    } = premise_kernel
    else {
        return None;
    };
    let instantiated =
        substitute_int32_variable_in_proposition(premise_body, *premise_var, argument_term);
    let (_, conclusion) = discharge_instantiated_guards(instantiated, discharge_kernels).ok()?;
    let closes_by_assumption =
        conclusion == *goal_conclusion || conclusion.clone() == goal_conclusion.clone();
    // Constant-argument instances offer several instantiation candidates, so
    // the caller may insist the instantiated conclusion provably reaches the
    // goal before accepting a transport that check would reject.
    if !closes_by_assumption
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
    let transport_closure = if closes_by_assumption {
        None
    } else {
        // A loop-exit universal invariant fact is written through an
        // `at(point, ...)` wrapper; peel it here and restore it on the
        // substituted transport source so the source lowers at the same
        // snapshot the premise denotes.
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
        if let Some((historical, current)) = comparison_snapshot_expression_pair(&source, &target) {
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
                proof: SourceProof::Script(vec![
                    ProofTactic::Rewrite(forward),
                    ProofTactic::Normalize,
                ]),
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
    tactics.push(ProofTactic::Assumption);
    Some(tactics)
}

/// Finds the comparison operand written as the same expression at a named
/// snapshot and at the current state. An equality bridge for that operand can
/// then carry the surrounding comparison by an ordinary checked rewrite.
fn comparison_snapshot_expression_pair(
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
        sort: Sort::CInt32,
        body: goal_body,
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
            Bitvector32Term::Variable(*goal_var),
            &ContractExpression::CFragment(CExpression::Variable(binder_name.clone())),
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
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
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
    crate::surface::checking::plan_signed_arithmetic_certificate(
        goal,
        &[forward.0.clone(), reverse.0.clone()],
    )?;
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
                    ConditionTerm::Bitvector32Equal(neq_left, neq_right),
                    false,
                ) => neq_left.as_ref() == left && neq_right.as_ref() == right,
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(neq_left, neq_right),
                        true,
                    ) if neq_left.as_ref() == left && neq_right.as_ref() == right
                ),
                _ => false,
            };
            if !matches_neq {
                continue;
            }
            let (surface_left, surface_right) = surface_nonstrict_parts(le_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_less_equal_and_not_equal_implies_less_than".to_string(),
                        arguments: vec![surface_left, surface_right],
                    },
                    premises: vec![le_surface.clone(), neq_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

pub(super) fn plan_explicit_loadability_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let goal_width;
    let goal_bytes = match goal {
        Proposition::CMemoryLoadable { bytes, .. } => bytes,
        Proposition::CMemoryReadDefined { value_type, .. } => {
            goal_width = Bitvector32Term::Constant(value_type.byte_width());
            &goal_width
        }
        _ => return None,
    };
    let mut sources = premise_pairs
        .iter()
        .filter(|(kernel, _)| {
            matches!(
                kernel,
                Proposition::CMemoryLoadable { .. } | Proposition::CMemoryReadDefined { .. }
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
        Proposition::CMemoryLoadable { bytes, .. } => (
            (!surface_is_range(surface)) as u8,
            (bytes == goal_bytes) as u8,
        ),
        Proposition::CMemoryReadDefined { .. } => (0, 0),
        _ => unreachable!(),
    });
    for (source, surface_source) in sources {
        let mut selected = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::CMemoryLoadable { .. }
                        | Proposition::CMemoryReadDefined { .. }
                        | Proposition::ConditionIs(_, _)
                )
            })
            .collect::<Vec<_>>();
        let proves_goal = |pairs: &[&(Proposition, ClickProposition)]| {
            let propositions = pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            assumptions_from_propositions(&propositions)
                .derive_simp_proposition(goal)
                .is_some()
        };
        if !proves_goal(&selected) {
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
        return Some(vec![
            ProofTactic::TransportUsing {
                source: surface_source.clone(),
                target: surface_goal.clone(),
                premises: selected
                    .into_iter()
                    .map(|(_, surface)| surface.clone())
                    .collect(),
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn signed_strict_parts(
    proposition: &Proposition,
) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left, right))
        }
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(left, right),
            true,
        ) => Some((right, left)),
        _ => None,
    }
}

pub(super) fn signed_nonstrict_parts(
    proposition: &Proposition,
) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left, right))
        }
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
            true,
        ) => Some((right, left)),
        _ => None,
    }
}

/// Transcribe one kernel-selected signed-order path. Each intermediate edge
/// is established with the matching named transitivity theorem and retained
/// as a nested `have`; the final two-edge suffix uses the ordinary exact
/// named-rule translator so the original goal orientation is preserved.
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

/// The kind (`true` for `uint64`) and the source premises of an atomic
/// 64-bit order decision's recorded chain, in chain order.
pub(super) fn recorded_wide_order_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<(bool, Vec<(Proposition, ClickProposition)>)> {
    let (unsigned, path) = derivation.wide_order_path()?;
    let pairs = path
        .iter()
        .map(|step| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == step.premise())
                .cloned()
        })
        .collect::<Option<Vec<_>>>()?;
    Some((unsigned, pairs))
}

/// A recorded 64-bit order chain written out as the standard library's
/// transitivity lemmas, `uint64_less_than_less_equal_transitive` and its siblings, each
/// link stated with `have` and the last closing the goal: the 64-bit
/// counterpart of [`plan_recorded_signed_order_path_for_context`]. A link
/// whose source premise is not written as `<`, `<=`, `>` or `>=` (a negated
/// order, say) has no lemma here, and the chain is left to other routes.
pub(super) fn plan_recorded_wide_order_path(
    unsigned: bool,
    path: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    if path.len() < 2 {
        return None;
    }
    let parts = |surface: &ClickProposition| {
        surface_strict_parts(surface)
            .map(|(lower, upper)| (lower, upper, true))
            .or_else(|| {
                surface_nonstrict_parts(surface).map(|(lower, upper)| (lower, upper, false))
            })
    };
    let carrier = if unsigned { "uint64" } else { "int64" };
    let (lower, mut middle, mut strict) = parts(&path[0].1)?;
    let mut current = path[0].1.clone();
    let mut tactics = Vec::new();
    for (position, next) in path.iter().enumerate().skip(1) {
        let (_, upper, next_strict) = parts(&next.1)?;
        let link = match (strict, next_strict) {
            (true, true) => "less_than_transitive",
            (true, false) => "less_than_less_equal_transitive",
            (false, true) => "less_equal_less_than_transitive",
            (false, false) => "less_equal_transitive",
        };
        let application = ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: format!("{carrier}_{link}"),
                arguments: vec![lower.clone(), middle.clone(), upper.clone()],
            },
            premises: vec![current.clone(), next.1.clone()],
        };
        strict |= next_strict;
        let target = ClickProposition::Comparison {
            left: lower.clone(),
            operator: if strict {
                ComparisonOperator::LessThan
            } else {
                ComparisonOperator::LessEqual
            },
            right: upper.clone(),
        };
        let mut proof = vec![application];
        if !fixed_state_application_closes_goal {
            proof.push(ProofTactic::Assumption);
        }
        if position + 1 == path.len() {
            tactics.extend(proof);
        } else {
            tactics.push(ProofTactic::Have(ProofHave {
                proposition: target.clone(),
                proof: SourceProof::Script(proof),
            }));
        }
        current = target;
        middle = upper;
    }
    Some(tactics)
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

/// A recorded rule's tactics, without the trailing theorem assumption when
/// the fixed-state application already closes the goal.
pub(super) fn for_context(
    tactics: Option<Vec<ProofTactic>>,
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = tactics?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
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

pub(super) fn plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_predecessor_upper_bound(goal, premise_pairs, false)?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_one_le_predecessor_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_one_le_predecessor(goal, premise_pairs)?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
        let ProofTactic::Have(have) = tactics.first_mut()? else {
            return None;
        };
        let SourceProof::Script(body) = &mut have.proof else {
            return None;
        };
        remove_trailing_theorem_assumption(body)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_equal_one_predecessor_for_context(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let path = derivation
        .int32_equal_one_predecessor_is_nonnegative_path()
        .or_else(|| derivation.int32_equal_one_predecessor_strictly_decreases_path())?;
    let value = one_le_predecessor_value(goal)?;
    let one_le_kernel = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(Bitvector32Term::Constant(1)),
            Box::new(value.clone()),
        ),
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
            ConditionTerm::Bitvector32Equal(
                Box::new(step.source().clone()),
                Box::new(step.target().clone()),
            ),
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        equality_tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    if !normalizes_context_free(&current) {
        return None;
    }
    equality_tactics.push(ProofTactic::Normalize);

    let mut predecessor_tactics =
        plan_explicit_one_le_predecessor(goal, &[(one_le_kernel, one_le_surface.clone())])?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut predecessor_tactics)?;
        let ProofTactic::Have(positive) = predecessor_tactics.first_mut()? else {
            return None;
        };
        let SourceProof::Script(body) = &mut positive.proof else {
            return None;
        };
        remove_trailing_theorem_assumption(body)?;
    }
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
            ConditionTerm::Bitvector32Equal(
                Box::new(step.source().clone()),
                Box::new(step.target().clone()),
            ),
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    if !normalizes_context_free(&current) {
        return None;
    }
    tactics.push(ProofTactic::Normalize);
    Some(tactics)
}

pub(super) fn plan_recorded_int32_successor_le_implies_lt_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_successor_le_implies_lt(goal, premise_pairs)?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    } else if matches!(
        goal,
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedGreaterThan(_, _), true)
    ) {
        let ProofTactic::ApplyTheoremUsing { application, .. } = tactics.first()? else {
            return None;
        };
        // Execution retains the theorem's `lower < value` conclusion.
        // Close the mirrored goal through checked condition normalization,
        // rather than claiming its different spelling is an exact premise.
        let mirror = ClickProposition::Comparison {
            left: application.arguments[0].clone(),
            operator: ComparisonOperator::LessThan,
            right: application.arguments[1].clone(),
        };
        *tactics.last_mut()? = ProofTactic::NormalizeUsing(vec![mirror]);
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_negated_strict_successor_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_negated_strict_successor_bound(goal, premise_pairs)?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
        let ProofTactic::Have(have) = tactics.first_mut()? else {
            return None;
        };
        let SourceProof::Script(body) = &mut have.proof else {
            return None;
        };
        remove_trailing_theorem_assumption(body)?;
    }
    Some(tactics)
}

/// A theorem application can complete an exact matching proposition goal.
/// Outcome check can instead add an equivalent snapshot fact, so callers
/// specify whether the checked application closes this particular goal.
pub(super) fn plan_recorded_signed_order_path_for_context(
    goal: &Proposition,
    path: &[(Proposition, ClickProposition)],
    fixed_state_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    if path.len() < 2 {
        let mut tactics = plan_explicit_named_signed_rule(goal, path)?;
        if fixed_state_application_closes_goal {
            remove_trailing_theorem_assumption(&mut tactics)?;
        }
        return Some(tactics);
    }
    let mut tactics = Vec::new();
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
        let (surface_lower, surface_middle) = if current_strict {
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
        let theorem = order_transitivity_theorem(
            current_strict,
            next_strict,
            unsigned_order_edge(&current.0),
        );
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
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(current_lower),
                    Box::new(next_upper),
                )
            } else {
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(current_lower),
                    Box::new(next_upper),
                )
            },
            true,
        );
        let mut proof = vec![ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: theorem.to_string(),
                arguments: vec![surface_lower, surface_middle, surface_upper],
            },
            premises: vec![current.1.clone(), next.1.clone()],
        }];
        if !fixed_state_application_closes_goal {
            proof.push(ProofTactic::Assumption);
        }
        tactics.push(ProofTactic::Have(ProofHave {
            proposition: surface_target.clone(),
            proof: SourceProof::Script(proof),
        }));
        current = (kernel_target, surface_target);
    }
    let final_edge = path.last()?.clone();
    if unsigned_order_edge(&current.0) {
        let mut suffix = plan_unsigned_order_suffix(goal, &current, &final_edge)?;
        if fixed_state_application_closes_goal {
            remove_trailing_theorem_assumption(&mut suffix)?;
        }
        tactics.extend(suffix);
        return Some(tactics);
    }
    let mut suffix = plan_explicit_named_signed_rule(goal, &[current, final_edge])?;
    if fixed_state_application_closes_goal {
        remove_trailing_theorem_assumption(&mut suffix)?;
    }
    tactics.extend(suffix);
    Some(tactics)
}

/// Whether an order fact is a 32-bit unsigned order: the signed order of
/// sign-flipped operands, a constant operand arriving already flipped.
fn unsigned_order_edge(proposition: &Proposition) -> bool {
    let flipped = |term: &Bitvector32Term| {
        matches!(term, Bitvector32Term::BitwiseXor(left, right)
            if left.as_const() == Some(0x8000_0000) || right.as_const() == Some(0x8000_0000))
    };
    signed_strict_parts(proposition)
        .or_else(|| signed_nonstrict_parts(proposition))
        .is_some_and(|(lower, upper)| flipped(lower) || flipped(upper))
}

/// The lemma composing two order facts, for the carrier the chain is over.
/// An unsigned chain's operands are `uint32` values, which the `int32`
/// lemmas do not accept.
fn order_transitivity_theorem(
    first_strict: bool,
    second_strict: bool,
    unsigned: bool,
) -> &'static str {
    match (unsigned, first_strict, second_strict) {
        (false, false, false) => "int32_less_equal_transitive",
        (false, false, true) => "int32_less_equal_less_than_transitive",
        (false, true, false) => "int32_less_than_less_equal_transitive",
        (false, true, true) => "int32_less_than_transitive",
        (true, false, false) => "uint32_less_equal_transitive",
        (true, false, true) => "uint32_less_equal_less_than_transitive",
        (true, true, false) => "uint32_less_than_less_equal_transitive",
        (true, true, true) => "uint32_less_than_transitive",
    }
}

/// The last two edges of an unsigned chain, composed by the matching
/// `uint32` transitivity lemma, whose conclusion is the chain's goal.
fn plan_unsigned_order_suffix(
    goal: &Proposition,
    current: &(Proposition, ClickProposition),
    last: &(Proposition, ClickProposition),
) -> Option<Vec<ProofTactic>> {
    let parts = |edge: &(Proposition, ClickProposition)| {
        if let Some((lower, upper)) = signed_strict_parts(&edge.0) {
            let (surface_lower, surface_upper) = surface_strict_parts(&edge.1)?;
            Some((
                lower.clone(),
                upper.clone(),
                true,
                surface_lower,
                surface_upper,
            ))
        } else {
            let (lower, upper) = signed_nonstrict_parts(&edge.0)?;
            let (surface_lower, surface_upper) = surface_nonstrict_parts(&edge.1)?;
            Some((
                lower.clone(),
                upper.clone(),
                false,
                surface_lower,
                surface_upper,
            ))
        }
    };
    let (lower, middle, first_strict, surface_lower, surface_middle) = parts(current)?;
    let (next_lower, upper, second_strict, _, surface_upper) = parts(last)?;
    if middle != next_lower {
        return None;
    }
    // The lemma concludes `lower < upper` or `lower <= upper`, written
    // that way round; a goal written the other way round is not this one.
    let concluded = if first_strict || second_strict {
        goal_exact_less_than_parts(goal)?
    } else {
        goal_exact_less_equal_parts(goal)?
    };
    if concluded != (&lower, &upper) {
        return None;
    }
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: order_transitivity_theorem(first_strict, second_strict, true).to_string(),
                arguments: vec![surface_lower, surface_middle, surface_upper],
            },
            premises: vec![current.1.clone(), last.1.clone()],
        },
        ProofTactic::Assumption,
    ])
}

pub(super) fn remove_trailing_theorem_assumption(tactics: &mut Vec<ProofTactic>) -> Option<()> {
    if !matches!(tactics.last(), Some(ProofTactic::Assumption))
        || !matches!(
            tactics.get(tactics.len().checked_sub(2)?),
            Some(ProofTactic::ApplyTheoremUsing { .. })
        )
    {
        return None;
    }
    tactics.pop();
    Some(())
}

fn orient_surface_bitvector_equality(
    step: &BitvectorEqualityDerivationStep,
    surface: &ClickProposition,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(premise_left, premise_right),
        true,
    ) = step.premise()
    else {
        return None;
    };
    let reverse = step.source() == premise_right.as_ref() && step.target() == premise_left.as_ref();
    if !(reverse
        || (step.source() == premise_left.as_ref() && step.target() == premise_right.as_ref()))
    {
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
            ConditionTerm::Bitvector32Equal(
                Box::new(step.source().clone()),
                Box::new(step.target().clone()),
            ),
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    if !normalizes_context_free(&current) {
        return None;
    }
    tactics.push(ProofTactic::Normalize);
    Some(tactics)
}

/// A pointer-word equality decision is certified by a checked special
/// certificate naming every retained fact, or by `normalize` when it used
/// none.
pub(super) fn plan_recorded_pointer_word(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
) -> Option<Vec<ProofTactic>> {
    let premises = derivation.pointer_word_premises()?;
    if premises.is_empty() {
        return normalizes_context_free(goal).then(|| vec![ProofTactic::Normalize]);
    }
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
    let plan = crate::surface::checking::plan_special_arithmetic_certificate(goal, &kernels)?;
    Some(vec![ProofTactic::ArithmeticCertificate(
        crate::surface::checking::special_plan_to_surface_certificate(
            &plan,
            &surfaces,
            surface_goal,
        ),
    )])
}

/// A pointer-alignment decision is certified by a checked special certificate
/// naming the retained base fact, or as `normalize` when the base is a heap
/// allocation and the alignment is intrinsic.
pub(super) fn plan_recorded_pointer_alignment(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
) -> Option<Vec<ProofTactic>> {
    match derivation.pointer_alignment_premise()? {
        None => normalizes_context_free(goal).then(|| vec![ProofTactic::Normalize]),
        Some(premise) => {
            let (_, surface) = premise_pairs.iter().find(|(kernel, _)| kernel == premise)?;
            let plan = crate::surface::checking::plan_special_arithmetic_certificate(
                goal,
                std::slice::from_ref(premise),
            )?;
            Some(vec![ProofTactic::ArithmeticCertificate(
                crate::surface::checking::special_plan_to_surface_certificate(
                    &plan,
                    std::slice::from_ref(surface),
                    surface_goal,
                ),
            )])
        }
    }
}

/// Expand registered-load address congruence into the ordinary exact
/// equality rewrites that establish it. `rewrite` descends through the
/// registered load origins, while `normalize` checks that the resulting
/// memory epoch and complete pointer are identical.
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
                ConditionTerm::Bitvector32Equal(
                    Box::new(step.source().clone()),
                    Box::new(step.target().clone()),
                ),
                true,
            );
            current = rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available)
                .ok()?;
            tactics.push(ProofTactic::Rewrite(oriented_surface));
        }
    }
    if !normalizes_context_free(&current) {
        return None;
    }
    tactics.push(ProofTactic::Normalize);
    Some(tactics)
}

/// The goal-side counterpart of [`signed_strict_parts`]. A named-rule
/// certificate closes with `assumption` against the applied theorem's exact
/// conclusion, so a rule whose theorem concludes `<` may only fire when the
/// goal is written `<`; a reversed (`>`) goal needs the reversed-form rule.
fn goal_exact_less_than_parts(goal: &Proposition) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match goal {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left, right))
        }
        _ => None,
    }
}

/// The goal-side counterpart of [`signed_nonstrict_parts`]; see
/// [`goal_exact_less_than_parts`].
fn goal_exact_less_equal_parts(goal: &Proposition) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match goal {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left, right))
        }
        _ => None,
    }
}

fn increment_base(term: &Bitvector32Term) -> Option<&Bitvector32Term> {
    let Bitvector32Term::Add(left, right) = term else {
        return None;
    };
    if right.as_ref() == &Bitvector32Term::Constant(1) {
        Some(left)
    } else if left.as_ref() == &Bitvector32Term::Constant(1) {
        Some(right)
    } else {
        None
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
    match operator {
        ComparisonOperator::LessThan => Some((left.clone(), right.clone())),
        ComparisonOperator::GreaterThan => Some((right.clone(), left.clone())),
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
    match operator {
        ComparisonOperator::LessEqual => Some((left.clone(), right.clone())),
        ComparisonOperator::GreaterEqual => Some((right.clone(), left.clone())),
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
        let (value, upper) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_upper_bound".to_string(),
                    arguments: vec![value, upper],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_positive_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // `0 <= value` and `value >= 0` are one order; the theorem's
    // `0 <= value` conclusion closes either spelling.
    let (goal_lower, goal_value) = signed_nonstrict_parts(goal)?;
    if goal_lower != &Bitvector32Term::Constant(0) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(0) || premise_value != goal_value {
            continue;
        }
        let (_, surface_value) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_positive_is_nonnegative".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_le_transitive_constant_lower(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(goal_lower, goal_value),
        true,
    ) = goal
    else {
        return None;
    };
    let Bitvector32Term::Constant(goal_lower_bits) = goal_lower.as_ref() else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        let Bitvector32Term::Constant(premise_lower_bits) = premise_lower else {
            continue;
        };
        if premise_value != goal_value.as_ref()
            || (*goal_lower_bits as i32) >= (*premise_lower_bits as i32)
        {
            continue;
        }
        let constant_leg = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(goal_lower.as_ref().clone()),
                Box::new(premise_lower.clone()),
            ),
            true,
        );
        if !normalizes_context_free(&constant_leg) {
            continue;
        }
        let (surface_middle, surface_value) = surface_nonstrict_parts(surface)?;
        let surface_lower =
            ContractExpression::CFragment(CExpression::Value(int32(*goal_lower_bits)));
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_less_equal_transitive".to_string(),
                    arguments: vec![surface_lower, surface_middle, surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_strict_implies_nonstrict(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let reversed = matches!(
        goal,
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedGreaterEqual(_, _), true,)
    );
    let (goal_left, goal_right) = signed_nonstrict_parts(goal)?;
    for (kernel, surface) in premise_pairs {
        let Some((premise_left, premise_right)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_left != goal_left || premise_right != goal_right {
            continue;
        }
        let (surface_left, surface_right) = surface_strict_parts(surface)?;
        let surface_nonstrict = ClickProposition::Comparison {
            left: surface_left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: surface_right.clone(),
        };
        let mut tactics = vec![ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_less_than_implies_less_equal".to_string(),
                arguments: vec![surface_left.clone(), surface_right.clone()],
            },
            premises: vec![surface.clone()],
        }];
        if reversed {
            tactics.push(ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_less_equal_implies_reversed_greater_equal".to_string(),
                    arguments: vec![surface_left, surface_right],
                },
                premises: vec![surface_nonstrict],
            });
        }
        tactics.push(ProofTactic::Assumption);
        return Some(tactics);
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
/// rule; `assumption` then closes the goal from the extracted fact.
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
                    ProofTactic::Assumption,
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
        ConditionTerm::Bitvector32SignedLessEqual(goal_lower, goal_greater),
        true,
    ) = goal
    else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(greater, lower),
            true,
        ) = kernel
        else {
            continue;
        };
        if greater != goal_greater || lower != goal_lower {
            continue;
        }
        let (surface_lower, surface_greater) = surface_nonstrict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_greater_equal_implies_reversed_less_equal".to_string(),
                    arguments: vec![surface_greater, surface_lower],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_not_strict_implies_greater_equal(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_left, goal_right, reversed_less_equal) = match goal {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
            true,
        ) => (left, right, false),
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(lower, greater),
            true,
        ) => (greater, lower, true),
        _ => return None,
    };
    for (kernel, surface) in premise_pairs {
        let matches = match kernel {
            Proposition::Not(body) => matches!(
                body.as_ref(),
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(left, right),
                    true,
                ) if left == goal_left && right == goal_right
            ),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(left, right),
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
        let (surface_left, surface_right) = surface_strict_parts(inner)?;
        let greater_equal = ClickProposition::Comparison {
            left: surface_left.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: surface_right.clone(),
        };
        let mut tactics = vec![ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_not_less_than_implies_greater_equal".to_string(),
                arguments: vec![surface_left.clone(), surface_right.clone()],
            },
            premises: vec![surface.clone()],
        }];
        if reversed_less_equal {
            tactics.push(ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_greater_equal_implies_reversed_less_equal".to_string(),
                    arguments: vec![surface_left, surface_right],
                },
                premises: vec![greater_equal],
            });
        } else {
            tactics.push(ProofTactic::Assumption);
        }
        return Some(tactics);
    }
    None
}

fn plan_explicit_greater_equal_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(goal_last, goal_first),
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
            let (surface_first, surface_middle) = surface_nonstrict_parts(first_surface)?;
            let (_, surface_last) = surface_nonstrict_parts(second_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_greater_equal_transitive".to_string(),
                        arguments: vec![surface_last, surface_middle, surface_first],
                    },
                    premises: vec![second_surface.clone(), first_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_negated_strict_successor_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(goal_value, goal_lower),
        true,
    ) = goal
    else {
        return None;
    };
    let Bitvector32Term::Constant(lower) = goal_lower.as_ref() else {
        return None;
    };
    let upper = (*lower as i32).checked_add(1)? as u32;
    for (kernel, surface) in premise_pairs {
        let (premise_value, premise_upper) = match kernel {
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(value, upper),
                    true,
                ) => (value.as_ref(), upper.as_ref()),
                _ => continue,
            },
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(value, upper),
                false,
            ) => (value.as_ref(), upper.as_ref()),
            _ => continue,
        };
        if premise_value != goal_value.as_ref()
            || premise_upper != &Bitvector32Term::Constant(upper)
        {
            continue;
        }
        let ClickProposition::Not(inner) = surface else {
            continue;
        };
        let (surface_value, surface_upper) = surface_strict_parts(inner)?;
        let surface_lower = ContractExpression::CFragment(CExpression::Value(int32(*lower)));
        let value_ge_upper = ClickProposition::Comparison {
            left: surface_value.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: surface_upper.clone(),
        };
        let upper_ge_lower = ClickProposition::Comparison {
            left: surface_upper.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: surface_lower.clone(),
        };
        return Some(vec![
            ProofTactic::Have(ProofHave {
                proposition: value_ge_upper.clone(),
                proof: SourceProof::Script(vec![
                    ProofTactic::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_not_less_than_implies_greater_equal".to_string(),
                            arguments: vec![surface_value.clone(), surface_upper.clone()],
                        },
                        premises: vec![surface.clone()],
                    },
                    ProofTactic::Assumption,
                ]),
            }),
            ProofTactic::Have(ProofHave {
                proposition: upper_ge_lower.clone(),
                proof: SourceProof::Script(vec![ProofTactic::Normalize]),
            }),
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_greater_equal_transitive".to_string(),
                    arguments: vec![surface_value, surface_upper, surface_lower],
                },
                premises: vec![value_ge_upper, upper_ge_lower],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_increment_greater_equal_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(incremented, goal_lower),
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
        let (surface_lower, surface_value) = surface_nonstrict_parts(lower_surface)?;
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let (_, surface_upper) = surface_strict_parts(upper_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_greater_equal_lower_bound".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![lower_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_strict_greater_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterThan(incremented, goal_lower),
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
        let (surface_lower, surface_value) = surface_nonstrict_parts(lower_surface)?;
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let (_, surface_upper) = surface_strict_parts(upper_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_greater_than_lower_bound".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![lower_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_strict_greater_from_strict_lower(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterThan(incremented, goal_lower),
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
    let (surface_lower, surface_value) = surface_strict_parts(lower_surface)?;
    let (surface_upper_base, surface_upper) = surface_strict_parts(upper_surface)?;
    if surface_upper_base != surface_value {
        return None;
    }
    let weakened_lower = ClickProposition::Comparison {
        left: surface_lower.clone(),
        operator: ComparisonOperator::LessEqual,
        right: surface_value.clone(),
    };
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_less_than_implies_less_equal".to_string(),
                arguments: vec![surface_lower.clone(), surface_value.clone()],
            },
            premises: vec![lower_surface.clone()],
        },
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_increment_greater_than_lower_bound".to_string(),
                arguments: vec![surface_value, surface_lower, surface_upper],
            },
            premises: vec![weakened_lower, upper_surface.clone()],
        },
        ProofTactic::Assumption,
    ])
}

/// The order of one leg of a signed transitive chain.
#[derive(Clone, Copy)]
enum SignedOrder {
    NonStrict,
    Strict,
}

impl SignedOrder {
    fn kernel_parts(
        self,
        proposition: &Proposition,
    ) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
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

/// The signed transitive chains the planner transcribes, tried in order:
/// the order of each leg and the theorem that composes them. A chain is
/// strict end to end when either leg is.
const SIGNED_TRANSITIVE_CHAINS: [(SignedOrder, SignedOrder, &str); 4] = [
    (
        SignedOrder::Strict,
        SignedOrder::Strict,
        "int32_less_than_transitive",
    ),
    (
        SignedOrder::NonStrict,
        SignedOrder::NonStrict,
        "int32_less_equal_transitive",
    ),
    (
        SignedOrder::NonStrict,
        SignedOrder::Strict,
        "int32_less_equal_less_than_transitive",
    ),
    (
        SignedOrder::Strict,
        SignedOrder::NonStrict,
        "int32_less_than_less_equal_transitive",
    ),
];

/// Listed `first ~ middle` and `middle ~ last` give the goal `first ~ last`
/// through the chain's named transitivity theorem.
fn plan_explicit_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    (first_order, second_order, theorem): (SignedOrder, SignedOrder, &str),
) -> Option<Vec<ProofTactic>> {
    let strict =
        matches!(first_order, SignedOrder::Strict) || matches!(second_order, SignedOrder::Strict);
    let (goal_first, goal_last) = match goal {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(goal_first, goal_last),
            true,
        ) if strict => (goal_first, goal_last),
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(goal_first, goal_last),
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
            let (surface_first, surface_middle) = first_order.surface_parts(first_surface)?;
            let (_, surface_last) = second_order.surface_parts(second_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: theorem.to_string(),
                        arguments: vec![surface_first, surface_middle, surface_last],
                    },
                    premises: vec![first_surface.clone(), second_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

/// A constant non-strict upper bound sharpens below any larger constant:
/// `x < c1` follows from a listed `x <= c2` when `c2 < c1`, through
/// `int32_less_equal_less_than_transitive` over the context-free constant order.
fn plan_explicit_constant_strict_upper_bound_weakening(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(goal_value, goal_upper),
        true,
    ) = goal
    else {
        return None;
    };
    let Bitvector32Term::Constant(goal_constant) = goal_upper.as_ref() else {
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
        let Bitvector32Term::Constant(premise_constant) = premise_upper else {
            continue;
        };
        if (*premise_constant as i32) >= (*goal_constant as i32) {
            continue;
        }
        let (surface_value, surface_premise_upper) = if strict {
            surface_strict_parts(premise_surface)?
        } else {
            surface_nonstrict_parts(premise_surface)?
        };
        let goal_upper_surface = ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(*goal_constant),
        )));
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: if strict {
                        "int32_less_than_transitive"
                    } else {
                        "int32_less_equal_less_than_transitive"
                    }
                    .to_string(),
                    arguments: vec![surface_value, surface_premise_upper, goal_upper_surface],
                },
                premises: vec![premise_surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

/// An increment stays under a constant bound that clears its base's constant
/// bound: `x + 1 <= c1` follows from a listed `x <= c2` when `c2 < c1`,
/// through the strict weakening and `int32_increment_upper_bound`.
pub(super) fn plan_explicit_increment_constant_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(incremented, goal_upper),
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    let Bitvector32Term::Constant(goal_constant) = goal_upper.as_ref() else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let Some((premise_value, premise_upper)) = signed_nonstrict_parts(premise_kernel) else {
            continue;
        };
        if premise_value != base {
            continue;
        }
        let Bitvector32Term::Constant(premise_constant) = premise_upper else {
            continue;
        };
        if (*premise_constant as i32) >= (*goal_constant as i32) {
            continue;
        }
        let (surface_value, surface_premise_upper) = surface_nonstrict_parts(premise_surface)?;
        let goal_upper_surface = ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(*goal_constant),
        )));
        let strict_surface = ClickProposition::Comparison {
            left: surface_value.clone(),
            operator: ComparisonOperator::LessThan,
            right: goal_upper_surface.clone(),
        };
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_less_equal_less_than_transitive".to_string(),
                    arguments: vec![
                        surface_value.clone(),
                        surface_premise_upper,
                        goal_upper_surface.clone(),
                    ],
                },
                premises: vec![premise_surface.clone()],
            },
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_upper_bound".to_string(),
                    arguments: vec![surface_value, goal_upper_surface],
                },
                premises: vec![strict_surface],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

/// A constant lower bound relaxes to any smaller constant: `c1 <= x` follows
/// from a listed `x >= c2` (in either form) when `c1 <= c2`, through
/// `int32_greater_equal_transitive` over the context-free constant order and the
/// reversed-form theorem.
fn plan_explicit_constant_lower_bound_weakening(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, goal_value) = signed_nonstrict_parts(goal)?;
    let Bitvector32Term::Constant(goal_constant) = goal_lower else {
        return None;
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(_, _), true) = goal
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
        let Bitvector32Term::Constant(premise_constant) = premise_lower else {
            continue;
        };
        if (*goal_constant as i32) > (*premise_constant as i32) || premise_constant == goal_constant
        {
            continue;
        }
        let (surface_premise_lower, surface_value) = surface_nonstrict_parts(premise_surface)?;
        let goal_lower_surface = ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(*goal_constant),
        )));
        let weakened_surface = ClickProposition::Comparison {
            left: surface_value.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: goal_lower_surface.clone(),
        };
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_greater_equal_transitive".to_string(),
                    arguments: vec![
                        surface_value.clone(),
                        surface_premise_lower,
                        goal_lower_surface.clone(),
                    ],
                },
                premises: vec![premise_surface.clone()],
            },
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_greater_equal_implies_reversed_less_equal".to_string(),
                    arguments: vec![surface_value, goal_lower_surface],
                },
                premises: vec![weakened_surface],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_increment_below_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(value, amount),
        false,
    ) = goal
    else {
        return None;
    };
    if amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &Bitvector32Term::Constant(i32::MAX as u32) {
            continue;
        }
        let (surface_value, _) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_below_max_is_defined".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_one_plus_below_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedAddOverflows(one, value), false) =
        goal
    else {
        return None;
    };
    if one.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &Bitvector32Term::Constant(i32::MAX as u32) {
            continue;
        }
        let (surface_value, _) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_left_below_max_is_defined".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_one_plus_strictly_increases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(value, sum), true) = goal
    else {
        return None;
    };
    let Bitvector32Term::Add(one, added_value) = sum.as_ref() else {
        return None;
    };
    if one.as_ref() != &Bitvector32Term::Constant(1) || added_value.as_ref() != value.as_ref() {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &Bitvector32Term::Constant(i32::MAX as u32) {
            continue;
        }
        let (surface_value, _) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_left_strictly_increases".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_nonnegative_add_within_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(value, amount),
        false,
    ) = goal
    else {
        return None;
    };
    let zero = Bitvector32Term::Constant(0);
    let headroom = Bitvector32Term::Subtract(
        Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
        Box::new(amount.as_ref().clone()),
    );
    let (nonnegative_kernel, nonnegative_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| signed_nonstrict_parts(kernel) == Some((&zero, amount.as_ref())))?;
    let (headroom_kernel, headroom_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| signed_nonstrict_parts(kernel) == Some((value.as_ref(), &headroom)))?;
    let (_, surface_amount) = surface_nonstrict_parts(nonnegative_surface)?;
    let (surface_value, _) = surface_nonstrict_parts(headroom_surface)?;
    debug_assert_eq!(
        signed_nonstrict_parts(nonnegative_kernel),
        Some((&zero, amount.as_ref()))
    );
    debug_assert_eq!(
        signed_nonstrict_parts(headroom_kernel),
        Some((value.as_ref(), &headroom))
    );
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_nonnegative_add_within_max_is_defined".to_string(),
                arguments: vec![surface_value, surface_amount],
            },
            premises: vec![nonnegative_surface.clone(), headroom_surface.clone()],
        },
        ProofTactic::Assumption,
    ])
}

pub(super) fn plan_explicit_nonnegative_subtract_within_value_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedSubtractOverflows(value, amount),
        false,
    ) = goal
    else {
        return None;
    };
    let zero = Bitvector32Term::Constant(0);
    let (_, nonnegative_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| signed_nonstrict_parts(kernel) == Some((&zero, amount.as_ref())))?;
    let (_, within_value_surface) = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel) == Some((amount.as_ref(), value.as_ref()))
    })?;
    let (_, surface_amount) = surface_nonstrict_parts(nonnegative_surface)?;
    let (_, surface_value) = surface_nonstrict_parts(within_value_surface)?;
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_nonnegative_subtract_within_value_is_defined".to_string(),
                arguments: vec![surface_value, surface_amount],
            },
            premises: vec![nonnegative_surface.clone(), within_value_surface.clone()],
        },
        ProofTactic::Assumption,
    ])
}

pub(super) fn plan_explicit_positive_predecessor_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, predecessor) = goal_exact_less_equal_parts(goal)?;
    if goal_lower != &Bitvector32Term::Constant(0) {
        return None;
    }
    let Bitvector32Term::Subtract(value, amount) = predecessor else {
        return None;
    };
    if amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(0) || premise_value != value.as_ref() {
            continue;
        }
        let (_, surface_value) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_positive_predecessor_is_nonnegative".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

/// From `0 <= value` and `value <= bound`, the predecessor keeps the bound:
/// `value - 1 <= bound` through `int32_nonnegative_predecessor_upper_bound`.
/// When the nonnegativity leg is not itself a selected premise and
/// `synthesize_missing_leg` is set, a nested `have` derives it from the same
/// premises with the explicit equality-rewrite search (closing by a listed
/// premise or context-free normalization), so the emitted certificate still
/// names every dependency. Only outcome contexts pass `synthesize_missing_leg`:
/// a pure theorem proof has no `have`, so its planner must not emit one.
fn plan_explicit_predecessor_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    synthesize_missing_leg: bool,
) -> Option<Vec<ProofTactic>> {
    let (predecessor, goal_upper) = goal_exact_less_equal_parts(goal)?;
    let Bitvector32Term::Subtract(value, amount) = predecessor else {
        return None;
    };
    if amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (bound_kernel, bound_surface) in premise_pairs {
        let Some((premise_value, premise_bound)) = signed_nonstrict_parts(bound_kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || premise_bound != goal_upper {
            continue;
        }
        let Some((surface_value, surface_bound)) = surface_nonstrict_parts(bound_surface) else {
            continue;
        };
        let nonnegative_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                value.clone(),
            ),
            true,
        );
        let mut tactics = Vec::new();
        let nonnegative_surface = if let Some((_, surface)) =
            premise_pairs.iter().find(|(kernel, _)| {
                signed_nonstrict_parts(kernel).is_some_and(|(lower, bounded)| {
                    lower == &Bitvector32Term::Constant(0) && bounded == value.as_ref()
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
            let surface_zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
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
        tactics.push(ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_nonnegative_predecessor_upper_bound".to_string(),
                arguments: vec![surface_value, surface_bound],
            },
            premises: vec![nonnegative_surface, bound_surface.clone()],
        });
        tactics.push(ProofTactic::Assumption);
        return Some(tactics);
    }
    None
}

fn plan_explicit_one_le_predecessor(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (value, final_theorem) = if let Some((goal_lower, predecessor)) =
        goal_exact_less_equal_parts(goal)
    {
        if goal_lower != &Bitvector32Term::Constant(0) {
            return None;
        }
        let Bitvector32Term::Subtract(value, amount) = predecessor else {
            return None;
        };
        if amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        (value.as_ref(), "int32_positive_predecessor_is_nonnegative")
    } else {
        let (predecessor, value) = goal_exact_less_than_parts(goal)?;
        let Bitvector32Term::Subtract(predecessor_value, amount) = predecessor else {
            return None;
        };
        if predecessor_value.as_ref() != value || amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        (value, "int32_positive_predecessor_strictly_decreases")
    };
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(1) || premise_value != value {
            continue;
        }
        let (_, surface_value) = surface_nonstrict_parts(surface)?;
        let surface_zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
        let positive = ClickProposition::Comparison {
            left: surface_zero.clone(),
            operator: ComparisonOperator::LessThan,
            right: surface_value.clone(),
        };
        return Some(vec![
            ProofTactic::Have(ProofHave {
                proposition: positive.clone(),
                proof: SourceProof::Script(vec![
                    ProofTactic::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_increment_less_equal_implies_less_than".to_string(),
                            arguments: vec![surface_zero, surface_value.clone()],
                        },
                        premises: vec![surface.clone()],
                    },
                    ProofTactic::Assumption,
                ]),
            }),
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: final_theorem.to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![positive],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn one_le_predecessor_value(goal: &Proposition) -> Option<Bitvector32Term> {
    if let Some((goal_lower, predecessor)) = goal_exact_less_equal_parts(goal) {
        if goal_lower != &Bitvector32Term::Constant(0) {
            return None;
        }
        let Bitvector32Term::Subtract(value, amount) = predecessor else {
            return None;
        };
        (amount.as_ref() == &Bitvector32Term::Constant(1)).then(|| value.as_ref().clone())
    } else {
        let (predecessor, value) = goal_exact_less_than_parts(goal)?;
        let Bitvector32Term::Subtract(predecessor_value, amount) = predecessor else {
            return None;
        };
        (predecessor_value.as_ref() == value && amount.as_ref() == &Bitvector32Term::Constant(1))
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
            left: ContractExpression::CFragment(CExpression::Value(int32(1))),
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
    let Bitvector32Term::Subtract(predecessor_value, amount) = predecessor else {
        return None;
    };
    if predecessor_value.as_ref() != value || amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(0) || premise_value != value {
            continue;
        }
        let (_, surface_value) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_positive_predecessor_strictly_decreases".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

pub(super) fn plan_explicit_le_and_not_lt_implies_eq(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
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
                    ConditionTerm::Bitvector32SignedLessThan(not_left, not_right),
                    false,
                ) => not_left.as_ref() == left.as_ref() && not_right.as_ref() == right.as_ref(),
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedLessThan(not_left, not_right),
                        true,
                    ) if not_left.as_ref() == left.as_ref()
                        && not_right.as_ref() == right.as_ref()
                ),
                _ => false,
            };
            if !matches_not_lt {
                continue;
            }
            let (surface_left, surface_right) = surface_nonstrict_parts(le_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_less_equal_and_not_less_than_implies_equal".to_string(),
                        arguments: vec![surface_left, surface_right],
                    },
                    premises: vec![le_surface.clone(), not_lt_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
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
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
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
            ConditionTerm::Bitvector32Equal(
                Box::new(source_index.clone()),
                Box::new(target_index.clone()),
            ),
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
            ProofTactic::Normalize,
        ]);
    }
    None
}

fn registered_load_pointer(term: &Bitvector32Term) -> Option<Pointer> {
    let Bitvector32Term::Variable(variable) = term else {
        return None;
    };
    crate::kernel::registered_load_origin_for_variable(variable).map(|(_, pointer)| pointer)
}

fn pointer_array_index_pair(
    source: &PointerOffsetTerm,
    target: &PointerOffsetTerm,
) -> Option<(Bitvector32Term, Bitvector32Term)> {
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

fn pointer_int32_scaled_value(offset: &PointerOffsetTerm) -> Option<Bitvector32Term> {
    let PointerOffsetTerm::Int32Scaled { value, byte_width } = offset else {
        return None;
    };
    (*byte_width == 4).then(|| value.as_ref().clone())
}

pub(super) fn plan_explicit_ge_and_not_gt_implies_eq(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
        return None;
    };
    for (ge_kernel, ge_surface) in premise_pairs {
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(ge_left, ge_right),
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
                    ConditionTerm::Bitvector32SignedGreaterThan(not_left, not_right),
                    false,
                ) => not_left == left && not_right == right,
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedGreaterThan(not_left, not_right),
                        true,
                    ) if not_left == left && not_right == right
                ),
                _ => false,
            };
            if !matches_not_gt {
                continue;
            }
            let (surface_right, surface_left) = surface_nonstrict_parts(ge_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_greater_equal_and_not_greater_than_implies_equal".to_string(),
                        arguments: vec![surface_left, surface_right],
                    },
                    premises: vec![ge_surface.clone(), not_gt_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
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
        let (value, upper) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_strictly_increases".to_string(),
                    arguments: vec![value, upper],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_successor_le_implies_lt(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (lower, value) = match goal {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(lower, value), true)
        | Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(value, lower),
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
                != &crate::kernel::canonical_term(&Bitvector32Term::add(
                    lower.clone(),
                    Bitvector32Term::Constant(1),
                ))
        {
            continue;
        }
        let no_overflow = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(lower.clone()),
                Box::new(successor.clone()),
            ),
            true,
        );
        if !normalizes_context_free(&no_overflow) {
            continue;
        }
        let Bitvector32Term::Constant(lower) = lower else {
            continue;
        };
        let surface_lower = ContractExpression::CFragment(CExpression::Value(int32(*lower)));
        let (_, surface_value) = surface_nonstrict_parts(bound_surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_less_equal_implies_less_than".to_string(),
                    arguments: vec![surface_lower, surface_value],
                },
                premises: vec![bound_surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
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
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::add(
                        lower.clone(),
                        Bitvector32Term::Constant(1),
                    )),
                    Box::new(Bitvector32Term::add(
                        value.clone(),
                        Bitvector32Term::Constant(1),
                    )),
                ),
                true,
            );
            if &expected != goal {
                continue;
            }
            let Some((surface_lower, _)) = surface_nonstrict_parts(order_surface) else {
                continue;
            };
            let Some((surface_value, surface_upper)) = surface_strict_parts(upper_surface) else {
                continue;
            };
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_preserves_order".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![order_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

pub(super) fn plan_explicit_increment_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // The theorem concludes in less-equal orientation; a greater-equal goal
    // form belongs to `int32_increment_greater_equal_lower_bound`, whose
    // conclusion the closing `assumption` can match exactly.
    let (goal_lower, incremented) = goal_exact_less_equal_parts(goal)?;
    let base = increment_base(incremented)?;

    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower || lower_base != base {
            continue;
        }
        let Some((surface_lower, _)) = surface_nonstrict_parts(lower_surface) else {
            continue;
        };
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let Some((surface_value, surface_upper)) = surface_strict_parts(upper_surface) else {
                continue;
            };
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_lower_bound".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![lower_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

pub(super) fn comparison_snapshot_variants(
    proposition: &ClickProposition,
    selectors: &[SnapshotSelector],
) -> Option<Vec<ClickProposition>> {
    if let ClickProposition::Not(body) = proposition {
        return Some(
            comparison_snapshot_variants(body, selectors)?
                .into_iter()
                .map(|variant| ClickProposition::Not(Box::new(variant)))
                .collect(),
        );
    }
    if let ClickProposition::ForAll {
        click_type: c_type,
        name,
        written_name,
        body,
    } = proposition
    {
        return Some(
            comparison_snapshot_variants(body, selectors)?
                .into_iter()
                .map(|body| ClickProposition::ForAll {
                    click_type: c_type.clone(),
                    name: name.clone(),
                    written_name: written_name.clone(),
                    body: Box::new(body),
                })
                .collect(),
        );
    }
    if let ClickProposition::Implies(left, right) = proposition {
        let mut variants = comparison_snapshot_variants(right, selectors)?
            .into_iter()
            .map(|right| ClickProposition::Implies(left.clone(), Box::new(right)))
            .collect::<Vec<_>>();
        if let Some(left_variants) = comparison_snapshot_variants(left, selectors) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::Implies(Box::new(left), right.clone())),
            );
        }
        return Some(variants);
    }
    if let ClickProposition::Or(left, right) = proposition {
        let left_variants = comparison_snapshot_variants(left, selectors)?;
        let right_variants = comparison_snapshot_variants(right, selectors)?;
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
        if let Some(right_variants) = comparison_snapshot_variants(right, selectors) {
            variants.extend(
                right_variants
                    .into_iter()
                    .map(|right| ClickProposition::And(left.clone(), Box::new(right))),
            );
        }
        if let Some(left_variants) = comparison_snapshot_variants(left, selectors) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::And(Box::new(left), right.clone())),
            );
        }
        return (!variants.is_empty()).then_some(variants);
    }
    // A predicate call names its memory snapshot only through its array-ref
    // arguments, so the snapshot is selected by wrapping the arguments —
    // uniformly, the way the recorded-form search in
    // `checked_surface_fact_in_state` already does. Wrapping a value argument
    // is harmless: it evaluates to the same value in every selected snapshot where it is
    // synthesizable at, and a wrapping that does not lower is discarded by the
    // caller's `check`.
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
    let at_snapshot =
        |expression: &ContractExpression, selector: &SnapshotSelector| ContractExpression::At {
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
    let snapshot_pairs = selectors
        .iter()
        .rev()
        .map(|selector| (at_snapshot(left, selector), at_snapshot(right, selector)))
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
    for (snapshot_left, snapshot_right) in &snapshot_pairs {
        push(snapshot_left.clone(), right.clone());
        push(left.clone(), snapshot_right.clone());
        push(snapshot_left.clone(), snapshot_right.clone());
    }

    let mut left_variants = vec![left.clone()];
    let mut right_variants = vec![right.clone()];
    if let Some(old_left) = old_left {
        left_variants.push(old_left);
    }
    if let Some(old_right) = old_right {
        right_variants.push(old_right);
    }
    for (snapshot_left, snapshot_right) in snapshot_pairs {
        left_variants.push(snapshot_left);
        right_variants.push(snapshot_right);
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
    state: &CState,
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
            view.recorded_snapshots,
        ),
        spec_definitions,
    )
    .map_err(ClickError::new)
}

fn c_expression_mentions_c_local(
    expression: &CExpression,
    parameter_names: &BTreeSet<&str>,
) -> bool {
    let mut names = BTreeSet::new();
    crate::surface::collect_c_expression_referenced_names(expression, &mut names);
    names
        .iter()
        .any(|name| !parameter_names.contains(name.as_str()))
}

pub(super) fn contract_expression_mentions_c_local(
    expression: &ContractExpression,
    parameter_names: &BTreeSet<&str>,
) -> bool {
    match expression {
        ContractExpression::IntegerLiteral(_) => false,
        ContractExpression::CUnary { operand: inner, .. } | ContractExpression::Negate(inner) => {
            contract_expression_mentions_c_local(inner, parameter_names)
        }
        ContractExpression::ResourceField(_) => false,
        ContractExpression::AlgebraicVariable { .. } => false,
        ContractExpression::Binding(name) => !parameter_names.contains(name.as_str()),
        ContractExpression::AlgebraicConstructor { arguments, .. } => arguments
            .iter()
            .any(|argument| contract_expression_mentions_c_local(argument, parameter_names)),
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            contract_expression_mentions_c_local(scrutinee, parameter_names)
                || arms.iter().any(|arm| {
                    let mut arm_names = parameter_names.clone();
                    arm_names.extend(arm.bindings.iter().map(String::as_str));
                    contract_expression_mentions_c_local(&arm.body, &arm_names)
                })
        }
        ContractExpression::SequenceLiteral(elements) => elements
            .iter()
            .any(|element| contract_expression_mentions_c_local(element, parameter_names)),
        ContractExpression::SequenceConcat(left, right) => {
            contract_expression_mentions_c_local(left, parameter_names)
                || contract_expression_mentions_c_local(right, parameter_names)
        }
        ContractExpression::CBinding(_) | ContractExpression::ResourceWildcard => false,
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => arguments
                .iter()
                .any(|argument| contract_expression_mentions_c_local(argument, parameter_names)),
            _ => false,
        },
        ContractExpression::CFragment(CExpression::Variable(name)) => {
            !parameter_names.contains(name.as_str())
        }
        ContractExpression::QualifiedC { .. } | ContractExpression::CFragment(_) => false,
        ContractExpression::ArrayIndex {
            base,
            indexes,
            lowered,
            ..
        } => {
            contract_expression_mentions_c_local(base, parameter_names)
                || indexes
                    .iter()
                    .any(|index| contract_expression_mentions_c_local(index, parameter_names))
                || (!matches!(base.as_ref(), ContractExpression::QualifiedC { .. })
                    && c_expression_mentions_c_local(lowered, parameter_names))
        }
        ContractExpression::Field { base, .. }
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::BitwiseNot(base) => {
            contract_expression_mentions_c_local(base, parameter_names)
        }
        crate::surface::binary_contract_expression!(left, right) => {
            contract_expression_mentions_c_local(left, parameter_names)
                || contract_expression_mentions_c_local(right, parameter_names)
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            contract_expression_mentions_c_local(then_branch, parameter_names)
                || contract_expression_mentions_c_local(else_branch, parameter_names)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contract_expression_mentions_c_local(start, parameter_names)
                || contract_expression_mentions_c_local(end, parameter_names)
                || contract_expression_mentions_c_local(initial, parameter_names)
                || contract_expression_mentions_c_local(body, parameter_names)
        }
        ContractExpression::Let { value, body, .. } => {
            contract_expression_mentions_c_local(value, parameter_names)
                || contract_expression_mentions_c_local(body, parameter_names)
        }
        ContractExpression::Call { arguments, .. } => arguments
            .iter()
            .any(|argument| contract_expression_mentions_c_local(argument, parameter_names)),
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

        let goal = Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        };
        let surface = ClickProposition::Loadable {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("p".into()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::CFragment(CExpression::Variable("p".into())),
                    start: ContractExpression::CFragment(CExpression::Value(int32(0))),
                    end: ContractExpression::CFragment(CExpression::Value(int32(1))),
                },
            },
        };
        // Give planning exactly the work needed to establish its candidate.
        // Repeating that query in a debug assertion then exhausts the budget.
        let (derivation, work) = measure_deterministic_work(|| {
            assumptions_from_propositions(std::slice::from_ref(&goal))
                .derive_simp_proposition(&goal)
        });
        assert!(derivation.is_some());
        assert!(work > 0);
        let tactic = TacticEvent {
            source_tactic_path: None,
            claim: "viewability".into(),
            tactic_index: 0,
            tactic_name: "simp".into(),
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
                ProofTactic::Assumption,
            ])
        );
    }
}
