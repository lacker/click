use super::*;

pub(in crate::lang::click) fn verify_theorem_definitions(
    theorem_definitions: &[TheoremDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = TheoremEnvironment::new(&[]);
    for theorem in theorem_definitions {
        let context =
            pure_theorem_context(theorem, predicate_environment, click_function_environment)?;
        for (ensure_index, ensure_clause) in theorem.ensures().iter().enumerate() {
            let claim_label = theorem_claim_label(theorem.name(), ensure_index, ensure_clause);
            let theorem = verify_theorem_ensure(
                theorem,
                ensure_index,
                ensure_clause,
                &claim_label,
                &context,
                predicate_environment,
                click_function_environment,
                &theorem_environment,
            )?;
            verified.push(theorem);
        }
        theorem_environment.insert(theorem.clone());
    }
    Ok(verified)
}

#[derive(Clone, Debug)]
pub(super) struct PureTheoremContext {
    pub(super) memory: CMemory,
    pub(super) values: BTreeMap<String, CValue>,
    pub(super) array_refs: ClickArrayRefs,
    pub(super) requires: Vec<Proposition>,
    pub(super) surface_requirements: SurfacePropositionMap,
}

#[derive(Clone, Debug)]
pub(super) struct PureInductionSetup {
    parameter: String,
    hypothesis: String,
    surface_requires: Vec<ClickProposition>,
    surface_goal: ClickProposition,
}

fn pure_induction_hypothesis(
    setup: &PureInductionSetup,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let Some(CValue::Int32(Bitvector32Term::Variable(current_variable))) =
        context.values.get(&setup.parameter)
    else {
        return Err(ClickError::new("invalid int32 induction parameter"));
    };
    let opaque_goal = lower_pure_theorem_proposition_opaque(
        &setup.hypothesis,
        &setup.surface_goal,
        &context.values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(ClickError::new)?;
    let opaque_requirements = setup
        .surface_requires
        .iter()
        .map(|requirement| {
            lower_pure_theorem_proposition_opaque(
                &setup.hypothesis,
                requirement,
                &context.values,
                &context.array_refs,
                &context.memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(ClickError::new)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut propositions = opaque_requirements.clone();
    propositions.push(opaque_goal.clone());
    let variable = fresh_int32_variable_for_propositions(&propositions);
    let value = Bitvector32Term::Variable(variable);
    let substitute = |proposition: &Proposition| {
        substitute_int32_variable_in_proposition(proposition, *current_variable, value.clone())
    };
    let mut body = substitute(&opaque_goal);
    for requirement in opaque_requirements.iter().rev() {
        let requirement = substitute(requirement);
        body = Proposition::Implies(Box::new(requirement), Box::new(body));
    }
    let smaller = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(value.clone()),
            Box::new(Bitvector32Term::Variable(*current_variable)),
        ),
        true,
    );
    body = Proposition::Implies(Box::new(smaller), Box::new(body));
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    body = Proposition::Implies(Box::new(nonnegative), Box::new(body));
    Ok(Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(body),
    })
}

fn prepare_pure_induction_tactics(
    theorem: &TheoremDefinition,
    goal: &ClickProposition,
    tactics: &[ProofTactic],
) -> Result<(Vec<ProofTactic>, Option<PureInductionSetup>), ClickError> {
    let Some(ProofTactic::Induct {
        parameter,
        hypothesis,
    }) = tactics.first()
    else {
        if tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Induct { .. }))
        {
            return Err(ClickError::new(
                "`induct` must be the first tactic in a pure theorem proof",
            ));
        }
        return Ok((tactics.to_vec(), None));
    };
    if !theorem
        .parameters()
        .iter()
        .any(|candidate| candidate.name() == parameter && candidate.c_type() == C0Type::Int32)
    {
        return Err(ClickError::new(format!(
            "`induct({parameter})` requires an int32 theorem parameter with that name"
        )));
    }
    let surface_requires = theorem
        .requires()
        .iter()
        .map(|requirement| {
            requirement.proposition().cloned().ok_or_else(|| {
                ClickError::new("pure induction supports proposition requirements only")
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    fn transform(
        tactics: &[ProofTactic],
        hypothesis: &str,
    ) -> Result<Vec<ProofTactic>, ClickError> {
        tactics
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::Induct { .. } => Err(ClickError::new(
                    "a pure theorem proof may contain only one top-level `induct` tactic",
                )),
                ProofTactic::ApplyTheorem(application) if application.name == hypothesis => {
                    let [argument] = application.arguments.as_slice() else {
                        return Err(ClickError::new(format!(
                            "induction hypothesis `{hypothesis}` expects one argument"
                        )));
                    };
                    Ok(ProofTactic::ApplyInduction {
                        hypothesis: hypothesis.to_string(),
                        argument: argument.clone(),
                    })
                }
                ProofTactic::If(proof_if) => Ok(ProofTactic::If(ProofIf {
                    condition: proof_if.condition.clone(),
                    then_tactics: transform(&proof_if.then_tactics, hypothesis)?,
                    else_tactics: transform(&proof_if.else_tactics, hypothesis)?,
                })),
                ProofTactic::Cases(proof_cases) => Ok(ProofTactic::Cases(ProofCases {
                    disjunction: proof_cases.disjunction.clone(),
                    left_tactics: transform(&proof_cases.left_tactics, hypothesis)?,
                    right_tactics: transform(&proof_cases.right_tactics, hypothesis)?,
                })),
                ProofTactic::ApplyInduction { .. } => Err(ClickError::new(
                    "internal induction-application syntax is not accepted directly",
                )),
                tactic => Ok(tactic.clone()),
            })
            .collect()
    }

    let mut prepared = vec![tactics[0].clone()];
    prepared.extend(transform(&tactics[1..], hypothesis)?);
    Ok((
        prepared,
        Some(PureInductionSetup {
            parameter: parameter.clone(),
            hypothesis: hypothesis.clone(),
            surface_requires,
            surface_goal: goal.clone(),
        }),
    ))
}

pub(super) fn pure_theorem_context(
    theorem: &TheoremDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<PureTheoremContext, ClickError> {
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(theorem.parameters());
    let array_refs = pure_theorem_array_refs(theorem.parameters(), &values, &memory);
    let requires = theorem
        .requires()
        .iter()
        .map(|requirement| {
            let Some(proposition) = requirement.proposition() else {
                return Err(ClickError::new(format!(
                    "pure theorem `{}` currently supports proposition `requires` clauses only",
                    theorem.name()
                )));
            };
            lower_pure_theorem_proposition(
                theorem.name(),
                proposition,
                &values,
                &array_refs,
                &memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "theorem `{}` setup failed: could not lower requirement: {message}",
                    theorem.name()
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut surface_requirements = SurfacePropositionMap::default();
    for (kernel, surface) in requires.iter().zip(
        theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition),
    ) {
        surface_requirements.record_lowering(surface, kernel)?;
    }
    Ok(PureTheoremContext {
        memory,
        values,
        array_refs,
        requires,
        surface_requirements,
    })
}

pub(in crate::lang::click) fn pure_theorem_parameter_values(
    parameters: &[FunctionParameter],
) -> BTreeMap<String, CValue> {
    parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let value = match parameter.c_type() {
                C0Type::Void => unreachable!("pure theorem parameters cannot be void"),
                C0Type::Int32 => CValue::Int32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt8 => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int32Pointer | C0Type::Int32Array(_) => CValue::Pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }),
                C0Type::UInt8Pointer | C0Type::UInt8Array(_) => CValue::Pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                }),
            };
            (parameter.name().to_string(), value)
        })
        .collect()
}

pub(in crate::lang::click) fn pure_theorem_array_refs(
    parameters: &[FunctionParameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.c_type())?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

fn theorem_claim_label(
    theorem_name: &str,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
) -> String {
    match ensure_clause.name() {
        Some(name) => format!("{theorem_name}.{name}"),
        None => format!("{theorem_name}.ensures_{ensure_index}"),
    }
}

fn lower_pure_simp_certificate(
    theorem: &TheoremDefinition,
    context: &PureTheoremContext,
    goal: &Proposition,
    certificate: &SimpEvidence,
) -> Option<Vec<ProofTactic>> {
    let tactic = match certificate {
        SimpEvidence::Assumption => ProofTactic::Assumption,
        SimpEvidence::Normalize => ProofTactic::Normalize,
        SimpEvidence::Derivation(derivation) => {
            let premise_pairs = derivation
                .context_premises()
                .iter()
                .map(|premise| {
                    context
                        .requires
                        .iter()
                        .position(|available| available == premise)
                        .and_then(|index| theorem.requires().get(index))
                        .and_then(Requirement::proposition)
                        .cloned()
                        .map(|surface| (premise.clone(), surface))
                })
                .collect::<Option<Vec<_>>>()?;
            if premise_pairs.is_empty() {
                ProofTactic::Normalize
            } else if let Some(ordered) = recorded_signed_order_pairs(derivation, &premise_pairs)
                && let Some(tactics) = plan_recorded_signed_order_path(goal, &ordered)
            {
                return Some(tactics);
            } else if let Ok(tactics) =
                lower_restricted_simp_plan(goal, None, certificate, &premise_pairs)
            {
                return Some(tactics);
            } else {
                return None;
            }
        }
    };
    ProofCertificate::from_proof_tactics(std::slice::from_ref(&tactic)).ok()?;
    Some(vec![tactic])
}

fn verify_theorem_ensure(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<VerifiedPureTheorem, ClickError> {
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(format!(
            "pure theorem `{}` currently supports proposition `ensures` clauses only",
            theorem.name()
        )));
    };
    let goal = lower_pure_theorem_proposition(
        theorem.name(),
        surface_goal,
        &context.values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` failed: could not lower conclusion: {message}"
        ))
    })?;

    if matches!(
        theorem.name(),
        "int32_increment_upper_bound"
            | "int32_increment_strictly_increases"
            | "int32_increment_lower_bound"
            | "int32_increment_greater_equal_lower_bound"
            | "int32_increment_strict_greater_lower_bound"
            | "int32_increment_preserves_order"
            | "int32_le_lt_transitive"
            | "int32_le_transitive"
            | "int32_lt_le_transitive"
            | "int32_lt_transitive"
            | "int32_ge_transitive"
            | "int32_ge_implies_reversed_le"
            | "int32_le_implies_reversed_ge"
            | "int32_le_and_not_lt_implies_eq"
            | "int32_le_and_neq_implies_lt"
            | "int32_ge_and_not_gt_implies_eq"
            | "int32_le_antisymmetric"
            | "int32_positive_is_nonnegative"
            | "int32_lt_implies_le"
            | "int32_not_lt_implies_ge"
            | "int32_strictly_positive_is_nonnegative"
            | "int32_increment_below_max_is_defined"
            | "int32_one_plus_below_max_is_defined"
            | "int32_one_plus_strictly_increases"
            | "int32_nonnegative_add_within_max_is_defined"
            | "int32_nonnegative_subtract_within_value_is_defined"
            | "int32_move_one_from_right_to_left_preserves_sum"
            | "int32_add_nonnegative_right_is_at_least_left"
            | "int32_add_nonnegative_left_is_at_least_right"
            | "int32_above_one_predecessor_is_at_least_one"
            | "int32_positive_predecessor_is_nonnegative"
            | "int32_positive_predecessor_strictly_decreases"
            | "int32_nonnegative_predecessor_upper_bound"
            | "int32_successor_le_implies_lt"
    ) {
        return verify_kernel_standard_theorem_axiom(
            theorem,
            ensure_index,
            ensure_clause,
            claim_label,
            context,
            goal,
        );
    }

    let checked_certificate;
    let (proof_kind, source_tactics, induction_setup) = match ensure_clause.proof() {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto) => {
            checked_certificate = check_direct_pure_goal_with_proof(
                claim_label,
                context,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            );
            if checked_certificate.is_none() {
                prove_pure_theorem_goal(
                    claim_label,
                    "auto",
                    &context.requires,
                    &goal,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    context,
                    &[],
                    &[],
                    true,
                )?;
            }
            (ProofKind::Pure, None, None)
        }
        SourceProof::Tactic(SmartTactic::Simp) => {
            checked_certificate = check_direct_pure_goal_with_proof(
                claim_label,
                context,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            );
            if checked_certificate.is_none() {
                prove_pure_theorem_goal(
                    claim_label,
                    "simp",
                    &context.requires,
                    &goal,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    context,
                    &[],
                    &[],
                    true,
                )?;
            }
            (ProofKind::Simp, None, None)
        }
        SourceProof::Tactic(SmartTactic::Frame) => {
            return Err(ClickError::new(format!(
                "`frame` is not available in the pure proof for theorem `{claim_label}`"
            )));
        }
        SourceProof::Script(tactics) => {
            if tactics.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` has an empty explicit proof script"
                )));
            }
            let (tactics, induction_setup) =
                prepare_pure_induction_tactics(theorem, surface_goal, tactics)?;
            checked_certificate = if induction_setup.is_none() {
                check_pure_script_with_proof(
                    claim_label,
                    context,
                    &goal,
                    &tactics,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                )?
            } else {
                None
            };
            if checked_certificate.is_some() {
                (ProofKind::TacticScript, None, induction_setup)
            } else {
                prove_pure_theorem_script(
                    claim_label,
                    &context.requires,
                    &goal,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    context,
                    &tactics,
                    induction_setup.as_ref(),
                )?;
                (ProofKind::TacticScript, Some(tactics), induction_setup)
            }
        }
    };

    let certificate = match checked_certificate {
        Some(certificate) => certificate,
        None => {
            let (certificate, ()) = pure_goal_proof_certificate_gateway(
                claim_label,
                || {
                    pure_theorem_surface_certificate(
                        theorem,
                        claim_label,
                        context,
                        &goal,
                        source_tactics.as_deref(),
                        predicate_environment,
                        click_function_environment,
                        induction_setup.as_ref(),
                    )
                },
                |certificate| {
                    replay_pure_theorem_certificate(
                        claim_label,
                        &context.requires,
                        &goal,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                        context,
                        certificate,
                        induction_setup.as_ref(),
                    )
                },
            )?;
            certificate
        }
    };
    let kernel_variables = theorem
        .parameters()
        .iter()
        .map(|parameter| match context.values.get(parameter.name()) {
            Some(CValue::Int32(Bitvector32Term::Variable(variable))) => Some(*variable),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    let kernel_authority = kernel_variables.and_then(|variables| {
        prove_universally_quantified_pure_implication(
            context.requires.clone(),
            goal.clone(),
            variables.clone(),
        )
        .or_else(|| {
            let steps = certificate.steps();
            let (rewrite_steps, closer) = steps.split_at(steps.len().saturating_sub(1));
            if !matches!(closer, [SimpleProofStep::Normalize]) {
                return None;
            }
            let rewrites = rewrite_steps
                .iter()
                .map(|step| match step {
                    SimpleProofStep::Rewrite(surface) => lower_pure_theorem_proposition(
                        claim_label,
                        surface,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .ok(),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            prove_universally_quantified_pure_implication_by_int32_rewrites(
                context.requires.clone(),
                goal.clone(),
                variables,
                rewrites,
            )
        })
    });
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind,
        proof: Some(certificate),
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority,
    })
}

/// Lets direct smart pure proofs search by applying checked simple steps.
///
/// Failed descendants are simply discarded. A successful descendant already
/// owns both the semantic successor and the exact simple certificate that
/// produced it, so ordinary operation does not reconstruct and replay that
/// certificate through the legacy gateway.
#[allow(clippy::too_many_arguments)]
fn check_direct_pure_goal_with_proof(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Option<ProofCertificate> {
    let root = Proof::for_pure_goal(
        claim_label,
        &context.requires,
        goal.clone(),
        context,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    );
    let proof = root.try_simp_closure()?;
    debug_assert!(proof.is_complete());
    Some(proof.certificate())
}

fn verify_kernel_standard_theorem_axiom(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: Proposition,
) -> Result<VerifiedPureTheorem, ClickError> {
    let (parameter_count, requirement_count) = match theorem.name() {
        "int32_increment_upper_bound" | "int32_increment_strictly_increases" => (2, 1),
        "int32_increment_lower_bound"
        | "int32_increment_greater_equal_lower_bound"
        | "int32_increment_strict_greater_lower_bound"
        | "int32_increment_preserves_order" => (3, 2),
        "int32_successor_le_implies_lt" => (2, 2),
        "int32_nonnegative_predecessor_upper_bound"
        | "int32_nonnegative_add_within_max_is_defined"
        | "int32_nonnegative_subtract_within_value_is_defined"
        | "int32_add_nonnegative_right_is_at_least_left"
        | "int32_add_nonnegative_left_is_at_least_right" => (2, 2),
        "int32_move_one_from_right_to_left_preserves_sum" => (3, 3),
        "int32_le_antisymmetric" => (2, 2),
        "int32_le_and_not_lt_implies_eq"
        | "int32_le_and_neq_implies_lt"
        | "int32_ge_and_not_gt_implies_eq" => (2, 2),
        "int32_ge_implies_reversed_le" => (2, 1),
        "int32_le_implies_reversed_ge" => (2, 1),
        "int32_lt_implies_le" | "int32_not_lt_implies_ge" => (2, 1),
        "int32_positive_is_nonnegative"
        | "int32_strictly_positive_is_nonnegative"
        | "int32_increment_below_max_is_defined"
        | "int32_one_plus_below_max_is_defined"
        | "int32_one_plus_strictly_increases"
        | "int32_above_one_predecessor_is_at_least_one"
        | "int32_positive_predecessor_is_nonnegative"
        | "int32_positive_predecessor_strictly_decreases" => (1, 1),
        "int32_le_lt_transitive"
        | "int32_le_transitive"
        | "int32_lt_le_transitive"
        | "int32_lt_transitive"
        | "int32_ge_transitive" => (3, 2),
        _ => unreachable!("only registered kernel standard theorems call this verifier"),
    };
    if ensure_index != 0
        || theorem.parameters().len() != parameter_count
        || theorem.requires().len() != requirement_count
        || theorem.ensures().len() != 1
        || !matches!(ensure_clause.proof(), SourceProof::Default)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` does not have the declaration shape required by its kernel axiom",
        )));
    }
    let int32_parameter = |index: usize| {
        let parameter = &theorem.parameters()[index];
        match context.values.get(parameter.name()) {
            Some(CValue::Int32(term)) => Ok(term.clone()),
            _ => Err(ClickError::new(format!(
                "`{claim_label}` kernel parameter `{}` must be int32",
                parameter.name()
            ))),
        }
    };
    let value = int32_parameter(0)?;
    let axiom = match theorem.name() {
        "int32_increment_upper_bound" => {
            prove_int32_increment_upper_bound(value, int32_parameter(1)?)
        }
        "int32_increment_strictly_increases" => {
            prove_int32_increment_strictly_increases(value, int32_parameter(1)?)
        }
        "int32_increment_lower_bound" => {
            prove_int32_increment_lower_bound(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_increment_greater_equal_lower_bound" => {
            prove_int32_increment_greater_equal_lower_bound(
                value,
                int32_parameter(1)?,
                int32_parameter(2)?,
            )
        }
        "int32_increment_strict_greater_lower_bound" => {
            prove_int32_increment_strict_greater_lower_bound(
                value,
                int32_parameter(1)?,
                int32_parameter(2)?,
            )
        }
        "int32_increment_preserves_order" => {
            prove_int32_increment_preserves_order(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_successor_le_implies_lt" => {
            prove_int32_successor_le_implies_lt(value, int32_parameter(1)?)
        }
        "int32_le_antisymmetric" => prove_int32_le_antisymmetric(value, int32_parameter(1)?),
        "int32_le_and_not_lt_implies_eq" => {
            prove_int32_le_and_not_lt_implies_eq(value, int32_parameter(1)?)
        }
        "int32_le_and_neq_implies_lt" => {
            prove_int32_le_and_neq_implies_lt(value, int32_parameter(1)?)
        }
        "int32_ge_and_not_gt_implies_eq" => {
            prove_int32_ge_and_not_gt_implies_eq(value, int32_parameter(1)?)
        }
        "int32_positive_is_nonnegative" => prove_int32_positive_is_nonnegative(value),
        "int32_lt_implies_le" => prove_int32_lt_implies_le(value, int32_parameter(1)?),
        "int32_not_lt_implies_ge" => prove_int32_not_lt_implies_ge(value, int32_parameter(1)?),
        "int32_strictly_positive_is_nonnegative" => {
            prove_int32_strictly_positive_is_nonnegative(value)
        }
        "int32_increment_below_max_is_defined" => prove_int32_increment_below_max_is_defined(value),
        "int32_one_plus_below_max_is_defined" => prove_int32_one_plus_below_max_is_defined(value),
        "int32_one_plus_strictly_increases" => prove_int32_one_plus_strictly_increases(value),
        "int32_nonnegative_add_within_max_is_defined" => {
            prove_int32_nonnegative_add_within_max_is_defined(value, int32_parameter(1)?)
        }
        "int32_nonnegative_subtract_within_value_is_defined" => {
            prove_int32_nonnegative_subtract_within_value_is_defined(value, int32_parameter(1)?)
        }
        "int32_move_one_from_right_to_left_preserves_sum" => {
            prove_int32_move_one_from_right_to_left_preserves_sum(
                value.clone(),
                int32_parameter(1)?,
                int32_parameter(2)?,
            )
        }
        "int32_add_nonnegative_right_is_at_least_left" => {
            prove_int32_add_nonnegative_right_is_at_least_left(value, int32_parameter(1)?)
        }
        "int32_add_nonnegative_left_is_at_least_right" => {
            prove_int32_add_nonnegative_left_is_at_least_right(value, int32_parameter(1)?)
        }
        "int32_above_one_predecessor_is_at_least_one" => {
            prove_int32_above_one_predecessor_is_at_least_one(value)
        }
        "int32_positive_predecessor_is_nonnegative" => {
            prove_int32_positive_predecessor_is_nonnegative(value)
        }
        "int32_positive_predecessor_strictly_decreases" => {
            prove_int32_positive_predecessor_strictly_decreases(value)
        }
        "int32_nonnegative_predecessor_upper_bound" => {
            prove_int32_nonnegative_predecessor_upper_bound(value, int32_parameter(1)?)
        }
        "int32_le_lt_transitive" => {
            prove_int32_le_lt_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_le_transitive" => {
            prove_int32_le_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_lt_le_transitive" => {
            prove_int32_lt_le_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_lt_transitive" => {
            prove_int32_lt_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_ge_transitive" => {
            prove_int32_ge_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
        }
        "int32_ge_implies_reversed_le" => {
            prove_int32_ge_implies_reversed_le(value, int32_parameter(1)?)
        }
        "int32_le_implies_reversed_ge" => {
            prove_int32_le_implies_reversed_ge(value, int32_parameter(1)?)
        }
        _ => unreachable!("checked above"),
    };
    let expected = context
        .requires
        .iter()
        .rev()
        .fold(goal.clone(), |body, requirement| {
            Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
        });
    if axiom.proposition() != &expected {
        return Err(ClickError::new(format!(
            "`{claim_label}` declaration does not match its kernel axiom",
        )));
    }
    let kernel_authority = match theorem.name() {
        "int32_above_one_predecessor_is_at_least_one" => {
            Some(certify_int32_above_one_predecessor_is_at_least_one())
        }
        "int32_move_one_from_right_to_left_preserves_sum" => {
            Some(certify_int32_move_one_from_right_to_left_preserves_sum())
        }
        _ => None,
    };
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind: ProofKind::Axiom,
        proof: None,
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority,
    })
}

/// Checks the pure-script subset already supported by the proof object.
///
/// Fully explicit proposition scripts advance directly through
/// `Proof::apply_step`. Linear scripts may interleave those checked steps with
/// bare theorem application and a final `simp`; both smart operations select
/// simple steps against the current `Proof`. Explicit `cases` certificates use
/// the audited branch/open/join operations recursively.
fn proof_supports_pure_certificate(certificate: &ProofCertificate) -> bool {
    certificate.steps().iter().all(|step| match step {
        SimpleProofStep::ApplyTheoremUsing { .. }
        | SimpleProofStep::UnfoldPredicate(_)
        | SimpleProofStep::Assumption
        | SimpleProofStep::Normalize
        | SimpleProofStep::Intro
        | SimpleProofStep::Split
        | SimpleProofStep::Left
        | SimpleProofStep::Right
        | SimpleProofStep::Enumerate
        | SimpleProofStep::Rewrite(_)
        | SimpleProofStep::Extract(_)
        | SimpleProofStep::Contradiction(_) => true,
        SimpleProofStep::Cases {
            left_proof,
            right_proof,
            ..
        } => {
            proof_supports_pure_certificate(left_proof)
                && proof_supports_pure_certificate(right_proof)
        }
        SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        } => {
            proof_supports_pure_certificate(then_proof)
                && proof_supports_pure_certificate(else_proof)
        }
        SimpleProofStep::Have { proof, .. } => proof_supports_pure_certificate(proof),
        _ => false,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_pure_script_with_proof(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    tactics: &[ProofTactic],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Option<ProofCertificate>, ClickError> {
    let root = Proof::for_pure_goal(
        claim_label,
        &context.requires,
        goal.clone(),
        context,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    );

    if let Some(proof) = root.try_linear_smart_script(tactics)? {
        return Ok(Some(proof.certificate()));
    }

    if let Ok(certificate) = ProofCertificate::from_proof_tactics(tactics)
        && proof_supports_pure_certificate(&certificate)
    {
        let Ok(proof) = root.check_certificate(&certificate) else {
            // Until every pure simple step uses `Proof`, retain the legacy
            // verifier's established failure diagnostics for rejected source
            // scripts. Successful migrated scripts still return directly.
            return Ok(None);
        };
        if !proof.is_complete() {
            return Ok(None);
        }
        return Ok(Some(proof.certificate()));
    }

    Ok(None)
}

fn pure_theorem_surface_certificate(
    theorem: &TheoremDefinition,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    source_tactics: Option<&[ProofTactic]>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<ProofCertificate, ClickError> {
    fn contains_restricted_simp(tactics: &[ProofTactic]) -> bool {
        tactics.iter().any(|tactic| match tactic {
            ProofTactic::SimpUsing(_) => true,
            ProofTactic::If(proof_if) => {
                contains_restricted_simp(&proof_if.then_tactics)
                    || contains_restricted_simp(&proof_if.else_tactics)
            }
            ProofTactic::Cases(proof_cases) => {
                contains_restricted_simp(&proof_cases.left_tactics)
                    || contains_restricted_simp(&proof_cases.right_tactics)
            }
            ProofTactic::Have(have) => match &have.proof {
                SourceProof::Script(tactics) => contains_restricted_simp(tactics),
                _ => false,
            },
            _ => false,
        })
    }

    if let (Some(tactics), Some(setup)) = (source_tactics, induction_setup) {
        let lowered = lower_pure_induction_tactics(&setup.surface_requires, tactics, setup)?;
        return ProofCertificate::from_proof_tactics(&lowered).map_err(|error| {
            ClickError::new(format!(
                "induction proof for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    if let Some(tactics) = source_tactics
        && let Ok(certificate) = ProofCertificate::from_proof_tactics(tactics)
    {
        return Ok(certificate);
    }

    if context.requires.contains(goal)
        || materialization_equivalent_available_fact(goal, &context.requires).is_some()
        || quantified_replay_equivalent_available_fact(goal, &context.requires).is_some()
    {
        return ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption]).map_err(
            |error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid assumption certificate: {error:?}"
                ))
            },
        );
    }
    if matches!(normalize_proposition(goal), SimpProposition::True) {
        return ProofCertificate::from_proof_tactics(&[ProofTactic::Normalize]).map_err(
            |error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid normalization certificate: {error:?}"
                ))
            },
        );
    }
    let restricted_simp = source_tactics.and_then(|tactics| {
        let (last, prefix) = tactics.split_last()?;
        let ProofTactic::SimpUsing(simp) = last else {
            return None;
        };
        let unfolded_predicates = prefix
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some((unfolded_predicates, simp))
    });
    if let Some((unfolded_predicates, simp)) = restricted_simp {
        let available = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            &context.requires,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let explicit_goal = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            goal,
            &assumptions_from_propositions(&available),
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let premise_entries = simp
            .premises
            .iter()
            .map(|surface| {
                let kernel = lower_pure_theorem_proposition(
                    claim_label,
                    surface,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "smart `simp() using` for `{claim_label}` could not lower listed premise `{}`: {message}",
                        describe_click_proposition(surface)
                    ))
                })?;
                if available.iter().any(|fact| {
                    fact == &kernel || condition_polarity_equivalent(fact, &kernel)
                }) {
                    return Ok((kernel, surface.clone(), false));
                }
                if exact_fact_is_available(&kernel, &available) {
                    return Ok((kernel, surface.clone(), true));
                }
                Err(ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` lost exact listed premise `{}` during certificate generation",
                    describe_click_proposition(surface)
                )))
            })
            .collect::<Result<Vec<_>, ClickError>>()?;
        let premise_pairs = premise_entries
            .iter()
            .map(|(kernel, surface, _)| (kernel.clone(), surface.clone()))
            .collect::<Vec<_>>();
        let explicit =
            plan_restricted_simp_expansion(&explicit_goal, None, &premise_pairs).map_err(
                |error| {
                ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` has no explicit simple certificate: {}",
                    error.message()
                ))
            })?;
        let mut tactics = unfolded_predicates
            .into_iter()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(
            premise_entries
                .into_iter()
                .filter_map(|(_, surface, extract)| {
                    extract.then_some(ProofTactic::Extract(surface))
                }),
        );
        tactics.extend(explicit);
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart `simp() using` for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    let assumptions = assumptions_from_propositions(&context.requires);
    if let Some(plan) = plan_simp_certificate(goal, &assumptions)
        && let Some(tactics) = lower_pure_simp_certificate(theorem, context, goal, &plan)
    {
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    // Some bounded arithmetic facts are certified by a named kernel theorem
    // even when the general proposition-derivation API does not retain a
    // derivation tree. The simple surface certificate can still be selected
    // directly from the theorem's exact requirements.
    let premise_pairs = context
        .requires
        .iter()
        .enumerate()
        .filter_map(|(index, kernel)| {
            theorem
                .requires()
                .get(index)
                .and_then(Requirement::proposition)
                .cloned()
                .map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    if premise_pairs.len() == context.requires.len()
        && let Some(tactics) = plan_explicit_named_signed_rule(goal, &premise_pairs)
    {
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid named-rule certificate: {error:?}"
            ))
        });
    }

    if let Some(tactics) = source_tactics
        && tactics.iter().any(|tactic| {
            matches!(
                tactic,
                ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. }
            )
        })
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        })
    {
        // An applied theorem's conclusion is an available fact, so a
        // trailing smart `simp` lowers to the deterministic `assumption`,
        // and a bare `apply` lowers to `apply using` with the proved
        // theorem's own requires as the explicit premise pool.
        let requirement_premises = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .cloned()
            .collect::<Vec<_>>();
        let tactics = tactics
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::Simp => ProofTactic::Assumption,
                ProofTactic::ApplyTheorem(application) => ProofTactic::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: requirement_premises.clone(),
                },
                other => other.clone(),
            })
            .collect::<Vec<_>>();
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid application certificate: {error:?}"
            ))
        });
    }

    if let Some(tactics) = source_tactics
        && tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Rewrite(_)))
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_)) || matches!(tactic, ProofTactic::Simp)
        })
    {
        let tactics = tactics
            .iter()
            .map(|tactic| {
                if matches!(tactic, ProofTactic::Simp) {
                    ProofTactic::Normalize
                } else {
                    tactic.clone()
                }
            })
            .collect::<Vec<_>>();
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid rewrite certificate: {error:?}"
            ))
        });
    }

    if source_tactics.is_some_and(contains_restricted_simp) {
        return Err(ClickError::new(format!(
            "smart `simp() using` for `{claim_label}` is not yet lowerable with the surrounding proof structure; keep it as a standalone proof until Click has an explicit simple certificate for that structure"
        )));
    }

    let unfolded_predicates = source_tactics
        .unwrap_or_default()
        .iter()
        .filter_map(|tactic| match tactic {
            ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !unfolded_predicates.is_empty() {
        fn flatten_surface_conjunction(
            proposition: ClickProposition,
            flattened: &mut Vec<ClickProposition>,
        ) {
            match proposition {
                ClickProposition::And(left, right) => {
                    flatten_surface_conjunction(*left, flattened);
                    flatten_surface_conjunction(*right, flattened);
                }
                proposition => flattened.push(proposition),
            }
        }

        let unfolded = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .map(|premise| {
                unfold_structural_invariant_proposition(
                    predicate_environment,
                    premise,
                    &unfolded_predicates,
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let mut premises = Vec::new();
        for proposition in unfolded {
            flatten_surface_conjunction(proposition, &mut premises);
        }
        let premise_pairs = premises
            .into_iter()
            .map(|surface| {
                let kernel = lower_pure_theorem_proposition(
                    claim_label,
                    &surface,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
                Ok((kernel, surface))
            })
            .collect::<Result<Vec<_>, ClickError>>()?;
        let available = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_goal = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            goal,
            &assumptions_from_propositions(&available),
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let plan =
            plan_simp_certificate(&explicit_goal, &assumptions_from_propositions(&available))
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "smart proof for `{claim_label}` has no explicit proof after unfolding"
                    ))
                })?;
        let mut tactics = unfolded_predicates
            .into_iter()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(
            lower_restricted_simp_plan(&explicit_goal, None, &plan, &premise_pairs).map_err(
                |error| {
                    ClickError::new(format!(
                        "smart proof for `{claim_label}` has no explicit unfolded certificate: {}",
                        error.message()
                    ))
                },
            )?,
        );
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid unfolded certificate: {error:?}"
            ))
        });
    }

    if let Some(tactics) = source_tactics
        && tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::If(_)))
    {
        let premise_pool = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .cloned()
            .collect::<Vec<_>>();
        if let Some(tactics) = lower_pure_branching_tactics(
            claim_label,
            context,
            goal,
            predicate_environment,
            click_function_environment,
            &premise_pool,
            tactics,
        ) {
            return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid branching certificate: {error:?}"
                ))
            });
        }
    }

    Err(ClickError::new(format!(
        "smart proof for `{claim_label}` succeeded but did not produce a pure surface certificate"
    )))
}

/// Lowers a branching pure proof script to deterministic tactics: each `if`
/// keeps its shape while contributing its (negated) condition to the branch's
/// premise pool, and each closing `simp` becomes an explicit proof of the goal
/// from exactly that pool.
fn lower_pure_branching_tactics(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
    tactics: &[ProofTactic],
) -> Option<Vec<ProofTactic>> {
    let mut lowered = Vec::new();
    for tactic in tactics {
        match tactic {
            ProofTactic::If(proof_if) => {
                let mut then_pool = premise_pool.to_vec();
                then_pool.push(proof_if.condition.clone());
                let mut else_pool = premise_pool.to_vec();
                else_pool.push(ClickProposition::Not(Box::new(proof_if.condition.clone())));
                lowered.push(ProofTactic::If(ProofIf {
                    condition: proof_if.condition.clone(),
                    then_tactics: lower_pure_branching_tactics(
                        claim_label,
                        context,
                        goal,
                        predicate_environment,
                        click_function_environment,
                        &then_pool,
                        &proof_if.then_tactics,
                    )?,
                    else_tactics: lower_pure_branching_tactics(
                        claim_label,
                        context,
                        goal,
                        predicate_environment,
                        click_function_environment,
                        &else_pool,
                        &proof_if.else_tactics,
                    )?,
                }));
            }
            ProofTactic::Simp => {
                let premise_pairs = premise_pool
                    .iter()
                    .map(|surface| {
                        let kernel = lower_pure_theorem_proposition(
                            claim_label,
                            surface,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                        .ok()?;
                        Some((kernel, surface.clone()))
                    })
                    .collect::<Option<Vec<_>>>()?;
                let available = premise_pairs
                    .iter()
                    .map(|(kernel, _)| kernel.clone())
                    .collect::<Vec<_>>();
                let certificate =
                    plan_simp_certificate(goal, &assumptions_from_propositions(&available))?;
                lowered.extend(
                    lower_restricted_simp_plan(goal, None, &certificate, &premise_pairs).ok()?,
                );
            }
            tactic if matches!(tactic.class(), TacticClass::Simple(_)) => {
                lowered.push(tactic.clone());
            }
            _ => return None,
        }
    }
    Some(lowered)
}

fn lower_pure_induction_tactics(
    premise_pool: &[ClickProposition],
    tactics: &[ProofTactic],
    setup: &PureInductionSetup,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut lowered = Vec::new();
    let mut current_pool = premise_pool.to_vec();
    for tactic in tactics {
        match tactic {
            ProofTactic::If(proof_if) => {
                let mut then_pool = current_pool.clone();
                then_pool.push(proof_if.condition.clone());
                let mut else_pool = current_pool.clone();
                else_pool.push(ClickProposition::Not(Box::new(proof_if.condition.clone())));
                lowered.push(ProofTactic::If(ProofIf {
                    condition: proof_if.condition.clone(),
                    then_tactics: lower_pure_induction_tactics(
                        &then_pool,
                        &proof_if.then_tactics,
                        setup,
                    )?,
                    else_tactics: lower_pure_induction_tactics(
                        &else_pool,
                        &proof_if.else_tactics,
                        setup,
                    )?,
                }));
            }
            ProofTactic::ApplyInduction {
                hypothesis,
                argument,
            } => {
                let substituted = substitute_click_proposition(
                    &setup.surface_goal,
                    &BTreeMap::from([(setup.parameter.clone(), argument.clone())]),
                )
                .map_err(ClickError::new)?;
                lowered.push(ProofTactic::ApplyInduction {
                    hypothesis: hypothesis.clone(),
                    argument: argument.clone(),
                });
                if !current_pool.contains(&substituted) {
                    current_pool.push(substituted);
                }
            }
            ProofTactic::Simp => lowered.push(ProofTactic::CloseInduction),
            tactic if matches!(tactic.class(), TacticClass::Simple(_)) => {
                lowered.push(tactic.clone());
            }
            _ => {
                return Err(ClickError::new(format!(
                    "pure induction currently cannot lower smart tactic `{}`; keep the step proof explicit",
                    tactic_name(tactic)
                )));
            }
        }
    }
    Ok(lowered)
}

/// Replay a validated certificate through the ordinary pure-tactic executor.
#[allow(clippy::too_many_arguments)]
pub(super) fn replay_pure_theorem_certificate(
    claim_label: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    certificate: &ProofCertificate,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<(), ClickError> {
    if induction_setup.is_none() && proof_supports_pure_certificate(certificate) {
        let root = Proof::for_pure_goal(
            claim_label,
            requires,
            goal.clone(),
            context,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        );
        let proof = root.check_certificate(certificate)?;
        if !proof.is_complete() {
            return Err(ClickError::new(format!(
                "pure goal `{claim_label}` certificate ended before closing its goal"
            )));
        }
        return Ok(());
    }
    prove_pure_theorem_script(
        claim_label,
        requires,
        goal,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        context,
        &certificate.to_proof_tactics(),
        induction_setup,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_theorem_script(
    claim_label: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    tactics: &[ProofTactic],
    induction_setup: Option<&PureInductionSetup>,
) -> Result<(), ClickError> {
    for proof_case in expand_proof_if_cases(tactics)? {
        prove_pure_theorem_tactics(
            claim_label,
            requires,
            goal,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            context,
            &proof_case,
            induction_setup,
        )?;
    }
    Ok(())
}

pub(super) fn lower_pure_theorem_proposition(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let mut lowerer = KernelPropositionLowerer::new(
        values.clone(),
        array_refs.clone(),
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    lowerer
        .lower_requirement_proposition(proposition)
        .map_err(|error| {
            error
                .message()
                .replace("`requires`", &format!("pure theorem `{theorem_name}`"))
        })
}

fn lower_pure_theorem_proposition_opaque(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let active = click_function_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let mut lowerer = KernelPropositionLowerer::new(
        values.clone(),
        array_refs.clone(),
        memory.clone(),
        predicate_environment,
        click_function_environment,
    )
    .with_active_functions(active);
    lowerer
        .lower_requirement_proposition(proposition)
        .map_err(|error| {
            error
                .message()
                .replace("`requires`", &format!("pure theorem `{theorem_name}`"))
        })
}

#[allow(clippy::too_many_arguments)]
fn apply_pure_induction_hypothesis(
    setup: &PureInductionSetup,
    hypothesis: &str,
    argument: &ContractExpression,
    claim_label: &str,
    tactic_index: usize,
    available: &mut Vec<Proposition>,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    if hypothesis != setup.hypothesis {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown induction hypothesis `{hypothesis}`"
        )));
    }
    let state = CState::new().with_memory(context.memory.clone());
    let assumptions = assumptions_from_propositions(available);
    let mut active_functions = BTreeSet::new();
    let value = evaluate_contract_expression_with_environment(
        &context.values,
        &context.array_refs,
        &state,
        &state,
        None,
        &assumptions,
        argument,
        predicate_environment,
        click_function_environment,
        &ProgramPointStates::new(),
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not evaluate induction argument: {message}"
        ))
    })?;
    let CValue::Int32(argument_term) = value else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction argument must have type int32"
        )));
    };
    let Some(CValue::Int32(current_term)) = context.values.get(&setup.parameter) else {
        return Err(ClickError::new("invalid induction parameter binding"));
    };
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(argument_term.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let smaller = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(argument_term.clone()),
            Box::new(current_term.clone()),
        ),
        true,
    );
    let proves = |fact: &Proposition| {
        available.contains(fact)
            || assumptions.derive_proposition(fact).is_some()
            || matches!(
                fact,
                Proposition::ConditionIs(condition, value)
                    if assumptions.decide(condition) == Some(*value)
            )
            || matches!(simp_proposition(fact, &assumptions), SimpProposition::True)
    };
    fn positive_subtraction_step(term: &Bitvector32Term, current: &Bitvector32Term) -> Option<u32> {
        let Bitvector32Term::Subtract(left, right) = term else {
            return None;
        };
        let step = right.as_const()?;
        if step == 0 {
            return None;
        }
        let prior = if left.as_ref() == current {
            0
        } else {
            positive_subtraction_step(left, current)?
        };
        prior
            .checked_add(step)
            .filter(|total| *total <= i32::MAX as u32)
    }
    let positive_subtraction = match positive_subtraction_step(&argument_term, current_term) {
        Some(step) => {
            let enough = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(current_term.clone()),
                    Box::new(Bitvector32Term::Constant(step)),
                ),
                true,
            );
            proves(&nonnegative)
                || proves(&enough)
                || assumptions.decide(&ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(current_term.clone()),
                    Box::new(Bitvector32Term::Constant(step - 1)),
                )) == Some(false)
        }
        None => false,
    };
    if !proves(&smaller) && !positive_subtraction {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction hypothesis argument is not proved smaller than `{}`",
            setup.parameter
        )));
    }
    if !proves(&nonnegative) && !positive_subtraction {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction hypothesis argument is not proved nonnegative: {nonnegative:?}\n  available: {available:#?}"
        )));
    }
    if !available.contains(&nonnegative) {
        available.push(nonnegative.clone());
    }
    if !available.contains(&smaller) {
        available.push(smaller.clone());
    }
    let assumptions = assumptions_from_propositions(available);
    let proves = |fact: &Proposition| {
        available.contains(fact)
            || assumptions.derive_proposition(fact).is_some()
            || matches!(
                fact,
                Proposition::ConditionIs(condition, value)
                    if assumptions.decide(condition) == Some(*value)
            )
            || matches!(simp_proposition(fact, &assumptions), SimpProposition::True)
    };
    let mut values = context.values.clone();
    values.insert(
        setup.parameter.clone(),
        CValue::Int32(argument_term.clone()),
    );
    let mut application_premises = vec![nonnegative.clone(), smaller.clone()];
    for requirement in &setup.surface_requires {
        let requirement = lower_pure_theorem_proposition_opaque(
            claim_label,
            requirement,
            &values,
            &context.array_refs,
            &context.memory,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        if requirement != nonnegative && !proves(&requirement) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: induction hypothesis requirement is unavailable: {requirement:?}"
            )));
        }
        application_premises.push(requirement);
    }
    let conclusion = lower_pure_theorem_proposition_opaque(
        claim_label,
        &setup.surface_goal,
        &values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    let quantified = pure_induction_hypothesis(
        setup,
        context,
        predicate_environment,
        click_function_environment,
    )?;
    if !available.contains(&quantified) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction hypothesis is not active"
        )));
    }
    let theorem = prove_forall_int32_application(
        &quantified,
        argument_term,
        &application_premises,
    )
    .ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: kernel rejected induction hypothesis instantiation"
        ))
    })?;
    let Proposition::Implies(theorem_quantified, mut theorem_body) = theorem.proposition().clone()
    else {
        return Err(ClickError::new("invalid induction application theorem"));
    };
    if theorem_quantified.as_ref() != &quantified {
        return Err(ClickError::new(
            "induction theorem changed its quantified premise",
        ));
    }
    for premise in &application_premises {
        let Proposition::Implies(theorem_premise, body) = theorem_body.as_ref() else {
            return Err(ClickError::new(
                "induction theorem omitted an application premise",
            ));
        };
        if theorem_premise.as_ref() != premise {
            return Err(ClickError::new(
                "induction theorem changed an application premise",
            ));
        }
        theorem_body = body.clone();
    }
    if theorem_body.as_ref() != &conclusion {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: kernel induction conclusion does not match `{hypothesis}`"
        )));
    }
    if !available.contains(&conclusion) {
        available.push(conclusion);
    }
    Ok(())
}

fn prove_pure_theorem_goal(
    claim_label: &str,
    proof_name: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    theorem_applications: &[(usize, TheoremApplication)],
    unfolded_predicates: &[String],
    use_simp: bool,
) -> Result<(), ClickError> {
    let mut available = unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        requires,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` failed: {message}")))?;
    let state = CState::new().with_memory(context.memory.clone());
    let program_point_states = ProgramPointStates::new();
    let application_context = TheoremApplicationContext {
        values: &context.values,
        array_refs: &context.array_refs,
        pre_state: &state,
        post_state: &state,
        result: None,
        program_point_states: &program_point_states,
    };
    available = apply_theorem_applications_to_available(
        theorem_environment,
        theorem_applications,
        claim_label,
        None,
        available,
        &application_context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        goal,
        &assumptions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` failed: {message}")))?;
    if available.contains(&goal) {
        return Ok(());
    }
    if use_simp {
        match simp_proposition(&goal, &assumptions) {
            SimpProposition::True => return Ok(()),
            simplified => {
                return Err(ClickError::new(format!(
                    "`{proof_name}` failed for `{claim_label}`: simplified proposition was not true: {simplified:?}\n  {}",
                    describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                )));
            }
        }
    }

    Err(ClickError::new(format!(
        "`{proof_name}` failed for `{claim_label}`: {}",
        describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
    )))
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_theorem_tactics(
    claim_label: &str,
    requires: &[Proposition],
    original_goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    proof_case: &ExpandedProofCase,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<(), ClickError> {
    let state = CState::new().with_memory(context.memory.clone());
    let program_point_states = ProgramPointStates::new();
    let application_context = TheoremApplicationContext {
        values: &context.values,
        array_refs: &context.array_refs,
        pre_state: &state,
        post_state: &state,
        result: None,
        program_point_states: &program_point_states,
    };
    let mut available = requires.to_vec();
    let mut unfolded_predicates = Vec::new();
    let mut goal = original_goal.clone();
    let mut closed = false;
    let mut induction_active = false;

    for (tactic_index, tactic) in proof_case.tactics.iter().enumerate() {
        for assumption in proof_case
            .assumptions
            .iter()
            .filter(|assumption| assumption.tactic_index == tactic_index)
        {
            match &assumption.kind {
                ProofCaseAssumptionKind::Condition { proposition, value } => {
                    let proposition = lower_pure_theorem_proposition(
                        claim_label,
                        proposition,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
                        ))
                    })?;
                    available.push(if *value {
                        proposition
                    } else {
                        Proposition::Not(Box::new(proposition))
                    });
                }
                ProofCaseAssumptionKind::Disjunct { disjunction, left } => {
                    let lowered = lower_pure_theorem_proposition(
                        claim_label,
                        disjunction,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `cases` disjunction: {message}"
                        ))
                    })?;
                    let Proposition::Or(left_disjunct, right_disjunct) = &lowered else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `cases` requires a disjunction, got {}",
                            describe_pure_fact(&lowered, &[], &[])
                        )));
                    };
                    if !pure_fact_is_replay_available(&lowered, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `cases` requires its exact disjunction as an available fact: {}",
                            describe_pure_fact(&lowered, &[], &[])
                        )));
                    }
                    available.push(if *left {
                        left_disjunct.as_ref().clone()
                    } else {
                        right_disjunct.as_ref().clone()
                    });
                }
            }
        }
        if closed {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{}` follows a goal-closing tactic",
                tactic_name(tactic)
            )));
        }

        match tactic {
            ProofTactic::Induct {
                parameter,
                hypothesis,
            } => {
                let Some(setup) = induction_setup else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unexpected induction certificate"
                    )));
                };
                if induction_active
                    || parameter != &setup.parameter
                    || hypothesis != &setup.hypothesis
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction certificate does not match its theorem setup"
                    )));
                }
                let Some(CValue::Int32(term)) = context.values.get(parameter) else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction parameter must have type int32"
                    )));
                };
                let nonnegative = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(term.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                );
                let assumptions = assumptions_from_propositions(&available);
                if !available.contains(&nonnegative)
                    && assumptions.derive_proposition(&nonnegative).is_none()
                    && !matches!(
                        simp_proposition(&nonnegative, &assumptions),
                        SimpProposition::True
                    )
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `induct({parameter})` requires a proof that `{parameter}` is nonnegative"
                    )));
                }
                induction_active = true;
                let hypothesis = pure_induction_hypothesis(
                    setup,
                    context,
                    predicate_environment,
                    click_function_environment,
                )?;
                if !available.contains(&hypothesis) {
                    available.push(hypothesis);
                }
            }
            ProofTactic::ApplyInduction {
                hypothesis,
                argument,
            } => {
                if !induction_active {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction hypothesis used before `induct`"
                    )));
                }
                apply_pure_induction_hypothesis(
                    induction_setup.expect("active induction has a setup"),
                    hypothesis,
                    argument,
                    claim_label,
                    tactic_index,
                    &mut available,
                    context,
                    predicate_environment,
                    click_function_environment,
                )?;
            }
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if !unfolded_predicates.contains(name) {
                    unfolded_predicates.push(name.clone());
                }
                available = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &available,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
                let assumptions = assumptions_from_propositions(&available);
                goal = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &goal,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
            }
            ProofTactic::ApplyTheorem(application) => {
                available = apply_theorem_applications_to_available(
                    theorem_environment,
                    &[(tactic_index, application.clone())],
                    claim_label,
                    None,
                    available,
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => {
                let explicit_premises = premises
                    .iter()
                    .map(|premise| {
                        lower_pure_theorem_proposition(
                            claim_label,
                            premise,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `apply using` requires an unavailable exact premise: {premise:?}"
                        )));
                    }
                }
                let mut applied = apply_theorem_applications_to_available_with_lowering_context(
                    theorem_environment,
                    &[(tactic_index, application.clone())],
                    claim_label,
                    None,
                    explicit_premises,
                    Some(&available),
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
                for fact in available {
                    if !applied.contains(&fact) {
                        applied.push(fact);
                    }
                }
                available = applied;
            }
            ProofTactic::Assumption => {
                if !available.contains(&goal)
                    && materialization_equivalent_available_fact(&goal, &available).is_none()
                    && quantified_replay_equivalent_available_fact(&goal, &available).is_none()
                {
                    return Err(ClickError::new(format!(
                        "`assumption` failed for `{claim_label}`: {}",
                        describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                    )));
                }
                closed = true;
            }
            ProofTactic::Extract(surface_proposition) => {
                let mut proposition = lower_pure_theorem_proposition(
                    claim_label,
                    surface_proposition,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`extract` failed for `{claim_label}`: could not lower proposition: {message}"
                    ))
                })?;
                proposition = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                    &proposition,
                    &assumptions_from_propositions(&available),
                )
                .map_err(|message| {
                    ClickError::new(format!("`extract` failed for `{claim_label}`: {message}"))
                })?;
                if !exact_proper_conjunct_is_available(&proposition, &available)
                    && !discharged_implication_consequent_is_available(&proposition, &available)
                {
                    return Err(ClickError::new(format!(
                        "`extract` failed for `{claim_label}`: proposition is not a proper conjunct of an exact available fact or a discharged implication consequent: {}",
                        describe_pure_fact(&proposition, &[], &[])
                    )));
                }
                if !available.contains(&proposition) {
                    available.push(proposition);
                }
            }
            ProofTactic::Normalize => {
                if !normalizes_context_free(&goal) {
                    return Err(ClickError::new(format!(
                        "`normalize` failed for `{claim_label}`: goal did not normalize to true: {}",
                        describe_pure_fact(&goal, &[], &[])
                    )));
                }
                closed = true;
            }
            ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Enumerate
            | ProofTactic::Contradiction(_) => {
                let contradiction_fact = match tactic {
                    ProofTactic::Contradiction(surface_fact) => Some(
                        lower_pure_theorem_proposition(
                            claim_label,
                            surface_fact,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`contradiction` failed for `{claim_label}`: could not lower fact: {message}"
                            ))
                        })?,
                    ),
                    _ => None,
                };
                closed = apply_logical_goal_tactic(
                    tactic,
                    &mut goal,
                    &mut available,
                    contradiction_fact,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
            }
            ProofTactic::SimpUsing(simp) => {
                let target = goal.clone();
                let premises = simp
                    .premises
                    .iter()
                    .map(|premise| {
                        lower_pure_theorem_proposition(
                            claim_label,
                            premise,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `simp` premise: {message}"
                        ))
                    })?;
                plan_restricted_simp_goal(&target, premises, &goal, &available).map_err(
                    |message| {
                        ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                    },
                )?;
                closed = true;
            }
            ProofTactic::Rewrite(surface_equality) => {
                let mut equality = lower_pure_theorem_proposition(
                    claim_label,
                    surface_equality,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`rewrite` failed for `{claim_label}`: could not lower equality: {message}"
                    ))
                })?;
                let assumptions = assumptions_from_propositions(&available);
                equality = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                    &equality,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!("`rewrite` failed for `{claim_label}`: {message}"))
                })?;
                goal = rewrite_proposition_by_exact_equality(&goal, &equality, &available)
                    .map_err(|message| {
                        ClickError::new(format!("`rewrite` failed for `{claim_label}`: {message}"))
                    })?;
            }
            ProofTactic::Simp | ProofTactic::CloseInduction => {
                if matches!(tactic, ProofTactic::CloseInduction) && !induction_active {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction closer used outside `induct`"
                    )));
                }
                let assumptions = assumptions_from_propositions(&available);
                if assumptions.derive_proposition(&goal).is_some() {
                    closed = true;
                    continue;
                }
                match simp_proposition(&goal, &assumptions) {
                    SimpProposition::True => closed = true,
                    simplified => {
                        return Err(ClickError::new(format!(
                            "`simp` failed for `{claim_label}`: simplified proposition was not true: {simplified:?}\n  {}",
                            describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                        )));
                    }
                }
            }
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` pure tactic {tactic_index}: `{}` is not available in a pure proof",
                    tactic_name(tactic)
                )));
            }
        }
    }

    if closed || available.contains(&goal) {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "tactics failed for `{claim_label}`: {}",
            describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
        )))
    }
}
