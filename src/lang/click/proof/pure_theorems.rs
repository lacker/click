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
    Ok(PureTheoremContext {
        memory,
        values,
        array_refs,
        requires,
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
    certificate: &ProofReplayPlan,
) -> Option<Vec<ProofTactic>> {
    let tactic = match certificate.tactics() {
        [ProofTactic::Normalize] => ProofTactic::Normalize,
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
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
            } else if let Some(tactics) =
                plan_explicit_equality_rewrites(goal, &premise_pairs, &context.requires)
            {
                return Some(tactics);
            } else {
                let derivation = ProofDerive {
                    premises: premise_pairs
                        .into_iter()
                        .map(|(_, surface)| surface)
                        .collect(),
                };
                ProofTactic::Derive(derivation)
            }
        }
        _ => return None,
    };
    TacticCertificate::from_proof_tactics(std::slice::from_ref(&tactic)).ok()?;
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

    let (proof_kind, source_tactics, induction_setup) = match ensure_clause.proof() {
        Proof::Default | Proof::Tactic(SmartTactic::Auto) => {
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
            (ProofKind::Pure, None, None)
        }
        Proof::Tactic(SmartTactic::Simp) => {
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
            (ProofKind::Simp, None, None)
        }
        Proof::Tactic(SmartTactic::Frame) => {
            return Err(ClickError::new(format!(
                "`frame` is not available in the pure proof for theorem `{claim_label}`"
            )));
        }
        Proof::Script(tactics) => {
            if tactics.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` has an empty explicit proof script"
                )));
            }
            let (tactics, induction_setup) =
                prepare_pure_induction_tactics(theorem, surface_goal, tactics)?;
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
    };

    let (certificate, ()) = pure_goal_certificate_gateway(
        claim_label,
        || {
            pure_theorem_surface_certificate(
                theorem,
                claim_label,
                context,
                &goal,
                source_tactics.as_deref(),
                predicate_environment,
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
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind,
        proof_tactics: Some(certificate.tactics().to_vec()),
        requires: context.requires.clone(),
        conclusion: goal,
    })
}

fn pure_theorem_surface_certificate(
    theorem: &TheoremDefinition,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    source_tactics: Option<&[ProofTactic]>,
    predicate_environment: &PredicateEnvironment,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<TacticCertificate, ClickError> {
    if let (Some(tactics), Some(setup)) = (source_tactics, induction_setup) {
        let lowered = lower_pure_induction_tactics(&setup.surface_requires, tactics, setup)?;
        return TacticCertificate::from_proof_tactics(&lowered).map_err(|error| {
            ClickError::new(format!(
                "induction proof for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    if let Some(tactics) = source_tactics
        && let Ok(certificate) = TacticCertificate::from_proof_tactics(tactics)
    {
        return Ok(certificate);
    }

    if context.requires.contains(goal)
        || materialization_equivalent_available_fact(goal, &context.requires).is_some()
        || quantified_replay_equivalent_available_fact(goal, &context.requires).is_some()
    {
        return TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption]).map_err(
            |error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid assumption certificate: {error:?}"
                ))
            },
        );
    }
    if matches!(normalize_proposition(goal), SimpProposition::True) {
        return TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize]).map_err(
            |error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid normalization certificate: {error:?}"
                ))
            },
        );
    }
    if let Some([ProofTactic::SimpUsing(simp)]) = source_tactics {
        let exact = simp
            .premises
            .iter()
            .map(|surface| {
                theorem
                    .requires()
                    .iter()
                    .position(|required| required.proposition() == Some(surface))
                    .and_then(|index| context.requires.get(index))
                    .cloned()
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` lost an exact listed premise during certificate generation"
                ))
            })?;
        let plan = plan_simp_certificate(goal, &assumptions_from_propositions(&exact)).ok_or_else(
            || {
                ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` did not reproduce its verified plan"
                ))
            },
        )?;
        let tactics =
            lower_pure_simp_certificate(theorem, context, goal, &plan).ok_or_else(|| {
                ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` has no surface certificate"
                ))
            })?;
        return TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart `simp() using` for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    let assumptions = assumptions_from_propositions(&context.requires);
    if let Some(plan) = plan_simp_certificate(goal, &assumptions)
        && let Some(tactics) = lower_pure_simp_certificate(theorem, context, goal, &plan)
    {
        return TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid surface certificate: {error:?}"
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
        return TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
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
        return TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid rewrite certificate: {error:?}"
            ))
        });
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
        let mut tactics = unfolded_predicates
            .into_iter()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.push(ProofTactic::Derive(ProofDerive { premises }));
        return TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
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
        if let Some(tactics) = lower_pure_branching_tactics(&premise_pool, tactics) {
            return TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
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
/// premise pool, and each closing `simp` becomes a `derive` of the goal from
/// exactly that pool.
fn lower_pure_branching_tactics(
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
                    then_tactics: lower_pure_branching_tactics(&then_pool, &proof_if.then_tactics)?,
                    else_tactics: lower_pure_branching_tactics(&else_pool, &proof_if.else_tactics)?,
                }));
            }
            ProofTactic::Simp => lowered.push(ProofTactic::Derive(ProofDerive {
                premises: premise_pool.to_vec(),
            })),
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
    certificate: &TacticCertificate,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<(), ClickError> {
    prove_pure_theorem_script(
        claim_label,
        requires,
        goal,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        context,
        certificate.tactics(),
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
            let proposition = lower_pure_theorem_proposition(
                claim_label,
                &assumption.proposition,
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
            available.push(if assumption.value {
                proposition
            } else {
                Proposition::Not(Box::new(proposition))
            });
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
            ProofTactic::ExactPropositionDerivation(derivation) => {
                let assumptions = assumptions_from_propositions(&available);
                if derivation.conclusion() != &goal || !derivation.replay(&assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: proposition derivation did not replay"
                    )));
                }
                closed = true;
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
            ProofTactic::Normalize => {
                if !normalizes_context_free(&goal) {
                    return Err(ClickError::new(format!(
                        "`normalize` failed for `{claim_label}`: goal did not normalize to true: {goal:?}"
                    )));
                }
                closed = true;
            }
            ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
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
            ProofTactic::Derive(derive) => {
                let target = goal.clone();
                let premises = derive
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
                            "`{claim_label}` tactic {tactic_index}: could not lower `{}` premise: {message}",
                            tactic_name(tactic)
                        ))
                    })?;
                check_atomic_derivation_goal(tactic, &target, premises, &goal, &available)
                    .map_err(|message| {
                        ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                    })?;
                closed = true;
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
