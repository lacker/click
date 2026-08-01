use super::diagnostics::*;
use super::validation::tactic_name;
use super::*;

type NextTopLevelStatement = (
    CState,
    CState,
    Option<CStatement>,
    CStatement,
    Option<CStatement>,
);

fn apply_logical_goal_tactic(
    tactic: &ProofTactic,
    goal: &mut Proposition,
    available: &mut Vec<Proposition>,
    contradiction_fact: Option<Proposition>,
) -> Result<bool, String> {
    match tactic {
        ProofTactic::Intro => match goal.clone() {
            Proposition::Implies(antecedent, consequent) => {
                if !available.contains(&antecedent) {
                    available.push(*antecedent);
                }
                *goal = *consequent;
                Ok(false)
            }
            Proposition::ForAll { body, .. } => {
                *goal = *body;
                Ok(false)
            }
            _ => Err(format!(
                "`intro` requires an implication or universal goal, got {goal:?}"
            )),
        },
        ProofTactic::Conjunction => {
            let Proposition::And(left, right) = goal else {
                return Err(format!(
                    "`conjunction` requires a conjunction goal, got {goal:?}"
                ));
            };
            if !available.contains(left.as_ref()) || !available.contains(right.as_ref()) {
                return Err(format!(
                    "`conjunction` requires both conjuncts as exact facts: {left:?} and {right:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Left => {
            let Proposition::Or(left, _) = goal else {
                return Err(format!("`left` requires a disjunction goal, got {goal:?}"));
            };
            if !available.contains(left.as_ref()) {
                return Err(format!(
                    "`left` requires its selected disjunct as an exact fact: {left:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Right => {
            let Proposition::Or(_, right) = goal else {
                return Err(format!("`right` requires a disjunction goal, got {goal:?}"));
            };
            if !available.contains(right.as_ref()) {
                return Err(format!(
                    "`right` requires its selected disjunct as an exact fact: {right:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::DoubleNegation => {
            let Proposition::Not(outer) = goal else {
                return Err(format!(
                    "`double_negation` requires a double-negation goal, got {goal:?}"
                ));
            };
            let Proposition::Not(inner) = outer.as_ref() else {
                return Err(format!(
                    "`double_negation` requires a double-negation goal, got {goal:?}"
                ));
            };
            if !available.contains(inner.as_ref()) {
                return Err(format!(
                    "`double_negation` requires its inner proposition as an exact fact: {inner:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Vacuous => {
            let Proposition::Implies(antecedent, _) = goal else {
                return Err(format!(
                    "`vacuous` requires an implication goal, got {goal:?}"
                ));
            };
            let negated = Proposition::Not(Box::new(antecedent.as_ref().clone()));
            if !available.contains(&negated) {
                return Err(format!(
                    "`vacuous` requires the negated antecedent as an exact fact: {negated:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Contradiction(_) => {
            let fact = contradiction_fact
                .ok_or_else(|| "`contradiction` is missing its lowered fact".to_string())?;
            let negated = Proposition::Not(Box::new(fact.clone()));
            if !available.contains(&fact) || !available.contains(&negated) {
                return Err(format!(
                    "`contradiction` requires both exact facts: {fact:?} and {negated:?}"
                ));
            }
            Ok(true)
        }
        _ => Err("not a logical goal tactic".to_string()),
    }
}

/// Checks a bitvector equality target by transitive chaining of the listed
/// equality premises, with canonical load spellings as term identity. The
/// decide engine chains constants and variables; certificates also chain
/// through load terms recorded at intermediate states.
fn equal_by_premise_chain(
    premises: &[Proposition],
    target: &Proposition,
    available: &[Proposition],
) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(target_left, target_right), true) =
        crate::kernel::c_condition_fact_with_canonical_loads(target)
    else {
        return false;
    };
    let frame_assumptions = assumptions_from_propositions(available);
    // Two spellings denote the same term when identical, or when they load
    // the same pointer from memories the recorded effect facts prove
    // unchanged between (frame-justified, never by ignoring havoc alone).
    let terms_equivalent = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || matches!((left, right), (
                Bitvector32Term::MemoryLoad(left_memory, left_pointer),
                Bitvector32Term::MemoryLoad(right_memory, right_pointer),
            ) if left_pointer == right_pointer
                && (crate::kernel::c_memory_load_is_unchanged(
                    left_memory,
                    right_memory,
                    left_pointer,
                    &frame_assumptions,
                ) || crate::kernel::c_memory_load_is_unchanged(
                    right_memory,
                    left_memory,
                    left_pointer,
                    &frame_assumptions,
                )))
    };
    let mut classes: Vec<Vec<Bitvector32Term>> = Vec::new();
    // Ambient equality facts are execution-certified (store equations,
    // recorded aliases) and may link the listed premises, the same way
    // frame facts justify load unification.
    for premise in premises.iter().chain(available) {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            crate::kernel::c_condition_fact_with_canonical_loads(premise)
        else {
            continue;
        };
        let left = *left;
        let right = *right;
        let left_class = classes
            .iter()
            .position(|class| class.iter().any(|term| terms_equivalent(term, &left)));
        let right_class = classes
            .iter()
            .position(|class| class.iter().any(|term| terms_equivalent(term, &right)));
        match (left_class, right_class) {
            (Some(a), Some(b)) if a != b => {
                let merged = classes.remove(a.max(b));
                classes[a.min(b)].extend(merged);
            }
            (Some(_), Some(_)) => {}
            (Some(a), None) => classes[a].push(right),
            (None, Some(b)) => classes[b].push(left),
            (None, None) => classes.push(vec![left, right]),
        }
    }
    let target_left = *target_left;
    let target_right = *target_right;
    terms_equivalent(&target_left, &target_right)
        || classes.iter().any(|class| {
            class.iter().any(|term| terms_equivalent(term, &target_left))
                && class.iter().any(|term| terms_equivalent(term, &target_right))
        })
}

fn check_atomic_derivation_goal(
    tactic: &ProofTactic,
    target: Proposition,
    premises: Vec<Proposition>,
    goal: &Proposition,
    available: &[Proposition],
) -> Result<(), String> {
    let target_matches_goal = &target == goal
        || quantified_replay_equivalent_available_fact(goal, std::slice::from_ref(&target))
            .is_some();
    if !target_matches_goal {
        return Err(format!(
            "`{}` target does not match the current goal\n  target: {target:?}\n  goal: {goal:?}",
            tactic_name(tactic)
        ));
    }
    let premise_part_available = |part: &Proposition| {
        let normalized = normalize_direct_atomic_memory_loads(part);
        available.iter().any(|available| {
            let mut conjuncts = Vec::new();
            atomic_conjuncts(available, &mut conjuncts);
            conjuncts.into_iter().any(|available| {
                let available = normalize_direct_atomic_memory_loads(available);
                available == normalized
                    || condition_polarity_equivalent(&available, &normalized)
                    || (matches!(available, Proposition::ForAll { .. })
                        && matches!(normalized, Proposition::ForAll { .. })
                        && assumptions_from_propositions(&[available])
                            .derive_simp_proposition(&normalized)
                            .is_some())
            })
        }) || snapshot_bridged_fact_is_available(&normalized, available, &[])
    };
    if let Some(missing) = premises.iter().find(|premise| {
        // A conjunction premise is available when each conjunct is; facts
        // are often assumed split even when the certificate lists them
        // joined.
        let mut parts = Vec::new();
        atomic_conjuncts(premise, &mut parts);
        !parts.into_iter().all(premise_part_available)
    }) {
        return Err(format!(
            "`{}` is missing an exact listed premise: {missing:?}",
            tactic_name(tactic)
        ));
    }
    let normalized_premises = premises
        .iter()
        .map(normalize_direct_atomic_memory_loads)
        .collect::<Vec<_>>();
    let normalized_target = normalize_direct_atomic_memory_loads(&target);
    // Effect summaries and certified-write records are deterministic
    // execution artifacts with no surface spelling; certificate generation
    // deliberately omits them from the premise list (mirroring its
    // loadability carve-out), so the replay environment supplies them.
    // Only these two shapes ride along: everything else the derivation
    // consumes must be a listed premise.
    let effect_context = available
        .iter()
        .filter(|fact| {
            matches!(
                fact,
                Proposition::CMemoryMutatesOnly { .. } | Proposition::CMemoryEffectSummary { .. }
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let with_effect_context = |facts: &[Proposition]| {
        let mut combined = facts.to_vec();
        combined.extend(effect_context.iter().cloned());
        combined
    };
    // Try the premises as spelled before normalizing: snapshot-bridging
    // derivations can depend on the recorded load spellings that
    // normalization rewrites.
    let raw_assumptions = assumptions_from_propositions(&with_effect_context(&premises));
    let raw_derivation = match tactic {
        ProofTactic::Derive(_) => raw_assumptions
            .derive_atomic_proposition(&target)
            .or_else(|| raw_assumptions.derive_proposition(&target)),
        ProofTactic::Calculate(_) => raw_assumptions
            .derive_simp_atomic_proposition(&target)
            .or_else(|| raw_assumptions.derive_simp_proposition(&target)),
        _ => return Err("not a derivation tactic".to_string()),
    };
    let assumptions = assumptions_from_propositions(&with_effect_context(&normalized_premises));
    let derivation = raw_derivation.or_else(|| match tactic {
        ProofTactic::Derive(_) => assumptions
            .derive_atomic_proposition(&normalized_target)
            .or_else(|| assumptions.derive_proposition(&normalized_target)),
        ProofTactic::Calculate(_) => assumptions
            .derive_simp_atomic_proposition(&normalized_target)
            .or_else(|| assumptions.derive_simp_proposition(&normalized_target)),
        _ => None,
    });
    // Premises recorded at different program points can spell the same load
    // through different snapshots; retry with canonical loads so the chain
    // unifies.
    let derivation = derivation.or_else(|| {
        let canonical_premises = normalized_premises
            .iter()
            .map(crate::kernel::c_condition_fact_with_canonical_loads)
            .collect::<Vec<_>>();
        let canonical_target =
            crate::kernel::c_condition_fact_with_canonical_loads(&normalized_target);
        if canonical_premises == normalized_premises && canonical_target == normalized_target {
            return None;
        }
        let canonical_assumptions =
            assumptions_from_propositions(&with_effect_context(&canonical_premises));
        match tactic {
            ProofTactic::Derive(_) => canonical_assumptions
                .derive_atomic_proposition(&canonical_target)
                .or_else(|| canonical_assumptions.derive_proposition(&canonical_target)),
            ProofTactic::Calculate(_) => canonical_assumptions
                .derive_simp_atomic_proposition(&canonical_target)
                .or_else(|| canonical_assumptions.derive_simp_proposition(&canonical_target)),
            _ => None,
        }
    });
    if derivation.is_none()
        && equal_by_premise_chain(&normalized_premises, &normalized_target, available)
    {
        return Ok(());
    }
    if derivation.is_none() {
        return Err(format!(
            "`{}` could not check the target from exactly the listed premises: {target:?}\n  premises: {normalized_premises:#?}",
            tactic_name(tactic),
        ));
    }
    Ok(())
}

fn normalizes_context_free(goal: &Proposition) -> bool {
    matches!(normalize_proposition(goal), SimpProposition::True)
        || Assumptions::new()
            .derive_atomic_proposition(goal)
            .or_else(|| Assumptions::new().derive_proposition(goal))
            .is_some()
}

pub(super) fn verify_theorem_definitions(
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
struct PureTheoremContext {
    memory: CMemory,
    values: BTreeMap<String, CValue>,
    array_refs: ClickArrayRefs,
    requires: Vec<Proposition>,
}

fn pure_theorem_context(
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

pub(super) fn pure_theorem_parameter_values(
    parameters: &[FunctionParameter],
) -> BTreeMap<String, CValue> {
    parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let value = match parameter.c_type() {
                C0Type::Int32 => CValue::Int32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt8 => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int32Pointer | C0Type::Int32Array(_) => CValue::Pointer(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.into(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }),
                C0Type::UInt8Pointer | C0Type::UInt8Array(_) => CValue::Pointer(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.into(),
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

pub(super) fn pure_theorem_array_refs(
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
    surface_goal: &ClickProposition,
    context: &PureTheoremContext,
    certificate: &ProofReplayPlan,
) -> Option<Vec<ProofTactic>> {
    let tactic = match certificate.tactics() {
        [ProofTactic::Normalize] => ProofTactic::Normalize,
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
            let premises = derivation
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
                })
                .collect::<Option<Vec<_>>>()?;
            if premises.is_empty() {
                ProofTactic::Normalize
            } else {
                let exact_premises = derivation.context_premises();
                let exact_assumptions = assumptions_from_propositions(&exact_premises);
                let derive = exact_assumptions
                    .derive_atomic_proposition(derivation.conclusion())
                    .or_else(|| exact_assumptions.derive_proposition(derivation.conclusion()))
                    .is_some();
                let derivation = ProofDerive {
                    proposition: surface_goal.clone(),
                    premises,
                };
                if derive {
                    ProofTactic::Derive(derivation)
                } else {
                    ProofTactic::Calculate(derivation)
                }
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

    let (proof_kind, source_tactics) = match ensure_clause.proof() {
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
            (ProofKind::Pure, None)
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
            (ProofKind::Simp, None)
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
            prove_pure_theorem_script(
                claim_label,
                &context.requires,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                context,
                tactics,
            )?;
            (ProofKind::TacticScript, Some(tactics.as_slice()))
        }
    };

    let (certificate, ()) = pure_goal_certificate_gateway(
        claim_label,
        || {
            pure_theorem_surface_certificate(
                theorem,
                surface_goal,
                claim_label,
                context,
                &goal,
                source_tactics,
                predicate_environment,
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

fn pure_goal_certificate_gateway<T>(
    claim_label: &str,
    planner: impl FnOnce() -> Result<TacticCertificate, ClickError>,
    replay: impl FnOnce(&TacticCertificate) -> Result<T, ClickError>,
) -> Result<(TacticCertificate, T), ClickError> {
    let certificate = planner()?;
    TacticCertificate::from_proof_tactics(certificate.tactics()).map_err(|error| {
        ClickError::new(format!(
            "pure goal `{claim_label}` planner returned a non-surface certificate: {error:?}"
        ))
    })?;
    let replayed = replay(&certificate).map_err(|error| {
        ClickError::new(format!(
            "pure goal `{claim_label}` certificate failed ordinary replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    Ok((certificate, replayed))
}

fn pure_theorem_surface_certificate(
    theorem: &TheoremDefinition,
    surface_goal: &ClickProposition,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    source_tactics: Option<&[ProofTactic]>,
    predicate_environment: &PredicateEnvironment,
) -> Result<TacticCertificate, ClickError> {
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
    let assumptions = assumptions_from_propositions(&context.requires);
    if let Some(plan) = plan_simp_certificate(goal, &assumptions)
        && let Some(tactics) = lower_pure_simp_certificate(theorem, surface_goal, context, &plan)
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
        // `unfold` rewrites the goal as well as the premises, so the closing
        // derivation targets the unfolded goal spelling.
        let unfolded_goal = unfold_structural_invariant_proposition(
            predicate_environment,
            surface_goal,
            &unfolded_predicates,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let mut tactics = unfolded_predicates
            .into_iter()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.push(ProofTactic::Derive(ProofDerive {
            proposition: unfolded_goal,
            premises,
        }));
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
        if let Some(tactics) =
            lower_pure_branching_tactics(surface_goal, &premise_pool, tactics)
        {
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
    surface_goal: &ClickProposition,
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
                        surface_goal,
                        &then_pool,
                        &proof_if.then_tactics,
                    )?,
                    else_tactics: lower_pure_branching_tactics(
                        surface_goal,
                        &else_pool,
                        &proof_if.else_tactics,
                    )?,
                }));
            }
            ProofTactic::Simp => lowered.push(ProofTactic::Derive(ProofDerive {
                proposition: surface_goal.clone(),
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

/// Replay a validated certificate through the ordinary pure-tactic executor.
#[allow(clippy::too_many_arguments)]
fn replay_pure_theorem_certificate(
    claim_label: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    certificate: &TacticCertificate,
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
) -> Result<(), ClickError> {
    for proof_case in expand_proof_if_cases(tactics, claim_label)? {
        prove_pure_theorem_tactics(
            claim_label,
            requires,
            goal,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            context,
            &proof_case,
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod certificate_tests {
    use super::*;

    fn linear_tactic_coordinates(node: &InternalProofNode) -> Vec<(usize, usize)> {
        match node {
            InternalProofNode::Done => Vec::new(),
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                let mut coordinates = tactics
                    .iter()
                    .map(|tactic| (tactic.index, tactic.source_index))
                    .collect::<Vec<_>>();
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
            InternalProofNode::If {
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                let mut coordinates = linear_tactic_coordinates(then_branch);
                coordinates.extend(linear_tactic_coordinates(else_branch));
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
            InternalProofNode::Advance {
                body, continuation, ..
            } => {
                let mut coordinates = linear_tactic_coordinates(body);
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
        }
    }

    #[test]
    fn generated_certificate_steps_retain_one_owning_source_occurrence() {
        let tactics = [ProofTactic::Step, ProofTactic::Assumption];
        let source = build_internal_proof(&tactics, "source").expect("source proof should build");
        let generated = build_generated_certificate_proof(&tactics, "generated", 7)
            .expect("generated certificate should build");

        assert_eq!(linear_tactic_coordinates(&source), vec![(0, 0), (1, 1)]);
        assert_eq!(linear_tactic_coordinates(&generated), vec![(0, 7), (1, 7)]);
    }

    #[test]
    fn deferred_tactics_retain_their_owning_source_occurrence() {
        let mut replay = TacticReplayState::default();
        replay.defer_post_execution(9, 2, PostExecutionTactic::Simp);

        let [deferred] = replay.post_execution_tactics.as_slice() else {
            panic!("expected one deferred tactic");
        };
        assert_eq!(deferred.tactic_index, 9);
        assert_eq!(deferred.source_index, 2);
        assert!(matches!(deferred.tactic, PostExecutionTactic::Simp));
    }

    #[test]
    fn timing_classifies_a_have_with_only_simple_tactics_as_simple() {
        let have = ProofTactic::Have(ProofHave {
            proposition: ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Value(int32(1))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(1))),
            },
            proof: Proof::Script(vec![ProofTactic::Assumption]),
        });

        assert_eq!(source_tactic_class(&have), SourceTacticClass::Simple);
    }

    #[test]
    fn pure_fact_replay_availability_ignores_quantifier_binder_ids() {
        let quantified_equality = |variable| Proposition::ForAll {
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Variable(variable)),
                ),
                true,
            )),
        };
        let available = quantified_equality(Variable(2_000_000));
        let replayed = quantified_equality(Variable(3_000_000));

        assert!(pure_fact_is_replay_available(&replayed, &[available]));
    }

    #[test]
    fn pure_certificate_replay_is_transactional() {
        let file = parse(
            r#"
                theorem reflexive(x: int32) {
                    ensures x == x by auto;
                }
            "#,
        )
        .expect("theorem should parse");
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem = &file.theorem_definitions()[0];
        let context =
            pure_theorem_context(theorem, &predicate_environment, &click_function_environment)
                .expect("theorem context should lower");
        let Ensure::Proposition(surface_goal) = theorem.ensures()[0].ensure() else {
            panic!("expected proposition goal");
        };
        let goal = lower_pure_theorem_proposition(
            theorem.name(),
            surface_goal,
            &context.values,
            &context.array_refs,
            &context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("goal should lower");
        let failing = TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple tactic");
        let succeeding = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a simple tactic");

        assert!(
            replay_pure_theorem_certificate(
                "reflexive.ensures_0",
                &context.requires,
                &goal,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &context,
                &failing,
            )
            .is_err()
        );
        replay_pure_theorem_certificate(
            "reflexive.ensures_0",
            &context.requires,
            &goal,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &context,
            &succeeding,
        )
        .expect("failed replay must not mutate the shared proof inputs");
    }

    #[test]
    fn path_aligned_certificates_preserve_branch_structure() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let assumption = TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a certificate");
        let normalize = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a certificate");

        let merged = merge_path_aligned_certificates(
            "branching",
            vec![
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: condition.clone(),
                        value: true,
                    }],
                    certificate: assumption,
                },
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: condition.clone(),
                        value: false,
                    }],
                    certificate: normalize,
                },
            ],
        )
        .expect("opposite path certificates should merge");

        let [ProofTactic::If(proof_if)] = merged.tactics() else {
            panic!("different path certificates should produce one proof branch");
        };
        assert_eq!(proof_if.condition, condition);
        assert_eq!(proof_if.then_tactics, vec![ProofTactic::Assumption]);
        assert_eq!(proof_if.else_tactics, vec![ProofTactic::Normalize]);
    }

    #[test]
    fn path_aligned_certificates_reject_incompatible_frontiers() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let other = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("y".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let assumption = TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a certificate");
        let normalize = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a certificate");

        let error = merge_path_aligned_certificates(
            "branching",
            vec![
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition,
                        value: true,
                    }],
                    certificate: assumption,
                },
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: other,
                        value: false,
                    }],
                    certificate: normalize,
                },
            ],
        )
        .expect_err("unrelated branch conditions must not be flattened together");

        assert!(error.message().contains("incompatible next branch"));
    }
}

struct ExpandedProofCase {
    tactics: Vec<ProofTactic>,
    assumptions: Vec<ProofCaseAssumption>,
    advance_checks: Vec<ProofAdvanceCheck>,
}

struct ProofCaseAssumption {
    tactic_index: usize,
    proposition: ClickProposition,
    value: bool,
}

struct ProofAdvanceCheck {
    join_id: usize,
    tactic_index: usize,
    target: ProgramPointRef,
    assertions: Vec<ProofAssertion>,
}

// Pure proofs and point-local `have` proofs use flat logical cases. Execution
// proofs use `InternalProofNode`, where `advance` has region-join semantics.
fn expand_proof_if_cases(
    tactics: &[ProofTactic],
    claim_label: &str,
) -> Result<Vec<ExpandedProofCase>, ClickError> {
    let mut next_join_id = 0;
    expand_structured_proof_cases(tactics, claim_label, &mut next_join_id)
}

fn expand_structured_proof_cases(
    tactics: &[ProofTactic],
    claim_label: &str,
    next_join_id: &mut usize,
) -> Result<Vec<ExpandedProofCase>, ClickError> {
    let Some((control_index, control_tactic)) = tactics
        .iter()
        .enumerate()
        .find(|(_, tactic)| matches!(tactic, ProofTactic::If(_) | ProofTactic::Advance(_)))
    else {
        return Ok(vec![ExpandedProofCase {
            tactics: tactics.to_vec(),
            assumptions: Vec::new(),
            advance_checks: Vec::new(),
        }]);
    };
    let prefix = &tactics[..control_index];
    match control_tactic {
        ProofTactic::If(proof_if) => {
            let suffix_cases = expand_structured_proof_cases(
                &tactics[control_index + 1..],
                claim_label,
                next_join_id,
            )?;
            let mut cases = Vec::new();
            for (value, branch_tactics) in [
                (true, proof_if.then_tactics.as_slice()),
                (false, proof_if.else_tactics.as_slice()),
            ] {
                for branch in
                    expand_structured_proof_cases(branch_tactics, claim_label, next_join_id)?
                {
                    for suffix in &suffix_cases {
                        let boundary = prefix.len() + branch.tactics.len();
                        let mut linear = prefix.to_vec();
                        linear.extend(branch.tactics.iter().cloned());
                        linear.extend(suffix.tactics.iter().cloned());
                        let mut assumptions = vec![ProofCaseAssumption {
                            tactic_index: prefix.len(),
                            proposition: proof_if.condition.clone(),
                            value,
                        }];
                        assumptions.extend(branch.assumptions.iter().map(|assumption| {
                            ProofCaseAssumption {
                                tactic_index: prefix.len() + assumption.tactic_index,
                                proposition: assumption.proposition.clone(),
                                value: assumption.value,
                            }
                        }));
                        assumptions.extend(suffix.assumptions.iter().map(|assumption| {
                            ProofCaseAssumption {
                                tactic_index: boundary + assumption.tactic_index,
                                proposition: assumption.proposition.clone(),
                                value: assumption.value,
                            }
                        }));
                        let mut advance_checks = branch
                            .advance_checks
                            .iter()
                            .map(|check| ProofAdvanceCheck {
                                join_id: check.join_id,
                                tactic_index: prefix.len() + check.tactic_index,
                                target: check.target.clone(),
                                assertions: check.assertions.clone(),
                            })
                            .collect::<Vec<_>>();
                        advance_checks.extend(suffix.advance_checks.iter().map(|check| {
                            ProofAdvanceCheck {
                                join_id: check.join_id,
                                tactic_index: boundary + check.tactic_index,
                                target: check.target.clone(),
                                assertions: check.assertions.clone(),
                            }
                        }));
                        cases.push(ExpandedProofCase {
                            tactics: linear,
                            assumptions,
                            advance_checks,
                        });
                    }
                }
            }
            Ok(cases)
        }
        ProofTactic::Advance(advance) => {
            let join_id = *next_join_id;
            *next_join_id += 1;
            let body_cases =
                expand_structured_proof_cases(&advance.tactics, claim_label, next_join_id)?;
            let suffix_cases = expand_structured_proof_cases(
                &tactics[control_index + 1..],
                claim_label,
                next_join_id,
            )?;
            let mut cases = Vec::new();
            for body in &body_cases {
                for suffix in &suffix_cases {
                    let boundary = prefix.len() + body.tactics.len();
                    let mut linear = prefix.to_vec();
                    linear.extend(body.tactics.iter().cloned());
                    linear.extend(suffix.tactics.iter().cloned());
                    let mut assumptions = body
                        .assumptions
                        .iter()
                        .map(|assumption| ProofCaseAssumption {
                            tactic_index: prefix.len() + assumption.tactic_index,
                            proposition: assumption.proposition.clone(),
                            value: assumption.value,
                        })
                        .collect::<Vec<_>>();
                    assumptions.extend(suffix.assumptions.iter().map(|assumption| {
                        ProofCaseAssumption {
                            tactic_index: boundary + assumption.tactic_index,
                            proposition: assumption.proposition.clone(),
                            value: assumption.value,
                        }
                    }));
                    let mut advance_checks = body
                        .advance_checks
                        .iter()
                        .map(|check| ProofAdvanceCheck {
                            join_id: check.join_id,
                            tactic_index: prefix.len() + check.tactic_index,
                            target: check.target.clone(),
                            assertions: check.assertions.clone(),
                        })
                        .collect::<Vec<_>>();
                    advance_checks.push(ProofAdvanceCheck {
                        join_id,
                        tactic_index: boundary,
                        target: advance.target.clone(),
                        assertions: advance.assertions.clone(),
                    });
                    advance_checks.extend(suffix.advance_checks.iter().map(|check| {
                        ProofAdvanceCheck {
                            join_id: check.join_id,
                            tactic_index: boundary + check.tactic_index,
                            target: check.target.clone(),
                            assertions: check.assertions.clone(),
                        }
                    }));
                    cases.push(ExpandedProofCase {
                        tactics: linear,
                        assumptions,
                        advance_checks,
                    });
                }
            }
            Ok(cases)
        }
        _ => unreachable!("control-tactic search only returns if or advance"),
    }
}

#[derive(Clone)]
struct IndexedTactic {
    index: usize,
    source_index: usize,
    tactic: ProofTactic,
}

enum InternalProofNode {
    Done,
    Linear {
        tactics: Vec<IndexedTactic>,
        continuation: Box<InternalProofNode>,
    },
    If {
        index: usize,
        condition: ClickProposition,
        then_branch: Box<InternalProofNode>,
        else_branch: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
    Advance {
        index: usize,
        _join_id: usize,
        target: ProgramPointRef,
        assertions: Vec<ProofAssertion>,
        body: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
}

#[derive(Clone, Copy)]
pub(super) enum ProofTacticSource {
    SourceSyntax,
    GeneratedBy { source_index: usize },
}

fn build_internal_proof_with_source(
    tactics: &[ProofTactic],
    claim_label: &str,
    source: ProofTacticSource,
) -> Result<InternalProofNode, ClickError> {
    match source {
        ProofTacticSource::SourceSyntax => build_internal_proof(tactics, claim_label),
        ProofTacticSource::GeneratedBy { source_index } => {
            build_generated_certificate_proof(tactics, claim_label, source_index)
        }
    }
}

fn build_internal_proof(
    tactics: &[ProofTactic],
    claim_label: &str,
) -> Result<InternalProofNode, ClickError> {
    let mut next_join_id = 0;
    build_internal_proof_at(tactics, claim_label, &mut next_join_id, 0, 0)
}

fn build_generated_certificate_proof(
    tactics: &[ProofTactic],
    claim_label: &str,
    owning_source_index: usize,
) -> Result<InternalProofNode, ClickError> {
    let mut proof = build_internal_proof(tactics, claim_label)?;
    set_generated_proof_source_index(&mut proof, owning_source_index);
    Ok(proof)
}

fn set_generated_proof_source_index(node: &mut InternalProofNode, owning_source_index: usize) {
    match node {
        InternalProofNode::Done => {}
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            for tactic in tactics {
                tactic.source_index = owning_source_index;
            }
            set_generated_proof_source_index(continuation, owning_source_index);
        }
        InternalProofNode::If {
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            set_generated_proof_source_index(then_branch, owning_source_index);
            set_generated_proof_source_index(else_branch, owning_source_index);
            set_generated_proof_source_index(continuation, owning_source_index);
        }
        InternalProofNode::Advance {
            body, continuation, ..
        } => {
            set_generated_proof_source_index(body, owning_source_index);
            set_generated_proof_source_index(continuation, owning_source_index);
        }
    }
}

fn build_internal_proof_at(
    tactics: &[ProofTactic],
    claim_label: &str,
    next_join_id: &mut usize,
    index_offset: usize,
    source_index_offset: usize,
) -> Result<InternalProofNode, ClickError> {
    let Some((control_index, control_tactic)) = tactics
        .iter()
        .enumerate()
        .find(|(_, tactic)| matches!(tactic, ProofTactic::If(_) | ProofTactic::Advance(_)))
    else {
        if tactics.is_empty() {
            return Ok(InternalProofNode::Done);
        }
        return Ok(InternalProofNode::Linear {
            tactics: tactics
                .iter()
                .cloned()
                .enumerate()
                .map(|(index, tactic)| IndexedTactic {
                    index: index_offset + index,
                    source_index: source_index_offset + index,
                    tactic,
                })
                .collect(),
            continuation: Box::new(InternalProofNode::Done),
        });
    };

    let index = index_offset + control_index;
    let source_index = source_index_offset + control_index;
    let control = match control_tactic {
        ProofTactic::If(proof_if) => {
            let then_width = source_tactic_count(&proof_if.then_tactics);
            InternalProofNode::If {
                index,
                condition: proof_if.condition.clone(),
                then_branch: Box::new(build_internal_proof_at(
                    &proof_if.then_tactics,
                    claim_label,
                    next_join_id,
                    index + 1,
                    source_index + 1,
                )?),
                else_branch: Box::new(build_internal_proof_at(
                    &proof_if.else_tactics,
                    claim_label,
                    next_join_id,
                    index + 1,
                    source_index + 1 + then_width,
                )?),
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    claim_label,
                    next_join_id,
                    index + 1,
                    source_index + source_tactic_width(control_tactic),
                )?),
            }
        }
        ProofTactic::Advance(advance) => {
            let join_id = *next_join_id;
            *next_join_id += 1;
            InternalProofNode::Advance {
                index,
                _join_id: join_id,
                target: advance.target.clone(),
                assertions: advance.assertions.clone(),
                body: Box::new(build_internal_proof_at(
                    &advance.tactics,
                    claim_label,
                    next_join_id,
                    index + 1,
                    source_index + 1,
                )?),
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    claim_label,
                    next_join_id,
                    index + 1,
                    source_index + source_tactic_width(control_tactic),
                )?),
            }
        }
        _ => unreachable!("control-tactic search only returns if or advance"),
    };

    if control_index == 0 {
        Ok(control)
    } else {
        Ok(InternalProofNode::Linear {
            tactics: tactics[..control_index]
                .iter()
                .cloned()
                .enumerate()
                .map(|(prefix_index, tactic)| IndexedTactic {
                    index: index_offset + prefix_index,
                    source_index: source_index_offset + prefix_index,
                    tactic,
                })
                .collect(),
            continuation: Box::new(control),
        })
    }
}

pub(super) fn source_tactic_count(tactics: &[ProofTactic]) -> usize {
    tactics.iter().map(source_tactic_width).sum()
}

fn source_tactic_width(tactic: &ProofTactic) -> usize {
    match tactic {
        ProofTactic::If(proof_if) => {
            1 + source_tactic_count(&proof_if.then_tactics)
                + source_tactic_count(&proof_if.else_tactics)
        }
        ProofTactic::Advance(advance) => 1 + source_tactic_count(&advance.tactics),
        _ => 1,
    }
}

fn lower_pure_theorem_proposition(
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
            | ProofTactic::Conjunction
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::DoubleNegation
            | ProofTactic::Vacuous
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
            ProofTactic::Derive(derive) | ProofTactic::Calculate(derive) => {
                let target = lower_pure_theorem_proposition(
                    claim_label,
                    &derive.proposition,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not lower `{}` target: {message}",
                        tactic_name(tactic)
                    ))
                })?;
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
                check_atomic_derivation_goal(tactic, target, premises, &goal, &available).map_err(
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
            ProofTactic::Simp => {
                let assumptions = assumptions_from_propositions(&available);
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

struct TheoremApplicationContext<'a> {
    values: &'a BTreeMap<String, CValue>,
    array_refs: &'a ClickArrayRefs,
    pre_state: &'a CState,
    post_state: &'a CState,
    result: Option<&'a CValue>,
    program_point_states: &'a ProgramPointStates,
}

fn apply_theorem_applications_to_available(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    available: Vec<Proposition>,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    apply_theorem_applications_to_available_with_lowering_context(
        theorem_environment,
        theorem_applications,
        claim_label,
        path_index,
        available,
        None,
        context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )
}

#[allow(clippy::too_many_arguments)]
fn apply_theorem_applications_to_available_with_lowering_context(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    mut available: Vec<Proposition>,
    lowering_context: Option<&[Proposition]>,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    for (tactic_index, application) in theorem_applications {
        available = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &available,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, *tactic_index, message)
        })?;
        let mut lowering_available = lowering_context.unwrap_or(&available).to_vec();
        for fact in &available {
            if !lowering_available.contains(fact) {
                lowering_available.push(fact.clone());
            }
        }
        let conclusions = instantiate_theorem_application(
            theorem_environment,
            application,
            claim_label,
            path_index,
            *tactic_index,
            &available,
            &lowering_available,
            context,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )?;
        for conclusion in conclusions {
            if !available.contains(&conclusion) {
                available.push(conclusion);
            }
        }
    }
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &available,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, 0, message))
}

fn instantiate_theorem_application(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    available: &[Proposition],
    lowering_available: &[Proposition],
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            format!("unknown theorem `{}`", application.name),
        )
    })?;
    if application.arguments.len() != theorem.parameters().len() {
        return Err(theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            format!(
                "theorem `{}` expects {} argument(s), got {}",
                theorem.name(),
                theorem.parameters().len(),
                application.arguments.len()
            ),
        ));
    }

    let assumptions = assumptions_from_propositions(available);
    let lowering_assumptions = assumptions_from_propositions(lowering_available);
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        &lowering_assumptions,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, tactic_index, message))?;
    let mut lowerer = KernelPropositionLowerer::new(
        values,
        array_refs,
        context.post_state.memory().clone(),
        predicate_environment,
        click_function_environment,
    );

    for requirement in theorem.requires() {
        let Some(requirement) = requirement.proposition() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "theorem `{}` has a non-proposition requirement that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let mut lowered = lowerer
            .lower_requirement_proposition(requirement)
            .map_err(|error| {
                theorem_application_error(
                    claim_label,
                    path_index,
                    tactic_index,
                    format!(
                        "could not lower theorem `{}` requirement: {}",
                        theorem.name(),
                        error.message()
                    ),
                )
            })?;
        lowered = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &lowered,
            &assumptions,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, tactic_index, message)
        })?;
        lowered = normalize_direct_atomic_memory_loads(&lowered);
        if !available
            .iter()
            .any(|fact| normalize_direct_atomic_memory_loads(fact) == lowered)
            && !matches!(normalize_proposition(&lowered), SimpProposition::True)
        {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "required exact fact for theorem `{}` is unavailable: {}",
                    theorem.name(),
                    describe_missing_pure_fact(&lowered, available, &[], &[], &[], &[])
                ),
            ));
        }
    }

    let mut conclusions = Vec::new();
    for ensure in theorem.ensures() {
        let Ensure::Proposition(conclusion) = ensure.ensure() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "theorem `{}` has a non-proposition conclusion that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let conclusion = lowerer
            .lower_requirement_proposition(conclusion)
            .map_err(|error| {
                theorem_application_error(
                    claim_label,
                    path_index,
                    tactic_index,
                    format!(
                        "could not lower theorem `{}` conclusion: {}",
                        theorem.name(),
                        error.message()
                    ),
                )
            })?;
        conclusions.push(normalize_direct_atomic_memory_loads(&conclusion));
    }
    Ok(conclusions)
}

fn theorem_application_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let mut active_functions = BTreeSet::new();
    let mut values = BTreeMap::new();
    let mut array_refs = BTreeMap::new();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                context.program_point_states,
                &mut active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "theorem `{}` parameter `{}` is not an array-ref parameter",
                        theorem.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    theorem.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            values.insert(
                parameter.name().to_string(),
                CValue::Pointer(array_ref.pointer.clone()),
            );
            array_refs.insert(parameter.name().to_string(), array_ref);
        } else {
            let value = evaluate_contract_expression_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                context.program_point_states,
                &mut active_functions,
            )?;
            if !c_value_matches_click_type(&value, parameter.c_type()) {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {}, got {value:?}",
                    theorem.name(),
                    parameter.name(),
                    describe_c0_type(parameter.c_type())
                ));
            }
            values.insert(parameter.name().to_string(), value);
        }
    }
    Ok((values, array_refs))
}

fn theorem_application_error(
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    message: impl Into<String>,
) -> ClickError {
    let path = path_index
        .map(|index| format!(" path {index},"))
        .unwrap_or_default();
    ClickError::new(format!(
        "`{claim_label}`{path} tactic {tactic_index}: `apply` failed: {}",
        message.into()
    ))
}

#[derive(Clone, Copy)]
pub(super) enum FunctionClaimRef<'a> {
    Effect(usize, &'a EffectClause),
    Ensure(usize, &'a EnsureClause),
}

impl<'a> FunctionClaimRef<'a> {
    pub(super) fn proof(self) -> &'a Proof {
        match self {
            Self::Effect(_, clause) => clause.proof(),
            Self::Ensure(_, clause) => clause.proof(),
        }
    }

    fn verified_claim(self) -> VerifiedClaim {
        match self {
            Self::Effect(index, clause) => VerifiedClaim::Effect {
                index,
                clause: clause.clone(),
            },
            Self::Ensure(index, clause) => VerifiedClaim::Ensure {
                index,
                clause: clause.clone(),
            },
        }
    }
}

pub(super) fn function_claims(function_block: &FunctionBlock) -> Vec<FunctionClaimRef<'_>> {
    function_block
        .effects()
        .iter()
        .enumerate()
        .map(|(index, clause)| FunctionClaimRef::Effect(index, clause))
        .chain(
            function_block
                .ensures()
                .iter()
                .enumerate()
                .map(|(index, clause)| FunctionClaimRef::Ensure(index, clause)),
        )
        .collect()
}

pub(super) fn initial_claim_context(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<
    (
        CState,
        Vec<CExpression>,
        Vec<Proposition>,
        SurfacePropositionMap,
    ),
    ClickError,
> {
    let (mut state, arguments) = initial_call_state(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
    )?;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        claim_label,
    )?;
    let mut requirement_pure_facts = requirement_propositions(
        function_block.requires(),
        parsed_function.parameters(),
        &arguments,
        state.memory(),
        predicate_environment,
        click_function_environment,
    )?;
    let mut surface_propositions = SurfacePropositionMap::default();
    for requirement in function_block.requires() {
        let surface = match requirement.inner() {
            Requirement::Proposition(proposition) => Some(proposition.clone()),
            Requirement::LoadableSegment { segment } => Some(ClickProposition::Loadable {
                segment: segment.clone(),
            }),
            Requirement::LoadableBytes { .. }
            | Requirement::Resource(_)
            | Requirement::Labeled { .. } => None,
        };
        let Some(surface) = surface else {
            continue;
        };
        let lowered = requirement_propositions(
            std::slice::from_ref(requirement),
            parsed_function.parameters(),
            &arguments,
            state.memory(),
            predicate_environment,
            click_function_environment,
        )?;
        if let [kernel] = lowered.as_slice() {
            surface_propositions.record_lowering(&surface, kernel)?;
        }
    }
    requirement_pure_facts = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_pure_facts,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    let include_owned_composite_cores = function_block
        .structural_clauses()
        .iter()
        .any(|clause| matches!(clause.region(), CodeRegion::Loop(_)));
    state = project_initial_composite_resource_cores(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &requirement_pure_facts,
        claim_label,
        include_owned_composite_cores,
    )?;
    requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        &state,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement.inner() else {
            continue;
        };
        record_initial_composite_surface_facts(
            resource_environment,
            resource,
            parsed_function.parameters(),
            &arguments,
            &state,
            &requirement_pure_facts,
            &mut surface_propositions,
            predicate_environment,
            click_function_environment,
            &mut BTreeSet::new(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed while recording resource facts: {message}"
            ))
        })?;
    }
    Ok((
        state,
        arguments,
        requirement_pure_facts,
        surface_propositions,
    ))
}

fn canonical_claim_caller_state(
    state: CState,
    has_verified_loops: bool,
    function: &CFunction,
    arguments: &[CExpression],
    pure_facts: &[Proposition],
    claim_label: &str,
) -> Result<CState, ClickError> {
    if !has_verified_loops {
        return Ok(state);
    }
    let entry = c_function_contract_entry_state(
        &state,
        function,
        arguments,
        &assumptions_from_propositions(pure_facts),
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` {message}")))?;
    Ok(state.with_resource_context(entry.resources().clone()))
}

pub(super) fn prove_claim_by_auto(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut loop_verification_error = None;
    for tactics in auto_loop_verification_tactic_candidates(function_block, claim) {
        match prove_claim_by_tactics(
            source_path,
            function_block,
            parsed_function,
            claim,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            &tactics,
            ProofTacticSource::GeneratedBy { source_index: 0 },
        ) {
            Ok(mut theorems) => {
                if let Err(error) = certify_auto_claim_result(
                    source_path,
                    function_block,
                    parsed_function,
                    claim,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    &theorems,
                ) {
                    loop_verification_error = Some(error);
                    continue;
                }
                for theorem in &mut theorems {
                    theorem.proof_kind = ProofKind::LoopVerification;
                }
                return Ok(theorems);
            }
            Err(error) => loop_verification_error = Some(error),
        }
    }

    let mut bounded_error = None;
    let mut bounded_certificate_error = None;
    for tactics in bounded_execution_tactic_candidates(claim) {
        match prove_claim_by_tactics(
            source_path,
            function_block,
            parsed_function,
            claim,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            &tactics,
            ProofTacticSource::GeneratedBy { source_index: 0 },
        ) {
            Ok(theorems) => {
                if let Err(error) = certify_auto_claim_result(
                    source_path,
                    function_block,
                    parsed_function,
                    claim,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    &theorems,
                ) {
                    bounded_certificate_error.get_or_insert(error);
                    continue;
                }
                return Ok(theorems);
            }
            Err(error) => bounded_error = Some(error),
        }
    }
    Err(bounded_certificate_error
        .or(loop_verification_error)
        .or(bounded_error)
        .unwrap_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}`: `auto` had no certificate candidate to try"
            ))
        }))
}

#[allow(clippy::too_many_arguments)]
fn certify_auto_claim_result(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    verified: &[VerifiedCTheorem],
) -> Result<(), ClickError> {
    let certificate = verified
        .first()
        .ok_or_else(|| ClickError::new(format!("`auto` proved no paths for `{claim_label}`")))?
        .expanded_proof_certificate()
        .map_err(|error| {
            ClickError::new(format!(
                "`auto` succeeded internally for `{claim_label}` without a surface certificate: {}",
                error.message()
            ))
        })?;
    let replayed = prove_claim_by_tactics(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        certificate.tactics(),
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`auto` surface certificate failed complete replay for `{claim_label}`:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    if replayed.len() != verified.len() {
        return Err(ClickError::new(format!(
            "`auto` surface certificate replayed {} paths for `{claim_label}`, expected {}",
            replayed.len(),
            verified.len()
        )));
    }
    Ok(())
}

pub(super) fn prove_claim_by_frame(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
        return Err(ClickError::new(format!(
            "`frame` only proves effect clauses for `{claim_label}`; use `by auto;` or `by simp;` for postconditions"
        )));
    }

    let tactics = [ProofTactic::ExecuteRest, ProofTactic::ContextualFrame];
    let mut theorems = prove_claim_by_tactics(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    for theorem in &mut theorems {
        theorem.proof_kind = ProofKind::Frame;
    }
    Ok(theorems)
}

pub(super) fn prove_claim_by_simp(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if matches!(claim, FunctionClaimRef::Effect(_, _)) {
        return Err(ClickError::new(format!(
            "`simp` does not prove effect clauses for `{claim_label}`; use `by frame;` or `by auto;`"
        )));
    }
    if count_loops(parsed_function.body()) != 0 {
        return Err(ClickError::new(format!(
            "`simp` does not prove loop-backed claims for `{claim_label}`; use `by auto;`"
        )));
    }

    let tactics = [ProofTactic::ExecuteRest, ProofTactic::Simp];
    let mut theorems = prove_claim_by_tactics(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    for theorem in &mut theorems {
        theorem.proof_kind = ProofKind::Simp;
    }
    Ok(theorems)
}

/// Identifies the `close_invariants` step of a replayed certificate well
/// enough to emit a `click timing:` line for the work its caller does on its
/// behalf: the same claim-relative indices `replay_linear_tactics` would use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct InvariantCloserStep {
    tactic_index: usize,
    source_index: usize,
    statement_index: usize,
}

#[derive(Clone, Default)]
struct TacticReplayState {
    proof_site: Option<ProofSite>,
    loop_effect_goal: Option<LoopEffectReplayGoal>,
    frontier: ExecutionFrontier,
    source_layout: SourceExecutionLayout,
    program_point_states: ProgramPointStates,
    frames: BTreeSet<Option<CodeRegionRef>>,
    unfolded_predicates: Vec<String>,
    post_execution_tactics: Vec<DeferredPostExecutionTactic>,
    region_simp: Option<(usize, usize)>,
    region_invariants_closed: bool,
    /// Where the replayed `close_invariants` tactic sat, so the invariant
    /// bundle check its caller performs after the replay finishes can be
    /// timed against that tactic's own identity instead of going unattributed.
    ///
    /// `close_invariants` only records the intent during replay; the kernel
    /// re-derivation that gives it meaning runs in
    /// `verify_one_loop_preservation_proof` once the whole certificate has
    /// replayed. Without this the dominant cost of the loop-invariant bundle
    /// carries no class tag at all (`git history (profiler coverage, 2026-07-31)`).
    invariant_closer_step: Option<InvariantCloserStep>,
    case_assumptions: Vec<ReplayCaseAssumption>,
    effect_facts: Vec<ExecutionPureFact>,
    region_proof: bool,
    loop_invariant_region: bool,
    ordered_finalization: bool,
    grouped_contract: bool,
    next_opaque_call: u64,
    next_verification_variable: u64,
    next_path_choice: usize,
    execution_start_facts: Vec<Proposition>,
    /// The snapshot that `old(...)` — and `at(function.entry, ...)`, which is
    /// the same reference under another spelling — names in this region.
    ///
    /// `old` denotes function entry, but certificate replay used to resolve it
    /// *positionally*, to whichever state the enclosing proof region started
    /// from. Inside a function-body proof those coincide; inside a
    /// loop-preservation region they do not, so the same surface text meant
    /// loop-entry memory here and function-entry memory in the Click -> Spec
    /// lowering the kernel certified against. Naming the state explicitly is
    /// what makes the two agree; see
    /// `docs/advanced/memory-dag.md` (stage 2a).
    ///
    /// `None` keeps the previous positional resolution, so every region that
    /// does not record a function-entry snapshot behaves exactly as before.
    function_entry_state: Option<CState>,
    concrete_loop_execution: bool,
    /// The execution frontier was intentionally replaced by an `advance`
    /// interface. Its state is a specification abstraction, not an exact
    /// symbolic body outcome; whole-function kernel certification checks every
    /// concrete path before any contract claim is exported.
    execution_abstraction: bool,
    planned_tactics: Vec<ProofTactic>,
    surface_propositions: SurfacePropositionMap,
    surface_replay: SurfaceReplay,
    deferred_tactic_capture: Option<DeferredTacticCapture>,
}

#[derive(Clone)]
struct LoopEffectReplayGoal {
    before_state: CState,
    check: CLoopEffectCheck,
    closed: bool,
}

#[derive(Clone)]
struct ReplayCaseAssumption {
    tactic_index: usize,
    condition: ClickProposition,
    value: bool,
    fact: Option<Proposition>,
}

#[derive(Clone, Default)]
struct SurfaceReplay {
    tactics: Vec<ProofTactic>,
    blocker: Option<String>,
    last_step_entry: Option<ProgramPointRef>,
    path_choices: Vec<SurfacePathChoice>,
}

#[derive(Clone)]
struct DeferredTacticCapture {
    tactic_index: usize,
    branch_skeleton: Vec<ProofTactic>,
}

struct TacticExpansionProbe {
    site: ProofSite,
    source_index: Option<usize>,
    active: bool,
    result: Option<Result<Vec<ProofTactic>, String>>,
}

thread_local! {
    static TACTIC_EXPANSION_PROBE: std::cell::RefCell<Option<TacticExpansionProbe>> =
        const { std::cell::RefCell::new(None) };
    static SUPPRESS_TACTIC_EXPANSION_CAPTURE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

pub(super) fn capture_c0_tactic_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
    source_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        if probe.is_some() {
            return Err(ClickError::new(
                "cannot nest selected-tactic expansion requests",
            ));
        }
        *probe = Some(TacticExpansionProbe {
            site: site.clone(),
            source_index: Some(source_index),
            active: false,
            result: None,
        });
        Ok(())
    })?;

    let verification = verify_c0_sources(click_source, c_sources);
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow_mut().take());
    let Some(captured) = captured else {
        return Err(ClickError::new("selected-tactic expansion probe was lost"));
    };
    if let Some(result) = captured.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) if !error.is_expansion_complete() => Err(error),
        Err(_) => Err(ClickError::new(
            "selected tactic completed without recording an expansion",
        )),
        Ok(_) => Err(ClickError::new(format!(
            "selected {} proof has no source tactic {source_index}",
            site.description()
        ))),
    }
}

pub(super) fn active_c0_tactic_expansion_request() -> Option<(ProofSite, Option<usize>)> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .map(|probe| (probe.site.clone(), probe.source_index))
    })
}

pub(super) fn capture_c0_proof_site_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        if probe.is_some() {
            return Err(ClickError::new(
                "cannot nest selected-proof expansion requests",
            ));
        }
        *probe = Some(TacticExpansionProbe {
            site: site.clone(),
            source_index: None,
            active: false,
            result: None,
        });
        Ok(())
    })?;

    let verification = verify_c0_sources(click_source, c_sources);
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow_mut().take());
    let Some(captured) = captured else {
        return Err(ClickError::new("selected-proof expansion probe was lost"));
    };
    if let Some(result) = captured.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) if !error.is_expansion_complete() => Err(error),
        Err(_) => Err(ClickError::new(
            "selected proof completed without recording an expansion",
        )),
        Ok(_) => Err(ClickError::new(format!(
            "verification did not retain a certificate for {}",
            site.description()
        ))),
    }
}

fn finish_proof_site_expansion_capture(
    site: &ProofSite,
    certificate: &TacticCertificate,
) -> Result<(), ClickError> {
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return false;
        };
        if probe.site != *site || probe.source_index.is_some() {
            return false;
        }
        probe.active = true;
        probe.result = Some(Ok(certificate.tactics().to_vec()));
        true
    });
    if captured {
        Err(ClickError::expansion_complete())
    } else {
        Ok(())
    }
}

fn record_proof_site_tactic_expansion(
    site: &ProofSite,
    source_index: usize,
    tactics: &[ProofTactic],
) {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return;
        };
        if probe.site != *site || probe.source_index != Some(source_index) {
            return;
        }
        probe.active = true;
        match &mut probe.result {
            None => probe.result = Some(Ok(tactics.to_vec())),
            Some(Ok(existing)) if existing == tactics => {}
            Some(Ok(_)) => {
                probe.result = Some(Err(
                    "selected tactic expands differently across proof obligations".to_string(),
                ));
            }
            Some(Err(_)) => {}
        }
    });
}

fn selected_tactic_index_for_site(site: &ProofSite) -> Option<usize> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .filter(|probe| probe.site == *site)
            .and_then(|probe| probe.source_index)
    })
}

fn proof_site_for_claims(
    function_block: &FunctionBlock,
    claims: &[FunctionClaimRef<'_>],
    grouped_contract: bool,
) -> Option<ProofSite> {
    let claim = if grouped_contract {
        CProofClaim::Grouped
    } else {
        match claims {
            [FunctionClaimRef::Ensure(index, _)] => CProofClaim::Ensure(*index),
            [FunctionClaimRef::Effect(index, _)] => CProofClaim::Effect(*index),
            _ => return None,
        }
    };
    Some(ProofSite::FunctionClaim {
        function_name: function_block.signature().name().to_string(),
        claim,
    })
}

/// Begins a selected-tactic capture when the probe matches this tactic.
/// Returns the branch skeleton of the surface tactics recorded so far
/// (computed before the surface replay is reset), or `None` when no capture
/// begins. The skeleton is only materialized on the single capturing
/// iteration, keeping ordinary verification free of that per-tactic cost.
fn begin_tactic_expansion_capture(
    source_index: usize,
    _tactic: &ProofTactic,
    replay: &mut TacticReplayState,
) -> Option<Vec<ProofTactic>> {
    if SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(std::cell::Cell::get) {
        return None;
    }
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let probe = slot.as_mut()?;
        if probe.active
            || probe.source_index != Some(source_index)
            || replay.proof_site.as_ref() != Some(&probe.site)
        {
            return None;
        }
        probe.active = true;
        let branch_skeleton = surface_branch_skeleton(&replay.surface_replay.tactics);
        let last_step_entry = replay.surface_replay.last_step_entry.clone();
        replay.surface_replay = SurfaceReplay {
            last_step_entry,
            ..SurfaceReplay::default()
        };
        Some(branch_skeleton)
    })
}

/// `allow_empty` accepts an empty expansion as the exact answer: the selected
/// tactic contributed no surface tactics to the accepted certificate, so the
/// rewrite removes it. Every other caller keeps the empty guard — for them an
/// empty capture means the lowering lost the tactics, not that none exist.
fn finish_tactic_expansion_capture(
    surface_replay: &SurfaceReplay,
    allow_empty: bool,
) -> ClickError {
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return false;
        };
        probe.result = Some(match &surface_replay.blocker {
            Some(blocker) => Err(format!("could not expand selected tactic: {blocker}")),
            None if surface_replay.tactics.is_empty() && !allow_empty => {
                Err("selected tactic produced no standalone surface expansion".to_string())
            }
            None => Ok(surface_replay.tactics.clone()),
        });
        true
    });
    if !captured {
        return ClickError::new(
            "could not expand the selected tactic: the expansion probe was no longer active",
        );
    }
    ClickError::expansion_complete()
}

fn tactic_expansion_capture_is_active() -> bool {
    TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow().as_ref().is_some_and(|probe| probe.active))
}

fn tactic_expansion_capture_matches(site: Option<&ProofSite>, source_index: usize) -> bool {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe.borrow().as_ref().is_some_and(|probe| {
            probe.active && site == Some(&probe.site) && probe.source_index == Some(source_index)
        })
    })
}

#[derive(Clone)]
struct SurfacePathChoice {
    occurrence: usize,
    condition: ClickProposition,
    value: bool,
    tactic_offset: usize,
}

impl SurfaceReplay {
    fn push(&mut self, tactic: ProofTactic) {
        if self.blocker.is_none() {
            append_surface_tactic_to_leaves(&mut self.tactics, tactic);
        }
    }

    fn block(&mut self, message: impl Into<String>) {
        if self.blocker.is_none() {
            self.blocker = Some(message.into());
            self.tactics.clear();
            self.path_choices.clear();
        }
    }
}

fn record_post_execution_surface_tactic(
    path_tactics: &mut Vec<ProofTactic>,
    capture_tactics: &mut Vec<ProofTactic>,
    deferred_capture: Option<&DeferredTacticCapture>,
    tactic_index: usize,
    tactic: ProofTactic,
) {
    if deferred_capture.is_some_and(|capture| capture.tactic_index == tactic_index) {
        capture_tactics.push(tactic.clone());
    }
    path_tactics.push(tactic);
}

fn append_surface_tactic_to_leaves(tactics: &mut Vec<ProofTactic>, tactic: ProofTactic) {
    if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
        append_surface_tactic_to_leaves(&mut proof_if.then_tactics, tactic.clone());
        append_surface_tactic_to_leaves(&mut proof_if.else_tactics, tactic);
    } else {
        tactics.push(tactic);
    }
}

fn append_surface_tactics_by_leaf(
    tactics: &mut Vec<ProofTactic>,
    path_tactics: &[Vec<ProofTactic>],
) -> Result<(), String> {
    fn append(
        tactics: &mut Vec<ProofTactic>,
        path_tactics: &[Vec<ProofTactic>],
        next_path: &mut usize,
    ) {
        if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
            append(&mut proof_if.then_tactics, path_tactics, next_path);
            append(&mut proof_if.else_tactics, path_tactics, next_path);
        } else if let Some(suffix) = path_tactics.get(*next_path) {
            tactics.extend(suffix.iter().cloned());
            *next_path += 1;
        }
    }

    let mut next_path = 0;
    append(tactics, path_tactics, &mut next_path);
    if next_path == path_tactics.len() {
        Ok(())
    } else {
        Err(format!(
            "surface proof has {next_path} leaves but frame certificate has {} paths",
            path_tactics.len()
        ))
    }
}

fn surface_branch_skeleton(tactics: &[ProofTactic]) -> Vec<ProofTactic> {
    let Some(proof_if) = tactics.iter().rev().find_map(|tactic| match tactic {
        ProofTactic::If(proof_if) => Some(proof_if),
        _ => None,
    }) else {
        return Vec::new();
    };
    vec![ProofTactic::If(ProofIf {
        condition: proof_if.condition.clone(),
        then_tactics: surface_branch_skeleton(&proof_if.then_tactics),
        else_tactics: surface_branch_skeleton(&proof_if.else_tactics),
    })]
}

fn synthesize_surface_alternatives(paths: Vec<SurfaceReplay>) -> Result<Vec<ProofTactic>, String> {
    if paths.is_empty() {
        return Err("certified alternatives contained no paths".to_string());
    }
    if let Some(blocker) = paths.iter().find_map(|path| path.blocker.clone()) {
        return Err(blocker);
    }
    synthesize_surface_paths(paths)
}

fn synthesize_surface_paths(paths: Vec<SurfaceReplay>) -> Result<Vec<ProofTactic>, String> {
    if paths.len() == 1 {
        return Ok(paths.into_iter().next().unwrap().tactics);
    }
    let first_choice = paths
        .first()
        .and_then(|path| path.path_choices.first())
        .ok_or_else(|| "distinct certified paths have no surface branch condition".to_string())?
        .clone();
    let prefix = paths[0]
        .tactics
        .get(..first_choice.tactic_offset)
        .ok_or_else(|| "surface branch offset exceeds its tactic trace".to_string())?
        .to_vec();

    let mut then_paths = Vec::new();
    let mut else_paths = Vec::new();
    for mut path in paths {
        let choice = path
            .path_choices
            .first()
            .ok_or_else(|| "only some certified paths contain a branch condition".to_string())?
            .clone();
        if choice.occurrence != first_choice.occurrence
            || choice.condition != first_choice.condition
            || choice.tactic_offset != first_choice.tactic_offset
            || path.tactics.get(..choice.tactic_offset) != Some(prefix.as_slice())
        {
            return Err("certified paths do not share one branch prefix".to_string());
        }
        path.tactics.drain(..choice.tactic_offset);
        path.path_choices.remove(0);
        for remaining in &mut path.path_choices {
            remaining.tactic_offset -= choice.tactic_offset;
        }
        if choice.value {
            then_paths.push(path);
        } else {
            else_paths.push(path);
        }
    }

    if then_paths.is_empty() {
        let mut tactics = prefix;
        tactics.extend(synthesize_surface_paths(else_paths)?);
        return Ok(tactics);
    }
    if else_paths.is_empty() {
        let mut tactics = prefix;
        tactics.extend(synthesize_surface_paths(then_paths)?);
        return Ok(tactics);
    }

    let mut tactics = prefix;
    tactics.push(ProofTactic::If(ProofIf {
        condition: first_choice.condition,
        then_tactics: synthesize_surface_paths(then_paths)?,
        else_tactics: synthesize_surface_paths(else_paths)?,
    }));
    Ok(tactics)
}

#[derive(Clone)]
enum PostExecutionTactic {
    Fold(ResourceClause),
    UnfoldPredicate(String),
    Apply(TheoremApplication),
    ApplyUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    Have(ProofHave),
    Transport {
        source: ClickProposition,
        target: ClickProposition,
        premises: Option<Vec<ClickProposition>>,
    },
    Choose(ProofChoice),
    Witness(ProofWitness),
    Assumption,
    Normalize,
    Rewrite(ClickProposition),
    FrameRegion(CodeRegionRef),
    Frame,
    CertifiedFrame(Vec<Vec<PropositionDerivation>>),
    Simp,
}

#[derive(Clone)]
struct DeferredPostExecutionTactic {
    tactic_index: usize,
    source_index: usize,
    tactic: PostExecutionTactic,
}

impl TacticReplayState {
    fn defer_post_execution(
        &mut self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
    ) {
        self.post_execution_tactics
            .push(DeferredPostExecutionTactic {
                tactic_index,
                source_index,
                tactic,
            });
    }
}

fn post_execution_tactic_timing(post_tactic: &PostExecutionTactic) -> (&'static str, &'static str) {
    match post_tactic {
        PostExecutionTactic::Apply(_) => ("apply", "smart"),
        PostExecutionTactic::Have(have) => (
            "have",
            if smart_simp_unfold_prefix(&have.proof).is_some() {
                "smart"
            } else {
                "simple"
            },
        ),
        PostExecutionTactic::Transport { premises, .. } => (
            "transport",
            if premises.is_some() {
                "simple"
            } else {
                "smart"
            },
        ),
        PostExecutionTactic::Simp => ("simp", "smart"),
        PostExecutionTactic::Fold(_) => ("fold", "simple"),
        PostExecutionTactic::UnfoldPredicate(_) => ("unfold", "simple"),
        PostExecutionTactic::ApplyUsing { .. } => ("apply", "simple"),
        PostExecutionTactic::Choose(_) => ("choose", "simple"),
        PostExecutionTactic::Witness(_) => ("witness", "simple"),
        PostExecutionTactic::Assumption => ("assumption", "simple"),
        PostExecutionTactic::Normalize => ("normalize", "simple"),
        PostExecutionTactic::Rewrite(_) => ("rewrite", "simple"),
        PostExecutionTactic::FrameRegion(_) => ("frame", "simple"),
        PostExecutionTactic::Frame => ("frame", "simple"),
        PostExecutionTactic::CertifiedFrame(_) => ("certified_frame", "simple"),
    }
}

#[derive(Clone, Default)]
struct ExecutionFrontier {
    point: ProofExecutionPoint,
    execution_start_state: Option<CState>,
    next_statement_index: usize,
    continuations: Vec<ProofExecutionContinuation>,
}

#[derive(Clone)]
struct ProofExecutionContinuation {
    remaining: Option<CStatement>,
    next_statement_index: usize,
    kind: ProofExecutionContinuationKind,
}

#[derive(Clone, Copy)]
enum ProofExecutionContinuationKind {
    Branch { statement_index: usize },
    LoopIteration,
}

#[derive(Clone, Default)]
enum ProofExecutionPoint {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: CStatement,
    },
    FunctionExit {
        execution: CFunctionExecutionCandidates,
    },
}

#[derive(Clone)]
struct ProofReplayContext {
    state: CState,
    pure_facts: Vec<Proposition>,
    replay: TacticReplayState,
    branch_path: Vec<String>,
}

impl TacticReplayState {
    fn is_at_function_exit(&self) -> bool {
        matches!(
            self.frontier.point,
            ProofExecutionPoint::FunctionExit { .. }
        )
    }

    fn is_at_function_entry(&self) -> bool {
        matches!(self.frontier.point, ProofExecutionPoint::FunctionEntry)
    }

    fn execution(&self) -> Option<&CFunctionExecutionCandidates> {
        match &self.frontier.point {
            ProofExecutionPoint::FunctionEntry | ProofExecutionPoint::StatementEntry { .. } => None,
            ProofExecutionPoint::FunctionExit { execution, .. } => Some(execution),
        }
    }

    fn execution_start_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        self.frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(current_state)
    }

    /// The state that `old(...)` and `at(function.entry, ...)` resolve to when
    /// a contract clause is lowered here.
    ///
    /// This is the one place that answers "which memory does `old` mean", so
    /// the answer is a *named* snapshot rather than whichever state happens to
    /// sit at the enclosing frame's `pre_state` position. When the region
    /// recorded its function-entry snapshot, that snapshot is the answer —
    /// it is the same `CState` the Click -> Spec lowering used as
    /// `SpecMemory::Fixed(entry_memory)` for every `old` operand in this
    /// function's contracts, so both sides name the same interned node.
    ///
    /// Nothing here is trusted on the strength of the naming alone. A lowered
    /// candidate is accepted only by exact equality against the certified
    /// proposition, and a `MemoryLoad` carries its snapshot inside the term,
    /// so a candidate resolved to the wrong state cannot match: selecting the
    /// state by name adds a spelling to search, and the certificate check
    /// remains the thing that validates it.
    ///
    /// Falling back to [`Self::execution_start_state`] keeps every region that
    /// records no function-entry snapshot on its previous behaviour.
    fn old_reference_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        match &self.function_entry_state {
            Some(entry_state) => entry_state,
            None => self.execution_start_state(current_state),
        }
    }
}

impl ExecutionFrontier {
    fn inside_branch(&self) -> bool {
        self.continuations.iter().any(|continuation| {
            matches!(
                continuation.kind,
                ProofExecutionContinuationKind::Branch { .. }
            )
        })
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn verify_loop_execution_proofs(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<CVerifiedLoopRule>, ClickError> {
    let has_structural_proofs = function_block.structural_clauses().iter().any(|clause| {
        matches!(clause.region(), CodeRegion::Loop(_))
            || clause
                .items()
                .iter()
                .any(|item| item.kind() == StructuralItemKind::Assert)
    });
    if !has_structural_proofs {
        return Ok(Vec::new());
    }

    let label = format!("{}.loop_preservation", function_block.signature().name());
    let (initial_state, arguments, requirement_facts, surface_propositions) =
        initial_claim_context(
            function_block,
            parsed_function,
            resource_environment,
            predicate_environment,
            click_function_environment,
            &label,
        )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &initial_state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;

    let entry_state = c_function_contract_entry_state(
        &initial_state,
        &function,
        &arguments,
        &assumptions_from_propositions(&requirement_facts),
    )
    .map_err(|message| ClickError::new(format!("`{label}` {message}")))?;
    let environment = ExecutionProofEnvironment {
        initial_state: &initial_state,
        function_block,
        parsed_function,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function: &function,
        arguments: &arguments,
        surface_propositions: &surface_propositions,
    };
    let mut verified_loop_rules = Vec::new();
    let mut next_loop_index = 0;
    verify_execution_proofs_forward(
        function.body(),
        vec![ExecutionProofContext {
            state: entry_state,
            pure_facts: requirement_facts,
            surface_propositions: surface_propositions.clone(),
            program_point_states: ProgramPointStates::new(),
            case_path: Vec::new(),
            next_opaque_call: 0,
            next_verification_variable: 0,
        }],
        &mut next_loop_index,
        &environment,
        &mut verified_loop_rules,
    )?;
    Ok(verified_loop_rules)
}

fn explicit_loop_preservation_tactics(clause: &StructuralClause) -> Option<&[ProofTactic]> {
    let Proof::Script(tactics) = clause.preserve_proof()? else {
        return None;
    };
    (!tactics
        .iter()
        .all(|tactic| matches!(tactic, ProofTactic::UnfoldPredicate(_))))
    .then_some(tactics)
}

struct ExecutionProofEnvironment<'a> {
    initial_state: &'a CState,
    function_block: &'a FunctionBlock,
    parsed_function: &'a syntax::C0Function,
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a CFunction,
    arguments: &'a [CExpression],
    surface_propositions: &'a SurfacePropositionMap,
}

#[derive(Clone)]
struct ExecutionProofContext {
    state: CState,
    pure_facts: Vec<Proposition>,
    surface_propositions: SurfacePropositionMap,
    program_point_states: ProgramPointStates,
    case_path: Vec<ProofCaseChoice>,
    next_opaque_call: u64,
    next_verification_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProofCaseChoice {
    condition: ClickProposition,
    value: bool,
}

#[derive(Clone)]
struct PathCertificate {
    case_path: Vec<ProofCaseChoice>,
    certificate: TacticCertificate,
}

fn merge_path_aligned_certificates(
    claim_label: &str,
    paths: Vec<PathCertificate>,
) -> Result<TacticCertificate, ClickError> {
    fn merge(
        claim_label: &str,
        mut paths: Vec<PathCertificate>,
    ) -> Result<TacticCertificate, ClickError> {
        let first = paths.first().ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` path-aligned certificate has no paths"
            ))
        })?;
        if paths
            .iter()
            .all(|path| path.certificate == first.certificate)
        {
            return Ok(first.certificate.clone());
        }
        while paths.iter().all(|path| {
            path.case_path.first() == paths.first().and_then(|first| first.case_path.first())
        }) && paths
            .first()
            .is_some_and(|first| !first.case_path.is_empty())
        {
            for path in &mut paths {
                path.case_path.remove(0);
            }
        }
        if paths.iter().any(|path| path.case_path.is_empty()) {
            return Err(ClickError::new(format!(
                "`{claim_label}` path-aligned certificates disagree after one proof path has already joined"
            )));
        }
        let condition = paths[0].case_path[0].condition.clone();
        if paths
            .iter()
            .any(|path| path.case_path[0].condition != condition)
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` path-aligned certificates have incompatible next branch conditions"
            )));
        }
        let mut then_paths = Vec::new();
        let mut else_paths = Vec::new();
        for mut path in paths {
            let choice = path.case_path.remove(0);
            if choice.value {
                then_paths.push(path);
            } else {
                else_paths.push(path);
            }
        }
        if then_paths.is_empty() || else_paths.is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` path-aligned certificate is missing one branch of `{}`",
                describe_click_proposition(&condition)
            )));
        }
        let then_certificate = merge(claim_label, then_paths)?;
        let else_certificate = merge(claim_label, else_paths)?;
        TacticCertificate::from_proof_tactics(&[ProofTactic::If(ProofIf {
            condition,
            then_tactics: then_certificate.tactics().to_vec(),
            else_tactics: else_certificate.tactics().to_vec(),
        })])
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` merged an invalid path-aligned certificate: {error:?}"
            ))
        })
    }

    let mut unique = Vec::<PathCertificate>::new();
    for path in paths {
        if let Some(existing) = unique
            .iter()
            .find(|existing| existing.case_path == path.case_path)
        {
            if existing.certificate != path.certificate {
                return Err(ClickError::new(format!(
                    "`{claim_label}` produced different certificates for the same proof path"
                )));
            }
        } else {
            unique.push(path);
        }
    }
    merge(claim_label, unique)
}

fn certificate_leaf_for_case_path(
    claim_label: &str,
    tactics: &[ProofTactic],
    case_path: &[ProofCaseChoice],
) -> Result<TacticCertificate, ClickError> {
    fn select(
        claim_label: &str,
        tactics: &[ProofTactic],
        case_path: &[ProofCaseChoice],
        next_case: &mut usize,
        selected: &mut Vec<ProofTactic>,
    ) -> Result<(), ClickError> {
        for tactic in tactics {
            let ProofTactic::If(proof_if) = tactic else {
                selected.push(tactic.clone());
                continue;
            };
            let choice = case_path.get(*next_case).ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` surface certificate has more branches than its replay path"
                ))
            })?;
            if choice.condition != proof_if.condition {
                return Err(ClickError::new(format!(
                    "`{claim_label}` surface certificate branch condition does not match its replay path"
                )));
            }
            *next_case += 1;
            select(
                claim_label,
                if choice.value {
                    &proof_if.then_tactics
                } else {
                    &proof_if.else_tactics
                },
                case_path,
                next_case,
                selected,
            )?;
        }
        Ok(())
    }

    let mut next_case = 0;
    let mut selected = Vec::new();
    select(
        claim_label,
        tactics,
        case_path,
        &mut next_case,
        &mut selected,
    )?;
    TacticCertificate::from_proof_tactics(&selected).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` selected a non-surface certificate leaf: {error:?}"
        ))
    })
}

#[derive(Clone)]
struct CertifiedConditionTransition {
    is_true: bool,
    pure_facts: Vec<Proposition>,
    path_facts: Vec<Proposition>,
    theorem: Theorem,
    prerequisite_derivations: Vec<PropositionDerivation>,
    planning_exact_premises: Vec<Proposition>,
}

fn append_statement_transition_certificate(
    replay: &mut TacticReplayState,
    transition: &CertifiedStatementTransition,
    loop_step_policy: LoopStepPolicy,
) {
    replay.planned_tactics.push(match loop_step_policy {
        LoopStepPolicy::EnterBody => {
            ProofTactic::CertifiedStatementReplay(Box::new(CertifiedStatementReplay {
                transition: transition.clone(),
                next_opaque_call: replay.next_opaque_call,
                next_verification_variable: replay.next_verification_variable,
            }))
        }
        LoopStepPolicy::ApplyVerifiedRule => {
            ProofTactic::CertifiedLoopSummaryReplay(Box::new(CertifiedStatementReplay {
                transition: transition.clone(),
                next_opaque_call: replay.next_opaque_call,
                next_verification_variable: replay.next_verification_variable,
            }))
        }
    });
    // Facts produced by the statement are not available until the certified
    // statement replay has run. Their transports are checked as part of that
    // replay; only facts that existed at statement entry need separate
    // transport tactics.
    let external_transports = transition
        .fact_transports
        .iter()
        .filter(|transport| {
            !transport.statement_local
                && normalize_direct_atomic_memory_loads(&transport.source)
                    != normalize_direct_atomic_memory_loads(&transport.target)
        })
        .collect::<Vec<_>>();
    replay
        .planned_tactics
        .extend(
            external_transports
                .iter()
                .map(|transport| ProofTactic::CertifiedFactTransport {
                    source: transport.source.clone(),
                    target: transport.target.clone(),
                    theorem: transport.theorem.clone(),
                }),
        );
    if !external_transports.is_empty() {
        replay
            .planned_tactics
            .push(ProofTactic::FinishCertifiedFactTransports(
                external_transports
                    .iter()
                    .map(|transport| transport.source.clone())
                    .collect(),
            ));
    }
}

fn theorem_implication_premises(theorem: &Theorem) -> Vec<Proposition> {
    let mut proposition = theorem.proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proposition {
        premises.push(premise.as_ref().clone());
        proposition = body;
    }
    premises
}

fn append_condition_transition_certificate(
    replay: &mut TacticReplayState,
    transition: &CertifiedConditionTransition,
    include_path_fact: bool,
) {
    let mut exact_premises = if include_path_fact {
        theorem_implication_premises(&transition.theorem)
    } else {
        Vec::new()
    };
    for premise in &transition.planning_exact_premises {
        if !exact_premises.contains(premise) {
            exact_premises.push(premise.clone());
        }
    }
    if include_path_fact {
        for fact in &transition.path_facts {
            if !exact_premises.contains(fact) {
                exact_premises.push(fact.clone());
            }
        }
    }
    replay
        .planned_tactics
        .push(ProofTactic::CertifiedStatementStep {
            prerequisite_derivations: transition.prerequisite_derivations.clone(),
            exact_premises,
        });
}

fn surface_c_condition(condition: &CExpression) -> ClickProposition {
    fn expression(expression: &CExpression) -> ContractExpression {
        substitute_c_fragment_as_contract(expression, &BTreeMap::new())
            .expect("converting a C expression without substitutions cannot fail")
    }

    let comparison = |left: &CExpression, operator: ComparisonOperator, right: &CExpression| {
        ClickProposition::Comparison {
            left: expression(left),
            operator,
            right: expression(right),
        }
    };
    match condition {
        CExpression::Equal(left, right) => comparison(left, ComparisonOperator::Equal, right),
        CExpression::NotEqual(left, right) => comparison(left, ComparisonOperator::NotEqual, right),
        CExpression::LessThan(left, right) => comparison(left, ComparisonOperator::LessThan, right),
        CExpression::LessEqual(left, right) => {
            comparison(left, ComparisonOperator::LessEqual, right)
        }
        CExpression::GreaterThan(left, right) => {
            comparison(left, ComparisonOperator::GreaterThan, right)
        }
        CExpression::GreaterEqual(left, right) => {
            comparison(left, ComparisonOperator::GreaterEqual, right)
        }
        CExpression::Not(body) => ClickProposition::Not(Box::new(surface_c_condition(body))),
        CExpression::And(left, right) => ClickProposition::And(
            Box::new(surface_c_condition(left)),
            Box::new(surface_c_condition(right)),
        ),
        CExpression::Or(left, right) => ClickProposition::Or(
            Box::new(surface_c_condition(left)),
            Box::new(surface_c_condition(right)),
        ),
        condition => ClickProposition::Comparison {
            left: expression(condition),
            operator: ComparisonOperator::NotEqual,
            right: expression(&CExpression::Value(int32(0))),
        },
    }
}

#[derive(Clone, Copy)]
pub(super) enum StatementPrerequisitePolicy {
    Exact,
    Explicit,
    Certified,
    Contextual,
    Planning,
}

#[derive(Clone, Copy)]
pub(super) enum StatementFactTransportPolicy {
    None,
    Selected,
    Automatic,
}

#[derive(Clone, Copy)]
enum LoopStepPolicy {
    EnterBody,
    ApplyVerifiedRule,
}

#[derive(Clone, Copy)]
enum BranchStepPolicy {
    RequireProven,
    Explore,
}

fn exact_fact_is_available(required: &Proposition, available: &[Proposition]) -> bool {
    exact_fact_is_available_across_effects(required, available, &[])
}

/// Availability where the required spelling may have been lowered at a later
/// program point than the available one: `framing` supplies the recorded
/// memory-effect facts that let the kernel see the two snapshots agree at the
/// loaded pointers.
///
/// `framing` never contributes a fact of its own — candidates come only from
/// `available` — so this cannot make an unestablished premise available.
fn exact_fact_is_available_across_effects(
    required: &Proposition,
    available: &[Proposition],
    framing: &[ExecutionPureFact],
) -> bool {
    available
        .iter()
        .any(|fact| exact_fact_contains_conjunct(fact, required))
        || snapshot_bridged_fact_is_available(required, available, framing)
}

/// Second chance for a required condition that failed exact matching only
/// because its load atoms carry different memory snapshots than the available
/// spelling — the same fact reached through a different program point.
///
/// The cheap snapshot-blind structural filter picks candidates; the kernel's
/// snapshot-bridging prover decides them under the available facts plus
/// `framing`. Structure must match exactly, so a candidate that survives both
/// is the same fact, not a weaker one. Kept off the hot path: exact matching
/// runs first and assumptions are built only once a candidate exists.
fn snapshot_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    framing: &[ExecutionPureFact],
) -> bool {
    let Some((required_condition, candidates)) = snapshot_blind_candidates(required, available)
    else {
        return false;
    };
    let assumptions = assumptions_from_propositions(available);
    snapshot_bridge_proves(&required_condition, &candidates, assumptions, framing)
}

/// `snapshot_bridged_fact_is_available` where the caller already holds the
/// assumption context the bridge should reason in.
///
/// Candidates still come only from `available`, so widening the assumptions
/// cannot make an unlisted fact available — the wider context only decides
/// whether two spellings denote one fact.
fn snapshot_bridged_fact_is_available_under(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &Assumptions,
    framing: &[ExecutionPureFact],
) -> bool {
    let Some((required_condition, candidates)) = snapshot_blind_candidates(required, available)
    else {
        return false;
    };
    snapshot_bridge_proves(&required_condition, &candidates, assumptions.clone(), framing)
}

/// Normalises `required` and collects the available conjuncts that could be
/// the same condition under a different memory snapshot. `None` when there is
/// nothing to bridge, which keeps the caller off the expensive path.
fn snapshot_blind_candidates(
    required: &Proposition,
    available: &[Proposition],
) -> Option<(ConditionTerm, Vec<ConditionTerm>)> {
    let normalized_required = normalize_direct_atomic_memory_loads(required);
    let Proposition::ConditionIs(required_condition, required_value) = normalized_required else {
        return None;
    };
    let mut candidates = Vec::new();
    for fact in available {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(fact, &mut conjuncts);
        for conjunct in conjuncts {
            if !matches!(conjunct, Proposition::ConditionIs(_, value) if *value == required_value) {
                continue;
            }
            let Proposition::ConditionIs(condition, _) =
                normalize_direct_atomic_memory_loads(conjunct)
            else {
                continue;
            };
            if conditions_equal_ignoring_memories(&condition, &required_condition) {
                candidates.push(condition);
            }
        }
    }
    (!candidates.is_empty()).then_some((required_condition, candidates))
}

fn snapshot_bridge_proves(
    required_condition: &ConditionTerm,
    candidates: &[ConditionTerm],
    assumptions: Assumptions,
    framing: &[ExecutionPureFact],
) -> bool {
    let assumptions = framing.iter().fold(assumptions, |assumptions, fact| {
        assumptions.assume_proposition(fact.proposition().clone())
    });
    candidates.iter().any(|candidate| {
        assumptions.conditions_equal_modulo_proven_snapshots(candidate, required_condition)
    })
}

fn exact_fact_contains_conjunct(fact: &Proposition, required: &Proposition) -> bool {
    condition_polarity_equivalent(fact, required)
        || matches!(fact, Proposition::And(left, right)
            if exact_fact_contains_conjunct(left, required)
                || exact_fact_contains_conjunct(right, required))
}

pub(super) fn condition_polarity_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            matches!(
                (
                    canonical_order_condition(left_condition, *left_value),
                    canonical_order_condition(right_condition, *right_value),
                ),
                (Some(left), Some(right)) if left == right
            )
        }
        (Proposition::Not(negated), Proposition::ConditionIs(right_condition, right_value)) => {
            matches!(
                negated.as_ref(),
                Proposition::ConditionIs(left_condition, left_value)
                    if left_condition == right_condition && left_value != right_value
            )
        }
        (Proposition::ConditionIs(left_condition, left_value), Proposition::Not(negated)) => {
            matches!(
                negated.as_ref(),
                Proposition::ConditionIs(right_condition, right_value)
                    if left_condition == right_condition && left_value != right_value
            )
        }
        _ => false,
    }
}

fn canonical_order_condition(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(right, left), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(right, left), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(right, left), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false)
        | (ConditionTerm::Bitvector32SignedGreaterThan(right, left), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        _ => None,
    }
}

fn quantified_replay_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let required = normalize_direct_atomic_memory_loads(required);
    if !matches!(required, Proposition::ForAll { .. }) {
        return None;
    }
    available.iter().find_map(|fact| {
        let fact = normalize_direct_atomic_memory_loads(fact);
        if !matches!(fact, Proposition::ForAll { .. }) {
            return None;
        }
        let forward = assumptions_from_propositions(std::slice::from_ref(&fact))
            .derive_simp_proposition(&required)
            .is_some();
        let reverse = assumptions_from_propositions(std::slice::from_ref(&required))
            .derive_simp_proposition(&fact)
            .is_some();
        (forward && reverse).then_some(fact)
    })
}

fn quantified_binder_equivalent(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        (
            Proposition::Exists {
                name: left_name,
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::Exists {
                name: right_name,
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_name == right_name
                && left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        _ => false,
    }
}

/// `quantified_binder_equivalent` sees through ONE binder renaming; a nested
/// quantifier needs the rename applied at every level.
///
/// Certificate generation compares a spelling it lowers itself against a fact
/// the drain lowered separately, and the two lowerings mint different binder
/// variables, so a nested `forall` fact is only recognizable up to renaming.
/// This is a generation-side recognizer: it decides which surface spelling to
/// WRITE, never whether a proof is accepted. The written spelling still has to
/// satisfy `derivation.replay` and then the replay judgment itself, both of
/// which instantiate quantifiers rather than compare them structurally.
/// Applies `normalize_direct_atomic_memory_loads` below the propositional
/// connectives and quantifier binders it does not itself descend through, so
/// two lowerings of one fact whose load memories differ only by
/// load-irrelevant blocks or cells (the canonical-load-memory relation)
/// compare equal. Deterministic and assumption-free, like the leaf
/// normalization it delegates to.
fn normalize_quantified_memory_loads(proposition: &Proposition, depth: usize) -> Proposition {
    if depth == 0 {
        return proposition.clone();
    }
    let recurse = |body: &Proposition| Box::new(normalize_quantified_memory_loads(body, depth - 1));
    match proposition {
        Proposition::And(left, right) => Proposition::And(recurse(left), recurse(right)),
        Proposition::Or(left, right) => Proposition::Or(recurse(left), recurse(right)),
        Proposition::Implies(left, right) => Proposition::Implies(recurse(left), recurse(right)),
        Proposition::Not(body) => Proposition::Not(recurse(body)),
        Proposition::ForAll { var, sort, body } => Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: recurse(body),
        },
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: recurse(body),
        },
        other => normalize_direct_atomic_memory_loads(other),
    }
}

/// Generation-side equality up to assumption-free canonical load spelling.
/// A selected spelling still has to replay from its own lowered proposition,
/// so this can broaden candidate recognition without broadening acceptance.
fn propositions_match_up_to_canonical_loads(left: &Proposition, right: &Proposition) -> bool {
    left == right
        || normalize_quantified_memory_loads(left, 64)
            == normalize_quantified_memory_loads(right, 64)
}

/// See the doc comment below: a generation-side recognizer only. Besides the
/// per-level binder renaming, bodies are also compared after canonical-load
/// normalization, because the drain records facts with canonicalized load
/// snapshots while a fresh lowering of the same spelling reads through the
/// retained program-point state, whose memory still carries load-irrelevant
/// local cells.
fn nested_quantified_binder_equivalent(
    left: &Proposition,
    right: &Proposition,
    depth: usize,
) -> bool {
    nested_quantified_binder_equivalent_exact(left, right, depth)
        || nested_quantified_binder_equivalent_exact(
            &normalize_quantified_memory_loads(left, 64),
            &normalize_quantified_memory_loads(right, 64),
            depth,
        )
}

fn nested_quantified_binder_equivalent_exact(
    left: &Proposition,
    right: &Proposition,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    if quantified_binder_equivalent(left, right) {
        return true;
    }
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && nested_quantified_binder_equivalent_exact(
                    &substitute_int32_variable_in_proposition(
                        left_body,
                        *left_var,
                        Bitvector32Term::Variable(*right_var),
                    ),
                    right_body,
                    depth - 1,
                )
        }
        _ => false,
    }
}

fn pure_fact_is_replay_available(required: &Proposition, available: &[Proposition]) -> bool {
    available.contains(required)
        || materialization_equivalent_available_fact(required, available).is_some()
        || available
            .iter()
            .any(|fact| quantified_binder_equivalent(required, fact))
        || quantified_replay_equivalent_available_fact(required, available).is_some()
}

fn atomic_conjuncts<'a>(proposition: &'a Proposition, output: &mut Vec<&'a Proposition>) {
    match proposition {
        Proposition::And(left, right) => {
            atomic_conjuncts(left, output);
            atomic_conjuncts(right, output);
        }
        proposition => output.push(proposition),
    }
}

fn materialization_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    fn matching_conjunct(
        fact: &Proposition,
        required: &Proposition,
        normalized_required: &Proposition,
    ) -> Option<Proposition> {
        if fact == required || normalize_direct_atomic_memory_loads(fact) == *normalized_required {
            return Some(fact.clone());
        }
        let Proposition::And(left, right) = fact else {
            return None;
        };
        matching_conjunct(left, required, normalized_required)
            .or_else(|| matching_conjunct(right, required, normalized_required))
    }

    let normalized_required = normalize_direct_atomic_memory_loads(required);
    available
        .iter()
        .find_map(|fact| matching_conjunct(fact, required, &normalized_required))
}

fn directly_matching_separation_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let Proposition::CResourceSeparate {
        left: required_left,
        right: required_right,
    } = required
    else {
        return None;
    };
    let assumptions = assumptions_from_propositions(available);
    available.iter().find_map(|fact| {
        let Proposition::CResourceSeparate { left, right } = fact else {
            return None;
        };
        let same_orientation = c_resources_directly_match(left, required_left, &assumptions)
            && c_resources_directly_match(right, required_right, &assumptions);
        let reverse_orientation = c_resources_directly_match(left, required_right, &assumptions)
            && c_resources_directly_match(right, required_left, &assumptions);
        (same_orientation || reverse_orientation).then(|| fact.clone())
    })
}

fn directly_covering_loadability_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    matches!(required, Proposition::CMemoryLoadable { .. }).then_some(())?;
    available.iter().find_map(|fact| {
        matches!(fact, Proposition::CMemoryLoadable { .. })
            .then(|| {
                assumptions_from_propositions(std::slice::from_ref(fact))
                    .derive_atomic_proposition(required)
                    .map(|_| fact.clone())
            })
            .flatten()
    })
}

fn proposition_has_contextual_derivation_rules(proposition: &Proposition) -> bool {
    !matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. } | Proposition::CMemoryEffectSummary { .. }
    )
}

fn minimal_proposition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Option<PropositionDerivation> {
    if !proposition_has_contextual_derivation_rules(proposition) {
        return None;
    }
    if matches!(proposition, Proposition::ConditionIs(_, _))
        && let Some(derivation) = bounded_condition_derivation(proposition, available)
    {
        return Some(derivation);
    }
    let derive = |facts: &[Proposition]| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_proposition(proposition)
            .or_else(|| assumptions.derive_simp_proposition(proposition))
    };
    let initial = derive(available)?;
    let mut selected = initial.context_premises().to_vec();
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if derive(&reduced).is_some() {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    derive(&selected)
}

fn minimal_simp_proposition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Option<PropositionDerivation> {
    if !proposition_has_contextual_derivation_rules(proposition) {
        return None;
    }
    let derive = |facts: &[Proposition]| {
        assumptions_from_propositions(facts).derive_simp_proposition(proposition)
    };
    let initial = derive(available)?;
    let mut selected = initial.context_premises().to_vec();
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if derive(&reduced).is_some() {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    derive(&selected)
}

fn bounded_condition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Option<PropositionDerivation> {
    const CANDIDATE_LIMIT: usize = 48;

    let candidates = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .take(CANDIDATE_LIMIT)
        .cloned()
        .collect::<Vec<_>>();
    let derive = |facts: &[Proposition]| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_atomic_proposition(proposition)
            .or_else(|| assumptions.derive_simp_atomic_proposition(proposition))
    };
    for fact in &candidates {
        if let Some(derivation) = derive(std::slice::from_ref(fact)) {
            return Some(derivation);
        }
    }
    for (left_index, left) in candidates.iter().enumerate() {
        for right in &candidates[left_index + 1..] {
            if let Some(derivation) = derive(&[left.clone(), right.clone()]) {
                return Some(derivation);
            }
        }
    }
    None
}

fn derivation_replays_with_materialized_context(
    derivation: &PropositionDerivation,
    available: &[Proposition],
) -> bool {
    let assumptions = assumptions_from_propositions(available);
    if derivation.replay(&assumptions) {
        return true;
    }
    let Some(materialized_context) = derivation
        .context_premises()
        .iter()
        .map(|premise| materialization_equivalent_available_fact(premise, available))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    minimal_proposition_derivation(derivation.conclusion(), &materialized_context).is_some()
}

fn exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    let left = normalize_direct_atomic_memory_loads(left);
    let right = normalize_direct_atomic_memory_loads(right);
    normalized_exact_facts_directly_conflict(&left, &right)
}

fn normalized_exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (Proposition::And(first, second), _) => {
            normalized_exact_facts_directly_conflict(first, right)
                || normalized_exact_facts_directly_conflict(second, right)
        }
        (_, Proposition::And(first, second)) => {
            normalized_exact_facts_directly_conflict(left, first)
                || normalized_exact_facts_directly_conflict(left, second)
        }
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
        }
        _ => false,
    }
}

fn fact_conflicts_with_assumptions(fact: &Proposition, assumptions: &Assumptions) -> bool {
    match fact {
        Proposition::And(left, right) => {
            fact_conflicts_with_assumptions(left, assumptions)
                || fact_conflicts_with_assumptions(right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => assumptions.proves(body),
        fact => assumptions.proves(&Proposition::Not(Box::new(fact.clone()))),
    }
}

fn assumptions_for_direct_fact_transport(propositions: &[Proposition]) -> Assumptions {
    fn collect(proposition: &Proposition, facts: &mut Vec<Proposition>) {
        match proposition {
            Proposition::ConditionIs(_, _)
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CResourceSeparate { .. } => facts.push(proposition.clone()),
            Proposition::And(left, right) => {
                collect(left, facts);
                collect(right, facts);
            }
            _ => {}
        }
    }

    let mut facts = Vec::new();
    for proposition in propositions {
        collect(proposition, &mut facts);
    }
    assumptions_from_propositions(&facts)
}

fn facts_for_direct_surface_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    propositions
        .iter()
        .filter(|proposition| {
            matches!(
                proposition,
                Proposition::CMemoryLoadable { .. }
                    | Proposition::CMemoryCanStore { .. }
                    | Proposition::CMemoryDisjoint { .. }
                    | Proposition::CResourceSeparate { .. }
                    | Proposition::CResourceContains { .. }
                    | Proposition::CMemoryMutatesOnly { .. }
                    | Proposition::CMemoryEffectSummary { .. }
            )
        })
        .cloned()
        .collect()
}

fn facts_for_direct_derivation_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_direct_surface_lowering(propositions);
    for proposition in propositions {
        let direct_condition = matches!(
            proposition,
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
        ) || matches!(proposition, Proposition::ConditionIs(_, _))
            && !c_condition_fact_has_memory(proposition);
        if direct_condition && !facts.contains(proposition) {
            facts.push(proposition.clone());
        }
    }
    facts
}

fn facts_for_smart_have_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_direct_derivation_lowering(propositions);
    for proposition in propositions {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            proposition
        else {
            continue;
        };
        let is_atomic_alias = matches!(
            (left.as_ref(), right.as_ref()),
            (
                Bitvector32Term::MemoryLoad(_, _),
                Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
            ) | (
                Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                Bitvector32Term::MemoryLoad(_, _)
            )
        );
        if is_atomic_alias && !facts.contains(proposition) {
            facts.push(proposition.clone());
        }
    }
    facts
}

fn facts_for_simple_goal_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_smart_have_lowering(propositions);
    for proposition in propositions {
        let include = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(_, _)
                | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                | ConditionTerm::Bitvector32SignedGreaterEqual(_, _)
                | ConditionTerm::PointerOffsetEqual(_, _),
                _,
            ) => true,
            // A false-polarity atomic alias decides branch conditions
            // (`if (p[i] == x)`) whose negative arm the goal's `If` terms
            // still carry; the smart-have set only admits the true polarity.
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), false) => {
                matches!(
                    (left.as_ref(), right.as_ref()),
                    (
                        Bitvector32Term::MemoryLoad(_, _),
                        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
                    ) | (
                        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                        Bitvector32Term::MemoryLoad(_, _)
                    )
                )
            }
            _ => false,
        };
        if include && !facts.contains(proposition) {
            facts.push(proposition.clone());
        }
    }
    facts
}

#[derive(Clone, Copy)]
enum LoopPreservationSource {
    Automatic,
    ExecutionProof,
}

fn certified_condition_transitions(
    state: &CState,
    pure_facts: &[Proposition],
    condition: &CExpression,
    context_label: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    certified_prerequisites: &[PropositionDerivation],
    filter_assumption_conflicts: bool,
) -> Result<Vec<CertifiedConditionTransition>, ClickError> {
    let mut transition_pure_facts = pure_facts.to_vec();
    let planning_assumptions = assumptions_from_propositions(pure_facts);
    let mut assumptions = match prerequisite_policy {
        StatementPrerequisitePolicy::Exact
        | StatementPrerequisitePolicy::Explicit
        | StatementPrerequisitePolicy::Certified
        | StatementPrerequisitePolicy::Contextual => assumptions_from_propositions(pure_facts),
        StatementPrerequisitePolicy::Planning => {
            assumptions_from_propositions(pure_facts).defer_non_exact_loadability_obligations()
        }
    };
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified) {
        for derivation in certified_prerequisites {
            if derivation_replays_with_materialized_context(derivation, pure_facts) {
                assumptions = assumptions.assume_proposition(derivation.conclusion().clone());
                if !transition_pure_facts.contains(derivation.conclusion()) {
                    transition_pure_facts.push(derivation.conclusion().clone());
                }
            }
        }
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
        assumptions = assumptions.defer_non_exact_condition_reasoning();
    } else if matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
    } else if matches!(prerequisite_policy, StatementPrerequisitePolicy::Explicit) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
    }
    let evaluation = prove_symbolic_c_condition_evaluation(
        state.clone(),
        condition.clone(),
        assumptions.clone(),
    );
    if let Some(limit) = evaluation.limit() {
        return Err(ClickError::new(format!(
            "{context_label} hit condition execution limit {limit:?}"
        )));
    }
    evaluation
        .paths()
        .iter()
        .filter(|path| {
            !path.facts().iter().any(|path_fact| {
                pure_facts.iter().any(|available| {
                    exact_facts_directly_conflict(available, path_fact.proposition())
                }) || filter_assumption_conflicts
                    && matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
                    && fact_conflicts_with_assumptions(
                        path_fact.proposition(),
                        &assumptions_from_propositions(pure_facts),
                    )
            })
        })
        .map(|path| {
            let mut successor_facts = transition_pure_facts.clone();
            successor_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let prerequisite_assumptions = assumptions_from_propositions(&successor_facts);
            let mut prerequisite_derivations = Vec::new();
            let mut planning_exact_premises = Vec::new();
            if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
                for path_fact in path.facts() {
                    let proposition = path_fact.proposition();
                    if exact_fact_is_available(proposition, pure_facts) {
                        if !planning_exact_premises.contains(proposition) {
                            planning_exact_premises.push(proposition.clone());
                        }
                        continue;
                    }
                    if matches!(normalize_proposition(proposition), SimpProposition::True) {
                        continue;
                    }
                    if let Some(derivation) =
                        minimal_proposition_derivation(proposition, pure_facts)
                    {
                        if !prerequisite_derivations
                            .iter()
                            .any(|existing: &PropositionDerivation| {
                                existing.conclusion() == derivation.conclusion()
                            })
                        {
                            prerequisite_derivations.push(derivation);
                        }
                        continue;
                    }
                    if planning_assumptions.proves(proposition) {
                        let mut selected = pure_facts.to_vec();
                        let mut index = 0;
                        while index < selected.len() {
                            let mut reduced = selected.clone();
                            reduced.remove(index);
                            if assumptions_from_propositions(&reduced).proves(proposition) {
                                selected = reduced;
                            } else {
                                index += 1;
                            }
                        }
                        for premise in selected {
                            if !planning_exact_premises.contains(&premise) {
                                planning_exact_premises.push(premise);
                            }
                        }
                    }
                }
            }
            for obligation in path.obligations() {
                let derivation = match prerequisite_policy {
                    StatementPrerequisitePolicy::Exact
                    | StatementPrerequisitePolicy::Certified => {
                        if exact_fact_is_available(obligation.proposition(), pure_facts)
                            || matches!(
                                normalize_proposition(obligation.proposition()),
                                SimpProposition::True
                            )
                            || matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified)
                                && certified_prerequisites.iter().any(|derivation| {
                                    derivation.conclusion() == obligation.proposition()
                                        && derivation.replay(&prerequisite_assumptions)
                                })
                        {
                            None
                        } else {
                            return Err(ClickError::new(format!(
                                "{context_label} is missing condition prerequisite{}: {:?}",
                                obligation
                                    .context()
                                    .map(|context| format!(" ({context})"))
                                    .unwrap_or_default(),
                                obligation.proposition()
                            )));
                        }
                    }
                    StatementPrerequisitePolicy::Explicit
                    | StatementPrerequisitePolicy::Contextual => {
                        if prerequisite_assumptions.proves(obligation.proposition()) {
                            None
                        } else {
                            return Err(ClickError::new(format!(
                                "{context_label} is missing condition prerequisite{}: {:?}",
                                obligation
                                    .context()
                                    .map(|context| format!(" ({context})"))
                                    .unwrap_or_default(),
                                obligation.proposition()
                            )));
                        }
                    }
                    StatementPrerequisitePolicy::Planning => Some(
                        prerequisite_assumptions
                            .derive_proposition(obligation.proposition())
                            .ok_or_else(|| {
                                ClickError::new(format!(
                                    "{context_label} is missing condition prerequisite{}: {:?}",
                                    obligation
                                        .context()
                                        .map(|context| format!(" ({context})"))
                                        .unwrap_or_default(),
                                    obligation.proposition()
                                ))
                            })?,
                    ),
                };
                if let Some(derivation) = derivation {
                    prerequisite_derivations.push(derivation);
                }
            }
            match implication_body(path.theorem().proposition()) {
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::Value(is_true),
                    ..
                } => Ok(CertifiedConditionTransition {
                    is_true: *is_true,
                    pure_facts: successor_facts,
                    path_facts: path
                        .facts()
                        .iter()
                        .map(|fact| fact.proposition().clone())
                        .collect(),
                    theorem: path.theorem().clone(),
                    prerequisite_derivations,
                    planning_exact_premises,
                }),
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::UndefinedBehavior(kind),
                    ..
                } => Err(ClickError::new(format!(
                    "{context_label} produced undefined behavior while evaluating the condition: {kind:?}"
                ))),
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::RuntimeError(error),
                    ..
                } => Err(ClickError::new(format!(
                    "{context_label} produced runtime error while evaluating the condition: {error:?}"
                ))),
                proposition => Err(ClickError::new(format!(
                    "{context_label} saw unexpected condition theorem {proposition:?}"
                ))),
            }
        })
        .collect()
}

pub(super) fn certified_statement_transitions(
    state: &CState,
    pure_facts: &[Proposition],
    statement: &CStatement,
    function_environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    context_label: &str,
    next_opaque_call: &mut u64,
    next_verification_variable: &mut u64,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    certified_prerequisites: &[PropositionDerivation],
) -> Result<(Vec<CertifiedStatementTransition>, Option<CVerifiedLoopRule>), ClickError> {
    let mut transition_pure_facts = pure_facts.to_vec();
    let mut assumptions = match prerequisite_policy {
        StatementPrerequisitePolicy::Exact
        | StatementPrerequisitePolicy::Explicit
        | StatementPrerequisitePolicy::Certified
        | StatementPrerequisitePolicy::Contextual
        | StatementPrerequisitePolicy::Planning => assumptions_from_propositions(pure_facts),
    };
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified) {
        for derivation in certified_prerequisites {
            if derivation_replays_with_materialized_context(derivation, pure_facts) {
                assumptions = assumptions.assume_proposition(derivation.conclusion().clone());
                if !transition_pure_facts.contains(derivation.conclusion()) {
                    transition_pure_facts.push(derivation.conclusion().clone());
                }
            }
        }
    }
    if matches!(
        prerequisite_policy,
        StatementPrerequisitePolicy::Exact
            | StatementPrerequisitePolicy::Explicit
            | StatementPrerequisitePolicy::Certified
    ) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
        assumptions = assumptions.prefer_symbolic_external_loads();
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
        assumptions = assumptions.defer_non_exact_condition_reasoning();
    }
    let mut budget = ExecutionBudget::default()
        .with_next_opaque_call(*next_opaque_call)
        .with_next_verification_variable(*next_verification_variable);
    let (execution, loop_rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            state.clone(),
            statement.clone(),
            assumptions,
            function_environment.clone(),
            execution_semantics,
            &mut budget,
        );
    // Certificate generation has to know whether the ambient conditions are
    // part of what this transition consumed. Planning reasons from the whole
    // ambient context, so a condition it used leaves no trace in the
    // transition: the undefined-behaviour path it ruled out is simply absent,
    // and the segment lookup it bounded simply succeeded.
    let consults_conditions = !matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
        || statement_consults_conditions(statement)
        || context_reasons_about_memory(state, &transition_pure_facts);
    *next_opaque_call = budget.next_opaque_call();
    *next_verification_variable = budget.next_verification_variable();
    let (mut transitions, loop_rule) = certified_transitions_from_execution(
        execution,
        loop_rule,
        &transition_pure_facts,
        context_label,
        prerequisite_policy,
        fact_transport_policy,
        certified_prerequisites,
        statement_contains_call_assign(statement),
    )?;
    for transition in &mut transitions {
        transition.consults_conditions = consults_conditions;
    }
    Ok((transitions, loop_rule))
}

/// Whether anything in this proof context can turn a condition into a memory or
/// resource conclusion.
///
/// Bounds justify segment lookups and sub-range loadability, so a context that
/// holds memory permissions or resources can consume a condition even where the
/// statement itself cannot. A context of nothing but conditions cannot.
fn context_reasons_about_memory(state: &CState, pure_facts: &[Proposition]) -> bool {
    if !state.resources().facts().is_empty() {
        return true;
    }
    let mut conjuncts = Vec::new();
    for fact in pure_facts {
        atomic_conjuncts(fact, &mut conjuncts);
    }
    conjuncts
        .iter()
        .any(|fact| !matches!(fact, Proposition::ConditionIs(_, _)))
}

/// The ambient conditions available at a proof point, as atomic conjuncts.
fn ambient_condition_facts(available: &[Proposition]) -> Vec<Proposition> {
    let mut conjuncts = Vec::new();
    for fact in available {
        atomic_conjuncts(fact, &mut conjuncts);
    }
    conjuncts
        .into_iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .cloned()
        .collect()
}

/// Whether executing this statement can consult the ambient condition context.
///
/// Planning reasons from the whole ambient context, so a condition it used
/// leaves no trace in the transition: the undefined-behaviour path it excluded
/// is simply missing, and the segment lookup it bounded simply succeeded. Only
/// operations that can be undefined, or that address memory, ever ask; reading a
/// variable or a constant never does, so a certificate for such a statement owes
/// the ambient conditions nothing and replays as a bare `step`.
fn statement_consults_conditions(statement: &CStatement) -> bool {
    fn expression_consults(expression: &CExpression) -> bool {
        !matches!(expression, CExpression::Value(_) | CExpression::Variable(_))
    }
    match statement {
        CStatement::Skip | CStatement::Declare { .. } => false,
        CStatement::Assign { expression, .. } | CStatement::Return(expression) => {
            expression_consults(expression)
        }
        CStatement::Seq(first, second) => {
            statement_consults_conditions(first) || statement_consults_conditions(second)
        }
        CStatement::CallAssign { .. }
        | CStatement::Assert { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::If { .. }
        | CStatement::While { .. } => true,
    }
}

fn certified_loop_exit_transitions_with_proven_phases(
    state: &CState,
    pure_facts: &[Proposition],
    statement: &CStatement,
    function_environment: &CExecutionEnvironment,
    context_label: &str,
    initialization_proven: bool,
    preservation_proven: bool,
    next_opaque_call: &mut u64,
    next_verification_variable: &mut u64,
) -> Result<(Vec<CertifiedStatementTransition>, Option<CVerifiedLoopRule>), ClickError> {
    let assumptions = assumptions_from_propositions(pure_facts);
    let mut budget = ExecutionBudget::default()
        .with_next_opaque_call(*next_opaque_call)
        .with_next_verification_variable(*next_verification_variable);
    let (execution, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
        state.clone(),
        statement.clone(),
        assumptions,
        function_environment.clone(),
        initialization_proven,
        preservation_proven,
        &mut budget,
    );
    *next_opaque_call = budget.next_opaque_call();
    *next_verification_variable = budget.next_verification_variable();
    certified_transitions_from_execution(
        execution,
        loop_rule,
        pure_facts,
        context_label,
        StatementPrerequisitePolicy::Contextual,
        StatementFactTransportPolicy::Automatic,
        &[],
        statement_contains_call_assign(statement),
    )
}

fn statement_contains_call_assign(statement: &CStatement) -> bool {
    match statement {
        CStatement::CallAssign { .. } => true,
        CStatement::Seq(first, second) => {
            statement_contains_call_assign(first) || statement_contains_call_assign(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_contains_call_assign(then_branch)
                || statement_contains_call_assign(else_branch)
        }
        CStatement::While { body, .. } => statement_contains_call_assign(body),
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => false,
    }
}

fn is_internal_snapshot_frame_witness(fact: &Proposition) -> bool {
    let same_load_address = |left: &Bitvector32Term, right: &Bitvector32Term| {
        matches!(
            (left, right),
            (
                Bitvector32Term::MemoryLoad(_, left_pointer),
                Bitvector32Term::MemoryLoad(_, right_pointer),
            ) if left_pointer == right_pointer
        )
    };
    let Proposition::ConditionIs(condition, true) = fact else {
        return false;
    };
    match condition {
        ConditionTerm::Bitvector32Equal(left, right) => same_load_address(left, right),
        ConditionTerm::PointerOffsetEqual(left, right) => matches!(
            (left.as_ref(), right.as_ref()),
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) if left_width == right_width && same_load_address(left, right)
        ),
        _ => false,
    }
}

fn certified_transitions_from_execution(
    execution: SymbolicCExecution,
    loop_rule: Option<CVerifiedLoopRule>,
    pure_facts: &[Proposition],
    context_label: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    certified_prerequisites: &[PropositionDerivation],
    normalize_statement_facts_to_exit: bool,
) -> Result<(Vec<CertifiedStatementTransition>, Option<CVerifiedLoopRule>), ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "{context_label} hit execution limit {limit:?}"
        )));
    }
    let has_failure_path = execution.paths().iter().any(|path| {
        matches!(
            implication_body(path.theorem().proposition()),
            Proposition::CStatementExecutes {
                outcome: CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_),
                ..
            }
        )
    });
    let transitions = execution
        .paths()
        .iter()
        .filter(|path| {
            !path.facts().iter().any(|path_fact| {
                pure_facts.iter().any(|available| {
                    exact_facts_directly_conflict(available, path_fact.proposition())
                })
            })
        })
        .map(|path| {
            let mut successor_facts = pure_facts.to_vec();
            let mut statement_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let mut statement_fact_sources = statement_facts.clone();
            successor_facts.extend(statement_facts.iter().cloned());
            let mut execution_facts = path.execution_facts();
            let mut transport_facts = successor_facts.clone();
            transport_facts.extend(
                execution_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            let transport_assumptions = assumptions_for_direct_fact_transport(&transport_facts);
            let prerequisite_assumptions = assumptions_from_propositions(&successor_facts);
            let planning_assumptions = assumptions_from_propositions(pure_facts);
            let mut prerequisite_derivations = Vec::new();
            if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
                let mut seen_prerequisites = BTreeSet::new();
                let mut theorem_context = pure_facts.to_vec();
                for premise in theorem_implication_premises(path.theorem()) {
                    // An ambient condition the theorem merely carried along is
                    // already replayable as itself; recording an identity
                    // derivation for it would advertise it as something the
                    // execution consumed and force it into the certificate.
                    if matches!(premise, Proposition::ConditionIs(_, _))
                        && !exact_fact_is_available(&premise, &theorem_context)
                        && let Some(derivation) =
                            bounded_condition_derivation(&premise, pure_facts)
                        && !derivation.context_premises().is_empty()
                    {
                        if !prerequisite_derivations
                            .iter()
                            .any(|existing: &PropositionDerivation| {
                                existing.conclusion() == derivation.conclusion()
                            })
                        {
                            prerequisite_derivations.push(derivation);
                        }
                        if !theorem_context.contains(&premise) {
                            theorem_context.push(premise);
                        }
                        continue;
                    }
                    let already_certified = exact_fact_is_available(&premise, &theorem_context)
                        || materialization_equivalent_available_fact(
                            &premise,
                            &theorem_context,
                        )
                        .is_some()
                        || matches!(normalize_proposition(&premise), SimpProposition::True)
                        || execution_facts.iter().any(|fact| {
                                fact.is_certified() && fact.proposition() == &premise
                            })
                            && !path
                                .obligations()
                                .iter()
                                .any(|obligation| obligation.proposition() == &premise);
                    if !already_certified {
                        let derivation =
                            minimal_proposition_derivation(&premise, &theorem_context).or_else(
                                || bounded_condition_derivation(&premise, &theorem_context),
                            );
                        let Some(derivation) = derivation else {
                            if has_failure_path {
                                if !theorem_context.contains(&premise) {
                                    theorem_context.push(premise);
                                }
                                continue;
                            }
                            return Err(ClickError::new(format!(
                                "{context_label} used an assumption-derived theorem premise without a replayable derivation: {premise:?}"
                            )));
                        };
                        if !prerequisite_derivations
                            .iter()
                            .any(|existing: &PropositionDerivation| {
                                existing.conclusion() == derivation.conclusion()
                            })
                        {
                            prerequisite_derivations.push(derivation);
                        }
                    }
                    if !theorem_context.contains(&premise) {
                        theorem_context.push(premise);
                    }
                }
                for path_fact in path.facts().iter().chain(execution_facts.iter()) {
                    if path_fact.is_certified()
                        || !seen_prerequisites.insert(path_fact.proposition().clone())
                    {
                        continue;
                    }
                    let proposition = path_fact.proposition();
                    if exact_fact_is_available(proposition, pure_facts)
                        || matches!(normalize_proposition(proposition), SimpProposition::True)
                    {
                        continue;
                    }
                    if let Some(derivation) =
                        minimal_proposition_derivation(proposition, pure_facts)
                    {
                        if !prerequisite_derivations
                            .iter()
                            .any(|existing: &PropositionDerivation| {
                                existing.conclusion() == derivation.conclusion()
                            })
                        {
                            prerequisite_derivations.push(derivation);
                        }
                    } else if proposition_has_contextual_derivation_rules(proposition)
                        && planning_assumptions.proves(proposition)
                    {
                        return Err(ClickError::new(format!(
                            "{context_label} used an assumption-derived execution fact without a replayable derivation: {proposition:?}"
                        )));
                    }
                }
            }
            for obligation in path.obligations() {
                let proposition = obligation.proposition();
                let derivation = match prerequisite_policy {
                    StatementPrerequisitePolicy::Exact
                    | StatementPrerequisitePolicy::Explicit
                    | StatementPrerequisitePolicy::Certified => {
                        if exact_fact_is_available(proposition, pure_facts)
                            || materialization_equivalent_available_fact(
                                proposition,
                                pure_facts,
                            )
                            .is_some()
                            || directly_matching_separation_fact(proposition, pure_facts).is_some()
                            || directly_covering_loadability_fact(proposition, pure_facts).is_some()
                            || matches!(normalize_proposition(proposition), SimpProposition::True)
                            || matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified)
                                && certified_prerequisites.iter().any(|derivation| {
                                    derivation.conclusion() == proposition
                                        && derivation.replay(&prerequisite_assumptions)
                                })
                        {
                            None
                        } else if matches!(
                            prerequisite_policy,
                            StatementPrerequisitePolicy::Explicit
                        ) {
                            // `step using` exposes a deliberately small premise
                            // set. Permit one proof-producing atomic check over
                            // exactly that set, after execution has deferred
                            // every non-exact obligation. This keeps certificate
                            // replay independent of the ambient proof context
                            // without requiring callers to spell out internal
                            // evaluator predicates such as no-overflow facts.
                            let exact_derivation = if matches!(
                                proposition,
                                Proposition::ConditionIs(_, _)
                            ) {
                                bounded_condition_derivation(proposition, pure_facts)
                            } else if matches!(
                                proposition,
                                Proposition::CResourceContains { .. }
                                    | Proposition::CResourceSeparate { .. }
                                    | Proposition::CMemoryLoadable { .. }
                            ) {
                                // Resource containment, separation, and
                                // loadability coverage are internal evaluator
                                // predicates like the no-overflow conditions
                                // above; derive them atomically over the same
                                // explicit set.
                                assumptions_from_propositions(pure_facts)
                                    .derive_atomic_proposition(proposition)
                            } else {
                                None
                            };
                            exact_derivation.ok_or_else(|| {
                                    ClickError::new(format!(
                                        "{context_label} is missing exact prerequisite{}: {:?}",
                                        obligation
                                            .context()
                                            .map(|context| format!(" ({context})"))
                                            .unwrap_or_default(),
                                        proposition
                                    ))
                                })
                                .map(Some)?
                        } else {
                            return Err(ClickError::new(format!(
                                "{context_label} is missing certified prerequisite{}: {:?}",
                                obligation
                                    .context()
                                    .map(|context| format!(" ({context})"))
                                    .unwrap_or_default(),
                                proposition
                            )));
                        }
                    }
                    StatementPrerequisitePolicy::Contextual => {
                        if prerequisite_assumptions.proves(proposition) {
                            None
                        } else {
                            return Err(ClickError::new(format!(
                                "{context_label} is missing prerequisite{}: {:?}",
                                obligation
                                    .context()
                                    .map(|context| format!(" ({context})"))
                                    .unwrap_or_default(),
                                proposition
                            )));
                        }
                    }
                    StatementPrerequisitePolicy::Planning => {
                        if exact_fact_is_available(proposition, pure_facts) {
                            None
                        } else {
                            let derivation_facts = successor_facts
                                .iter()
                                .filter(|fact| *fact != proposition)
                                .cloned()
                                .collect::<Vec<_>>();
                            Some(
                                minimal_proposition_derivation(proposition, &derivation_facts)
                                    .ok_or_else(|| {
                                    ClickError::new(format!(
                                        "{context_label} is missing prerequisite{}: {:?}",
                                        obligation
                                            .context()
                                            .map(|context| format!(" ({context})"))
                                            .unwrap_or_default(),
                                        proposition
                                    ))
                                })?,
                            )
                        }
                    }
                };
                if let Some(derivation) = derivation {
                    prerequisite_derivations.push(derivation);
                }
            }
            if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
                let is_derived_prerequisite = |fact: &Proposition| {
                    prerequisite_derivations
                        .iter()
                        .any(|derivation| derivation.conclusion() == fact)
                        && !exact_fact_is_available(fact, pure_facts)
                };
                statement_facts.retain(|fact| !is_derived_prerequisite(fact));
                statement_fact_sources.retain(|fact| !is_derived_prerequisite(fact));
                successor_facts.retain(|fact| !is_derived_prerequisite(fact));
                execution_facts
                    .retain(|fact| !is_derived_prerequisite(fact.proposition()));
            }
            let Proposition::CStatementExecutes {
                state: statement_pre_state,
                outcome,
                ..
            } =
                implication_body(path.theorem().proposition())
            else {
                return Err(ClickError::new(format!(
                    "{context_label} saw an unexpected execution theorem"
                )));
            };
            if let CStatementOutcome::Normal(post_state)
            | CStatementOutcome::Return {
                state: post_state, ..
            } = outcome
            {
                // A compound source statement can produce a fact before its
                // final internal state change. For example, a verified call
                // produces postcondition facts before CallAssign stores the
                // return value in a stack local. That intermediate snapshot
                // has no source-level program point, so normalize facts
                // produced by the statement itself to the statement exit as
                // part of the statement step. Surface transports remain
                // responsible only for facts that predated the statement.
                let mut transported_facts = Vec::new();
                let mut certified_transport_sources = Vec::new();
                if normalize_statement_facts_to_exit {
                    let omit_internal_frame_witnesses =
                        matches!(prerequisite_policy, StatementPrerequisitePolicy::Explicit);
                    let mut normalization_sources = statement_facts
                        .into_iter()
                        .filter(|fact| {
                            !omit_internal_frame_witnesses
                                || !is_internal_snapshot_frame_witness(fact)
                        })
                        .collect::<Vec<_>>();
                    for execution_fact in &execution_facts {
                        if execution_fact.is_certified()
                            && (!omit_internal_frame_witnesses
                                || !is_internal_snapshot_frame_witness(
                                    execution_fact.proposition(),
                                ))
                            && materialization_equivalent_available_fact(
                                execution_fact.proposition(),
                                pure_facts,
                            )
                            .is_none()
                            && !normalization_sources.contains(execution_fact.proposition())
                        {
                            normalization_sources.push(execution_fact.proposition().clone());
                        }
                    }
                    for fact in normalization_sources {
                        let Some(theorem) = prove_c_condition_fact_direct_transport(
                            &fact,
                            post_state.memory(),
                            &transport_assumptions,
                        ) else {
                            continue;
                        };
                        let Proposition::Implies(_, conclusion) = theorem.proposition() else {
                            unreachable!("condition transport must produce an implication")
                        };
                        let target = conclusion.as_ref();
                        if target == &fact {
                            continue;
                        }
                        successor_facts.retain(|available| available != &fact);
                        if !successor_facts.contains(target) {
                            successor_facts.push(target.clone());
                        }
                        if execution_facts.iter().any(|execution_fact| {
                            execution_fact.is_certified() && execution_fact.proposition() == &fact
                        }) && !certified_transport_sources.contains(&fact)
                        {
                            certified_transport_sources.push(fact.clone());
                        }
                        transported_facts.push(CertifiedFactTransport {
                            source: fact,
                            target: target.clone(),
                            theorem,
                            statement_local: true,
                        });
                    }
                }
                let statement_memory_changed =
                    statement_pre_state.memory() != post_state.memory();

                if !matches!(fact_transport_policy, StatementFactTransportPolicy::None)
                    && statement_memory_changed
                {
                    let automatic_sources = if normalize_statement_facts_to_exit {
                        pure_facts.to_vec()
                    } else {
                        successor_facts.clone()
                    };
                    for fact in automatic_sources {
                        if !c_condition_fact_has_memory(&fact) {
                            continue;
                        }
                        let statement_local =
                            exact_fact_is_available(&fact, &statement_fact_sources);
                        let theorem = match fact_transport_policy {
                            StatementFactTransportPolicy::Selected => {
                                prove_c_condition_fact_direct_transport(
                                    &fact,
                                    post_state.memory(),
                                    &transport_assumptions,
                                )
                            }
                            StatementFactTransportPolicy::Automatic => {
                                prove_c_condition_fact_direct_transport(
                                    &fact,
                                    post_state.memory(),
                                    &transport_assumptions,
                                )
                            }
                            StatementFactTransportPolicy::None => unreachable!(),
                        };
                        let Some(theorem) = theorem else {
                            continue;
                        };
                        let Proposition::Implies(_, conclusion) = theorem.proposition() else {
                            unreachable!("condition transport must produce an implication")
                        };
                        transported_facts.push(CertifiedFactTransport {
                            source: fact,
                            target: conclusion.as_ref().clone(),
                            theorem,
                            statement_local,
                        });
                    }
                }
                let mut transported_execution_facts = Vec::new();
                for transport in &transported_facts {
                    successor_facts.retain(|fact| fact != &transport.source);
                    if !successor_facts.contains(&transport.target) {
                        successor_facts.push(transport.target.clone());
                    }
                    for fact in &mut execution_facts {
                        if fact.proposition() == &transport.source {
                            if fact.is_certified() {
                                // Preserve the certified producer-side fact:
                                // the execution theorem can name that exact
                                // intermediate snapshot as a premise. The
                                // transported copy is the fact exposed at the
                                // source-statement exit.
                                transported_execution_facts.push(
                                    fact.clone().with_proposition(transport.target.clone()),
                                );
                            } else {
                                *fact = fact
                                    .clone()
                                    .with_proposition(transport.target.clone());
                            }
                        }
                    }
                }
                for fact in transported_execution_facts {
                    if !execution_facts.contains(&fact) {
                        execution_facts.push(fact);
                    }
                }
                let mut path_facts = path
                    .facts()
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .filter(|fact| statement_fact_sources.contains(fact))
                    .collect::<Vec<_>>();
                for source in certified_transport_sources {
                    if !path_facts.contains(&source) {
                        path_facts.push(source);
                    }
                }
                return Ok(CertifiedStatementTransition {
                    theorem: path.theorem().clone(),
                    outcome: outcome.clone(),
                    execution_facts,
                    path_facts,
                    obligations: path.obligations().to_vec(),
                    pure_facts: successor_facts,
                    prerequisite_derivations,
                    consults_conditions: false,
                    fact_transports: transported_facts,
                });
            }
            Ok(CertifiedStatementTransition {
                theorem: path.theorem().clone(),
                outcome: outcome.clone(),
                execution_facts,
                path_facts: path
                    .facts()
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .filter(|fact| statement_fact_sources.contains(fact))
                    .collect(),
                obligations: path.obligations().to_vec(),
                pure_facts: successor_facts,
                prerequisite_derivations,
                consults_conditions: false,
                fact_transports: Vec::new(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((transitions, loop_rule))
}

#[allow(clippy::too_many_arguments)]
fn verify_execution_proofs_forward(
    statement: &CStatement,
    contexts: Vec<ExecutionProofContext>,
    next_loop_index: &mut usize,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    match statement {
        CStatement::Seq(first, second) => {
            let contexts = verify_execution_proofs_forward(
                first,
                contexts,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            verify_execution_proofs_forward(
                second,
                contexts,
                next_loop_index,
                environment,
                verified_loop_rules,
            )
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let (then_contexts, else_contexts) =
                split_execution_proof_branch_contexts(condition, contexts)?;
            let mut joined = verify_execution_proofs_forward(
                then_branch,
                then_contexts,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            joined.extend(verify_execution_proofs_forward(
                else_branch,
                else_contexts,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?);
            Ok(joined)
        }
        CStatement::Assert {
            label: Some(label), ..
        } if label.starts_with("statement ") && label.ends_with(" assert 0") => {
            let statement_index = label
                .strip_prefix("statement ")
                .and_then(|label| label.strip_suffix(" assert 0"))
                .and_then(|index| index.parse::<usize>().ok())
                .ok_or_else(|| {
                    ClickError::new(format!("malformed structural assertion label `{label}`"))
                })?;
            let contexts = certify_structural_assertions(
                CodeRegion::Statement(statement_index),
                contexts,
                environment,
            )?;
            // The structural proof has certified the assertion and added its
            // proposition to every path context. A C assertion has no state
            // effect, so do not evaluate its expression again: doing so would
            // require reopening resources that the proof was allowed to use
            // through their certified pure facts.
            Ok(contexts)
        }
        CStatement::While {
            condition,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            let contexts =
                certify_structural_assertions(CodeRegion::Loop(loop_index), contexts, environment)?;
            let loop_clause = environment
                .function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index));
            let explicit_tactics = loop_clause.and_then(explicit_loop_preservation_tactics);
            let default_initialization = Proof::Default;
            let initialization_proof = loop_clause.map(|clause| {
                (
                    clause,
                    clause.initialize_proof().unwrap_or(&default_initialization),
                )
            });
            let mut iteration_contexts = Vec::new();
            let mut initialization_path_certificates = Vec::new();
            let mut preservation_path_certificates = Vec::new();
            let mut effect_path_certificates = BTreeMap::<usize, Vec<PathCertificate>>::new();
            for context in &contexts {
                let assumptions = assumptions_from_propositions(&context.pure_facts);
                if let Some((clause, proof)) = initialization_proof {
                    let certificate = verify_loop_initialization_pure_proof(
                        loop_index,
                        proof,
                        clause,
                        context,
                        invariant_checks,
                        environment,
                    )?;
                    initialization_path_certificates.push(PathCertificate {
                        case_path: context.case_path.clone(),
                        certificate,
                    });
                } else {
                    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{}.loop({loop_index}).initialize`: {message}",
                                environment.function_block.signature().name()
                            ))
                        })?;
                }
                let preservation_contexts = c_loop_preservation_contexts(
                    &context.state,
                    condition,
                    invariant_checks,
                    effect_checks,
                    body,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{}.loop({loop_index}).preserve`: {message}",
                        environment.function_block.signature().name()
                    ))
                })?;
                for preservation in preservation_contexts {
                    let mut pure_facts = context.pure_facts.clone();
                    pure_facts.extend_from_slice(preservation.pure_facts());
                    pure_facts.sort();
                    pure_facts.dedup();
                    if let Some(clause) = loop_clause {
                        let preservation_tactics = if let Some(tactics) = explicit_tactics {
                            tactics.to_vec()
                        } else {
                            let body_certificate = plan_automatic_loop_preservation_body(
                                loop_index,
                                &preservation,
                                &pure_facts,
                                body,
                                environment,
                            )?;
                            let mut tactics = clause
                                .preserve_proof()
                                .and_then(Proof::tactics)
                                .unwrap_or_default()
                                .iter()
                                .filter(|tactic| matches!(tactic, ProofTactic::UnfoldPredicate(_)))
                                .cloned()
                                .collect::<Vec<_>>();
                            tactics.extend(body_certificate.tactics().iter().cloned());
                            tactics.push(ProofTactic::Simp);
                            tactics
                        };
                        let result = verify_one_loop_preservation_proof(
                            loop_index,
                            &preservation_tactics,
                            &preservation,
                            &pure_facts,
                            invariant_checks,
                            effect_checks,
                            body,
                            environment,
                        )?;
                        preservation_path_certificates.push(PathCertificate {
                            case_path: context.case_path.clone(),
                            certificate: result.certificate,
                        });
                        for (item_index, certificate) in result.effect_certificates {
                            effect_path_certificates
                                .entry(item_index)
                                .or_default()
                                .push(PathCertificate {
                                    case_path: context.case_path.clone(),
                                    certificate,
                                });
                        }
                    }
                    iteration_contexts.push(ExecutionProofContext {
                        state: preservation.state().clone(),
                        pure_facts,
                        surface_propositions: context.surface_propositions.clone(),
                        program_point_states: context.program_point_states.clone(),
                        case_path: context.case_path.clone(),
                        next_opaque_call: context.next_opaque_call,
                        next_verification_variable: context.next_verification_variable,
                    });
                }
            }
            if initialization_proof.is_some() {
                let claim_label = format!(
                    "{}.loop({loop_index}).initialize",
                    environment.function_block.signature().name()
                );
                let initialization_certificate = merge_path_aligned_certificates(
                    &claim_label,
                    initialization_path_certificates,
                )?;
                let site = ProofSite::LoopPhase {
                    function_name: environment.function_block.signature().name().to_string(),
                    loop_index,
                    phase: "initialize",
                };
                if let Some(source_index) = selected_tactic_index_for_site(&site)
                    && let Some((_, Proof::Script(source_tactics))) = initialization_proof
                    && matches!(source_tactics.get(source_index), Some(ProofTactic::Simp))
                {
                    record_proof_site_tactic_expansion(
                        &site,
                        source_index,
                        initialization_certificate.tactics(),
                    );
                }
                finish_proof_site_expansion_capture(&site, &initialization_certificate)?;
            }
            if !preservation_path_certificates.is_empty() {
                let claim_label = format!(
                    "{}.loop({loop_index}).preserve",
                    environment.function_block.signature().name()
                );
                let preservation_certificate =
                    merge_path_aligned_certificates(&claim_label, preservation_path_certificates)?;
                finish_proof_site_expansion_capture(
                    &ProofSite::LoopPhase {
                        function_name: environment.function_block.signature().name().to_string(),
                        loop_index,
                        phase: "preserve",
                    },
                    &preservation_certificate,
                )?;
            }
            for (item_index, paths) in effect_path_certificates {
                let site = ProofSite::StructuralItem {
                    function_name: environment.function_block.signature().name().to_string(),
                    region: CodeRegion::Loop(loop_index),
                    item_index,
                    kind: environment
                        .function_block
                        .structural_clauses()
                        .iter()
                        .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
                        .and_then(|clause| clause.items().get(item_index))
                        .map(StructuralItem::kind)
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "`{}.loop({loop_index})`: certified an effect for item {item_index}, which the loop region does not declare",
                                environment.function_block.signature().name()
                            ))
                        })?,
                };
                let certificate = merge_path_aligned_certificates(&site.description(), paths)?;
                finish_proof_site_expansion_capture(&site, &certificate)?;
            }

            if kernel_statement_contains_loop(body) {
                // Nested loop regions are encountered from the arbitrary iteration
                // frontier, exactly where the outer induction hypothesis applies.
                let _ = verify_execution_proofs_forward(
                    body,
                    iteration_contexts,
                    next_loop_index,
                    environment,
                    verified_loop_rules,
                )?;
            }

            advance_execution_proof_statement(
                statement,
                contexts,
                loop_index,
                environment,
                verified_loop_rules,
                if loop_clause.is_some() {
                    LoopPreservationSource::ExecutionProof
                } else {
                    LoopPreservationSource::Automatic
                },
                initialization_proof.is_some(),
            )
        }
        CStatement::Return(_) => Ok(Vec::new()),
        _ => advance_execution_proof_statement(
            statement,
            contexts,
            *next_loop_index,
            environment,
            verified_loop_rules,
            LoopPreservationSource::Automatic,
            false,
        ),
    }
}

fn kernel_statement_contains_loop(statement: &CStatement) -> bool {
    match statement {
        CStatement::While { .. } => true,
        CStatement::Seq(first, second) => {
            kernel_statement_contains_loop(first) || kernel_statement_contains_loop(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            kernel_statement_contains_loop(then_branch)
                || kernel_statement_contains_loop(else_branch)
        }
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Assert { .. } => false,
    }
}

fn split_execution_proof_branch_contexts(
    condition: &CExpression,
    contexts: Vec<ExecutionProofContext>,
) -> Result<(Vec<ExecutionProofContext>, Vec<ExecutionProofContext>), ClickError> {
    let mut then_contexts = Vec::new();
    let mut else_contexts = Vec::new();
    for context in contexts {
        for transition in certified_condition_transitions(
            &context.state,
            &context.pure_facts,
            condition,
            "execution proof traversal",
            StatementPrerequisitePolicy::Contextual,
            &[],
            true,
        )? {
            let next = ExecutionProofContext {
                state: context.state.clone(),
                pure_facts: transition.pure_facts,
                surface_propositions: context.surface_propositions.clone(),
                program_point_states: context.program_point_states.clone(),
                case_path: {
                    let mut case_path = context.case_path.clone();
                    case_path.push(ProofCaseChoice {
                        condition: surface_c_condition(condition),
                        value: transition.is_true,
                    });
                    case_path
                },
                next_opaque_call: context.next_opaque_call,
                next_verification_variable: context.next_verification_variable,
            };
            if transition.is_true {
                then_contexts.push(next);
            } else {
                else_contexts.push(next);
            }
        }
    }
    Ok((then_contexts, else_contexts))
}

#[allow(clippy::too_many_arguments)]
fn plan_point_pure_goal_certificate(
    proof_site: &ProofSite,
    proposition: &ClickProposition,
    proof: &Proof,
    claim_label: &str,
    proof_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    surface_propositions: &SurfacePropositionMap,
    prelowered_goal: Option<&Proposition>,
    theorem_environment: &TheoremEnvironment,
) -> Result<(Proposition, TacticCertificate), ClickError> {
    let applied_theorem_script;
    let proof = if let Proof::Script(tactics) = proof
        && tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::ApplyTheorem(_)))
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        })
    {
        // An applied theorem's conclusion becomes an available fact, so the
        // trailing smart `simp` lowers to the deterministic `assumption` and
        // a bare `apply` lowers to `apply using` with the theorem's own
        // requires as the explicit premise pool.
        applied_theorem_script = Proof::Script(
            tactics
                .iter()
                .map(|tactic| match tactic {
                    ProofTactic::Simp => ProofTactic::Assumption,
                    ProofTactic::ApplyTheorem(application) => {
                        let premises = theorem_environment
                            .get(&application.name)
                            .map(|theorem| {
                                theorem
                                    .requires()
                                    .iter()
                                    .filter_map(Requirement::proposition)
                                    .cloned()
                                    .collect()
                            })
                            .unwrap_or_default();
                        ProofTactic::ApplyTheoremUsing {
                            application: application.clone(),
                            premises,
                        }
                    }
                    other => other.clone(),
                })
                .collect(),
        );
        &applied_theorem_script
    } else {
        proof
    };
    if let Proof::Script(tactics) = proof
        && let Ok(certificate) = TacticCertificate::from_proof_tactics(tactics)
    {
        let fact = if let Some(prelowered_goal) = prelowered_goal {
            prelowered_goal.clone()
        } else {
            lower_point_proposition(
                proposition,
                available,
                parameters,
                arguments,
                pre_state,
                state,
                None,
                program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` proof {proof_index}: could not lower pure goal: {message}"
                ))
            })?
        };
        return Ok((fact, certificate));
    }

    let unfolded_predicates = smart_simp_unfold_prefix(proof).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` proof {proof_index} contains a smart pure proof that has no certificate planner"
        ))
    })?;
    let have = ProofHave {
        proposition: proposition.clone(),
        proof: proof.clone(),
    };
    let (fact, plan) = plan_smart_have_at_current_point(
        &have,
        claim_label,
        proof_index,
        available,
        parameters,
        arguments,
        pre_state,
        state,
        program_point_states,
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        prelowered_goal,
    )?;
    let mut surface_replay = TacticReplayState {
        surface_propositions: surface_propositions.clone(),
        program_point_states: program_point_states.clone(),
        ..TacticReplayState::default()
    };
    surface_replay
        .surface_propositions
        .record_lowering(proposition, &fact)?;
    if !unfolded_predicates.is_empty() {
        let assumptions = assumptions_from_propositions(available);
        let recorded_unfoldings = surface_replay
            .surface_propositions
            .kernel_facts()
            .flat_map(|kernel| {
                surface_replay
                    .surface_propositions
                    .surfaces(kernel)
                    .filter_map(|surface| {
                        let mut unfolded_surface = unfold_structural_invariant_proposition(
                            predicate_environment,
                            surface,
                            &unfolded_predicates,
                        )
                        .ok()?;
                        if unfolded_surface == *surface {
                            return None;
                        }
                        if let Some(point) = predicate_call_source_site(surface) {
                            unfolded_surface =
                                surface_with_source_site(&unfolded_surface, &point).ok()?;
                        }
                        let unfolded_kernel = unfold_predicates_in_proposition(
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                            kernel,
                            &assumptions,
                        )
                        .ok()?;
                        let available_kernel = available
                            .iter()
                            .find(|available| {
                                **available == unfolded_kernel
                                    || quantified_binder_equivalent(
                                        &normalize_direct_atomic_memory_loads(&unfolded_kernel),
                                        &normalize_direct_atomic_memory_loads(available),
                                    )
                            })?
                            .clone();
                        Some((unfolded_surface, available_kernel))
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for (surface, kernel) in recorded_unfoldings {
            surface_replay
                .surface_propositions
                .record_lowering(&surface, &kernel)?;
        }
        let unfolded_surface = unfold_structural_invariant_proposition(
            predicate_environment,
            proposition,
            &unfolded_predicates,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let unfolded_fact = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            &fact,
            &assumptions,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        surface_replay
            .surface_propositions
            .record_lowering(&unfolded_surface, &unfolded_fact)?;
    }
    let surface_proof = surface_simp_plan_proof(
        &mut surface_replay,
        state,
        available,
        parameters,
        arguments,
        predicate_environment,
        click_function_environment,
        proposition,
        &plan,
        &unfolded_predicates,
    )?;
    let Proof::Script(tactics) = surface_proof else {
        return Err(ClickError::new(format!(
            "`{claim_label}` did not lower to an explicit proof script"
        )));
    };
    let certificate = TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` produced an invalid point-pure certificate: {error:?}"
        ))
    })?;
    if matches!(proof_site, ProofSite::StructuralItem { .. })
        && let Proof::Script(source_tactics) = proof
    {
        let source_index = TACTIC_EXPANSION_PROBE.with(|probe| {
            probe
                .borrow()
                .as_ref()
                .filter(|probe| probe.site == *proof_site)
                .and_then(|probe| probe.source_index)
        });
        if let Some(source_index) = source_index
            && matches!(source_tactics.get(source_index), Some(ProofTactic::Simp))
            && source_index <= certificate.tactics().len()
        {
            record_proof_site_tactic_expansion(
                proof_site,
                source_index,
                &certificate.tactics()[source_index..],
            );
        }
    }
    Ok((fact, certificate))
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_arguments)]
fn certify_structural_assertions(
    region: CodeRegion,
    mut contexts: Vec<ExecutionProofContext>,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    let Some(clause) = environment
        .function_block
        .structural_clauses()
        .iter()
        .find(|clause| clause.region() == &region)
    else {
        return Ok(contexts);
    };
    let assertions = clause
        .items()
        .iter()
        .enumerate()
        .filter(|(_, item)| item.kind() == StructuralItemKind::Assert)
        .collect::<Vec<_>>();
    if assertions.is_empty() {
        return Ok(contexts);
    }

    let region_label = match region {
        CodeRegion::Function => "function".to_string(),
        CodeRegion::Loop(index) => format!("loop({index})"),
        CodeRegion::Statement(index) => format!("statement({index})"),
    };
    let mut site_certificates = vec![Vec::new(); assertions.len()];
    for context in &mut contexts {
        let mut program_point_states = context.program_point_states.clone();
        let point_region = match region {
            CodeRegion::Function => CodeRegionRef::Function,
            CodeRegion::Loop(index) => CodeRegionRef::Loop(index),
            CodeRegion::Statement(index) => CodeRegionRef::Statement(index),
        };
        program_point_states.insert(
            ProgramPointRef {
                region: point_region,
                kind: ProgramPointKind::Entry,
            },
            context.state.clone(),
        );
        for (assertion_index, (item_index, item)) in assertions.iter().enumerate() {
            let proposition = item
                .proposition()
                .expect("assert structural item should contain a proposition");
            let claim_label = format!(
                "{}.{region_label}.assert_{}",
                environment.function_block.signature().name(),
                item_index
            );
            let (planned_fact, planned_certificate) = plan_point_pure_goal_certificate(
                &ProofSite::StructuralItem {
                    function_name: environment.function_block.signature().name().to_string(),
                    region,
                    item_index: *item_index,
                    kind: item.kind(),
                },
                proposition,
                item.proof(),
                &claim_label,
                assertion_index,
                &context.pure_facts,
                environment.parsed_function.parameters(),
                environment.arguments,
                environment.initial_state,
                &context.state,
                &program_point_states,
                environment.predicate_environment,
                environment.click_function_environment,
                &context.surface_propositions,
                None,
                environment.theorem_environment,
            )?;
            let (certificate, replayed_fact) = pure_goal_certificate_gateway(
                &claim_label,
                || Ok(planned_certificate),
                |certificate| {
                    prove_pure_proposition_at_point(
                        proposition,
                        None,
                        &Proof::Script(certificate.tactics().to_vec()),
                        "assert",
                        environment.theorem_environment,
                        &claim_label,
                        assertion_index,
                        &context.pure_facts,
                        environment.parsed_function.parameters(),
                        environment.arguments,
                        environment.initial_state,
                        &context.state,
                        None,
                        &program_point_states,
                        None,
                        environment.predicate_environment,
                        environment.click_function_environment,
                        environment.function_block.requires(),
                        None,
                    )
                },
            )?;
            debug_assert!(TacticCertificate::from_proof_tactics(certificate.tactics()).is_ok());
            site_certificates[assertion_index].push(PathCertificate {
                case_path: context.case_path.clone(),
                certificate,
            });
            if replayed_fact != planned_fact {
                return Err(ClickError::new(format!(
                    "`{claim_label}` certificate replay changed the proved proposition"
                )));
            }
            if !context.pure_facts.contains(&replayed_fact) {
                context.pure_facts.push(replayed_fact);
            }
            context
                .surface_propositions
                .record_lowering(proposition, &planned_fact)?;
        }
    }
    for ((item_index, _), certificates) in assertions.iter().zip(site_certificates) {
        let site = ProofSite::StructuralItem {
            function_name: environment.function_block.signature().name().to_string(),
            region,
            item_index: *item_index,
            kind: StructuralItemKind::Assert,
        };
        let certificate = merge_path_aligned_certificates(&site.description(), certificates)?;
        finish_proof_site_expansion_capture(&site, &certificate)?;
    }
    Ok(contexts)
}

fn advance_execution_proof_statement(
    statement: &CStatement,
    contexts: Vec<ExecutionProofContext>,
    region_index: usize,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
    loop_preservation_source: LoopPreservationSource,
    initialization_proven: bool,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    let mut advanced = Vec::new();
    for mut context in contexts {
        let label = format!("execution proof traversal at region {region_index}");
        let preservation_proven = matches!(
            loop_preservation_source,
            LoopPreservationSource::ExecutionProof
        );
        let (transitions, loop_rule) = match (initialization_proven, preservation_proven) {
            (false, false) => certified_statement_transitions(
                &context.state,
                &context.pure_facts,
                statement,
                environment.function_environment,
                CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                &label,
                &mut context.next_opaque_call,
                &mut context.next_verification_variable,
                StatementPrerequisitePolicy::Contextual,
                StatementFactTransportPolicy::Automatic,
                &[],
            )?,
            _ => certified_loop_exit_transitions_with_proven_phases(
                &context.state,
                &context.pure_facts,
                statement,
                environment.function_environment,
                &label,
                initialization_proven,
                preservation_proven,
                &mut context.next_opaque_call,
                &mut context.next_verification_variable,
            )?,
        };
        if matches!(statement, CStatement::While { .. }) {
            let loop_rule = loop_rule.ok_or_else(|| {
                let unresolved = transitions
                    .iter()
                    .flat_map(|transition| transition.obligations.iter())
                    .filter(|obligation| !obligation.is_assumable())
                    .map(|obligation| {
                        obligation
                            .context()
                            .unwrap_or("unlabeled verification condition")
                            .to_string()
                    })
                    .collect::<Vec<_>>();
                let mut unresolved = unresolved;
                unresolved.sort();
                unresolved.dedup();
                ClickError::new(format!(
                    "`{}` loop({region_index}) did not produce an obligation-free verified loop rule{}",
                    environment.function_block.signature().name(),
                    if unresolved.is_empty() {
                        String::new()
                    } else {
                        format!("; unresolved verification conditions: {}", unresolved.join(", "))
                    }
                ))
            })?;
            verified_loop_rules.push(loop_rule);
        }
        for transition in transitions {
            let mut surface_propositions = context.surface_propositions.clone();
            let mut program_point_states = context.program_point_states.clone();
            if matches!(statement, CStatement::While { .. }) {
                let loop_labels = environment
                    .function_block
                    .structural_clauses()
                    .iter()
                    .filter(|clause| clause.region() == &CodeRegion::Loop(region_index))
                    .filter_map(StructuralClause::label)
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                let entry_point = ProgramPointRef {
                    region: CodeRegionRef::Loop(region_index),
                    kind: ProgramPointKind::Entry,
                };
                program_point_states.insert(entry_point, context.state.clone());
                for label in &loop_labels {
                    program_point_states.insert(
                        ProgramPointRef {
                            region: CodeRegionRef::Label(label.clone()),
                            kind: ProgramPointKind::Entry,
                        },
                        context.state.clone(),
                    );
                }
                if let CStatementOutcome::Normal(exit_state) = &transition.outcome {
                    let exit_point = ProgramPointRef {
                        region: CodeRegionRef::Loop(region_index),
                        kind: ProgramPointKind::Exit,
                    };
                    program_point_states.insert(exit_point.clone(), exit_state.clone());
                    for label in &loop_labels {
                        program_point_states.insert(
                            ProgramPointRef {
                                region: CodeRegionRef::Label(label.clone()),
                                kind: ProgramPointKind::Exit,
                            },
                            exit_state.clone(),
                        );
                    }
                    if let Some(loop_clause) = environment
                        .function_block
                        .structural_clauses()
                        .iter()
                        .find(|clause| clause.region() == &CodeRegion::Loop(region_index))
                    {
                        let mut invariant_targets = transition.pure_facts.iter().filter(|fact| {
                            !context.pure_facts.contains(fact)
                                && !matches!(
                                    fact,
                                    Proposition::CMemoryEffectSummary { .. }
                                        | Proposition::CMemoryMutatesOnly { .. }
                                )
                        });
                        for surface in loop_clause
                            .items()
                            .iter()
                            .filter(|item| item.kind() == StructuralItemKind::Invariant)
                            .filter_map(StructuralItem::proposition)
                        {
                            let target = invariant_targets.next().ok_or_else(|| {
                                ClickError::new(format!(
                                    "execution proof traversal loop({region_index}) omitted an exported fact for an invariant"
                                ))
                            })?;
                            let exit_surface = surface_with_source_site(surface, &exit_point)?;
                            surface_propositions.record_lowering(&exit_surface, target)?;
                        }
                    }
                    if let CStatement::While { condition, .. } = statement {
                        let exit_condition =
                            ClickProposition::Not(Box::new(surface_c_condition(condition)));
                        let lowered_exit_condition = lower_point_proposition(
                            &exit_condition,
                            &transition.pure_facts,
                            environment.parsed_function.parameters(),
                            environment.arguments,
                            environment.initial_state,
                            exit_state,
                            None,
                            &program_point_states,
                            environment.predicate_environment,
                            environment.click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "could not lower loop({region_index}) exit condition provenance: {message}"
                            ))
                        })?;
                        if transition.pure_facts.contains(&lowered_exit_condition) {
                            let exit_surface =
                                surface_with_source_site(&exit_condition, &exit_point)?;
                            surface_propositions
                                .record_lowering(&exit_surface, &lowered_exit_condition)?;
                        }
                    }
                }
            }
            match transition.outcome {
                CStatementOutcome::Normal(state) => advanced.push(ExecutionProofContext {
                    state,
                    pure_facts: transition.pure_facts,
                    surface_propositions,
                    program_point_states,
                    case_path: context.case_path.clone(),
                    next_opaque_call: context.next_opaque_call,
                    next_verification_variable: context.next_verification_variable,
                }),
                CStatementOutcome::Return { .. } => {}
                CStatementOutcome::UndefinedBehavior(kind) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal produced undefined behavior: {kind:?}"
                    )));
                }
                CStatementOutcome::RuntimeError(error) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({region_index}) produced runtime error: {error:?}\navailable resources: {:?}",
                        environment.function_block.signature().name(),
                        context.state.resources().facts()
                    )));
                }
            }
        }
    }
    Ok(advanced)
}

#[allow(clippy::too_many_arguments)]
fn verify_loop_initialization_pure_proof(
    loop_index: usize,
    proof: &Proof,
    clause: &StructuralClause,
    context: &ExecutionProofContext,
    invariant_checks: &[CLoopInvariantCheck],
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<TacticCertificate, ClickError> {
    let claim_label = format!(
        "{}.loop({loop_index}).initialize",
        environment.function_block.signature().name()
    );
    let mut program_point_states = context.program_point_states.clone();
    program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        context.state.clone(),
    );
    for label in environment
        .function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .filter_map(StructuralClause::label)
    {
        program_point_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind: ProgramPointKind::Entry,
            },
            context.state.clone(),
        );
    }
    let invariant_items = clause
        .items()
        .iter()
        .filter(|item| item.kind() == StructuralItemKind::Invariant)
        .collect::<Vec<_>>();
    let initialization_surface_propositions =
        std::cell::RefCell::new(context.surface_propositions.clone());
    // The whole initialize phase is one source `by` clause, so every step it
    // plans or replays reports source tactic 0 — the clause itself — and the
    // loop's body entry as its statement. Computing the layout is only worth
    // it when something will read the timings.
    let timings_enabled = std::env::var_os("CLICK_TIMINGS").is_some();
    let initialize_source_index = 0;
    let initialize_statement_index = if timings_enabled {
        SourceExecutionLayout::new(environment.parsed_function.body())
            .loop_body_entry(loop_index)
            .unwrap_or(0)
    } else {
        0
    };
    let entry_obligations = c_loop_invariant_obligations_at_entry(
        &context.state,
        invariant_checks,
        &assumptions_from_propositions(&context.pure_facts),
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    let (certificate, available) = pure_goal_certificate_gateway(
        &claim_label,
        || {
            let mut planning_available = context.pure_facts.clone();
            let mut tactics = Vec::new();
            for (invariant_index, item) in invariant_items.iter().enumerate() {
                let proposition = item
                    .proposition()
                    .expect("invariant region proof item should contain a proposition");
                let invariant_claim_label =
                    format!("{claim_label} (loop {loop_index} invariant {invariant_index} entry)");
                let obligation_context =
                    format!("loop {loop_index} invariant {invariant_index} entry");
                let expected_goal = entry_obligations
                    .iter()
                    .find(|obligation| obligation.context() == Some(&obligation_context))
                    .map(|obligation| obligation.proposition().clone());
                let planning_assumptions = assumptions_from_propositions(&planning_available);
                let expected_goal = expected_goal.map(|mut expected_goal| {
                    while let Proposition::Implies(antecedent, body) = &expected_goal {
                        if !planning_assumptions.proves(antecedent) {
                            break;
                        }
                        expected_goal = body.as_ref().clone();
                    }
                    expected_goal
                });
                // Planning an invariant's entry proof is proof search, not
                // replay. Classify it by the `by` clause the search is
                // discharging, exactly as if it were written as a `have`.
                let planned_step = timings_enabled.then(|| {
                    ProofTactic::Have(ProofHave {
                        proposition: proposition.clone(),
                        proof: proof.clone(),
                    })
                });
                let _timing = planned_step.as_ref().and_then(|planned_step| {
                    TacticTiming::named_for_tactic(
                        &claim_label,
                        "plan_invariant_entry",
                        planned_step,
                        invariant_index,
                        initialize_source_index,
                        initialize_statement_index,
                    )
                });
                let direct_plan = plan_point_pure_goal_certificate(
                    &ProofSite::LoopPhase {
                        function_name: environment.function_block.signature().name().to_string(),
                        loop_index,
                        phase: "initialize",
                    },
                    proposition,
                    proof,
                    &invariant_claim_label,
                    invariant_index,
                    &planning_available,
                    environment.parsed_function.parameters(),
                    environment.arguments,
                    environment.initial_state,
                    &context.state,
                    &program_point_states,
                    environment.predicate_environment,
                    environment.click_function_environment,
                    &context.surface_propositions,
                    expected_goal.as_ref(),
                    environment.theorem_environment,
                )?;
                let (planned_fact, planned_certificate) = direct_plan;
                initialization_surface_propositions
                    .borrow_mut()
                    .record_lowering(proposition, &planned_fact)?;
                tactics.push(ProofTactic::Have(ProofHave {
                    proposition: proposition.clone(),
                    proof: Proof::Script(planned_certificate.tactics().to_vec()),
                }));
                if !planning_available.contains(&planned_fact) {
                    planning_available.push(planned_fact);
                }
            }
            TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` produced an invalid initialization certificate: {error:?}"
                ))
            })
        },
        |certificate| {
            if certificate.tactics().len() < invariant_items.len() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` certificate has only {} steps for {} invariants",
                    certificate.tactics().len(),
                    invariant_items.len()
                )));
            }
            let mut replay_available = context.pure_facts.clone();
            let invariant_start = certificate.tactics().len() - invariant_items.len();
            for (certificate_index, tactic) in certificate.tactics().iter().enumerate() {
                // Certificate replay for the initialize phase never reaches
                // `replay_linear_tactics`, so time each step here in the same
                // format and let `source_tactic_class` classify it.
                let _timing = TacticTiming::new(
                    &claim_label,
                    certificate_index,
                    initialize_source_index,
                    tactic,
                    initialize_statement_index,
                );
                if certificate_index < invariant_start
                    && let ProofTactic::UnfoldPredicate(name) = tactic
                {
                    if environment.predicate_environment.get(name).is_none() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index} names unknown predicate `{name}`"
                        )));
                    }
                    replay_available = unfold_available_predicate_facts(
                        environment.predicate_environment,
                        environment.click_function_environment,
                        std::slice::from_ref(name),
                        &replay_available,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index}: {message}"
                        ))
                    })?;
                    continue;
                }
                let ProofTactic::Have(have) = tactic else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` certificate step {certificate_index} is not a pure `have`"
                    )));
                };
                let invariant_index = certificate_index.checked_sub(invariant_start);
                if let Some(invariant_index) = invariant_index {
                    let proposition = invariant_items[invariant_index]
                        .proposition()
                        .expect("invariant region proof item should contain a proposition");
                    if &have.proposition != proposition {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index} changed invariant {invariant_index}"
                        )));
                    }
                }
                let step_claim_label = invariant_index
                    .map(|invariant_index| {
                        format!(
                            "{claim_label} (loop {loop_index} invariant {invariant_index} entry)"
                        )
                    })
                    .unwrap_or_else(|| format!("{claim_label} prerequisite {certificate_index}"));
                let surface_propositions = initialization_surface_propositions.borrow();
                let fact = prove_pure_proposition_at_point(
                    &have.proposition,
                    surface_propositions.unique_kernel(&have.proposition),
                    &have.proof,
                    "initialize",
                    environment.theorem_environment,
                    &step_claim_label,
                    certificate_index,
                    &replay_available,
                    environment.parsed_function.parameters(),
                    environment.arguments,
                    environment.initial_state,
                    &context.state,
                    None,
                    &program_point_states,
                    Some(&surface_propositions),
                    environment.predicate_environment,
                    environment.click_function_environment,
                    environment.function_block.requires(),
                    None,
                )?;
                if !replay_available.contains(&fact) {
                    replay_available.push(fact);
                }
            }
            Ok(replay_available)
        },
    )?;
    let assumptions = assumptions_from_propositions(&available);
    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    Ok(certificate)
}

#[allow(clippy::too_many_arguments)]
fn plan_automatic_loop_preservation_body(
    loop_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    body: &CStatement,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<TacticCertificate, ClickError> {
    let claim_label = format!(
        "{}.loop({loop_index}).preserve",
        environment.function_block.signature().name()
    );
    let sentinel = CStatement::Return(CExpression::Value(int32(0)));
    let remaining = c_seq(body.clone(), sentinel.clone());
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        frontier: ExecutionFrontier {
            point: ProofExecutionPoint::StatementEntry { remaining },
            execution_start_state: Some(preservation.state().clone()),
            next_statement_index: loop_body_statement_index,
            ..ExecutionFrontier::default()
        },
        source_layout,
        region_proof: true,
        loop_invariant_region: true,
        function_entry_state: Some(environment.initial_state.clone()),
        surface_propositions: environment.surface_propositions.clone(),
        ..TacticReplayState::default()
    };
    record_statement_program_point_state(
        &mut replay,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_loop_program_point_state(
        &mut replay,
        environment.function_block,
        loop_index,
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    let mut pending = vec![ProofReplayContext {
        state: preservation.state().clone(),
        pure_facts: pure_facts.to_vec(),
        replay,
        branch_path: Vec::new(),
    }];
    let mut completed = Vec::new();
    let mut steps = 0;
    while let Some(context) = pending.pop() {
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if at_back_edge {
            completed.push(context);
            continue;
        }
        if steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget"
            )));
        }
        steps += 1;
        let is_branch = context
            .replay
            .source_layout
            .statement(context.replay.frontier.next_statement_index)
            .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }));
        let candidates = if is_branch {
            let ProofExecutionPoint::StatementEntry { remaining } = &context.replay.frontier.point
            else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` automatic preservation branch is not at a statement entry"
                )));
            };
            let assertion_prefix_count = source_assertion_prefix_count(
                environment.function_block,
                context.replay.frontier.next_statement_index,
                None,
            );
            let (_, source_statement, _) =
                split_next_source_operation(remaining, assertion_prefix_count)
                    .map_err(ClickError::new)?;
            let CStatement::If { condition, .. } = source_statement else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` source branch does not match the lowered statement"
                )));
            };
            vec![ProofTactic::If(ProofIf {
                condition: surface_c_condition(&condition),
                then_tactics: vec![ProofTactic::ExecuteThenStep],
                else_tactics: vec![ProofTactic::ExecuteElseStep],
            })]
        } else {
            vec![ProofTactic::ExecuteStep]
        };
        let mut advanced = Vec::new();
        let mut errors = Vec::new();
        for tactic in candidates {
            let program = build_internal_proof(std::slice::from_ref(&tactic), &claim_label)?;
            match execute_internal_proof(
                &program,
                context.clone(),
                environment.function_block,
                environment.parsed_function,
                &[],
                &claim_label,
                environment.function_environment,
                environment.predicate_environment,
                environment.click_function_environment,
                environment.resource_environment,
                environment.theorem_environment,
                environment.function,
                environment.arguments,
            ) {
                Ok(contexts) => advanced.extend(contexts),
                Err(error) => errors.push(error),
            }
        }
        if advanced.is_empty() {
            return Err(errors.pop().unwrap_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` automatic preservation could not advance the loop body"
                ))
            }));
        }
        pending.extend(advanced);
    }
    let mut paths = Vec::new();
    for context in completed {
        if let Some(blocker) = &context.replay.surface_replay.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation could not lower a body step: {blocker}"
            )));
        }
        let case_path = context
            .replay
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let certificate = certificate_leaf_for_case_path(
            &claim_label,
            &context.replay.surface_replay.tactics,
            &case_path,
        )?;
        paths.push(PathCertificate {
            case_path,
            certificate,
        });
    }
    merge_path_aligned_certificates(&claim_label, paths)
}

#[allow(clippy::too_many_arguments)]
fn verify_structural_effect_proof(
    loop_index: usize,
    item_index: usize,
    item: &StructuralItem,
    check: &CLoopEffectCheck,
    before_state: &CState,
    context: &ProofReplayContext,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<TacticCertificate, ClickError> {
    let site = ProofSite::StructuralItem {
        function_name: environment.function_block.signature().name().to_string(),
        region: CodeRegion::Loop(loop_index),
        item_index,
        kind: item.kind(),
    };
    let claim_label = site.description();
    let certificate = match item.proof() {
        Proof::Default | Proof::Tactic(SmartTactic::Auto) | Proof::Tactic(SmartTactic::Frame) => {
            TacticCertificate::from_proof_tactics(&[ProofTactic::Frame(None)])
        }
        Proof::Script(tactics) => TacticCertificate::from_proof_tactics(tactics),
        Proof::Tactic(SmartTactic::Simp) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` must use `auto`, `frame`, or a simple proof script"
            )));
        }
    }
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` produced an invalid structural-effect certificate: {error:?}"
        ))
    })?;
    let program = build_internal_proof(certificate.tactics(), &claim_label)?;
    let mut replay = context.replay.clone();
    replay.proof_site = Some(site);
    replay.loop_effect_goal = Some(LoopEffectReplayGoal {
        before_state: before_state.clone(),
        check: check.clone(),
        closed: false,
    });
    replay.surface_replay = SurfaceReplay::default();
    let replayed = execute_internal_proof(
        &program,
        ProofReplayContext {
            state: context.state.clone(),
            pure_facts: context.pure_facts.clone(),
            replay,
            branch_path: context.branch_path.clone(),
        },
        environment.function_block,
        environment.parsed_function,
        &[],
        &claim_label,
        environment.function_environment,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.resource_environment,
        environment.theorem_environment,
        environment.function,
        environment.arguments,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` structural-effect certificate failed ordinary replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    if replayed.is_empty()
        || replayed.iter().any(|context| {
            !context
                .replay
                .loop_effect_goal
                .as_ref()
                .is_some_and(|goal| goal.closed)
        })
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` structural-effect certificate did not close every replay path"
        )));
    }
    Ok(certificate)
}

struct LoopPreservationProofResult {
    certificate: TacticCertificate,
    effect_certificates: Vec<(usize, TacticCertificate)>,
}

#[allow(clippy::too_many_arguments)]
fn verify_one_loop_preservation_proof(
    loop_index: usize,
    tactics: &[ProofTactic],
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<LoopPreservationProofResult, ClickError> {
    let claim_label = format!(
        "{}.loop({loop_index}).preserve",
        environment.function_block.signature().name()
    );

    let proof_claims = [];
    // Positive closer results from the planner half, keyed by the exact
    // inputs that vary between contexts: the back-edge state and the pure
    // facts the closer's assumptions are built from. `loop_entry_state` and
    // `invariant_checks` are identical for both halves by construction. The
    // certificate replay below re-runs the same deterministic derivation on
    // identical inputs, so an exact-key hit reuses the planner's Ok instead
    // of re-deriving it; any input difference falls through to the full
    // check, so a would-fail replay can never be turned into a pass.
    let mut verified_closer_inputs: Vec<(CState, Vec<Proposition>)> = Vec::new();
    let program = build_internal_proof(tactics, &claim_label)?;
    let sentinel = CStatement::Return(CExpression::Value(int32(0)));
    let remaining = c_seq(body.clone(), sentinel.clone());
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        proof_site: Some(ProofSite::LoopPhase {
            function_name: environment.function_block.signature().name().to_string(),
            loop_index,
            phase: "preserve",
        }),
        frontier: ExecutionFrontier {
            point: ProofExecutionPoint::StatementEntry { remaining },
            execution_start_state: Some(preservation.state().clone()),
            next_statement_index: loop_body_statement_index,
            ..ExecutionFrontier::default()
        },
        source_layout,
        region_proof: true,
        loop_invariant_region: true,
        function_entry_state: Some(environment.initial_state.clone()),
        surface_propositions: environment.surface_propositions.clone(),
        ..TacticReplayState::default()
    };
    record_statement_program_point_state(
        &mut replay,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    replay.program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        preservation.loop_entry_state().clone(),
    );
    let replay_start = replay.clone();
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state: preservation.state().clone(),
            pure_facts: pure_facts.to_vec(),
            replay,
            branch_path: Vec::new(),
        },
        environment.function_block,
        environment.parsed_function,
        &proof_claims,
        &claim_label,
        environment.function_environment,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.resource_environment,
        environment.theorem_environment,
        environment.function,
        environment.arguments,
    )?;
    let mut certificate_paths = Vec::new();
    for context in &contexts {
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if !at_back_edge {
            return Err(ClickError::new(format!(
                "`{claim_label}` must execute exactly one complete loop-body iteration"
            )));
        }
        let (closer_index, closer_source, closer_name, closer_class) =
            if let Some((tactic_index, source_index)) = context.replay.region_simp {
                (tactic_index, source_index, "simp", "smart")
            } else {
                (tactics.len(), tactics.len(), "assumption", "simple")
            };
        let _timing = std::env::var_os("CLICK_TIMINGS").is_some().then(|| {
            if std::env::var_os("CLICK_TIMING_STARTS").is_some() {
                eprintln!(
                    "click timing: started tactic {} {} {} class {} statement {} source {}",
                    claim_label,
                    closer_index,
                    closer_name,
                    closer_class,
                    context.replay.frontier.next_statement_index,
                    closer_source
                );
            }
            TacticTiming {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class,
                statement_index: context.replay.frontier.next_statement_index,
                start: std::time::Instant::now(),
            }
        });
        let closer_tactics = if invariant_checks.is_empty()
            || context.replay.region_invariants_closed
        {
            Vec::new()
        } else {
            if let Err(message) = c_loop_invariants_hold_at_back_edge_using(
                &context.state,
                preservation.loop_entry_state(),
                invariant_checks,
                &assumptions_from_propositions(&context.pure_facts),
            ) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} invariant bundle preservation) could not certify every guarded invariant-lowering path: {message}"
                )));
            }
            verified_closer_inputs.push((context.state.clone(), context.pure_facts.clone()));
            vec![ProofTactic::CloseInvariants]
        };
        if context.replay.region_simp.is_some_and(|(_, source_index)| {
            tactic_expansion_capture_matches(context.replay.proof_site.as_ref(), source_index)
        }) {
            let capture = SurfaceReplay {
                tactics: closer_tactics.clone(),
                ..SurfaceReplay::default()
            };
            return Err(finish_tactic_expansion_capture(&capture, false));
        }
        let case_path = context
            .replay
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let prefix = certificate_leaf_for_case_path(
            &claim_label,
            &context.replay.surface_replay.tactics,
            &case_path,
        )?;
        let mut leaf_tactics = prefix.tactics().to_vec();
        leaf_tactics.extend(closer_tactics);
        let certificate =
            TacticCertificate::from_proof_tactics(&leaf_tactics).map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` produced an invalid preservation leaf certificate: {error:?}"
                ))
            })?;
        certificate_paths.push(PathCertificate {
            case_path,
            certificate,
        });
    }
    let certificate = merge_path_aligned_certificates(&claim_label, certificate_paths)?;
    let certificate_program = build_internal_proof(certificate.tactics(), &claim_label)?;
    let replayed = execute_internal_proof(
        &certificate_program,
        ProofReplayContext {
            state: preservation.state().clone(),
            pure_facts: pure_facts.to_vec(),
            replay: replay_start,
            branch_path: Vec::new(),
        },
        environment.function_block,
        environment.parsed_function,
        &proof_claims,
        &claim_label,
        environment.function_environment,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.resource_environment,
        environment.theorem_environment,
        environment.function,
        environment.arguments,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` preservation certificate failed ordinary replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    let effect_items = environment
        .function_block
        .structural_clauses()
        .iter()
        .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .into_iter()
        .flat_map(|clause| clause.items().iter().enumerate())
        .filter(|(_, item)| item.is_effect_kind())
        .collect::<Vec<_>>();
    if effect_items.len() != effect_checks.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has {} structural effect items but {} lowered effect checks",
            effect_items.len(),
            effect_checks.len()
        )));
    }
    let mut effect_certificate_paths = vec![Vec::new(); effect_items.len()];
    for context in replayed {
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if !at_back_edge {
            return Err(ClickError::new(format!(
                "`{claim_label}` replayed certificate did not finish at the loop back edge"
            )));
        }
        if context.replay.region_invariants_closed != !invariant_checks.is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` replayed the wrong number of invariant-bundle closers"
            )));
        }
        if !invariant_checks.is_empty() {
            // `close_invariants` only sets a flag while the certificate
            // replays; this is where the bundle is actually re-derived, so
            // this is where that tactic's time is spent. Time it against the
            // tactic's own identity and let `source_tactic_class` classify it.
            let _timing = context.replay.invariant_closer_step.and_then(|step| {
                TacticTiming::new(
                    &claim_label,
                    step.tactic_index,
                    step.source_index,
                    &ProofTactic::CloseInvariants,
                    step.statement_index,
                )
            });
            let planner_already_verified =
                std::env::var_os("CLICK_DISABLE_CLOSER_REUSE").is_none()
                    && verified_closer_inputs.iter().any(|(state, facts)| {
                        state == &context.state && facts == &context.pure_facts
                    });
            if !planner_already_verified {
                c_loop_invariants_hold_at_back_edge_using(
                    &context.state,
                    preservation.loop_entry_state(),
                    invariant_checks,
                    &assumptions_from_propositions(&context.pure_facts),
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` invariant bundle: {message}"))
                })?;
            }
        }
        let case_path = context
            .replay
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        for (effect_index, ((item_index, item), check)) in
            effect_items.iter().zip(effect_checks).enumerate()
        {
            let effect_certificate = verify_structural_effect_proof(
                loop_index,
                *item_index,
                item,
                check,
                preservation.state(),
                &context,
                environment,
            )?;
            effect_certificate_paths[effect_index].push(PathCertificate {
                case_path: case_path.clone(),
                certificate: effect_certificate,
            });
        }
    }
    let effect_certificates = effect_items
        .iter()
        .zip(effect_certificate_paths)
        .map(|((item_index, item), paths)| {
            let site = ProofSite::StructuralItem {
                function_name: environment.function_block.signature().name().to_string(),
                region: CodeRegion::Loop(loop_index),
                item_index: *item_index,
                kind: item.kind(),
            };
            Ok((
                *item_index,
                merge_path_aligned_certificates(&site.description(), paths)?,
            ))
        })
        .collect::<Result<Vec<_>, ClickError>>()?;
    Ok(LoopPreservationProofResult {
        certificate,
        effect_certificates,
    })
}

#[allow(clippy::too_many_arguments)]
fn apply_theorem_at_current_point(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    tactic_index: usize,
    available: Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    lowering_context: Option<&[Proposition]>,
) -> Result<Vec<Proposition>, ClickError> {
    let values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state: state,
        result: None,
        program_point_states,
    };
    let available = apply_theorem_applications_to_available_with_lowering_context(
        theorem_environment,
        &[(tactic_index, application.clone())],
        claim_label,
        None,
        available,
        lowering_context,
        &context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    Ok(available)
}

#[allow(clippy::too_many_arguments)]
fn lower_theorem_application_requirements(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    premises: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, String> {
    let theorem = theorem_environment
        .get(&application.name)
        .ok_or_else(|| format!("unknown theorem `{}`", application.name))?;
    let assumptions = assumptions_from_propositions(premises);
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        &assumptions,
        predicate_environment,
        click_function_environment,
    )?;
    let mut lowerer = KernelPropositionLowerer::new(
        values,
        array_refs,
        context.post_state.memory().clone(),
        predicate_environment,
        click_function_environment,
    );
    theorem
        .requires()
        .iter()
        .map(|requirement| {
            let requirement = requirement.proposition().ok_or_else(|| {
                format!(
                    "theorem `{}` has a non-proposition requirement",
                    theorem.name()
                )
            })?;
            let lowered = lowerer
                .lower_requirement_proposition(requirement)
                .map_err(|error| error.message().to_string())?;
            unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &lowered,
                &assumptions,
            )
            .map(|lowered| normalize_direct_atomic_memory_loads(&lowered))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn plan_explicit_theorem_application(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    replay: &TacticReplayState,
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ClickProposition>, ClickError> {
    let pre_state = replay.old_reference_state(state);
    let values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state: state,
        result: None,
        program_point_states: &replay.program_point_states,
    };
    let requirements = lower_theorem_application_requirements(
        theorem_environment,
        application,
        &context,
        available,
        predicate_environment,
        click_function_environment,
        &replay.unfolded_predicates,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower theorem requirements: {message}"
        ))
    })?;
    let mut lowering_facts = available.to_vec();
    append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
    let mut selected = Vec::new();
    for requirement in requirements {
        if matches!(normalize_proposition(&requirement), SimpProposition::True) {
            continue;
        }
        let matched = materialization_equivalent_available_fact(&requirement, available)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "theorem application `{}` requires an unavailable exact premise: {requirement:?}",
                    application.name
                ))
            })?;
        let surface = checked_surface_comparison_fact_at_point(
            replay,
            &matched,
            SurfaceFactMatch::CanonicalExact,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "theorem application `{}` has no checked Click spelling for exact premise `{requirement:?}`: {}",
                application.name,
                error.message(),
            ))
        })?;
        let lowered = lower_point_proposition(
            &surface,
            &lowering_facts,
            parameters,
            arguments,
            pre_state,
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "theorem application `{}` could not check premise `{}`: {message}",
                application.name,
                describe_click_proposition(&surface),
            ))
        })?;
        if materialization_equivalent_available_fact(&lowered, available).is_none() {
            return Err(ClickError::new(format!(
                "theorem application `{}` synthesized a premise that is not exactly available\n  Click: {}\n  lowered: {lowered:?}\n  required: {requirement:?}",
                application.name,
                describe_click_proposition(&surface),
            )));
        }
        if !selected
            .iter()
            .any(|(_, selected_surface)| selected_surface == &surface)
        {
            selected.push((matched, surface));
        }
    }
    let application_replays = |selected: &[(Proposition, ClickProposition)]| {
        let mut lowering_facts = available.to_vec();
        append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
        let mut explicit_premises = Vec::new();
        for (_, surface) in selected {
            let premise = if let Some(recorded) = replay
                .surface_propositions
                .available_kernel(surface, available)
            {
                recorded.clone()
            } else {
                let Ok(premise) = lower_point_proposition(
                    surface,
                    &lowering_facts,
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                ) else {
                    return Err(ClickError::new(format!(
                        "could not lower explicit premise `{}`",
                        describe_click_proposition(surface),
                    )));
                };
                premise
            };
            if !exact_fact_is_available(&premise, available)
                && materialization_equivalent_available_fact(&premise, available).is_none()
            {
                return Err(ClickError::new(format!(
                    "explicit premise `{}` did not lower to an available fact: {premise:?}",
                    describe_click_proposition(surface),
                )));
            }
            if !explicit_premises.contains(&premise) {
                explicit_premises.push(premise);
            }
        }
        apply_theorem_at_current_point(
            theorem_environment,
            application,
            claim_label,
            tactic_index,
            explicit_premises,
            parameters,
            arguments,
            pre_state,
            state,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            Some(&lowering_facts),
        )
    };
    if let Err(error) = application_replays(&selected) {
        return Err(ClickError::new(format!(
            "theorem application `{}` did not replay from its exact synthesized premises: {}\n  premises: {}",
            application.name,
            error.message(),
            selected
                .iter()
                .map(|(kernel, surface)| format!(
                    "{} => {kernel:?}",
                    describe_click_proposition(surface)
                ))
                .collect::<Vec<_>>()
                .join("\n            "),
        )));
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_fact_at_outcome(
    replay: &TacticReplayState,
    kernel: &Proposition,
    match_kind: SurfaceFactMatch,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let lowering_facts = facts_for_smart_have_lowering(available);
    let check = |surface: &ClickProposition| {
        lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            &lowering_facts,
            surface,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
        .map_err(ClickError::new)
    };
    let matches_kernel = |lowered: &Proposition| {
        if matches!(match_kind, SurfaceFactMatch::CanonicalExact) {
            return condition_polarity_equivalent(lowered, kernel);
        }
        condition_polarity_equivalent(
            &normalize_direct_atomic_memory_loads(lowered),
            &normalize_direct_atomic_memory_loads(kernel),
        ) || materialization_equivalent_available_fact(
            &normalize_direct_atomic_memory_loads(kernel),
            std::slice::from_ref(&normalize_direct_atomic_memory_loads(lowered)),
        )
        .is_some()
            || quantified_replay_equivalent_available_fact(kernel, std::slice::from_ref(lowered))
                .is_some()
    };
    // Recorded source spellings are the cheapest exact candidates and cover
    // ordinary premises. Check them before synthesizing variants at every
    // retained program point; an ambiguous spelling simply fails `check` and
    // falls through to the point-qualified search below.
    if let Ok(surface) = replay.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    for (point, point_state) in replay.program_point_states.iter().rev() {
        let Some(base) = synthesize_surface_proposition(kernel, parameters, arguments, point_state)
        else {
            continue;
        };
        let Some(variants) = comparison_program_point_variants(&base, std::slice::from_ref(point))
        else {
            continue;
        };
        for candidate in variants {
            if check(&candidate).is_ok_and(|lowered| matches_kernel(&lowered)) {
                return Ok(candidate);
            }
        }
    }
    let mut bases = Vec::new();
    if let Ok(surface) = replay.surface_propositions.surface(kernel) {
        bases.push(surface.clone());
    }
    for recorded in replay.surface_propositions.kernel_facts() {
        // The quantifier-shape test is checked first on purpose: it is the
        // weaker of the two conditions, so whenever it holds the mutual
        // `derive_simp_proposition` search below is redundant — and on nested
        // quantified predicate bodies that search costs minutes.
        if (matches!(
            (kernel, recorded),
            (Proposition::ForAll { .. }, Proposition::ForAll { .. })
        ) || quantified_replay_equivalent_available_fact(kernel, std::slice::from_ref(recorded))
            .is_some())
            && let Ok(surface) = replay.surface_propositions.surface(recorded)
            && !bases.contains(surface)
        {
            bases.push(surface.clone());
        }
    }
    if let Some(surface) = synthesize_surface_proposition(kernel, parameters, arguments, post_state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    let points = replay
        .program_point_states
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    for base in &bases {
        let Some(variants) = comparison_program_point_variants(base, &points) else {
            continue;
        };
        for candidate in variants {
            if check(&candidate).is_ok_and(|lowered| matches_kernel(&lowered)) {
                return Ok(candidate);
            }
        }
    }
    for (point, point_state) in &replay.program_point_states {
        let Some(base) = synthesize_surface_proposition(kernel, parameters, arguments, point_state)
        else {
            continue;
        };
        let Some(variants) = comparison_program_point_variants(&base, std::slice::from_ref(point))
        else {
            continue;
        };
        for candidate in variants {
            if check(&candidate).is_ok_and(|lowered| matches_kernel(&lowered)) {
                return Ok(candidate);
            }
        }
    }
    // A drain that unfolds predicates unfolds its ambient facts too, and the
    // unfolded body of an opaque predicate is not itself a recorded fact, so
    // it has no spelling of its own. Unfold a spelling of the FOLDED fact at
    // the surface instead — the same rewrite the script's `unfold(...)`
    // performs — and let the round trip below decide whether the result is the
    // fact we were asked for.
    if matches!(kernel, Proposition::ForAll { .. } | Proposition::Exists { .. })
        && !replay.unfolded_predicates.is_empty()
    {
        // A drain that unfolds an ambient predicate replaces the folded fact
        // with its quantified body, so the body can carry a recorded folded
        // spelling while no Predicate fact survives in `available` for the
        // loop below to start from. Unfold that recorded spelling at the
        // surface and let the round trip decide.
        let mut kernel_folded_bases = Vec::new();
        for surface in replay.surface_propositions.surfaces(kernel) {
            if matches!(surface, ClickProposition::PredicateCall { .. })
                && !kernel_folded_bases.contains(surface)
            {
                kernel_folded_bases.push(surface.clone());
            }
        }
        for base in &kernel_folded_bases {
            let Some(variants) = comparison_program_point_variants(base, &points) else {
                continue;
            };
            for candidate in variants {
                let Ok(unfolded) = unfold_structural_invariant_proposition(
                    predicate_environment,
                    &candidate,
                    &replay.unfolded_predicates,
                ) else {
                    continue;
                };
                if unfolded == candidate {
                    continue;
                }
                if check(&unfolded).is_ok_and(|lowered| {
                    matches_kernel(&lowered)
                        || nested_quantified_binder_equivalent(&lowered, kernel, 8)
                }) {
                    return Ok(unfolded);
                }
            }
        }
        for fact in available {
            if !matches!(fact, Proposition::Predicate { .. }) {
                continue;
            }
            let mut folded_bases = Vec::new();
            for surface in replay.surface_propositions.surfaces(fact) {
                if !folded_bases.contains(surface) {
                    folded_bases.push(surface.clone());
                }
            }
            for state in std::iter::once(post_state).chain(replay.program_point_states.values()) {
                if let Some(surface) =
                    synthesize_surface_proposition(fact, parameters, arguments, state)
                    && !folded_bases.contains(&surface)
                {
                    folded_bases.push(surface);
                }
            }
            for base in &folded_bases {
                let Some(variants) = comparison_program_point_variants(base, &points) else {
                    continue;
                };
                for candidate in variants {
                    let Ok(unfolded) = unfold_structural_invariant_proposition(
                        predicate_environment,
                        &candidate,
                        &replay.unfolded_predicates,
                    ) else {
                        continue;
                    };
                    if unfolded == candidate {
                        continue;
                    }
                    if check(&unfolded).is_ok_and(|lowered| {
                        matches_kernel(&lowered)
                            || nested_quantified_binder_equivalent(&lowered, kernel, 8)
                    }) {
                        return Ok(unfolded);
                    }
                }
            }
        }
    }
    let surface = synthesize_surface_proposition(kernel, parameters, arguments, post_state)
        .ok_or_else(|| {
            ClickError::new(format!(
                "no checked Click spelling for post-execution fact {kernel:?}"
            ))
        })?;
    if matches_kernel(&check(&surface)?) {
        Ok(surface)
    } else {
        Err(ClickError::new(format!(
            "synthesized post-execution spelling did not lower to {kernel:?}"
        )))
    }
}

#[allow(clippy::too_many_arguments)]
fn apply_theorem_using_at_outcome(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    surface_premises: &[ClickProposition],
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let mut lowering_available = available.clone();
    append_resource_context_observable_facts(post_state.resources(), &mut lowering_available);
    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let premise = lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            &lowering_available,
            surface_premise,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `apply using` premise: {message}"
            ))
        })?;
        if !exact_fact_is_available(&premise, &available)
            && materialization_equivalent_available_fact(&premise, &available).is_none()
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: `apply using` requires an exact post-execution premise: {premise:?}"
            )));
        }
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }
    let values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let application_context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state,
        result: Some(result),
        program_point_states: &replay.program_point_states,
    };
    let mut applied = apply_theorem_applications_to_available_with_lowering_context(
        theorem_environment,
        &[(tactic_index, application.clone())],
        claim_label,
        Some(path_index),
        explicit_premises,
        Some(&lowering_available),
        &application_context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    for fact in available {
        if !applied.contains(&fact) {
            applied.push(fact);
        }
    }
    Ok(applied)
}

#[allow(clippy::too_many_arguments)]
fn plan_explicit_theorem_application_at_outcome(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<ClickProposition>, ClickError> {
    let candidates = available
        .iter()
        .filter_map(|kernel| {
            checked_surface_fact_at_outcome(
                replay,
                kernel,
                SurfaceFactMatch::ReplayEquivalent,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            )
            .ok()
            .map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    let application_replays = |selected: &[(Proposition, ClickProposition)]| {
        apply_theorem_using_at_outcome(
            theorem_environment,
            application,
            &selected
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>(),
            claim_label,
            path_index,
            tactic_index,
            available.to_vec(),
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            replay,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )
        .is_ok()
    };
    if !application_replays(&candidates) {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: theorem application depends on a post-execution fact with no checked Click spelling"
        )));
    }
    let mut selected = candidates;
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if application_replays(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

#[allow(clippy::too_many_arguments)]
fn replay_outcome_apply_certificate(
    certificate: &TacticCertificate,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let [
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        },
    ] = certificate.tactics()
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: post-execution `apply` produced an unexpected certificate"
        )));
    };
    apply_theorem_using_at_outcome(
        theorem_environment,
        application,
        premises,
        claim_label,
        path_index,
        tactic_index,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        replay,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: post-execution `apply` certificate failed replay: {}",
            error.message()
        ))
    })
}

#[allow(clippy::too_many_arguments)]
fn plan_explicit_fact_transport(
    surface_source: &ClickProposition,
    source: &Proposition,
    target: &Proposition,
    available: &[Proposition],
    effect_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    replay: &TacticReplayState,
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ClickProposition>, ClickError> {
    let mut candidates = available
        .iter()
        .filter_map(|kernel| {
            let surface = checked_surface_comparison_fact_at_point(
                replay,
                kernel,
                SurfaceFactMatch::ReplayEquivalent,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .ok();
            surface.map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    let mut selected = Vec::new();
    if exact_fact_is_available(source, available) {
        let source_pair = (source.clone(), surface_source.clone());
        if !candidates.contains(&source_pair) {
            candidates.push(source_pair.clone());
        }
        selected.push(source_pair);
    }
    let replays = |selected: &[(Proposition, ClickProposition)]| {
        let explicit = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_assumptions = assumptions_from_propositions(&explicit);
        let resource_facts = state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let selected_assumptions = available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        if selected_assumptions.derive_proposition(source).is_none() {
            return false;
        }
        if selected_assumptions.derive_proposition(target).is_some() {
            return true;
        }
        let transport_assumptions = effect_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        certified_fact_transport_reaches(source, target, state.memory(), &transport_assumptions)
    };

    if !replays(&selected) {
        let rank = |proposition: &Proposition| match proposition {
            Proposition::CResourceSeparate { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. } => 0,
            Proposition::ConditionIs(_, _) => 1,
            Proposition::CMemoryMutatesOnly { .. } | Proposition::CMemoryEffectSummary { .. } => 2,
            _ => 3,
        };
        let mut remaining = candidates
            .iter()
            .filter(|pair| !selected.contains(pair))
            .cloned()
            .collect::<Vec<_>>();
        remaining.sort_by_key(|(kernel, _)| rank(kernel));
        for pair in remaining {
            selected.push(pair);
            if replays(&selected) {
                break;
            }
        }
    }
    if !replays(&selected) {
        let unavailable = available
            .iter()
            .filter(|fact| !candidates.iter().any(|(candidate, _)| candidate == *fact))
            .collect::<Vec<_>>();
        return Err(ClickError::new(format!(
            "explicit surface premises do not replay the certified fact transport\n  source: {source:?}\n  target: {target:?}\n  selected surface premises: {}\n  unspellable ambient facts: {unavailable:#?}",
            selected.len(),
        )));
    }
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if replays(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

#[allow(clippy::too_many_arguments)]
fn replay_fact_transport_at_outcome(
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    surface_premises: Option<&[ClickProposition]>,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: &mut Vec<Proposition>,
    surface_propositions: &mut SurfacePropositionMap,
    transition_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ProofTactic, ClickError> {
    let lower = |surface: &ClickProposition, facts: &[Proposition]| {
        lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            facts,
            surface,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
    };
    let recorded_or_lowered = |surface: &ClickProposition,
                               facts: &[Proposition],
                               recorded_surfaces: &SurfacePropositionMap|
     -> Result<Proposition, ClickError> {
        if let Some(recorded) = recorded_surfaces.available_kernel(surface, facts) {
            Ok(recorded.clone())
        } else {
            lower(surface, facts).map_err(ClickError::new)
        }
    };

    let mut explicit_premises = Vec::new();
    if let Some(surface_premises) = surface_premises {
        for surface_premise in surface_premises {
            let premise =
                recorded_or_lowered(surface_premise, available, surface_propositions).map_err(
                    |error| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport using` premise: {}",
                            error.message()
                        ))
                    },
                )?;
            if !exact_fact_is_available(&premise, available) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}, tactic {tactic_index}: `transport using` requires an exact premise: {premise:?}"
                )));
            }
            surface_propositions.record_lowering(surface_premise, &premise)?;
            if !explicit_premises.contains(&premise) {
                explicit_premises.push(premise);
            }
        }
    }

    let source = recorded_or_lowered(surface_source, available, surface_propositions).map_err(
        |error| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport` source: {}",
                error.message()
            ))
        },
    )?;
    surface_propositions.record_lowering(surface_source, &source)?;
    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
    let selected_assumptions = if surface_premises.is_some() {
        let resource_facts = post_state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            })
    } else {
        assumptions_from_propositions(available)
    };
    // A transport source spelled at a different snapshot than its explicit
    // fact is the same fact when the kernel proves the snapshots agree at
    // the loaded pointers; this previously matched only through the
    // None==None polarity bug, so make the legitimate case deliberate.
    if !exact_fact_is_available(&source, &explicit_premises)
        && !snapshot_bridged_fact_is_available(&source, &explicit_premises, transition_facts)
        && selected_assumptions
            .derive_atomic_proposition(&source)
            .is_none()
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: `transport{}` requires a source derivable from its {}facts: {source:?}",
            if surface_premises.is_some() {
                " using"
            } else {
                ""
            },
            if surface_premises.is_some() {
                "explicit "
            } else {
                "ambient "
            },
        )));
    }

    let mut direct_lowering_facts = facts_for_direct_surface_lowering(available);
    for premise in &explicit_premises {
        if !direct_lowering_facts.contains(premise) {
            direct_lowering_facts.push(premise.clone());
        }
    }
    let target = lower(surface_target, &direct_lowering_facts).map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport` target: {message}"
        ))
    })?;
    surface_propositions.record_lowering(surface_target, &target)?;

    let emitted_premises = if surface_premises.is_some() {
        None
    } else {
        Some(plan_explicit_fact_transport_at_outcome(
            surface_source,
            &source,
            &target,
            available,
            transition_facts,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            replay,
            predicate_environment,
            click_function_environment,
        )?)
    };
    if exact_fact_is_available(&target, available)
        || materialization_equivalent_available_fact(&target, available).is_some()
    {
        if !available.contains(&target) {
            available.push(target.clone());
        }
    } else {
        let transport_assumptions = transition_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        if !certified_fact_transport_reaches(
            &source,
            &target,
            post_state.memory(),
            &transport_assumptions,
        ) {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: no certified frame transport applies to the exact source fact"
            )));
        }
        available.push(target.clone());
    }

    Ok(match emitted_premises {
        Some(premises) => ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        },
        None => ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises: surface_premises.unwrap_or_default().to_vec(),
        },
    })
}

#[allow(clippy::too_many_arguments)]
fn plan_explicit_fact_transport_at_outcome(
    surface_source: &ClickProposition,
    source: &Proposition,
    target: &Proposition,
    available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ClickProposition>, ClickError> {
    let mut candidates = available
        .iter()
        .filter_map(|kernel| {
            checked_surface_fact_at_outcome(
                replay,
                kernel,
                SurfaceFactMatch::ReplayEquivalent,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            )
            .ok()
            .map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    let mut selected = Vec::new();
    if exact_fact_is_available(source, available) {
        let source_pair = (source.clone(), surface_source.clone());
        if !candidates.contains(&source_pair) {
            candidates.push(source_pair.clone());
        }
        selected.push(source_pair);
    }
    let replays = |selected: &[(Proposition, ClickProposition)]| {
        let explicit = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_assumptions = assumptions_from_propositions(&explicit);
        let resource_facts = post_state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let selected_assumptions = available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        if selected_assumptions.derive_proposition(source).is_none() {
            return false;
        }
        if selected_assumptions.derive_proposition(target).is_some() {
            return true;
        }
        let transport_assumptions = transition_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        certified_fact_transport_reaches(
            source,
            target,
            post_state.memory(),
            &transport_assumptions,
        )
    };
    if !replays(&selected) {
        for pair in candidates {
            if !selected.contains(&pair) {
                selected.push(pair);
                if replays(&selected) {
                    break;
                }
            }
        }
    }
    if !replays(&selected) {
        return Err(ClickError::new(
            "post-execution fact transport has no explicit surface-premise certificate",
        ));
    }
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if replays(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

/// Erases every embedded memory snapshot from a comparison proposition so
/// two spellings of the same comparison at different snapshots compare
/// equal; used as a cheap prefilter before attempting a transport proof.
fn memory_erased_comparison(proposition: &Proposition) -> Option<Proposition> {
    fn erase_term(term: &Bitvector32Term) -> Bitvector32Term {
        match term {
            Bitvector32Term::MemoryLoad(_, pointer) => Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(CMemory::default()),
                Box::new(Pointer {
                    block: pointer.block.clone(),
                    offset: erase_offset(&pointer.offset),
                }),
            ),
            Bitvector32Term::Add(left, right) => {
                Bitvector32Term::Add(Box::new(erase_term(left)), Box::new(erase_term(right)))
            }
            Bitvector32Term::Subtract(left, right) => {
                Bitvector32Term::Subtract(Box::new(erase_term(left)), Box::new(erase_term(right)))
            }
            Bitvector32Term::Multiply(left, right) => {
                Bitvector32Term::Multiply(Box::new(erase_term(left)), Box::new(erase_term(right)))
            }
            other => other.clone(),
        }
    }
    fn erase_offset(offset: &PointerOffsetTerm) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::Add(
                Box::new(erase_offset(left)),
                Box::new(erase_offset(right)),
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(erase_term(value)),
                    byte_width: *byte_width,
                }
            }
            other => other.clone(),
        }
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let erased = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::Bitvector32Equal(
            Box::new(erase_term(left)),
            Box::new(erase_term(right)),
        ),
        _ => return None,
    };
    Some(Proposition::ConditionIs(erased, *value))
}

/// The outermost memory snapshot a comparison proposition loads from, used
/// to pick the transport destination for certified-fact matching.
fn proposition_outer_load_memory(proposition: &Proposition) -> Option<&CMemory> {
    fn term_outer(term: &Bitvector32Term) -> Option<&CMemory> {
        match term {
            Bitvector32Term::MemoryLoad(memory, _) => Some(memory),
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right) => {
                term_outer(left).or_else(|| term_outer(right))
            }
            _ => None,
        }
    }
    let Proposition::ConditionIs(condition, _) = proposition else {
        return None;
    };
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right) => {
            term_outer(left).or_else(|| term_outer(right))
        }
        _ => None,
    }
}

/// Like [`certified_fact_transport_reaches`], but first rewrites the source
/// through the transition facts' certified stores, so a fact spelled in
/// pre-store terms can reach a post-store spelling.
fn certified_fact_transport_reaches_through(
    source: &Proposition,
    target: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
    transitions: &[ExecutionPureFact],
) -> bool {
    if certified_fact_transport_reaches(source, target, after, assumptions) {
        return true;
    }
    let rewritten =
        crate::kernel::rewrite_condition_through_certified_stores(source, transitions);
    if &rewritten == source {
        return false;
    }
    let spelled = normalize_direct_atomic_memory_loads(&rewritten)
        == normalize_direct_atomic_memory_loads(target)
        || crate::kernel::c_condition_facts_equivalent_for_memory_resolution(
            &rewritten,
            target,
            assumptions,
        )
        || certified_fact_transport_reaches(&rewritten, target, after, assumptions);
    spelled
}

fn certified_fact_transport_reaches(
    source: &Proposition,
    target: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    if matches!(target, Proposition::CMemoryLoadable { .. }) {
        return assumptions.derive_atomic_proposition(target).is_some();
    }
    let Some(theorem) = prove_c_condition_fact_transport(source, after, assumptions) else {
        return false;
    };
    let Proposition::Implies(_, conclusion) = theorem.proposition() else {
        unreachable!("condition transport must produce an implication")
    };
    normalize_direct_atomic_memory_loads(conclusion) == normalize_direct_atomic_memory_loads(target)
}

#[allow(clippy::too_many_arguments)]
fn fold_composite_resource_at_current_point(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
    available_pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<CState, ClickError> {
    let outcome = CFunctionOutcome::Return {
        value: CValue::Int32(Bitvector32Term::Constant(0)),
        state,
    };
    let outcome = fold_composite_resources_on_outcome(
        resource_environment,
        std::slice::from_ref(resource),
        claim_label,
        tactic_index,
        &[],
        available_pure_facts,
        parameters,
        arguments,
        pre_state,
        outcome,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    let CFunctionOutcome::Return { state, .. } = outcome else {
        unreachable!("folding a synthetic return outcome preserves its outcome kind")
    };
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
fn lower_point_proposition(
    proposition: &ClickProposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    lower_point_proposition_with_values(
        proposition,
        available,
        values,
        &array_refs,
        pre_state,
        state,
        result,
        program_point_states,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_point_proposition_with_values(
    proposition: &ClickProposition,
    available: &[Proposition],
    mut values: BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let assumptions = assumptions_from_propositions(available);
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        array_refs,
        pre_state,
        state,
        result,
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_have_at_current_point(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
) -> Result<Proposition, ClickError> {
    prove_have_at_point(
        have,
        theorem_environment,
        claim_label,
        outer_tactic_index,
        outer_available,
        parameters,
        arguments,
        pre_state,
        state,
        None,
        program_point_states,
        Some(surface_propositions),
        predicate_environment,
        click_function_environment,
        original_requirements,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn plan_smart_have_at_current_point(
    have: &ProofHave,
    claim_label: &str,
    outer_tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    prelowered_goal: Option<&Proposition>,
) -> Result<(Proposition, ProofReplayPlan), ClickError> {
    // Plan and replay this proof once. Surface expansion must lower this exact
    // plan; it must not search for a different proof if lowering is incomplete.
    // Snapshot transport belongs to the statement transition that changed the
    // memory and reaches a later `have` as an exact current-state assumption.
    let direct_lowering_facts = facts_for_smart_have_lowering(available);
    let fact = match lower_point_proposition(
        &have.proposition,
        &direct_lowering_facts,
        parameters,
        arguments,
        pre_state,
        state,
        None,
        program_point_states,
        predicate_environment,
        click_function_environment,
    ) {
        Ok(fact) => fact,
        Err(_) if prelowered_goal.is_some() => prelowered_goal.expect("checked above").clone(),
        Err(message) => match lower_point_proposition(
            &have.proposition,
            &facts_for_simple_goal_lowering(available),
            parameters,
            arguments,
            pre_state,
            state,
            None,
            program_point_states,
            predicate_environment,
            click_function_environment,
        ) {
            Ok(fact) => fact,
            Err(_) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: could not lower pure goal: {message}"
                )));
            }
        },
    };
    let available = if unfolded_predicates.is_empty() {
        available.to_vec()
    } else {
        unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            available,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` have proof {outer_tactic_index}: could not unfold available facts: {message}"
            ))
        })?
    };
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &fact,
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` have proof {outer_tactic_index}: could not unfold pure goal: {message}"
        ))
    })?;
    if available.contains(&goal) {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    if matches!(normalize_proposition(&goal), SimpProposition::True) {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a simple replay tactic");
        return Ok((fact, plan));
    }
    if materialization_equivalent_available_fact(&goal, &available).is_some() {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    if quantified_replay_equivalent_available_fact(&goal, &available).is_some() {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    let normalized_fact = normalize_direct_atomic_memory_loads(&goal);
    if let Some(equivalent) = available
        .iter()
        .find(|available| normalize_direct_atomic_memory_loads(available) == normalized_fact)
        && let Some(derivation) =
            minimal_proposition_derivation(&goal, std::slice::from_ref(equivalent))
    {
        let plan =
            ProofReplayPlan::from_planned_tactics(&[ProofTactic::ExactPropositionDerivation(
                derivation,
            )])
            .expect("a directly normalized derivation is a simple replay tactic");
        return Ok((fact, plan));
    }
    if let Some(derivation) = bounded_condition_derivation(&goal, &available) {
        let plan =
            ProofReplayPlan::from_planned_tactics(&[ProofTactic::ExactPropositionDerivation(
                derivation,
            )])
            .expect("a bounded condition derivation is a simple replay tactic");
        return Ok((fact, plan));
    }

    let Some(plan) = plan_simp_certificate(&goal, &assumptions) else {
        if let Ok(dir) = std::env::var("CLICK_HAVE_DUMP_DIR") {
            let _ = std::fs::write(format!("{dir}/have-goal.txt"), format!("{goal:#?}"));
            if let Proposition::ForAll { body, .. } = &goal
                && let Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::Bitvector32Equal(left, right),
                    _,
                ) = body.as_ref()
            {
                let canonical_left = crate::kernel::canonicalize_atomic_loads(left);
                let canonical_right = crate::kernel::canonicalize_atomic_loads(right);
                eprintln!("HAVE PROBE canonical_eq={}", canonical_left == canonical_right);
                let _ = std::fs::write(
                    format!("{dir}/canonical-left.txt"),
                    format!("{canonical_left:#?}"),
                );
                let _ = std::fs::write(
                    format!("{dir}/canonical-right.txt"),
                    format!("{canonical_right:#?}"),
                );
            }
        }
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {}",
            describe_missing_pure_fact(
                &goal,
                &available,
                state.resources().facts(),
                parameters,
                arguments,
                &[],
            )
        )));
    };
    if !replay_simp_certificate(&goal, &assumptions, &plan) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: planned smart `have` certificate did not replay"
        )));
    }
    Ok((fact, plan))
}

#[allow(clippy::too_many_arguments)]
fn prove_have_at_point(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    prove_pure_proposition_at_point(
        &have.proposition,
        None,
        &have.proof,
        "have",
        theorem_environment,
        claim_label,
        outer_tactic_index,
        outer_available,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        program_point_states,
        surface_propositions,
        predicate_environment,
        click_function_environment,
        original_requirements,
        path_index,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_proposition_at_point(
    proposition: &ClickProposition,
    prelowered_goal: Option<&Proposition>,
    proof: &Proof,
    proof_name: &str,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    let (proof_cases, tactic_simp) = match proof {
        Proof::Script(tactics) => (expand_proof_if_cases(tactics, claim_label)?, false),
        Proof::Default | Proof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => (
            vec![ExpandedProofCase {
                tactics: Vec::new(),
                assumptions: Vec::new(),
                advance_checks: Vec::new(),
            }],
            true,
        ),
        Proof::Tactic(SmartTactic::Frame) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `frame` is not available in a pure proof"
            )));
        }
    };
    if proof_cases
        .iter()
        .any(|proof_case| !proof_case.advance_checks.is_empty())
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index}: `advance` is not available in a pure proof"
        )));
    }

    let mut proven_fact = None;
    for proof_case in proof_cases {
        let fact = prove_pure_proposition_case_at_point(
            proposition,
            prelowered_goal,
            &proof_case,
            tactic_simp,
            proof_name,
            theorem_environment,
            claim_label,
            outer_tactic_index,
            outer_available,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            original_requirements,
            path_index,
        )?;
        if let Some(expected) = &proven_fact
            && expected != &fact
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {outer_tactic_index}: `have` cases lowered the same surface fact differently"
            )));
        }
        proven_fact = Some(fact);
    }
    proven_fact.ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index} has no proof cases"
        ))
    })
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_proposition_case_at_point(
    proposition: &ClickProposition,
    prelowered_goal: Option<&Proposition>,
    proof_case: &ExpandedProofCase,
    tactic_simp: bool,
    proof_name: &str,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    let mut available = outer_available.to_vec();
    let mut unfolded_predicates = Vec::new();
    let mut use_simp = tactic_simp;
    let parameter_values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, state.memory());
    let (mut values, array_refs) =
        contract_environment_at_state(&parameter_values, &array_refs, state);
    let mut fact = None;
    let mut goal = None;
    let mut goal_closed = false;
    let mut next_choice_variable = 3_000_000;

    for (inner_tactic_index, tactic) in proof_case.tactics.iter().enumerate() {
        add_have_case_assumptions(
            proof_case,
            inner_tactic_index,
            &mut available,
            claim_label,
            outer_tactic_index,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            program_point_states,
            predicate_environment,
            click_function_environment,
        )?;
        if goal_closed {
            return Err(ClickError::new(format!(
                "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `{}` follows a goal-closing simple tactic",
                tactic_name(tactic)
            )));
        }
        match tactic {
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: unknown predicate `{name}`"
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
                .map_err(|message| ClickError::new(format!(
                    "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: {message}"
                )))?;
            }
            ProofTactic::ApplyTheorem(application) => {
                let application_context = TheoremApplicationContext {
                    values: &values,
                    array_refs: &array_refs,
                    pre_state,
                    post_state: state,
                    result,
                    program_point_states,
                };
                available = apply_theorem_applications_to_available(
                    theorem_environment,
                    &[(inner_tactic_index, application.clone())],
                    claim_label,
                    path_index,
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
                        lower_point_proposition_with_values(
                            premise,
                            &available,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `apply using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `apply using` requires an unavailable exact premise: {premise:?}"
                        )));
                    }
                }
                let application_context = TheoremApplicationContext {
                    values: &values,
                    array_refs: &array_refs,
                    pre_state,
                    post_state: state,
                    result,
                    program_point_states,
                };
                let mut applied = apply_theorem_applications_to_available_with_lowering_context(
                    theorem_environment,
                    &[(inner_tactic_index, application.clone())],
                    claim_label,
                    path_index,
                    explicit_premises,
                    Some(&available),
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
                for available_fact in available {
                    if !applied.contains(&available_fact) {
                        applied.push(available_fact);
                    }
                }
                available = applied;
            }
            ProofTactic::Have(inner_have) => {
                let inner_fact = prove_have_at_point(
                    inner_have,
                    theorem_environment,
                    claim_label,
                    outer_tactic_index,
                    &available,
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    result,
                    program_point_states,
                    surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    original_requirements,
                    path_index,
                )?;
                if !available.contains(&inner_fact) {
                    available.push(inner_fact);
                }
            }
            ProofTactic::Choose(choice) => {
                apply_choose_tactic(
                    choice,
                    claim_label,
                    path_index.unwrap_or(0),
                    inner_tactic_index,
                    &mut available,
                    &mut values,
                    original_requirements,
                    &mut next_choice_variable,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
            }
            ProofTactic::Witness(witness) => {
                if goal.is_none() {
                    let lowered = if let Some(prelowered_goal) = prelowered_goal {
                        prelowered_goal.clone()
                    } else {
                        lower_point_proposition_with_values(
                            proposition,
                            &available,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower pure goal: {message}"
                            ))
                        })?
                    };
                    fact = Some(lowered.clone());
                    goal = Some(lowered);
                }
                let assumptions = assumptions_from_propositions(&available);
                let unfolded_goal = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                    goal.as_ref().expect("witness goal should be initialized"),
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not unfold pure goal: {message}"
                    ))
                })?;
                let witness_value = evaluate_witness_tactic_value(
                    witness,
                    claim_label,
                    path_index.unwrap_or(0),
                    inner_tactic_index,
                    &values,
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    &assumptions,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                )?;
                goal = Some(apply_witness_tactic(
                    witness,
                    witness_value,
                    unfolded_goal,
                    claim_label,
                    path_index.unwrap_or(0),
                    inner_tactic_index,
                )?);
            }
            ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Intro
            | ProofTactic::Conjunction
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::DoubleNegation
            | ProofTactic::Vacuous
            | ProofTactic::Contradiction(_)
            | ProofTactic::Derive(_)
            | ProofTactic::Calculate(_)
            | ProofTactic::Rewrite(_) => {
                let mut prepared_derivation_lowering_facts = None;
                let direct_goal_lowering_facts =
                    matches!(tactic, ProofTactic::Assumption | ProofTactic::Normalize)
                        .then(|| facts_for_simple_goal_lowering(&available));
                if let ProofTactic::Derive(derive) | ProofTactic::Calculate(derive) = tactic {
                    let mut lowering_facts = facts_for_direct_derivation_lowering(&available);
                    let mut unresolved = derive.premises.iter().collect::<Vec<_>>();
                    while !unresolved.is_empty() {
                        let mut next = Vec::new();
                        let prior_fact_count = lowering_facts.len();
                        for premise in unresolved {
                            let lowered = surface_propositions
                                .and_then(|propositions| {
                                    propositions.available_kernel(premise, &available).cloned()
                                })
                                .map(Ok)
                                .unwrap_or_else(|| {
                                    lower_point_proposition_with_values(
                                        premise,
                                        &lowering_facts,
                                        values.clone(),
                                        &array_refs,
                                        pre_state,
                                        state,
                                        result,
                                        program_point_states,
                                        predicate_environment,
                                        click_function_environment,
                                    )
                                });
                            match lowered {
                                Ok(lowered) => {
                                    if !lowering_facts.contains(&lowered) {
                                        lowering_facts.push(lowered);
                                    }
                                }
                                Err(_) => next.push(premise),
                            }
                        }
                        if lowering_facts.len() == prior_fact_count && !next.is_empty() {
                            let premise = next[0];
                            let message = lower_point_proposition_with_values(
                                premise,
                                &lowering_facts,
                                values.clone(),
                                &array_refs,
                                pre_state,
                                state,
                                result,
                                program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .err()
                            .unwrap_or_else(|| {
                                "no further premise lowered against the facts already available"
                                    .to_string()
                            });
                            return Err(ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `{}` premise `{}`: {message}",
                                tactic_name(tactic),
                                describe_click_proposition(premise),
                            )));
                        }
                        unresolved = next;
                    }
                    prepared_derivation_lowering_facts = Some(lowering_facts);
                }
                if goal.is_none() {
                    let lowered = if let Some(prelowered_goal) = prelowered_goal {
                        prelowered_goal.clone()
                    } else {
                        lower_point_proposition_with_values(
                            proposition,
                            prepared_derivation_lowering_facts
                                .as_deref()
                                .or(direct_goal_lowering_facts.as_deref())
                                .unwrap_or(&available),
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower pure goal: {message}"
                            ))
                        })?
                    };
                    fact = Some(lowered.clone());
                    goal = Some(lowered);
                }
                let unfolded_goal = if unfolded_predicates.is_empty() {
                    goal.as_ref()
                        .expect("simple tactic goal should be initialized")
                        .clone()
                } else {
                    let assumptions = assumptions_from_propositions(&available);
                    unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        &unfolded_predicates,
                        goal.as_ref().expect("simple tactic goal should be initialized"),
                        &assumptions,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not unfold pure goal: {message}"
                        ))
                    })?
                };
                match tactic {
                    ProofTactic::Assumption => {
                        if !available.contains(&unfolded_goal)
                            && materialization_equivalent_available_fact(&unfolded_goal, &available)
                                .is_none()
                            && quantified_replay_equivalent_available_fact(
                                &unfolded_goal,
                                &available,
                            )
                            .is_none()
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `assumption` failed: {}",
                                describe_missing_pure_fact(
                                    &unfolded_goal,
                                    &available,
                                    state.resources().facts(),
                                    parameters,
                                    arguments,
                                    &[]
                                )
                            )));
                        }
                        goal_closed = true;
                    }
                    ProofTactic::Normalize => {
                        if !normalizes_context_free(&unfolded_goal) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `normalize` failed because the goal did not normalize to true: {unfolded_goal:?}"
                            )));
                        }
                        goal_closed = true;
                    }
                    ProofTactic::Intro
                    | ProofTactic::Conjunction
                    | ProofTactic::Left
                    | ProofTactic::Right
                    | ProofTactic::DoubleNegation
                    | ProofTactic::Vacuous
                    | ProofTactic::Contradiction(_) => {
                        let contradiction_fact = match tactic {
                            ProofTactic::Contradiction(surface_fact) => Some(
                                lower_point_proposition_with_values(
                                    surface_fact,
                                    &available,
                                    values.clone(),
                                    &array_refs,
                                    pre_state,
                                    state,
                                    result,
                                    program_point_states,
                                    predicate_environment,
                                    click_function_environment,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: `contradiction` could not lower fact: {message}"
                                    ))
                                })?,
                            ),
                            _ => None,
                        };
                        let mut logical_goal = unfolded_goal;
                        goal_closed = apply_logical_goal_tactic(
                            tactic,
                            &mut logical_goal,
                            &mut available,
                            contradiction_fact,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: {message}"
                            ))
                        })?;
                        goal = Some(logical_goal);
                    }
                    ProofTactic::Derive(derive) | ProofTactic::Calculate(derive) => {
                        let derivation_lowering_facts = prepared_derivation_lowering_facts
                            .as_ref()
                            .expect("derive lowering facts should be prepared");
                        let target = if derive.proposition == *proposition {
                            unfolded_goal.clone()
                        } else {
                            lower_point_proposition_with_values(
                                &derive.proposition,
                                &derivation_lowering_facts,
                                values.clone(),
                                &array_refs,
                                pre_state,
                                state,
                                result,
                                program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `{}` target: {message}",
                                    tactic_name(tactic)
                                ))
                            })?
                        };
                        let premises = derive
                            .premises
                            .iter()
                            .map(|premise| {
                                if let Some(recorded) = surface_propositions.and_then(
                                    |propositions| {
                                        propositions.available_kernel(premise, &available)
                                    },
                                ) {
                                    Ok(recorded.clone())
                                } else {
                                    lower_point_proposition_with_values(
                                        premise,
                                        &derivation_lowering_facts,
                                        values.clone(),
                                        &array_refs,
                                        pre_state,
                                        state,
                                        result,
                                        program_point_states,
                                        predicate_environment,
                                        click_function_environment,
                                    )
                                }
                            })
                            .collect::<Result<Vec<_>, _>>()
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `{}` premise: {message}",
                                    tactic_name(tactic)
                                ))
                            })?;
                        check_atomic_derivation_goal(
                            tactic,
                            target,
                            premises,
                            &unfolded_goal,
                            &available,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: {message}"
                            ))
                        })?;
                        goal_closed = true;
                    }
                    ProofTactic::Rewrite(surface_equality) => {
                        let equality = lower_point_proposition_with_values(
                            surface_equality,
                            &available,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `rewrite` could not lower equality: {message}"
                            ))
                        })?;
                        goal = Some(
                            rewrite_proposition_by_exact_equality(
                                &unfolded_goal,
                                &equality,
                                &available,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` {proof_name} proof {outer_tactic_index}: {message}"
                                ))
                            })?,
                        );
                    }
                    _ => unreachable!(),
                }
            }
            ProofTactic::Simp => use_simp = true,
            ProofTactic::If(_) => unreachable!("proof-level if tactics are expanded before replay"),
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `{}` is not available in a pure proof",
                    tactic_name(tactic)
                )));
            }
        }
    }
    add_have_case_assumptions(
        proof_case,
        proof_case.tactics.len(),
        &mut available,
        claim_label,
        outer_tactic_index,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        program_point_states,
        predicate_environment,
        click_function_environment,
    )?;

    let fact = match fact {
        Some(fact) => fact,
        None => {
            if let Some(prelowered_goal) = prelowered_goal {
                prelowered_goal.clone()
            } else {
                lower_point_proposition_with_values(
                    proposition,
                    &available,
                    values,
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower pure goal: {message}"
                    ))
                })?
            }
        }
    };
    if goal_closed {
        return Ok(fact);
    }
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        goal.as_ref().unwrap_or(&fact),
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not unfold pure goal: {message}"
        ))
    })?;
    if pure_fact_is_replay_available(&goal, &available)
        || (use_simp && matches!(simp_proposition(&goal, &assumptions), SimpProposition::True))
    {
        return Ok(fact);
    }
    let failure = describe_missing_pure_fact(
        &goal,
        &available,
        state.resources().facts(),
        parameters,
        arguments,
        &[],
    );
    if proof_name == "have" {
        Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {failure}"
        )))
    } else {
        Err(ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index} failed: {failure}"
        )))
    }
}

#[allow(clippy::too_many_arguments)]
fn add_have_case_assumptions(
    proof_case: &ExpandedProofCase,
    inner_tactic_index: usize,
    available: &mut Vec<Proposition>,
    claim_label: &str,
    outer_tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    for case_assumption in proof_case
        .assumptions
        .iter()
        .filter(|assumption| assumption.tactic_index == inner_tactic_index)
    {
        let proposition = lower_point_proposition(
            &case_assumption.proposition,
            available,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {outer_tactic_index}, `have` tactic {inner_tactic_index}: could not lower `if` condition: {message}"
            ))
        })?;
        available.push(if case_assumption.value {
            proposition
        } else {
            Proposition::Not(Box::new(proposition))
        });
    }
    Ok(())
}

pub(super) fn prove_claim_by_tactics(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty explicit proof script"
        )));
    }
    let program = build_internal_proof_with_source(tactics, claim_label, tactic_source)?;
    let (state, arguments, pure_facts, surface_propositions) = initial_claim_context(
        function_block,
        parsed_function,
        resource_environment,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;
    let state = canonical_claim_caller_state(
        state,
        function_block
            .structural_clauses()
            .iter()
            .any(|clause| matches!(clause.region(), CodeRegion::Loop(_))),
        &function,
        &arguments,
        &pure_facts,
        claim_label,
    )?;
    let proof_claims = [*claim];
    let mut replay = TacticReplayState {
        proof_site: proof_site_for_claims(function_block, &proof_claims, false),
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        ordered_finalization: true,
        execution_start_facts: pure_facts.clone(),
        surface_propositions,
        ..TacticReplayState::default()
    };
    record_current_statement_entry(
        &mut replay,
        &state,
        function_block,
        &function,
        &arguments,
        claim_label,
        0,
        "proof entry",
    )?;
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path: Vec::new(),
        },
        function_block,
        parsed_function,
        &proof_claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    )?;

    let mut verified = Vec::new();
    for context in contexts {
        for theorem in finish_ordered_proof_replay(
            context,
            source_path,
            function_block,
            parsed_function,
            &proof_claims,
            false,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function_environment,
            &function,
            &arguments,
            tactics,
        )? {
            if !verified.contains(&theorem) {
                verified.push(theorem);
            }
        }
    }
    Ok(verified)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_claims_by_grouped_tactics(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let proof_label = format!("{}.contract", function_block.signature().name());
    if claims.is_empty() {
        return Err(ClickError::new(format!(
            "`{proof_label}` grouped proof has no contract claims"
        )));
    }
    if tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{proof_label}` has an empty grouped explicit proof script"
        )));
    }
    let program = build_internal_proof_with_source(tactics, &proof_label, tactic_source)?;
    let (state, arguments, pure_facts, surface_propositions) = initial_claim_context(
        function_block,
        parsed_function,
        resource_environment,
        predicate_environment,
        click_function_environment,
        &proof_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;
    let state = canonical_claim_caller_state(
        state,
        function_block
            .structural_clauses()
            .iter()
            .any(|clause| matches!(clause.region(), CodeRegion::Loop(_))),
        &function,
        &arguments,
        &pure_facts,
        &proof_label,
    )?;
    let mut replay = TacticReplayState {
        proof_site: proof_site_for_claims(function_block, claims, true),
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        ordered_finalization: true,
        grouped_contract: true,
        execution_start_facts: pure_facts.clone(),
        surface_propositions,
        ..TacticReplayState::default()
    };
    record_current_statement_entry(
        &mut replay,
        &state,
        function_block,
        &function,
        &arguments,
        &proof_label,
        0,
        "proof entry",
    )?;
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path: Vec::new(),
        },
        function_block,
        parsed_function,
        claims,
        &proof_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    )?;

    let mut verified = Vec::new();
    for context in contexts {
        for theorem in finish_ordered_proof_replay(
            context,
            source_path,
            function_block,
            parsed_function,
            claims,
            true,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function_environment,
            &function,
            &arguments,
            tactics,
        )? {
            if !verified.contains(&theorem) {
                verified.push(theorem);
            }
        }
    }
    Ok(verified)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_claims_by_grouped_auto(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut tactics = vec![ProofTactic::ExecuteRest];
    tactics.extend(
        loop_effect_summary_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofTactic::Frame(Some(CodeRegionRef::Loop(loop_index)))),
    );
    if claims
        .iter()
        .any(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
    {
        tactics.push(ProofTactic::Frame(None));
    }
    if claims
        .iter()
        .any(|claim| matches!(claim, FunctionClaimRef::Ensure(_, _)))
    {
        tactics.push(ProofTactic::Simp);
    }

    let verified = prove_claims_by_grouped_tactics(
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    let certificate = verified
        .first()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`auto` proved no grouped claims for `{}.contract`",
                function_block.signature().name()
            ))
        })?
        .expanded_proof_certificate()
        .map_err(|error| {
            ClickError::new(format!(
                "`auto` succeeded internally for `{}.contract` without a surface certificate: {}",
                function_block.signature().name(),
                error.message()
            ))
        })?;
    let replayed = prove_claims_by_grouped_tactics(
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        certificate.tactics(),
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`auto` surface certificate failed complete replay for `{}.contract`:\n{}\n{}",
            function_block.signature().name(),
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    if replayed.len() != verified.len() {
        return Err(ClickError::new(format!(
            "`auto` surface certificate replayed {} grouped theorems for `{}.contract`, expected {}",
            replayed.len(),
            function_block.signature().name(),
            verified.len()
        )));
    }
    Ok(verified)
}

/// Exit-claim closure: the structural form of the settled invariant that a
/// smart success must replay through a surface-expressible certificate
/// before acceptance.
///
/// Mid-execution the invariant is already structural — a smart step can only
/// continue from the replay context `replay_smart_plan` returns, and there is
/// no other way to obtain one, so "accepted without a certificate" is not
/// spellable. At function exit the per-claim drain used to spell it easily:
/// closure was `closed_claims[i] = true`, a bool any site could set, with the
/// certificates hanging off parallel arrays and the gate re-asserted by hand
/// at every closing site.
///
/// `ClosedClaim` restores the mid-execution shape. Its field is private to
/// this module, so no site outside can build one, and the variant that carries
/// a generated certificate has exactly one constructor:
/// `discharge_exit_simp_claim`, which builds the certificate and replays it
/// before it can hand back a closure. The other constructors each take the
/// evidence that discharged the claim.
mod exit_claim {
    use super::*;

    /// The certificate a closed exit claim carries.
    #[derive(Clone, Debug)]
    pub(super) enum ClaimCertificate {
        /// Surface tactics that discharge exactly this claim. They are
        /// appended to the claim's own expansion.
        Claim(Vec<ProofTactic>),
        /// Discharged by the path's grouped transition certificate, which
        /// covers every claim the transition closes and is recorded once for
        /// the path rather than once per claim.
        GroupedTransition,
        /// Discharged by an exact kernel check rather than a proof search:
        /// `assumption`, `normalize`, `frame`, a certified frame, or the
        /// implicit closer of a single-claim proof. Where the script spelled
        /// a closing tactic it is already in the path's recorded surface
        /// tactics; there is no search to certify.
        ExactCheck,
    }

    /// A claim closed at function exit, holding the certificate that
    /// discharged it. Only this module can build one.
    #[derive(Clone, Debug)]
    pub(super) struct ClosedClaim {
        certificate: ClaimCertificate,
    }

    impl ClosedClaim {
        /// The tactics this claim contributes to its own expansion. Grouped
        /// and exact closures contribute none: their tactics belong to the
        /// path's tactic list, not to one claim.
        pub(super) fn claim_tactics(&self) -> &[ProofTactic] {
            match &self.certificate {
                ClaimCertificate::Claim(tactics) => tactics,
                ClaimCertificate::GroupedTransition | ClaimCertificate::ExactCheck => &[],
            }
        }
    }

    /// A claim's state in the per-path exit drain.
    #[derive(Clone, Debug)]
    pub(super) enum ClaimClosure {
        /// Not discharged yet; carries the last closing attempt's message so
        /// the drain can explain an unproved claim.
        Open(Option<String>),
        Closed(ClosedClaim),
    }

    impl Default for ClaimClosure {
        fn default() -> Self {
            Self::Open(None)
        }
    }

    impl ClaimClosure {
        pub(super) fn is_closed(&self) -> bool {
            matches!(self, Self::Closed(_))
        }

        pub(super) fn closed(&self) -> Option<&ClosedClaim> {
            match self {
                Self::Closed(closed) => Some(closed),
                Self::Open(_) => None,
            }
        }

        pub(super) fn last_error(&self) -> Option<&str> {
            match self {
                Self::Open(error) => error.as_deref(),
                Self::Closed(_) => None,
            }
        }

        pub(super) fn record_failure(&mut self, message: String) {
            if let Self::Open(error) = self {
                *error = Some(message);
            }
        }

        /// Close a claim with the certificate a smart exit `simp` generated
        /// for it. Private to this module, and inside it reachable only from
        /// `discharge_exit_simp_claim`: the `TacticCertificate` is the
        /// evidence, and it exists only once the generator replayed the
        /// tactics through the replay judgment and got the claim's kernel
        /// goal back.
        fn by_replayed_certificate(certificate: &TacticCertificate) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::Claim(certificate.tactics().to_vec()),
            })
        }

        /// Close a claim covered by the path's grouped transition
        /// certificate. Taking the certificate is the point: the only way to
        /// hold one is to have run `certify_grouped_outcome_simp_transition`,
        /// which builds every claim's `have` and replays it.
        pub(super) fn by_grouped_transition(_certificate: &TacticCertificate) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::GroupedTransition,
            })
        }

        /// Close a claim that an exact kernel check discharged.
        pub(super) fn by_exact_check() -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::ExactCheck,
            })
        }
    }

    /// What running the exit `simp` closer on one claim produced.
    pub(super) enum ExitSimpClosure {
        /// The claim closed, carrying the certificate that discharged it.
        Closed(ClaimClosure),
        /// The claim joins the path's grouped transition, which is certified
        /// and replayed as one unit once every claim has been offered. The
        /// goal is `None` for a resource ensure: it has no proposition to
        /// certify and is discharged by one of the transition's trailing
        /// `assumption`s.
        JoinsGroupedTransition(Option<GroupedOutcomeSimpGoal>),
    }

    /// What the exit drain holds when it reaches its `simp` closer.
    ///
    /// Gathered into one value so the closer can be a function instead of an
    /// inline block, which is what lets `ClosedClaim`'s certificate
    /// constructor be private to it.
    pub(super) struct ExitClaimContext<'a> {
        pub(super) replay: &'a TacticReplayState,
        pub(super) outcome_surface_propositions: &'a SurfacePropositionMap,
        pub(super) path_requirements: &'a [Proposition],
        pub(super) surface_certificate_facts: &'a [Proposition],
        pub(super) execution_facts: &'a [ExecutionPureFact],
        pub(super) unfolded_predicates: &'a [String],
        pub(super) existence_tactics: &'a [ProofTactic],
        pub(super) parameters: &'a [syntax::C0Parameter],
        pub(super) arguments: &'a [CExpression],
        pub(super) pre_state: &'a CState,
        pub(super) outcome: &'a CFunctionOutcome,
        pub(super) predicate_environment: &'a PredicateEnvironment,
        pub(super) click_function_environment: &'a ClickFunctionEnvironment,
        pub(super) theorem_environment: &'a TheoremEnvironment,
        pub(super) function_requires: &'a [Requirement],
        pub(super) path_index: usize,
        pub(super) tactic_index: usize,
    }

    impl ExitClaimContext<'_> {
        /// Lower a claim's surface goal under the drain's unfold set.
        fn lower_claim_goal(&self, surface_goal: &ClickProposition) -> Result<Proposition, String> {
            lower_ensure_proposition_goal(
                self.path_requirements,
                surface_goal,
                self.parameters,
                self.arguments,
                self.pre_state,
                self.outcome,
                self.predicate_environment,
                self.click_function_environment,
                &self.replay.program_point_states,
                self.unfolded_predicates,
            )
        }

        /// The fact set a per-claim exit certificate is generated against.
        ///
        /// `surface_certificate_facts` is the drain's running certificate
        /// context. The ambient effect facts (`CMemoryMutatesOnly` /
        /// `CMemoryEffectSummary`) join it because the closer replays with
        /// them in scope, and the drain's `unfold(...)` set is applied because
        /// the emitted `have` script carries that prefix: generation must plan
        /// against exactly the context replay will hold. The grouped
        /// transition emits no `unfold(...)` prefix and so plans against the
        /// raw snapshot instead.
        fn certificate_facts(&self) -> Result<Vec<Proposition>, String> {
            let mut certificate_facts = self.surface_certificate_facts.to_vec();
            certificate_facts.extend(
                self.execution_facts
                    .iter()
                    .filter(|fact| {
                        matches!(
                            fact.proposition(),
                            Proposition::CMemoryMutatesOnly { .. }
                                | Proposition::CMemoryEffectSummary { .. }
                        )
                    })
                    .map(|fact| fact.proposition().clone()),
            );
            unfold_available_predicate_facts(
                self.predicate_environment,
                self.click_function_environment,
                self.unfolded_predicates,
                &certificate_facts,
            )
        }

        /// The replay state a per-claim exit certificate is generated in.
        fn certificate_replay(&self) -> TacticReplayState {
            let mut certificate_replay = self.replay.clone();
            certificate_replay.surface_propositions = self.outcome_surface_propositions.clone();
            // The goal was proved with the drain's unfold set active; the
            // certificate must re-lower the surface goal under the same
            // unfolds or the two spellings cannot match.
            certificate_replay.unfolded_predicates = self.unfolded_predicates.to_vec();
            certificate_replay
        }

        fn certificate_failure(&self, claim_label: &str, message: &str) -> ClickError {
            ClickError::new(format!(
                "`{claim_label}` path {}: smart `simp` closed the claim but its certificate did not lower or replay: {message}",
                self.path_index
            ))
        }
    }

    /// Discharge one exit claim whose ambient `simp` check just succeeded.
    ///
    /// This is the only place a claim can acquire a generated certificate.
    /// Every arm either returns a closure built from a certificate the
    /// generator already replayed, hands the claim to the path's grouped
    /// transition — which certifies and replays before anything closes — or
    /// fails verification. There is no arm that accepts without one, which is
    /// what makes the exit gate structural instead of a check to remember.
    pub(super) fn discharge_exit_simp_claim(
        context: &ExitClaimContext<'_>,
        claim_index: usize,
        claim_label: &str,
        ensure: &Ensure,
        rewritten_goal: Option<&Proposition>,
        frame_certified_goal: Option<&Proposition>,
    ) -> Result<ExitSimpClosure, ClickError> {
        let outcome = context.outcome;
        if !context.existence_tactics.is_empty() {
            let certificate = match (rewritten_goal, ensure, outcome) {
                (
                    None,
                    Ensure::Proposition(surface_goal),
                    CFunctionOutcome::Return {
                        value: result,
                        state: post_state,
                    },
                ) if !context.replay.grouped_contract => {
                    context.lower_claim_goal(surface_goal).and_then(|goal| {
                        let certificate_facts = context.certificate_facts()?;
                        certify_outcome_existential_simp(
                            &context.certificate_replay(),
                            surface_goal,
                            &goal,
                            &certificate_facts,
                            context.existence_tactics,
                            context.parameters,
                            context.arguments,
                            context.pre_state,
                            post_state,
                            result,
                            context.predicate_environment,
                            context.click_function_environment,
                            context.theorem_environment,
                            context.function_requires,
                            claim_label,
                            context.tactic_index,
                            context.path_index,
                        )
                        .map_err(|error| error.message().to_string())
                    })
                }
                _ => Err(
                    "surface `simp` lowering with existential tactics requires an ungrouped proposition return goal"
                        .to_string(),
                ),
            }
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {}: smart `simp` closed the claim with existential tactics, but its certificate did not lower or replay: {message}",
                    context.path_index
                ))
            })?;
            return Ok(ExitSimpClosure::Closed(
                ClaimClosure::by_replayed_certificate(&certificate),
            ));
        }

        if context.replay.grouped_contract {
            // The grouped transition certificate is the proof-producing
            // authority for the whole claim set. The ambient check only
            // decides that this claim joins the transition; it closes once
            // that certificate has been built and replayed.
            return match (rewritten_goal, ensure, outcome) {
                (None, Ensure::Proposition(surface_goal), CFunctionOutcome::Return { .. }) => {
                    let goal = match frame_certified_goal {
                        Some(goal) => goal.clone(),
                        None => context.lower_claim_goal(surface_goal).map_err(|message| {
                            context.certificate_failure(claim_label, &message)
                        })?,
                    };
                    Ok(ExitSimpClosure::JoinsGroupedTransition(Some(
                        GroupedOutcomeSimpGoal {
                            claim_index,
                            claim_label: claim_label.to_string(),
                            surface_goal: surface_goal.clone(),
                            goal,
                        },
                    )))
                }
                (None, Ensure::Resource(_), _) => Ok(ExitSimpClosure::JoinsGroupedTransition(None)),
                (Some(_), _, _) => Err(context.certificate_failure(
                    claim_label,
                    "surface lowering after `rewrite` is not implemented",
                )),
                _ => Err(context.certificate_failure(
                    claim_label,
                    "surface `simp` lowering requires a proposition return goal",
                )),
            };
        }

        let certificate = match (rewritten_goal, ensure, outcome) {
            (
                None,
                Ensure::Proposition(surface_goal),
                CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                },
            ) => frame_certified_goal
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| context.lower_claim_goal(surface_goal))
                .and_then(|goal| {
                    let certificate_facts = context.certificate_facts()?;
                    certify_outcome_simp(
                        &context.certificate_replay(),
                        surface_goal,
                        &goal,
                        &certificate_facts,
                        context.parameters,
                        context.arguments,
                        context.pre_state,
                        post_state,
                        result,
                        context.predicate_environment,
                        context.click_function_environment,
                        context.theorem_environment,
                        context.function_requires,
                        claim_label,
                        context.tactic_index,
                        context.path_index,
                    )
                    .map_err(|error| error.message().to_string())
                }),
            (None, Ensure::Resource(_), _) => {
                TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption]).map_err(|error| {
                    format!("resource `simp` produced an invalid surface certificate: {error:?}")
                })
            }
            (Some(_), _, _) => {
                Err("surface lowering after `rewrite` is not implemented".to_string())
            }
            _ => Err("surface `simp` lowering requires a proposition return goal".to_string()),
        }
        .map_err(|message| context.certificate_failure(claim_label, &message))?;
        Ok(ExitSimpClosure::Closed(
            ClaimClosure::by_replayed_certificate(&certificate),
        ))
    }
}

use exit_claim::{ClaimClosure, ClosedClaim, ExitClaimContext, ExitSimpClosure};

#[allow(clippy::too_many_arguments)]
fn finish_ordered_proof_replay(
    context: ProofReplayContext,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    require_explicit_closers: bool,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: &CExecutionEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    certificate_tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let ProofReplayContext {
        state,
        pure_facts,
        replay,
        branch_path,
    } = context;
    let proof_label = if require_explicit_closers {
        format!("{}.contract", function_block.signature().name())
    } else {
        function_claim_label(function_block.signature().name(), &claims[0])
    };
    let result = (|| {
        let execution = replay.execution().ok_or_else(|| {
            ClickError::new(format!(
                "`{proof_label}` execution proof must reach function exit with `execute_step()`, `execute_rest()`, or `bounded_execute()`"
            ))
        })?;
        if execution.paths().is_empty() {
            return Err(ClickError::new(format!(
                "execution proof could not prove any complete execution path for `{proof_label}`"
            )));
        }
        let pre_state = replay.execution_start_state(&state);
        let mut certification_facts = replay.execution_start_facts.clone();
        certification_facts.extend(
            replay
                .case_assumptions
                .iter()
                .filter_map(|case| case.fact.clone()),
        );
        let execution_start_assumptions = assumptions_from_propositions(&certification_facts);
        let certified_execution = if replay.concrete_loop_execution {
            prove_symbolic_c_function_execution_paths_with_environment(
                pre_state.clone(),
                function.clone(),
                arguments.to_vec(),
                execution_start_assumptions,
                function_environment.clone(),
                CExecutionSemantics::APPLY_VERIFIED_RULES,
            )
        } else {
            prove_symbolic_c_function_contract_verification_paths_with_environment(
                pre_state.clone(),
                function.clone(),
                arguments.to_vec(),
                execution_start_assumptions,
                function_environment.clone(),
                CExecutionSemantics::APPLY_VERIFIED_RULES,
            )
        };
        if let Some(limit) = certified_execution.limit() {
            return Err(ClickError::new(format!(
                "kernel certification hit execution limit {limit:?} for `{proof_label}`"
            )));
        }
        let certified_outcomes = certified_execution
            .paths()
            .iter()
            .map(|path| match implication_body(path.theorem().proposition()) {
                Proposition::CFunctionExecutes {
                    state,
                    function: proved_function,
                    arguments: proved_arguments,
                    outcome,
                } if state == pre_state
                    && proved_function == function
                    && proved_arguments == arguments =>
                {
                    Ok(outcome.clone())
                }
                proposition => Err(ClickError::new(format!(
                    "kernel certification for `{proof_label}` produced an inexact theorem body {proposition:?}"
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let replay_outcomes = execution
            .paths()
            .iter()
            .map(|path| path.outcome().clone())
            .collect::<Vec<_>>();
        let outcomes_match = |replayed: &crate::kernel::CFunctionExecutionCandidate,
                              certified_index: usize| {
            let certified = &certified_outcomes[certified_index];
            let certified_path = &certified_execution.paths()[certified_index];
            let certified_facts = certified_path
                .execution_facts()
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let mut path_assumptions = certified_path.assumptions().clone();
            for fact in certification_facts.iter().chain(&certified_facts) {
                path_assumptions = path_assumptions.assume_proposition(fact.clone());
            }
            for fact in &pure_facts {
                path_assumptions = path_assumptions.assume_proposition(fact.clone());
            }
            for fact in replayed.execution_facts() {
                path_assumptions = path_assumptions.assume_proposition(fact.proposition().clone());
            }
            if let CFunctionOutcome::Return { state, .. } = certified
                && let Ok(resource_facts) = state.resources().observable_facts(&path_assumptions)
            {
                for fact in resource_facts {
                    path_assumptions = path_assumptions.assume_proposition(fact);
                }
            }
            c_function_outcomes_definitionally_equal(
                function,
                replayed.outcome(),
                certified,
                &path_assumptions,
            ) || crate::kernel::c_function_outcomes_equal_by_store_provenance(
                function,
                replayed.outcome(),
                &replayed.execution_facts(),
                certified,
                &certified_path.execution_facts(),
                &path_assumptions,
            )
        };
        let certified_path_for_replay = if replay.execution_abstraction {
            (!certified_outcomes.is_empty()).then(|| vec![0; execution.paths().len()])
        } else {
            execution
                .paths()
                .iter()
                .map(|replayed| {
                    (0..certified_outcomes.len())
                        .find(|certified_index| outcomes_match(replayed, *certified_index))
                })
                .collect::<Option<Vec<_>>>()
        };
        let Some(certified_path_for_replay) = certified_path_for_replay else {
            return Err(ClickError::new(format!(
                "execution replay for `{proof_label}` contains a path not reproduced by kernel certification\n  replay: {replay_outcomes:?}\n  certified: {certified_outcomes:?}"
            )));
        };
        let mut verified = Vec::new();
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_grouped_closers_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_tactics_by_path = Vec::with_capacity(execution.paths().len());

        for (path_index, path) in execution.paths().iter().enumerate() {
            let certified_path =
                &certified_execution.paths()[certified_path_for_replay[path_index]];
            let mut path_grouped_surface_closers = Vec::new();
            let mut path_surface_post_tactics = Vec::new();
            let mut path_deferred_capture_tactics = Vec::new();
            if !path.obligations().is_empty() {
                return Err(ClickError::new(format!(
                    "execution proof failed for `{proof_label}` path {path_index}: {}",
                    describe_missing_proof_obligations(
                        path.obligations(),
                        &pure_facts,
                        pre_state.resources().facts(),
                        parsed_function.parameters(),
                        arguments,
                        path.facts()
                    )
                )));
            }
            let mut outcome = path.outcome().clone();
            let mut path_requirements = pure_facts.clone();
            path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));

            if !replay.case_assumptions.is_empty() {
                let CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                } = &outcome
                else {
                    return Err(ClickError::new(format!(
                        "execution proof failed for `{proof_label}` path {path_index}: proof-level `if` requires a return outcome"
                    )));
                };
                for case in &replay.case_assumptions {
                    let fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let condition = lower_outcome_proposition_with_program_points(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &path_requirements,
                            &case.condition,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {}: could not lower `if` condition: {message}",
                                case.tactic_index
                            ))
                        })?;
                        if case.value {
                            condition
                        } else {
                            Proposition::Not(Box::new(condition))
                        }
                    };
                    path_requirements.push(fact);
                }
            }
            let mut unfolded_predicates = replay.unfolded_predicates.clone();
            path_requirements = unfold_available_predicate_facts(
                predicate_environment,
                click_function_environment,
                &unfolded_predicates,
                &path_requirements,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "execution proof failed for `{proof_label}` path {path_index}: {message}"
                ))
            })?;
            path_requirements = project_outcome_resource_facts(
                resource_environment,
                parsed_function.parameters(),
                arguments,
                pre_state,
                &outcome,
                &path_requirements,
                predicate_environment,
                click_function_environment,
                &proof_label,
                path_index,
            )?;

            let mut closures = vec![ClaimClosure::default(); claims.len()];
            let mut rewritten_claim_goals: Vec<Option<Proposition>> = vec![None; claims.len()];
            let mut frame_certified_claim_goals: Vec<Option<Proposition>> =
                vec![None; claims.len()];
            let mut existence_tactics = Vec::new();
            let mut surface_certificate_facts = path_requirements.clone();
            let mut outcome_surface_propositions = replay.surface_propositions.clone();
            for deferred in &replay.post_execution_tactics {
                let tactic_index = &deferred.tactic_index;
                let source_index = &deferred.source_index;
                let post_tactic = &deferred.tactic;
                let _timing = std::env::var_os("CLICK_TIMINGS").is_some().then(|| {
                    let (tactic_name, tactic_class) = post_execution_tactic_timing(post_tactic);
                    if std::env::var_os("CLICK_TIMING_STARTS").is_some() {
                        eprintln!(
                            "click timing: started tactic {} {} {} class {} statement {} source {}",
                            proof_label,
                            tactic_index,
                            tactic_name,
                            tactic_class,
                            replay.frontier.next_statement_index,
                            source_index
                        );
                    }
                    TacticTiming {
                        claim_label: proof_label.clone(),
                        tactic_index: *tactic_index,
                        source_index: *source_index,
                        tactic_name: tactic_name.to_string(),
                        tactic_class,
                        statement_index: replay.frontier.next_statement_index,
                        start: std::time::Instant::now(),
                    }
                });
                match post_tactic {
                    PostExecutionTactic::Fold(resource) => {
                        outcome = fold_composite_resources_on_outcome(
                            resource_environment,
                            std::slice::from_ref(resource),
                            &proof_label,
                            path_index,
                            path.facts(),
                            &path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            outcome,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        path_requirements = project_outcome_resource_facts(
                            resource_environment,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            &outcome,
                            &path_requirements,
                            predicate_environment,
                            click_function_environment,
                            &proof_label,
                            path_index,
                        )?;
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::FoldResource(resource.clone()),
                        );
                    }
                    PostExecutionTactic::UnfoldPredicate(name) => {
                        if !unfolded_predicates.contains(name) {
                            unfolded_predicates.push(name.clone());
                        }
                        path_requirements = unfold_available_predicate_facts(
                            predicate_environment,
                            click_function_environment,
                            std::slice::from_ref(name),
                            &path_requirements,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: {message}"
                            ))
                        })?;
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::UnfoldPredicate(name.clone()),
                        );
                    }
                    PostExecutionTactic::Apply(application) => {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = &outcome
                        else {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: theorem application requires a return outcome"
                            )));
                        };
                        let premises = plan_explicit_theorem_application_at_outcome(
                            theorem_environment,
                            application,
                            &proof_label,
                            path_index,
                            *tactic_index,
                            &path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        let surface_tactic = ProofTactic::ApplyTheoremUsing {
                            application: application.clone(),
                            premises,
                        };
                        let certificate = TacticCertificate::from_proof_tactics(
                            std::slice::from_ref(&surface_tactic),
                        )
                        .expect("post-execution smart apply must lower to a simple tactic");
                        let requirements_before = path_requirements.clone();
                        path_requirements = replay_outcome_apply_certificate(
                            &certificate,
                            theorem_environment,
                            &proof_label,
                            path_index,
                            *tactic_index,
                            path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        // The recorded `apply` tactic is prefixed to every
                        // claim certificate, so replay holds the theorem's
                        // conclusions when the closer runs. These facts were
                        // produced by replaying that very certificate, so
                        // planning the closer against them is planning
                        // against exactly the replay context.
                        record_certificate_facts_from_replay(
                            &requirements_before,
                            &path_requirements,
                            &mut surface_certificate_facts,
                        );
                        for tactic in certificate.tactics() {
                            record_post_execution_surface_tactic(
                                &mut path_surface_post_tactics,
                                &mut path_deferred_capture_tactics,
                                replay.deferred_tactic_capture.as_ref(),
                                *tactic_index,
                                tactic.clone(),
                            );
                        }
                    }
                    PostExecutionTactic::ApplyUsing {
                        application,
                        premises,
                    } => {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = &outcome
                        else {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: theorem application requires a return outcome"
                            )));
                        };
                        path_requirements = apply_theorem_using_at_outcome(
                            theorem_environment,
                            application,
                            premises,
                            &proof_label,
                            path_index,
                            *tactic_index,
                            path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::ApplyTheoremUsing {
                                application: application.clone(),
                                premises: premises.clone(),
                            },
                        );
                    }
                    PostExecutionTactic::Have(have) => {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = &outcome
                        else {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `have` requires a return outcome"
                            )));
                        };
                        let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                        let (surface_have, fact) = if let Some(smart_unfolds) = smart_unfolds {
                            let fact = lower_outcome_proposition_with_program_points(
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &path_requirements,
                                &have.proposition,
                                predicate_environment,
                                click_function_environment,
                                &replay.program_point_states,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: could not lower smart `have` goal: {message}"
                                ))
                            })?;
                            let planning_available = unfold_available_predicate_facts(
                                predicate_environment,
                                click_function_environment,
                                &smart_unfolds,
                                &path_requirements,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: could not unfold smart `have` context: {message}"
                                ))
                            })?;
                            let unfolded_goal = unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                &smart_unfolds,
                                &fact,
                                &assumptions_from_propositions(&planning_available),
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: could not unfold smart `have` goal: {message}"
                                ))
                            })?;
                            let surface_goal = if smart_unfolds.is_empty() {
                                have.proposition.clone()
                            } else {
                                unfold_structural_invariant_proposition(
                                    predicate_environment,
                                    &have.proposition,
                                    &smart_unfolds,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: could not express unfolded smart `have` goal: {message}"
                                    ))
                                })?
                            };
                            let mut certificate_replay = replay.clone();
                            certificate_replay.surface_propositions =
                                outcome_surface_propositions.clone();
                            let proof_tactic = lower_outcome_simp_tactic(
                                &certificate_replay,
                                &surface_goal,
                                &unfolded_goal,
                                &planning_available,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|error| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `have` failed: {}",
                                    error.message()
                                ))
                            })?;
                            let mut proof_tactics = smart_unfolds
                                .iter()
                                .cloned()
                                .map(ProofTactic::UnfoldPredicate)
                                .collect::<Vec<_>>();
                            proof_tactics.push(proof_tactic);
                            let surface_have = ProofHave {
                                proposition: have.proposition.clone(),
                                proof: Proof::Script(proof_tactics),
                            };
                            let surface_tactic = ProofTactic::Have(surface_have.clone());
                            TacticCertificate::from_proof_tactics(std::slice::from_ref(
                                &surface_tactic,
                            ))
                            .expect("post-execution smart have must lower to a simple tactic");
                            let replayed_fact = prove_have_at_point(
                                &surface_have,
                                theorem_environment,
                                &proof_label,
                                *tactic_index,
                                &path_requirements,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                Some(result),
                                &replay.program_point_states,
                                Some(&certificate_replay.surface_propositions),
                                predicate_environment,
                                click_function_environment,
                                function_block.requires(),
                                Some(path_index),
                            )?;
                            if replayed_fact != fact {
                                return Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: smart `have` surface certificate replayed a different fact"
                                )));
                            }
                            (surface_tactic, replayed_fact)
                        } else {
                            // A script that validates as a certificate is its
                            // own certificate: `prove_have_at_point` is
                            // deterministic replay of surface tactics, which
                            // is exactly what the gate requires.
                            // `validate_certificate_tactics` is the settled
                            // judgment for "surface-expressible" and already
                            // descends through nested `have`/`if`/`advance`
                            // bodies, so use it rather than a flat scan that
                            // mistakes any structured script for a smart one.
                            //
                            // Replay runs first so a script rejected on its
                            // own terms (`advance` in a pure proof, say) still
                            // reports that, and the expressibility gate only
                            // decides whether a *successful* smart closure may
                            // stand.
                            let fact = prove_have_at_point(
                                have,
                                theorem_environment,
                                &proof_label,
                                *tactic_index,
                                &path_requirements,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                Some(result),
                                &replay.program_point_states,
                                Some(&outcome_surface_propositions),
                                predicate_environment,
                                click_function_environment,
                                function_block.requires(),
                                Some(path_index),
                            )?;
                            let mut surface_tactic = ProofTactic::Have(have.clone());
                            if let Err(error) = TacticCertificate::from_proof_tactics(
                                std::slice::from_ref(&surface_tactic),
                            ) {
                                match lower_smart_simp_suffix_have(
                                    have,
                                    &fact,
                                    theorem_environment,
                                    &proof_label,
                                    *tactic_index,
                                    &path_requirements,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    post_state,
                                    result,
                                    &replay.program_point_states,
                                    Some(&outcome_surface_propositions),
                                    predicate_environment,
                                    click_function_environment,
                                    function_block.requires(),
                                    path_index,
                                ) {
                                    Some(lowered) => {
                                        surface_tactic = ProofTactic::Have(lowered);
                                    }
                                    None => {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: post-execution `have` script is not expressible as a certificate: {error:?}"
                                        )));
                                    }
                                }
                            }
                            (surface_tactic, fact)
                        };
                        outcome_surface_propositions.record_lowering(&have.proposition, &fact)?;
                        if !path_requirements.contains(&fact) {
                            path_requirements.push(fact);
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            surface_have,
                        );
                    }
                    PostExecutionTactic::Transport {
                        source,
                        target,
                        premises,
                    } => {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = &outcome
                        else {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `transport` requires a return outcome"
                            )));
                        };
                        let certificate_context = premises.is_none().then(|| {
                            (
                                path_requirements.clone(),
                                outcome_surface_propositions.clone(),
                            )
                        });
                        let surface_tactic = replay_fact_transport_at_outcome(
                            source,
                            target,
                            premises.as_deref(),
                            &proof_label,
                            path_index,
                            *tactic_index,
                            &mut path_requirements,
                            &mut outcome_surface_propositions,
                            &path.execution_facts(),
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                        )?;
                        if let Some((mut certificate_facts, mut certificate_surfaces)) =
                            certificate_context
                        {
                            let ProofTactic::TransportUsing {
                                source,
                                target,
                                premises,
                            } = &surface_tactic
                            else {
                                unreachable!(
                                    "smart post-execution transport must emit explicit premises"
                                )
                            };
                            TacticCertificate::from_proof_tactics(std::slice::from_ref(
                                &surface_tactic,
                            ))
                            .expect("explicit fact transport must be a simple certificate");
                            replay_fact_transport_at_outcome(
                                source,
                                target,
                                Some(premises),
                                &proof_label,
                                path_index,
                                *tactic_index,
                                &mut certificate_facts,
                                &mut certificate_surfaces,
                                &path.execution_facts(),
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &replay,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|error| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: post-execution `transport` certificate failed replay: {}",
                                    error.message()
                                ))
                            })?;
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            surface_tactic,
                        );
                    }
                    PostExecutionTactic::Choose(choice) => {
                        existence_tactics.push(ProofTactic::Choose(choice.clone()));
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::Choose(choice.clone()),
                        );
                    }
                    PostExecutionTactic::Witness(witness) => {
                        existence_tactics.push(ProofTactic::Witness(witness.clone()));
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::Witness(witness.clone()),
                        );
                    }
                    PostExecutionTactic::Assumption => {
                        let mut closed_any = false;
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                continue;
                            };
                            if let Ensure::Resource(resource) = ensure_clause.ensure() {
                                if prove_ensure_resource(
                                    &function_claim_label(function_block.signature().name(), claim),
                                    path_index,
                                    &path.execution_facts(),
                                    &path_requirements,
                                    resource,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                )
                                .is_ok()
                                {
                                    closures[claim_index] = ClaimClosure::by_exact_check();
                                    closed_any = true;
                                    break;
                                }
                                continue;
                            }
                            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
                                unreachable!("resource ensures were handled above")
                            };
                            let goal = match &rewritten_claim_goals[claim_index] {
                                Some(goal) => goal.clone(),
                                None => {
                                    if let Some(recorded) = outcome_surface_propositions
                                        .available_kernel(surface_goal, &path_requirements)
                                    {
                                        recorded.clone()
                                    } else {
                                        lower_ensure_proposition_goal(
                                            &path_requirements,
                                            surface_goal,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                            predicate_environment,
                                            click_function_environment,
                                            &replay.program_point_states,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` could not lower goal: {message}"
                                            ))
                                        })?
                                    }
                                }
                            };
                            if path_requirements.contains(&goal) {
                                closures[claim_index] = ClaimClosure::by_exact_check();
                                closed_any = true;
                                break;
                            }
                        }
                        if !closed_any {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` did not match any current proposition goal"
                            )));
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::Assumption,
                        );
                    }
                    PostExecutionTactic::Normalize => {
                        let mut closed_any = false;
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                continue;
                            };
                            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
                                continue;
                            };
                            let goal = match &rewritten_claim_goals[claim_index] {
                                Some(goal) => goal.clone(),
                                None => lower_ensure_proposition_goal(
                                    &path_requirements,
                                    surface_goal,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &replay.program_point_states,
                                    &unfolded_predicates,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` could not lower goal: {message}"
                                    ))
                                })?,
                            };
                            if matches!(normalize_proposition(&goal), SimpProposition::True) {
                                closures[claim_index] = ClaimClosure::by_exact_check();
                                closed_any = true;
                            }
                        }
                        if !closed_any {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` did not prove any current proposition goal"
                            )));
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::Normalize,
                        );
                    }
                    PostExecutionTactic::Rewrite(surface_equality) => {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = &outcome
                        else {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` requires a return outcome"
                            )));
                        };
                        let equality = lower_outcome_proposition_with_program_points(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &path_requirements,
                            surface_equality,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` could not lower equality: {message}"
                            ))
                        })?;
                        let mut rewrote_any = false;
                        let mut first_error = None;
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                continue;
                            };
                            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
                                continue;
                            };
                            let goal = match &rewritten_claim_goals[claim_index] {
                                Some(goal) => goal.clone(),
                                None => lower_ensure_proposition_goal(
                                    &path_requirements,
                                    surface_goal,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &replay.program_point_states,
                                    &unfolded_predicates,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` could not lower goal: {message}"
                                    ))
                                })?,
                            };
                            match rewrite_proposition_by_exact_equality(
                                &goal,
                                &equality,
                                &path_requirements,
                            ) {
                                Ok(rewritten) => {
                                    rewritten_claim_goals[claim_index] = Some(rewritten);
                                    rewrote_any = true;
                                }
                                Err(message) => {
                                    first_error.get_or_insert(message);
                                }
                            }
                        }
                        if !rewrote_any {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` failed: {}",
                                first_error.unwrap_or_else(|| {
                                    "there is no current proposition goal".to_string()
                                })
                            )));
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::Rewrite(surface_equality.clone()),
                        );
                    }
                    PostExecutionTactic::FrameRegion(_region) => {
                        for (claim_index, goal) in frame_certified_ensure_goals(
                            claims,
                            &path.execution_facts(),
                            &path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            &outcome,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
                            &unfolded_predicates,
                        ) {
                            frame_certified_claim_goals[claim_index] = Some(goal.clone());
                            if !path_requirements.contains(&goal) {
                                path_requirements.push(goal.clone());
                                if !surface_certificate_facts.contains(&goal) {
                                    surface_certificate_facts.push(goal);
                                }
                            }
                        }
                    }
                    PostExecutionTactic::Frame => {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            check_effect_claim_exact(
                                &claim_label,
                                path_index,
                                &path.execution_facts(),
                                &path_requirements,
                                claim,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                &outcome,
                            )?;
                            closures[claim_index] = ClaimClosure::by_exact_check();
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            *tactic_index,
                            ProofTactic::Frame(None),
                        );
                    }
                    PostExecutionTactic::CertifiedFrame(path_derivations) => {
                        let derivations = path_derivations.get(path_index).ok_or_else(|| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: certified frame has no derivations for this execution path"
                            ))
                        })?;
                        let mut frame_facts = path_requirements.clone();
                        frame_facts.extend(
                            path.execution_facts()
                                .iter()
                                .map(|fact| fact.proposition().clone()),
                        );
                        let assumptions = assumptions_from_propositions(&frame_facts);
                        for derivation in derivations {
                            if !derivation.replay(&assumptions) {
                                return Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: certified frame derivation did not replay for {:?}",
                                    derivation.conclusion()
                                )));
                            }
                            if !path_requirements.contains(derivation.conclusion()) {
                                path_requirements.push(derivation.conclusion().clone());
                            }
                        }
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            check_effect_claim_exact(
                                &claim_label,
                                path_index,
                                &path.execution_facts(),
                                &path_requirements,
                                claim,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                &outcome,
                            )?;
                            closures[claim_index] = ClaimClosure::by_exact_check();
                        }
                    }
                    PostExecutionTactic::Simp => {
                        let capturing_this_tactic = replay
                            .deferred_tactic_capture
                            .as_ref()
                            .is_some_and(|capture| capture.tactic_index == *tactic_index);
                        // Claims this `simp` discharges. A grouped contract
                        // certifies all of them with one transition, so they
                        // stay pending until it is built and replayed;
                        // `grouped_contract` picks which iteration builds the
                        // certificate, never what closure is allowed to mean.
                        let mut newly_closed: Vec<usize> = Vec::new();
                        let mut grouped_pending: Vec<usize> = Vec::new();
                        let mut grouped_transition_goals = Vec::new();
                        let path_execution_facts = path.execution_facts();
                        let closer_context = ExitClaimContext {
                            replay: &replay,
                            outcome_surface_propositions: &outcome_surface_propositions,
                            path_requirements: &path_requirements,
                            surface_certificate_facts: &surface_certificate_facts,
                            execution_facts: &path_execution_facts,
                            unfolded_predicates: &unfolded_predicates,
                            existence_tactics: &existence_tactics,
                            parameters: parsed_function.parameters(),
                            arguments,
                            pre_state,
                            outcome: &outcome,
                            predicate_environment,
                            click_function_environment,
                            theorem_environment,
                            function_requires: function_block.requires(),
                            path_index,
                            tactic_index: *tactic_index,
                        };
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                continue;
                            };
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            let result = if let Some(goal) = &rewritten_claim_goals[claim_index] {
                                if !existence_tactics.is_empty() {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: rewritten existential goals are not yet supported"
                                    )));
                                }
                                let mut reasoning_facts = path_requirements.clone();
                                reasoning_facts.extend(
                                    path.execution_facts()
                                        .iter()
                                        .filter(|fact| {
                                            matches!(
                                                fact.proposition(),
                                                Proposition::CMemoryMutatesOnly { .. }
                                                    | Proposition::CMemoryEffectSummary { .. }
                                            )
                                        })
                                        .map(|fact| fact.proposition().clone()),
                                );
                                let assumptions = assumptions_from_propositions(&reasoning_facts);
                                match simp_proposition(goal, &assumptions) {
                                    SimpProposition::True => Ok(()),
                                    simplified => Err(ClickError::new(format!(
                                        "`simp` failed for `{claim_label}` path {path_index}: simplified rewritten proposition was not true: {simplified:?}"
                                    ))),
                                }
                            } else if frame_certified_claim_goals[claim_index].is_some() {
                                Ok(())
                            } else if existence_tactics.is_empty() {
                                check_function_claim_by_simp(
                                    &claim_label,
                                    path_index,
                                    &path.execution_facts(),
                                    &path_requirements,
                                    claim,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &replay.program_point_states,
                                    &unfolded_predicates,
                                )
                            } else {
                                let mut available = path_requirements.clone();
                                check_function_claim_with_existence_tactics(
                                    &claim_label,
                                    path_index,
                                    &path.execution_facts(),
                                    &mut available,
                                    claim,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &unfolded_predicates,
                                    &existence_tactics,
                                    function_block.requires(),
                                    &replay.program_point_states,
                                    true,
                                )
                            };
                            match result {
                                Ok(()) => {
                                    match exit_claim::discharge_exit_simp_claim(
                                        &closer_context,
                                        claim_index,
                                        &claim_label,
                                        ensure_clause.ensure(),
                                        rewritten_claim_goals[claim_index].as_ref(),
                                        frame_certified_claim_goals[claim_index].as_ref(),
                                    )? {
                                        ExitSimpClosure::Closed(closure) => {
                                            closures[claim_index] = closure;
                                            newly_closed.push(claim_index);
                                        }
                                        ExitSimpClosure::JoinsGroupedTransition(goal) => {
                                            grouped_transition_goals.extend(goal);
                                            grouped_pending.push(claim_index);
                                        }
                                    }
                                }
                                Err(error) => {
                                    closures[claim_index]
                                        .record_failure(error.message().to_string());
                                    // The grouped certificate is the
                                    // proof-producing authority for proposition
                                    // claims. The ambient `simp` check above is
                                    // only a fast path and can miss a valid
                                    // source-site derivation, so retain the
                                    // lowered goal for exact certificate
                                    // construction below.
                                    if replay.grouped_contract
                                        && existence_tactics.is_empty()
                                        && rewritten_claim_goals[claim_index].is_none()
                                        && let Ensure::Proposition(surface_goal) =
                                            ensure_clause.ensure()
                                        && let CFunctionOutcome::Return { .. } = &outcome
                                        && let Ok(goal) = lower_ensure_proposition_goal(
                                            &path_requirements,
                                            surface_goal,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                            predicate_environment,
                                            click_function_environment,
                                            &replay.program_point_states,
                                            &unfolded_predicates,
                                        )
                                    {
                                        grouped_transition_goals.push(GroupedOutcomeSimpGoal {
                                            claim_index,
                                            claim_label,
                                            surface_goal: surface_goal.clone(),
                                            goal,
                                        });
                                        grouped_pending.push(claim_index);
                                    }
                                }
                            }
                        }
                        if replay.grouped_contract {
                            let certificate = match &outcome {
                                CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
                                } if existence_tactics.is_empty() => {
                                    let mut certificate_replay = replay.clone();
                                    certificate_replay.surface_propositions =
                                        outcome_surface_propositions.clone();
                                    certify_grouped_outcome_simp_transition(
                                        &certificate_replay,
                                        grouped_transition_goals,
                                        grouped_pending.len(),
                                        &surface_certificate_facts,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        result,
                                        predicate_environment,
                                        click_function_environment,
                                        theorem_environment,
                                        function_block.requires(),
                                        &proof_label,
                                        *tactic_index,
                                        path_index,
                                    )
                                }
                                _ => Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped `simp` transition is not surface-certifiable"
                                ))),
                            }?;
                            // Only now may the claims close: this transition is
                            // the certificate every one of them carries.
                            for claim_index in grouped_pending {
                                closures[claim_index] =
                                    ClaimClosure::by_grouped_transition(&certificate);
                            }
                            path_grouped_surface_closers.extend_from_slice(certificate.tactics());
                            if capturing_this_tactic {
                                path_deferred_capture_tactics
                                    .extend_from_slice(certificate.tactics());
                            }
                        } else if capturing_this_tactic {
                            for claim_index in newly_closed {
                                path_deferred_capture_tactics.extend_from_slice(
                                    closures[claim_index]
                                        .closed()
                                        .expect("a claim this `simp` closed holds its certificate")
                                        .claim_tactics(),
                                );
                            }
                        }
                    }
                }
            }

            if !require_explicit_closers {
                for (claim_index, claim) in claims.iter().enumerate() {
                    if closures[claim_index].is_closed() {
                        continue;
                    }
                    let claim_label =
                        function_claim_label(function_block.signature().name(), claim);
                    let result = if !existence_tactics.is_empty() {
                        let mut available = path_requirements.clone();
                        check_function_claim_with_existence_tactics(
                            &claim_label,
                            path_index,
                            &path.execution_facts(),
                            &mut available,
                            claim,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            &outcome,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                            &existence_tactics,
                            function_block.requires(),
                            &replay.program_point_states,
                            false,
                        )
                    } else {
                        check_function_claim(
                            &claim_label,
                            path_index,
                            &path.execution_facts(),
                            &path_requirements,
                            claim,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            &outcome,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
                            &unfolded_predicates,
                        )
                    };
                    match result {
                        Ok(()) => closures[claim_index] = ClaimClosure::by_exact_check(),
                        Err(error) => {
                            closures[claim_index].record_failure(error.message().to_string())
                        }
                    }
                }
            }

            if let Some((claim_index, claim)) = claims
                .iter()
                .enumerate()
                .find(|(claim_index, _)| !closures[*claim_index].is_closed())
            {
                let claim_label = function_claim_label(function_block.signature().name(), claim);
                let closer = match claim {
                    FunctionClaimRef::Effect(_, _) => "`frame()`",
                    FunctionClaimRef::Ensure(_, _) => "`simp()`",
                };
                let detail = closures[claim_index]
                    .last_error()
                    .map(|message| format!("\nlast closing attempt:\n{message}"))
                    .unwrap_or_default();
                return Err(ClickError::new(format!(
                    "`{proof_label}` path {path_index} left `{claim_label}` unproved; use {closer} after establishing the facts and resources it needs (claim index {claim_index}){detail}"
                )));
            }

            let (certified_path, specification_outcome, specification_requirements) = if replay
                .execution_abstraction
            {
                (
                    certified_path.clone(),
                    certified_outcomes[certified_path_for_replay[path_index]].clone(),
                    certification_facts.clone(),
                )
            } else {
                let certified_path =
                        certify_c_function_execution_path_resource_representation(
                            certified_path,
                            outcome.clone(),
                            &path.execution_facts(),
                        )
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "execution proof for `{proof_label}` path {path_index} changed more than the certified ghost resource representation\n  desired outcome: {outcome:?}\n  certified path: {:?}",
                                certified_path.theorem().proposition()
                            ))
                        })?;
                (certified_path, outcome.clone(), path_requirements.clone())
            };
            let specification = c_function_specification(
                pre_state.clone(),
                arguments.to_vec(),
                specification_requirements,
                specification_outcome,
            );
            let theorem = prove_c_function_satisfies_specification_from_symbolic_path(
                function.clone(),
                specification.clone(),
                &certified_path,
            )
            .ok_or_else(|| {
                ClickError::new(format!(
                    "execution proof for `{proof_label}` path {path_index} does not certify its exact function specification\n  specification: {specification:?}\n  certified path: {:?}",
                    certified_path.theorem().proposition()
                ))
            })?;
            for claim in claims {
                verified.push(VerifiedCTheorem {
                    source_path: source_path.to_string(),
                    function_block: function_block.clone(),
                    claim: claim.verified_claim(),
                    proof_kind: ProofKind::TacticScript,
                    proof_tactics: Some(certificate_tactics.to_vec()),
                    expanded_proof_tactics: replay
                        .surface_replay
                        .blocker
                        .is_none()
                        .then(|| replay.surface_replay.tactics.clone()),
                    expansion_blocker: replay.surface_replay.blocker.clone(),
                    specification: specification.clone(),
                    theorem: theorem.clone(),
                    concrete_loop_execution: replay.concrete_loop_execution,
                });
            }
            // Expansion prints what verification holds: the tactics come out
            // of the closure that accepted the claim, not from a parallel
            // record that could disagree with it.
            for (claim_index, closure) in closures.iter().enumerate() {
                surface_closers_by_claim[claim_index].push(
                    closure
                        .closed()
                        .map(ClosedClaim::claim_tactics)
                        .unwrap_or_default()
                        .to_vec(),
                );
            }
            surface_grouped_closers_by_path.push(path_grouped_surface_closers);
            surface_post_tactics_by_path.push(path_surface_post_tactics);
            deferred_capture_tactics_by_path.push(path_deferred_capture_tactics);
        }
        if replay.grouped_contract {
            let mut expanded = replay.surface_replay.clone();
            if surface_post_tactics_by_path
                .iter()
                .any(|tactics| !tactics.is_empty())
                && let Err(message) = append_surface_tactics_by_leaf(
                    &mut expanded.tactics,
                    &surface_post_tactics_by_path,
                )
            {
                expanded.block(message);
            }
            if surface_grouped_closers_by_path
                .iter()
                .any(|tactics| !tactics.is_empty())
                && let Err(message) = append_surface_tactics_by_leaf(
                    &mut expanded.tactics,
                    &surface_grouped_closers_by_path,
                )
            {
                expanded.block(message);
            }
            for theorem in &mut verified {
                theorem.expanded_proof_tactics =
                    expanded.blocker.is_none().then(|| expanded.tactics.clone());
                theorem.expansion_blocker = expanded.blocker.clone();
            }
        } else {
            for (claim_index, claim) in claims.iter().enumerate() {
                let mut expanded = replay.surface_replay.clone();
                if surface_post_tactics_by_path
                    .iter()
                    .any(|tactics| !tactics.is_empty())
                    && let Err(message) = append_surface_tactics_by_leaf(
                        &mut expanded.tactics,
                        &surface_post_tactics_by_path,
                    )
                {
                    expanded.block(message);
                }
                if surface_closers_by_claim[claim_index]
                    .iter()
                    .any(|tactics| !tactics.is_empty())
                    && let Err(message) = append_surface_tactics_by_leaf(
                        &mut expanded.tactics,
                        &surface_closers_by_claim[claim_index],
                    )
                {
                    expanded.block(message);
                }
                let verified_claim = claim.verified_claim();
                for theorem in &mut verified {
                    if theorem.claim == verified_claim {
                        theorem.expanded_proof_tactics =
                            expanded.blocker.is_none().then(|| expanded.tactics.clone());
                        theorem.expansion_blocker = expanded.blocker.clone();
                    }
                }
            }
        }
        if tactic_expansion_capture_is_active() {
            let deferred = replay.deferred_tactic_capture.as_ref().ok_or_else(|| {
                ClickError::new(format!(
                    "`{proof_label}` selected post-execution tactic lost its deferred capture"
                ))
            })?;
            // A tactic whose claims all closed by exact checks or grouped
            // transitions contributes no surface tactics of its own (see
            // `ClosedClaim::claim_tactics`): its exact expansion is empty and
            // the tactic is simply removed. Grafting the enclosing branch
            // skeleton around empty leaves would instead re-split every
            // already-merged execution path at path end, losing the
            // execution-path/branch-trace pairing certificate replay keeps —
            // proof-level `if` conditions lower at each path's own outcome, so
            // an alien path meets another path's branch conditions as
            // contradictory facts it cannot use.
            let contributes_no_tactics = deferred_capture_tactics_by_path
                .iter()
                .all(|tactics| tactics.is_empty());
            let mut capture = SurfaceReplay::default();
            if !contributes_no_tactics {
                capture.tactics = deferred.branch_skeleton.clone();
                if let Err(message) = append_surface_tactics_by_leaf(
                    &mut capture.tactics,
                    &deferred_capture_tactics_by_path,
                ) {
                    capture.block(message);
                }
            }
            return Err(finish_tactic_expansion_capture(
                &capture,
                contributes_no_tactics,
            ));
        }
        Ok(verified)
    })();
    result.map_err(|error| add_proof_branch_path(error, &branch_path))
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_fact_at_point(
    replay: &TacticReplayState,
    kernel: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let check = |surface: &ClickProposition| {
        lower_point_proposition(
            surface,
            available,
            parameters,
            arguments,
            replay.old_reference_state(state),
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(ClickError::new)
    };
    if let Ok(surface) = replay.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    if let Ok(ClickProposition::Loadable { segment }) = replay.surface_propositions.surface(kernel)
    {
        let mut old_segment = segment.clone();
        old_segment.state = ContractSegmentState::Old;
        let old_candidate = ClickProposition::Loadable {
            segment: old_segment,
        };
        if check(&old_candidate).ok().as_ref() == Some(kernel) {
            return Ok(old_candidate);
        }
    }
    if let Proposition::Predicate {
        name,
        arguments: target_arguments,
    } = kernel
    {
        let same_non_memory_arguments = |arguments: &[Term]| {
            arguments.len() == target_arguments.len()
                && arguments.iter().zip(target_arguments).all(|(left, right)| {
                    matches!((left, right), (Term::CMemory(_), Term::CMemory(_))) || left == right
                })
        };
        for recorded in replay.surface_propositions.kernel_facts() {
            let Proposition::Predicate {
                name: recorded_name,
                arguments,
            } = recorded
            else {
                continue;
            };
            if recorded_name != name || !same_non_memory_arguments(arguments) {
                continue;
            }
            let Ok(ClickProposition::PredicateCall {
                name: surface_name,
                arguments: surface_arguments,
            }) = replay.surface_propositions.surface(recorded)
            else {
                continue;
            };
            for point in replay.program_point_states.keys().rev() {
                let candidate = ClickProposition::PredicateCall {
                    name: surface_name.clone(),
                    arguments: surface_arguments
                        .iter()
                        .map(|argument| ContractExpression::At {
                            selector: VisitSelector::ProgramPoint(point.clone()),
                            expression: Box::new(argument.clone()),
                        })
                        .collect(),
                };
                if check(&candidate).ok().as_ref() == Some(kernel) {
                    return Ok(candidate);
                }
            }
        }
    }
    let kernel_memories = c_condition_fact_memories(kernel);
    if !kernel_memories.is_empty()
        && kernel_memories
            .iter()
            .any(|memory| !memory.has_same_snapshot_markers(state.memory()))
    {
        return Err(ClickError::new(format!(
            "kernel fact belongs to a different recorded memory snapshot: {kernel:?}"
        )));
    }
    let candidate = synthesize_surface_proposition(kernel, parameters, arguments, state)
        .ok_or_else(|| {
            ClickError::new(format!(
                "kernel fact has no recorded or structurally synthesized Click spelling: {kernel:?}"
            ))
        })?;
    let lowered = check(&candidate);
    if lowered.as_ref().is_ok_and(|lowered| lowered == kernel) {
        return Ok(candidate);
    }
    if let ClickProposition::Loadable { segment } = &candidate {
        let mut old_segment = segment.clone();
        old_segment.state = ContractSegmentState::Old;
        let old_candidate = ClickProposition::Loadable {
            segment: old_segment,
        };
        if check(&old_candidate).ok().as_ref() == Some(kernel) {
            return Ok(old_candidate);
        }
    }
    match lowered {
        Ok(lowered) => Err(ClickError::new(format!(
            "synthesized Click fact does not lower to the kernel fact at this proof point\n  Click: {candidate:?}\n  lowered: {lowered:?}\n  kernel: {kernel:?}"
        ))),
        Err(error) => Err(ClickError::new(format!(
            "synthesized Click fact could not be lowered at this proof point\n  Click: {candidate:?}\n  error: {}\n  kernel: {kernel:?}",
            error.message()
        ))),
    }
}

#[derive(Clone, Copy)]
enum SurfaceFactMatch {
    CanonicalExact,
    ReplayEquivalent,
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_comparison_fact_at_point(
    replay: &TacticReplayState,
    kernel: &Proposition,
    match_kind: SurfaceFactMatch,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let matches_kernel = |lowered: &Proposition| {
        if matches!(match_kind, SurfaceFactMatch::CanonicalExact) {
            return normalize_direct_atomic_memory_loads(lowered)
                == normalize_direct_atomic_memory_loads(kernel);
        }
        let lowered = normalize_direct_atomic_memory_loads(lowered);
        let kernel = normalize_direct_atomic_memory_loads(kernel);
        condition_polarity_equivalent(&lowered, &kernel)
            || lowered == kernel
            || materialization_equivalent_available_fact(&kernel, std::slice::from_ref(&lowered))
                .is_some()
            || quantified_binder_equivalent(&lowered, &kernel)
    };
    // Candidates below are matched through the permissive candidate lowering
    // (symbolic contract loads allowed), but the emitted certificate is
    // replayed by the ordinary executor, whose strict lowering carries
    // loadability obligations. A spelling that only lowers permissively —
    // for example a snapshot fact whose `at(...)` anchor was dropped so its
    // current-state loads are not provably loadable — must not be emitted.
    let strictly_replayable = |surface: &ClickProposition| {
        replay
            .surface_propositions
            .available_kernel(surface, available)
            .is_some()
            || lower_point_proposition(
                surface,
                available,
                parameters,
                arguments,
                replay.old_reference_state(state),
                state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .is_ok_and(|premise| {
                exact_fact_is_available(&premise, available)
                    || materialization_equivalent_available_fact(&premise, available).is_some()
            })
    };
    if let Ok(surface) = checked_surface_fact_at_point(
        replay,
        kernel,
        available,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    ) {
        return Ok(surface);
    }

    let mut bases = Vec::new();
    for surface in replay.surface_propositions.surfaces(kernel) {
        if !bases.contains(surface) {
            bases.push(surface.clone());
        }
    }
    let kernel_memories = c_condition_fact_memories(kernel);
    let matching_points = replay
        .program_point_states
        .iter()
        .rev()
        .filter(|(_, point_state)| {
            kernel_memories
                .iter()
                .any(|memory| memory.has_same_snapshot_markers(point_state.memory()))
        })
        .collect::<Vec<_>>();
    if let Some(surface) = synthesize_surface_proposition(kernel, parameters, arguments, state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    for (_, point_state) in &matching_points {
        if let Some(surface) =
            synthesize_surface_proposition(kernel, parameters, arguments, point_state)
            && !bases.contains(&surface)
        {
            bases.push(surface);
        }
    }
    for base in &bases {
        if let Ok(lowered) = lower_surface_candidate_at_point(
            replay,
            base,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) && (matches_kernel(&lowered)
            || proposition_contains_at_expression(base)
                && quantified_replay_equivalent_available_fact(
                    kernel,
                    std::slice::from_ref(&lowered),
                )
                .is_some())
            && strictly_replayable(base)
        {
            return Ok(base.clone());
        }
    }
    for (point, _) in matching_points {
        for base in &bases {
            let ClickProposition::Comparison {
                left,
                operator,
                right,
            } = base
            else {
                continue;
            };
            let at_point = |expression: &ContractExpression| ContractExpression::At {
                selector: VisitSelector::ProgramPoint(point.clone()),
                expression: Box::new(expression.clone()),
            };
            let candidates = [
                ClickProposition::Comparison {
                    left: at_point(left),
                    operator: *operator,
                    right: at_point(right),
                },
                ClickProposition::Comparison {
                    left: at_point(left),
                    operator: *operator,
                    right: right.clone(),
                },
                ClickProposition::Comparison {
                    left: left.clone(),
                    operator: *operator,
                    right: at_point(right),
                },
            ];
            for candidate in candidates {
                let lowered = lower_surface_candidate_at_point(
                    replay,
                    &candidate,
                    available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                );
                if lowered.is_ok_and(|lowered| matches_kernel(&lowered))
                    && strictly_replayable(&candidate)
                {
                    return Ok(candidate);
                }
            }
        }
    }
    let points = replay
        .program_point_states
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    for base in &bases {
        let Some(variants) = comparison_program_point_variants(base, &points) else {
            continue;
        };
        for candidate in variants {
            if lower_surface_candidate_at_point(
                replay,
                &candidate,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .is_ok_and(|lowered| matches_kernel(&lowered))
                && strictly_replayable(&candidate)
            {
                return Ok(candidate);
            }
        }
    }
    Err(ClickError::new(format!(
        "comparison fact has no checked Click spelling at this proof point: {kernel:?}\n  candidate spellings: {}",
        bases
            .iter()
            .map(describe_click_proposition)
            .collect::<Vec<_>>()
            .join(", ")
    )))
}

pub(super) fn synthesize_surface_proposition(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ClickProposition> {
    match proposition {
        Proposition::And(left, right) => {
            return Some(ClickProposition::And(
                Box::new(synthesize_surface_proposition(
                    left, parameters, arguments, state,
                )?),
                Box::new(synthesize_surface_proposition(
                    right, parameters, arguments, state,
                )?),
            ));
        }
        Proposition::Or(left, right) => {
            return Some(ClickProposition::Or(
                Box::new(synthesize_surface_proposition(
                    left, parameters, arguments, state,
                )?),
                Box::new(synthesize_surface_proposition(
                    right, parameters, arguments, state,
                )?),
            ));
        }
        Proposition::Implies(left, right) => {
            return Some(ClickProposition::Implies(
                Box::new(synthesize_surface_proposition(
                    left, parameters, arguments, state,
                )?),
                Box::new(synthesize_surface_proposition(
                    right, parameters, arguments, state,
                )?),
            ));
        }
        _ => {}
    }
    // A predicate call lowers each array-ref argument to a (memory, pointer)
    // term pair and each value argument to a single value term, so the kernel
    // argument list reads back unambiguously: a `CMemory` term always opens an
    // array-ref pair. The snapshot the pair names is not spelled here — the
    // current memory needs no spelling, and every caller re-lowers the
    // candidate and compares it to the kernel fact, so a candidate built
    // against the wrong snapshot is rejected by that round trip rather than by
    // a guess made here.
    if let Proposition::Predicate {
        name,
        arguments: kernel_arguments,
    } = proposition
    {
        let mut call_arguments = Vec::new();
        let mut index = 0;
        while index < kernel_arguments.len() {
            match &kernel_arguments[index] {
                Term::CMemory(_) => {
                    let Some(Term::CValue(CValue::Pointer(pointer))) =
                        kernel_arguments.get(index + 1)
                    else {
                        return None;
                    };
                    call_arguments.push(ContractExpression::CFragment(synthesize_surface_pointer(
                        pointer, parameters, arguments, state,
                    )?));
                    index += 2;
                }
                Term::CValue(CValue::Pointer(pointer)) => {
                    call_arguments.push(ContractExpression::CFragment(synthesize_surface_pointer(
                        pointer, parameters, arguments, state,
                    )?));
                    index += 1;
                }
                Term::CValue(CValue::Int32(value) | CValue::UInt8(value)) => {
                    call_arguments.push(synthesize_surface_bitvector(
                        value, parameters, arguments, state,
                    )?);
                    index += 1;
                }
                _ => return None,
            }
        }
        return Some(ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: call_arguments,
        });
    }
    if let Proposition::CResourceSeparate { left, right } = proposition {
        return Some(ClickProposition::Separate {
            left: synthesize_surface_resource_subject(left, parameters, arguments, state)?,
            right: synthesize_surface_resource_subject(right, parameters, arguments, state)?,
        });
    }
    if let Proposition::CMemoryLoadable { base, bytes, .. } = proposition {
        let element_count = if let Some(byte_count) = bytes.as_const() {
            if !byte_count.is_multiple_of(4) {
                return None;
            }
            CExpression::Value(int32(byte_count / 4))
        } else if let Bitvector32Term::Multiply(left, right) = bytes {
            let elements = if right.as_const() == Some(4) {
                left.as_ref()
            } else if left.as_const() == Some(4) {
                right.as_ref()
            } else {
                return None;
            };
            contract_expression_to_c_fragment(&synthesize_surface_bitvector(
                elements, parameters, arguments, state,
            )?)?
        } else {
            return None;
        };
        let semantic_base = synthesize_surface_pointer(base, parameters, arguments, state)?;
        let surface_base =
            synthesize_surface_pointer_offset(&base.offset, parameters, arguments, state)
                .unwrap_or_else(|| ContractExpression::CFragment(semantic_base.clone()));
        return Some(ClickProposition::Loadable {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: semantic_base,
                start: CExpression::Value(int32(0)),
                end: element_count.clone(),
                surface: ContractSegmentSurface::Range {
                    base: surface_base,
                    start: ContractExpression::CFragment(CExpression::Value(int32(0))),
                    end: ContractExpression::CFragment(element_count),
                },
            },
        });
    }
    if let Proposition::Not(body) = proposition {
        return Some(ClickProposition::Not(Box::new(
            synthesize_surface_proposition(body, parameters, arguments, state)?,
        )));
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    if let ConditionTerm::Constant(condition) = condition {
        return Some(ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: if condition == value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        });
    }
    if let ConditionTerm::PointerOffsetEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_pointer_offset(left, parameters, arguments, state)?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_offset(right, parameters, arguments, state)?,
        });
    }
    if let ConditionTerm::PointerEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: ContractExpression::CFragment(synthesize_surface_pointer(
                left, parameters, arguments, state,
            )?),
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: ContractExpression::CFragment(synthesize_surface_pointer(
                right, parameters, arguments, state,
            )?),
        });
    }
    let (left, operator, right) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            (left, ComparisonOperator::LessThan, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            (left, ComparisonOperator::LessEqual, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            (left, ComparisonOperator::GreaterThan, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            (left, ComparisonOperator::GreaterEqual, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => (left, ComparisonOperator::Equal, right),
        _ => return None,
    };
    let comparison = ClickProposition::Comparison {
        left: synthesize_surface_bitvector(left, parameters, arguments, state)?,
        operator,
        right: synthesize_surface_bitvector(right, parameters, arguments, state)?,
    };
    if *value {
        Some(comparison)
    } else if operator == ComparisonOperator::Equal {
        let ClickProposition::Comparison { left, right, .. } = comparison else {
            unreachable!()
        };
        Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        })
    } else {
        Some(ClickProposition::Not(Box::new(comparison)))
    }
}

fn synthesize_surface_resource_subject(
    resource: &CResource,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ResourceSubject> {
    let CResource::Memory(range) = resource else {
        return None;
    };
    let semantic_base = synthesize_surface_pointer(range.base(), parameters, arguments, state)?;
    let surface_base =
        synthesize_surface_pointer_offset(&range.base().offset, parameters, arguments, state)
            .unwrap_or_else(|| ContractExpression::CFragment(semantic_base.clone()));
    let surface_start = synthesize_surface_bitvector(range.start(), parameters, arguments, state)?;
    let surface_end = synthesize_surface_bitvector(range.end(), parameters, arguments, state)?;
    let start = contract_expression_to_c_fragment(&surface_start)?;
    let end = contract_expression_to_c_fragment(&surface_end)?;
    Some(ResourceSubject::Memory(ContractSegment {
        state: ContractSegmentState::Current,
        base: semantic_base,
        start,
        end,
        surface: ContractSegmentSurface::Range {
            base: surface_base,
            start: surface_start,
            end: surface_end,
        },
    }))
}

fn synthesize_surface_pointer_offset(
    term: &PointerOffsetTerm,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ContractExpression> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        if let CExpression::Value(CValue::Pointer(pointer)) = argument
            && pointer.offset == *term
        {
            return Some(ContractExpression::CFragment(CExpression::Variable(
                parameter.name().to_string(),
            )));
        }
    }
    match term {
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } if matches!(value.as_ref(), Bitvector32Term::MemoryLoad(_, _)) => {
            let Bitvector32Term::MemoryLoad(_, pointer) = value.as_ref() else {
                unreachable!()
            };
            if let Some(field) =
                synthesize_parameter_field_load(pointer, CType::Int32Pointer, parameters, arguments)
            {
                Some(field)
            } else {
                Some(ContractExpression::CFragment(CExpression::TypedLoad {
                    pointer: Box::new(synthesize_surface_pointer(
                        pointer, parameters, arguments, state,
                    )?),
                    value_type: CType::Int32Pointer,
                }))
            }
        }
        PointerOffsetTerm::Add(left, right) => {
            let indexed_pointer = |base: &PointerOffsetTerm, byte_offset: &PointerOffsetTerm| {
                let PointerOffsetTerm::Constant(byte_offset) = byte_offset else {
                    return None;
                };
                if byte_offset % 4 != 0 {
                    return None;
                }
                let ContractExpression::CFragment(base) =
                    synthesize_surface_pointer_offset(base, parameters, arguments, state)?
                else {
                    return None;
                };
                Some(ContractExpression::CFragment(CExpression::Add(
                    Box::new(base),
                    Box::new(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant((byte_offset / 4) as u32),
                    ))),
                )))
            };
            indexed_pointer(left, right).or_else(|| indexed_pointer(right, left))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if matches!(*byte_width, 1 | 4) => {
            synthesize_surface_bitvector(value, parameters, arguments, state)
        }
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int32Scaled { .. } => None,
    }
}

fn synthesize_surface_bitvector(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ContractExpression> {
    if let Some((name, _)) = state.locals().object_values().find(
        |(_, value)| matches!(value, CValue::Int32(local) | CValue::UInt8(local) if local == term),
    ) {
        return Some(if name == "result" {
            ContractExpression::CBinding(name.to_string())
        } else {
            ContractExpression::CFragment(CExpression::Variable(name.to_string()))
        });
    }
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return Some(if name == "result" {
            ContractExpression::CBinding(name)
        } else {
            ContractExpression::CFragment(CExpression::Variable(name))
        });
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        Some((
            Box::new(synthesize_surface_bitvector(
                left, parameters, arguments, state,
            )?),
            Box::new(synthesize_surface_bitvector(
                right, parameters, arguments, state,
            )?),
        ))
    };
    match term {
        Bitvector32Term::Constant(_) => Some(ContractExpression::CFragment(CExpression::Value(
            CValue::Int32(term.clone()),
        ))),
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Add(left, right))
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Subtract(left, right))
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Multiply(left, right))
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftLeft(left, right))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseAnd(left, right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseOr(left, right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseXor(left, right))
        }
        Bitvector32Term::BitwiseNot(value) => Some(ContractExpression::BitwiseNot(Box::new(
            synthesize_surface_bitvector(value, parameters, arguments, state)?,
        ))),
        Bitvector32Term::MemoryLoad(_, pointer) => {
            if let Some(field) =
                synthesize_parameter_field_load(pointer, CType::Int32, parameters, arguments)
            {
                Some(field)
            } else if let Some(indexed_field) =
                synthesize_parameter_field_indexed_int32_load(pointer, parameters, arguments, state)
            {
                Some(indexed_field)
            } else {
                let pointer = synthesize_surface_pointer(pointer, parameters, arguments, state)?;
                Some(ContractExpression::CFragment(CExpression::Load(Box::new(
                    pointer,
                ))))
            }
        }
        Bitvector32Term::Variable(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. } => None,
    }
}

fn synthesize_parameter_field_indexed_int32_load(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ContractExpression> {
    let pointer_field_and_index = |base: &PointerOffsetTerm,
                                   index: Option<&PointerOffsetTerm>|
     -> Option<(ContractExpression, ContractExpression)> {
        let PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } = base
        else {
            return None;
        };
        let Bitvector32Term::MemoryLoad(_, field_pointer) = value.as_ref() else {
            return None;
        };
        let field = synthesize_parameter_field_load(
            field_pointer,
            CType::Int32Pointer,
            parameters,
            arguments,
        )?;
        let index = match index {
            None => ContractExpression::CFragment(CExpression::Value(int32(0))),
            Some(PointerOffsetTerm::Int32Scaled {
                value,
                byte_width: 4,
            }) => synthesize_surface_bitvector(value, parameters, arguments, state)?,
            Some(_) => return None,
        };
        Some((field, index))
    };
    let (field, index) = match &pointer.offset {
        base @ PointerOffsetTerm::Int32Scaled { .. } => pointer_field_and_index(base, None)?,
        PointerOffsetTerm::Add(left, right) => pointer_field_and_index(left, Some(right))
            .or_else(|| pointer_field_and_index(right, Some(left)))?,
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => return None,
    };
    Some(ContractExpression::Index(Box::new(field), Box::new(index)))
}

fn synthesize_parameter_field_load(
    pointer: &Pointer,
    value_type: CType,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ContractExpression> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let (Some(layout), CExpression::Value(CValue::Pointer(base))) =
            (parameter.struct_layout(), argument)
        else {
            continue;
        };
        let Some(element_offset) = pointer
            .element_index_from_base(base)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        let offset_bytes = element_offset.checked_mul(4)?;
        let Some((field_name, field)) = layout
            .fields()
            .iter()
            .find(|(_, field)| field.offset_bytes() == offset_bytes)
        else {
            continue;
        };
        if field.c_type().to_kernel_type() != value_type {
            continue;
        }
        let base = CExpression::Variable(parameter.name().to_string());
        let field_pointer = if offset_bytes == 0 {
            base.clone()
        } else {
            CExpression::PointerOffsetBytes {
                pointer: Box::new(base.clone()),
                bytes: offset_bytes,
            }
        };
        return Some(ContractExpression::Field {
            base: Box::new(ContractExpression::CFragment(base)),
            field: field_name.clone(),
            lowered: CExpression::TypedLoad {
                pointer: Box::new(field_pointer),
                value_type,
            },
        });
    }
    None
}

fn synthesize_surface_pointer(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<CExpression> {
    if let Some(expression) = parameters
        .iter()
        .zip(arguments)
        .find_map(|(parameter, argument)| {
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return None;
            };
            let index = pointer.element_index_from_base(base)?;
            let base = CExpression::Variable(parameter.name().to_string());
            if index == Bitvector32Term::Constant(0) {
                return Some(base);
            }
            let index = synthesize_surface_bitvector(&index, parameters, arguments, state)?;
            let ContractExpression::CFragment(index) = index else {
                return None;
            };
            Some(CExpression::Add(Box::new(base), Box::new(index)))
        })
    {
        return Some(expression);
    }
    if !arguments.iter().any(|argument| {
        matches!(
            argument,
            CExpression::Value(CValue::Pointer(base)) if base.block == pointer.block
        )
    }) {
        return None;
    }
    let ContractExpression::CFragment(expression) =
        synthesize_surface_pointer_offset(&pointer.offset, parameters, arguments, state)?
    else {
        return None;
    };
    Some(expression)
}

#[allow(clippy::too_many_arguments)]
fn lower_surface_atomic_derivation(
    replay: &TacticReplayState,
    derivation: &PropositionDerivation,
    preferred_conclusion: Option<&ClickProposition>,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(ClickProposition, Proof), ClickError> {
    let conclusion = match preferred_conclusion {
        Some(conclusion) => conclusion.clone(),
        None => checked_surface_fact_at_point(
            replay,
            derivation.conclusion(),
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )?,
    };
    let mut premise_pairs = Vec::new();
    let mut unexpressed_premises = Vec::new();
    for premise in derivation.context_premises() {
        match checked_surface_comparison_fact_at_point(
            replay,
            &premise,
            SurfaceFactMatch::ReplayEquivalent,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) {
            Ok(surface) => premise_pairs.push((premise, surface)),
            Err(error) => unexpressed_premises.push((premise, error)),
        }
    }
    let replay_kind = |pairs: &[(Proposition, ClickProposition)]| {
        let kernel_premises = pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let assumptions = assumptions_from_propositions(&kernel_premises);
        if assumptions
            .derive_atomic_proposition(derivation.conclusion())
            .or_else(|| assumptions.derive_proposition(derivation.conclusion()))
            .is_some()
        {
            Some(false)
        } else if assumptions
            .derive_simp_atomic_proposition(derivation.conclusion())
            .or_else(|| assumptions.derive_simp_proposition(derivation.conclusion()))
            .is_some()
        {
            Some(true)
        } else {
            None
        }
    };
    if !matches!(
        normalize_proposition(derivation.conclusion()),
        SimpProposition::True
    ) && replay_kind(&premise_pairs).is_none()
    {
        return Err(ClickError::new(format!(
            "surface premises do not replay the atomic derivation of {:?}\nunexpressed derivation premises:\n{}",
            derivation.conclusion(),
            unexpressed_premises
                .iter()
                .map(|(premise, error)| format!("  {premise:?}: {}", error.message()))
                .collect::<Vec<_>>()
                .join("\n"),
        )));
    }
    let mut index = 0;
    while index < premise_pairs.len() {
        let mut reduced = premise_pairs.clone();
        reduced.remove(index);
        if matches!(
            normalize_proposition(derivation.conclusion()),
            SimpProposition::True
        ) || replay_kind(&reduced).is_some()
        {
            premise_pairs = reduced;
        } else {
            index += 1;
        }
    }
    let kind = replay_kind(&premise_pairs);
    let surface_premises = premise_pairs
        .into_iter()
        .map(|(_, surface)| surface)
        .collect::<Vec<_>>();
    let proof_tactic = if matches!(
        normalize_proposition(derivation.conclusion()),
        SimpProposition::True
    ) {
        ProofTactic::Normalize
    } else if kind == Some(false) {
        ProofTactic::Derive(ProofDerive {
            proposition: conclusion.clone(),
            premises: surface_premises,
        })
    } else {
        ProofTactic::Calculate(ProofDerive {
            proposition: conclusion.clone(),
            premises: surface_premises,
        })
    };
    Ok((conclusion, Proof::Script(vec![proof_tactic])))
}

#[allow(clippy::too_many_arguments)]
fn lower_outcome_simp_tactic(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ProofTactic, ClickError> {
    if matches!(normalize_proposition(goal), SimpProposition::True) {
        return Ok(ProofTactic::Normalize);
    }

    let check = |surface: &ClickProposition| {
        lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            available,
            surface,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
    };
    if check(surface_goal)
        .is_ok_and(|surface_goal| pure_fact_is_replay_available(&surface_goal, available))
    {
        return Ok(ProofTactic::Assumption);
    }
    let normalized_goal = normalize_direct_atomic_memory_loads(goal);
    let mut atomic_available = Vec::new();
    for fact in available {
        atomic_conjuncts(fact, &mut atomic_available);
    }
    let atomic_available = atomic_available.into_iter().cloned().collect::<Vec<_>>();
    let normalized_available = atomic_available
        .iter()
        .map(normalize_direct_atomic_memory_loads)
        .collect::<Vec<_>>();
    let source_for_required = |required: &Proposition| {
        let loadability_source = directly_covering_loadability_fact(required, &atomic_available);
        let checked_source = |fact: &Proposition| {
            checked_surface_fact_at_outcome(
                replay,
                fact,
                SurfaceFactMatch::CanonicalExact,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            )
            .ok()
            .filter(|surface| {
                check(surface).is_ok_and(|lowered| {
                    condition_polarity_equivalent(&lowered, fact)
                        || nested_quantified_binder_equivalent(&lowered, fact, 8)
                })
            })
            .map(|surface| (fact.clone(), surface))
        };

        // Exact facts (and the one preselected covering loadability fact) are
        // overwhelmingly the common case. Do not surface-lower every
        // snapshot-equivalent ambient fact before trying them.
        atomic_available
            .iter()
            .filter(|fact| {
                *fact == required
                    || loadability_source
                        .as_ref()
                        .is_some_and(|source| source == *fact)
            })
            .find_map(&checked_source)
            .or_else(|| {
                atomic_available
                    .iter()
                    .filter(|fact| {
                        condition_polarity_equivalent(
                            &normalize_direct_atomic_memory_loads(fact),
                            &normalize_direct_atomic_memory_loads(required),
                        ) || matches!(
                            (fact, required),
                            (Proposition::ForAll { .. }, Proposition::ForAll { .. })
                        )
                    })
                    .find_map(checked_source)
            })
    };
    // Plan against the kernel facts, then require an exact checked Surface
    // spelling for every premise the derivation actually selected. The
    // derivation context is the complete dependency boundary; eagerly
    // translating every ambient fact is both unnecessary and pathologically
    // expensive when facts contain symbolic memory snapshots.
    if let Some(plan) =
        plan_simp_certificate(goal, &assumptions_from_propositions(&atomic_available))
        && let [ProofTactic::ExactPropositionDerivation(derivation)] = plan.tactics()
    {
        let ambient = assumptions_from_propositions(&atomic_available);
        let context = derivation
            .context_premises()
            .into_iter()
            .filter(|premise| {
                !matches!(normalize_proposition(premise), SimpProposition::True)
                    && !matches!(
                        premise,
                        Proposition::CMemoryMutatesOnly { .. }
                            | Proposition::CMemoryEffectSummary { .. }
                    )
                    // A loadability premise the ambient context re-derives
                    // (for example from materialized memory) needs no
                    // surface spelling; replay re-derives it the same way.
                    && !(matches!(premise, Proposition::CMemoryLoadable { .. })
                        && ambient.derive_atomic_proposition(premise).is_some())
            })
            .collect::<Vec<_>>();
        let mut selected_premises = Vec::new();
        for required in &context {
            let selected = source_for_required(required).ok_or_else(|| {
                ClickError::new(format!(
                    "planned `simp` context premise is not an available source fact: {required:?}"
                ))
            })?;
            if !selected_premises.contains(&selected) {
                selected_premises.push(selected);
            }
        }
        let selected_kernel = selected_premises
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        if derivation.replay(&assumptions_from_propositions(&selected_kernel)) {
            return Ok(ProofTactic::Calculate(ProofDerive {
                proposition: surface_goal.clone(),
                premises: selected_premises
                    .into_iter()
                    .map(|(_, surface)| surface)
                    .collect(),
            }));
        }
    }
    if matches!(normalized_goal, Proposition::ForAll { .. }) {
        let derives_goal = |facts: &[Proposition]| {
            let facts = facts
                .iter()
                .map(normalize_direct_atomic_memory_loads)
                .collect::<Vec<_>>();
            assumptions_from_propositions(&facts)
                .derive_simp_proposition(&normalized_goal)
                .is_some()
        };
        let mut selected = atomic_available
            .iter()
            .filter(|fact| {
                matches!(
                    fact,
                    Proposition::ForAll { .. } | Proposition::ConditionIs(_, _)
                )
            })
            .cloned()
            .collect::<Vec<_>>();
        if derives_goal(&selected) {
            let mut index = 0;
            while index < selected.len() {
                let mut reduced = selected.clone();
                reduced.remove(index);
                if derives_goal(&reduced) {
                    selected = reduced;
                } else {
                    index += 1;
                }
            }
            for fact in &atomic_available {
                if matches!(fact, Proposition::CMemoryLoadable { .. }) && !selected.contains(fact) {
                    selected.push(fact.clone());
                }
            }
            let surface_premises = selected
                .iter()
                .map(|fact| {
                    checked_surface_fact_at_outcome(
                        replay,
                        fact,
                        SurfaceFactMatch::CanonicalExact,
                        available,
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        predicate_environment,
                        click_function_environment,
                    )
                })
                .collect::<Result<Vec<_>, _>>();
            if let Ok(surface_premises) = surface_premises {
                return Ok(ProofTactic::Calculate(ProofDerive {
                    proposition: surface_goal.clone(),
                    premises: surface_premises,
                }));
            }
        }
    }
    if let Some(derivation) =
        minimal_simp_proposition_derivation(&normalized_goal, &normalized_available)
    {
        let context = derivation.context_premises();
        let selected = context
            .iter()
            .filter_map(|required| {
                atomic_available.iter().find(|fact| {
                    condition_polarity_equivalent(
                        &normalize_direct_atomic_memory_loads(fact),
                        required,
                    )
                })
            })
            .collect::<Vec<_>>();
        if selected.len() == context.len() {
            let surface_premises = selected
                .iter()
                .map(|fact| {
                    checked_surface_fact_at_outcome(
                        replay,
                        fact,
                        SurfaceFactMatch::CanonicalExact,
                        available,
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        predicate_environment,
                        click_function_environment,
                    )
                })
                .collect::<Result<Vec<_>, _>>();
            if let Ok(surface_premises) = surface_premises {
                return Ok(ProofTactic::Calculate(ProofDerive {
                    proposition: surface_goal.clone(),
                    premises: surface_premises,
                }));
            }
        }
    }
    let points = replay
        .program_point_states
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    if let Some(variants) = comparison_program_point_variants(surface_goal, &points) {
        for candidate in variants {
            let Ok(lowered) = check(&candidate) else {
                continue;
            };
            let Some(available_fact) = available
                .iter()
                .find(|fact| condition_polarity_equivalent(fact, &lowered))
                .cloned()
            else {
                continue;
            };
            let assumptions = assumptions_from_propositions(std::slice::from_ref(&available_fact));
            if assumptions.derive_simp_proposition(goal).is_some() {
                return Ok(ProofTactic::Calculate(ProofDerive {
                    proposition: surface_goal.clone(),
                    premises: vec![candidate],
                }));
            }
        }
    }
    if let Some(fact) = available.iter().find(|fact| {
        condition_polarity_equivalent(
            &normalize_direct_atomic_memory_loads(fact),
            &normalized_goal,
        )
    }) && let Ok(surface) = checked_surface_fact_at_outcome(
        replay,
        fact,
        SurfaceFactMatch::CanonicalExact,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    ) && check(&surface).is_ok_and(|lowered| condition_polarity_equivalent(&lowered, fact))
    {
        let assumptions = assumptions_from_propositions(std::slice::from_ref(fact));
        if assumptions
            .derive_atomic_proposition(goal)
            .or_else(|| assumptions.derive_proposition(goal))
            .is_some()
        {
            return Ok(ProofTactic::Derive(ProofDerive {
                proposition: surface_goal.clone(),
                premises: vec![surface],
            }));
        }
        if assumptions
            .derive_simp_atomic_proposition(goal)
            .or_else(|| assumptions.derive_simp_proposition(goal))
            .is_some()
        {
            return Ok(ProofTactic::Calculate(ProofDerive {
                proposition: surface_goal.clone(),
                premises: vec![surface],
            }));
        }
    }
    let mut premise_pairs = Vec::new();
    for fact in available {
        let Ok(surface) = checked_surface_fact_at_outcome(
            replay,
            fact,
            SurfaceFactMatch::CanonicalExact,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        ) else {
            continue;
        };
        if check(&surface).is_ok_and(|lowered| condition_polarity_equivalent(&lowered, fact))
            && !premise_pairs
                .iter()
                .any(|(kernel, recorded_surface)| kernel == fact || recorded_surface == &surface)
        {
            premise_pairs.push((fact.clone(), surface));
        }
    }
    let kernel_premises = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let surface_premises = premise_pairs
        .iter()
        .cloned()
        .map(|(_, surface)| surface)
        .collect::<Vec<_>>();
    if surface_premises.is_empty() {
        return Err(ClickError::new(format!(
            "postcondition has no expressible premises for surface `simp` lowering: {goal:?}"
        )));
    }
    let normalized_kernel_premises = kernel_premises
        .iter()
        .map(normalize_direct_atomic_memory_loads)
        .collect::<Vec<_>>();
    let assumptions = assumptions_from_propositions(&normalized_kernel_premises);
    let exact_assumptions = assumptions_from_propositions(&kernel_premises);
    if let Some(plan) = plan_simp_certificate(goal, &assumptions_from_propositions(available))
        && let [ProofTactic::ExactPropositionDerivation(derivation)] = plan.tactics()
    {
        let context = derivation.context_premises();
        let selected = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                context
                    .iter()
                    .any(|required| exact_fact_contains_conjunct(kernel, required))
            })
            .cloned()
            .collect::<Vec<_>>();
        let selected_kernel = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        if derivation.replay(&assumptions_from_propositions(&selected_kernel)) {
            return Ok(ProofTactic::Calculate(ProofDerive {
                proposition: surface_goal.clone(),
                premises: selected.into_iter().map(|(_, surface)| surface).collect(),
            }));
        }
    }
    if exact_assumptions
        .derive_atomic_proposition(goal)
        .or_else(|| exact_assumptions.derive_proposition(goal))
        .is_some()
        && assumptions
            .derive_atomic_proposition(&normalized_goal)
            .or_else(|| assumptions.derive_proposition(&normalized_goal))
            .is_some()
    {
        Ok(ProofTactic::Derive(ProofDerive {
            proposition: surface_goal.clone(),
            premises: surface_premises,
        }))
    } else if exact_assumptions
        .derive_simp_atomic_proposition(goal)
        .or_else(|| exact_assumptions.derive_simp_proposition(goal))
        .is_some()
        && assumptions
            .derive_simp_atomic_proposition(&normalized_goal)
            .or_else(|| assumptions.derive_simp_proposition(&normalized_goal))
            .is_some()
    {
        Ok(ProofTactic::Calculate(ProofDerive {
            proposition: surface_goal.clone(),
            premises: surface_premises,
        }))
    } else {
        // Effect-backed postconditions derive from kernel-certified facts
        // (statement effect facts and certified store equations). Everything
        // gets a surface spelling: express each premise the minimized
        // derivation needs, synthesizing an `at(point, ...)` spelling from a
        // recorded program-point state when no ambient fact carries it.
        let mut certified_context = available.to_vec();
        for fact in &replay.effect_facts {
            if !certified_context.contains(fact.proposition()) {
                certified_context.push(fact.proposition().clone());
            }
        }
        for equation in crate::kernel::certified_store_equations(&replay.effect_facts) {
            if !certified_context.contains(&equation) {
                certified_context.push(equation);
            }
        }
        let minimized = minimal_proposition_derivation(goal, &certified_context)
            .map(|derivation| (derivation, false))
            .or_else(|| {
                minimal_simp_proposition_derivation(goal, &certified_context)
                    .map(|derivation| (derivation, true))
            });
        if minimized.is_none()
            && let Ok(dir) = std::env::var("CLICK_DERIVE_DUMP_DIR")
        {
            let stamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|duration| duration.subsec_nanos())
                .unwrap_or(0);
            let _ = std::fs::write(format!("{dir}/goal-{stamp}.txt"), format!("{goal:#?}"));
            let _ = std::fs::write(
                format!("{dir}/context-{stamp}.txt"),
                format!("{certified_context:#?}"),
            );
        }
        if let Some((derivation, for_simp)) = minimized {
            let entry_point = ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            };
            let mut spelled_premises: Vec<ClickProposition> = Vec::new();
            let mut kernel_premises: Vec<Proposition> = Vec::new();
            let mut complete = true;
            'premises: for required in derivation.context_premises() {
                // A recorded lowering round-trips exactly: replay resolves
                // the spelling through the same map before re-lowering.
                if let Ok(surface) = replay.surface_propositions.surface(&required)
                    && replay
                        .surface_propositions
                        .available_kernel(surface, &certified_context)
                        == Some(&required)
                {
                    if !kernel_premises.contains(&required) {
                        kernel_premises.push(required.clone());
                        spelled_premises.push(surface.clone());
                    }
                    continue;
                }
                if let Some((surface, lowered)) = available.iter().find_map(|fact| {
                    if !exact_fact_contains_conjunct(fact, &required) {
                        return None;
                    }
                    let surface = checked_surface_fact_at_outcome(
                        replay,
                        fact,
                        SurfaceFactMatch::ReplayEquivalent,
                        available,
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        predicate_environment,
                        click_function_environment,
                    )
                    .ok()?;
                    // Record what the spelling actually lowers to. Canonical
                    // load spelling only recognizes candidates; the replay
                    // below must derive from this exact lowered proposition.
                    let lowered = check(&surface).ok()?;
                    propositions_match_up_to_canonical_loads(&lowered, &required)
                        .then_some((surface, lowered))
                }) {
                    if !kernel_premises.contains(&lowered) {
                        kernel_premises.push(lowered);
                        spelled_premises.push(surface);
                    }
                    continue;
                }
                let candidate_states = std::iter::once((&entry_point, pre_state)).chain(
                    replay
                        .program_point_states
                        .iter()
                        .rev()
                        .map(|(point, state)| (point, state)),
                );
                for (point, point_state) in candidate_states {
                    let Some(core) = synthesize_surface_proposition(
                        &required,
                        parameters,
                        arguments,
                        point_state,
                    ) else {
                        continue;
                    };
                    let surface = ClickProposition::At {
                        selector: VisitSelector::ProgramPoint(point.clone()),
                        proposition: Box::new(core),
                    };
                    if let Ok(lowered) = check(&surface)
                        && propositions_match_up_to_canonical_loads(&lowered, &required)
                    {
                        if !kernel_premises.contains(&lowered) {
                            kernel_premises.push(lowered);
                            spelled_premises.push(surface);
                        }
                        continue 'premises;
                    }
                }
                complete = false;
                break;
            }
            if complete && !spelled_premises.is_empty() {
                let derive = ProofDerive {
                    proposition: surface_goal.clone(),
                    premises: spelled_premises,
                };
                let candidate = if for_simp {
                    ProofTactic::Calculate(derive)
                } else {
                    ProofTactic::Derive(derive)
                };
                // Self-check with exactly the check the tactic replay runs,
                // against the replay context (which carries the certified
                // store equations).
                if check_atomic_derivation_goal(
                    &candidate,
                    goal.clone(),
                    kernel_premises,
                    goal,
                    &certified_context,
                )
                .is_ok()
                {
                    return Ok(candidate);
                }
            }
        }
        Err(ClickError::new(format!(
            "expressible path facts do not replay the postcondition derivation: {goal:?}\n  surface premises: {}",
            surface_premises
                .iter()
                .map(describe_click_proposition)
                .collect::<Vec<_>>()
                .join(", ")
        )))
    }
}

fn collect_definable_predicate_names(
    proposition: &Proposition,
    predicate_environment: &PredicateEnvironment,
    names: &mut Vec<String>,
) {
    match proposition {
        Proposition::Predicate { name, .. } => {
            if predicate_environment.get(name).is_some() && !names.contains(name) {
                names.push(name.clone());
            }
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_definable_predicate_names(left, predicate_environment, names);
            collect_definable_predicate_names(right, predicate_environment, names);
        }
        Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
            collect_definable_predicate_names(body, predicate_environment, names);
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_outcome_simp_proof(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proof, ClickError> {
    // An opaque predicate in the goal is unfolded by the certificate: the
    // replay-side derivation judgment has no predicate rules, so the
    // emitted proof must carry `unfold(...)` and prove the body. The goal
    // comparison in the caller keeps working because it accepts the goal
    // in either spelling.
    // The emitted have script must carry its own unfolds: replay lowers the
    // surface proposition under exactly the unfolds written in the script,
    // while the kernel goal here was lowered with the drain's unfold set
    // active. Two cases produce a spelling gap. (a) The kernel goal still
    // holds an opaque predicate: unfold it and prove the body — the
    // replay-side derivation judgment has no predicate rules. (b) The
    // kernel goal is already the unfolded body while the surface goal is a
    // predicate call: without the prefix, replay would lower the surface
    // goal opaquely and prove a different proposition than the tactics
    // certify.
    let mut opaque_names = Vec::new();
    collect_definable_predicate_names(goal, predicate_environment, &mut opaque_names);
    if !opaque_names.is_empty() {
        // Best effort: a deliberately opaque predicate (whose body's loads
        // the contract does not establish) fails to unfold here; such goals
        // must close without unfolding, so fall through to the direct path.
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &opaque_names,
            goal,
            &assumptions_from_propositions(available),
        );
        if let Ok(unfolded_goal) = unfolded {
            let mut unfolding_replay = replay.clone();
            unfolding_replay
                .unfolded_predicates
                .extend(opaque_names.iter().cloned());
            if let Ok(Proof::Script(inner_tactics)) = lower_outcome_simp_proof_direct(
                &unfolding_replay,
                surface_goal,
                &unfolded_goal,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            ) {
                let mut tactics = opaque_names
                    .into_iter()
                    .map(ProofTactic::UnfoldPredicate)
                    .collect::<Vec<_>>();
                tactics.extend(inner_tactics);
                return Ok(Proof::Script(tactics));
            }
        }
    } else {
        // Carry the drain's whole unfold set: replay lowers the goal AND
        // every listed premise under the script's unfolds, and a premise
        // can be an unfold-active predicate call even when the goal is not.
        let mut surface_names = replay.unfolded_predicates.clone();
        surface_names.retain(|name| predicate_environment.get(name).is_some());
        if !surface_names.is_empty() {
            let inner = lower_outcome_simp_proof_direct(
                replay,
                surface_goal,
                goal,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            )?;
            let Proof::Script(inner_tactics) = inner else {
                return Err(ClickError::new(
                    "predicate-goal certificate lowering produced a non-script proof",
                ));
            };
            let mut tactics = surface_names
                .into_iter()
                .map(ProofTactic::UnfoldPredicate)
                .collect::<Vec<_>>();
            tactics.extend(inner_tactics);
            return Ok(Proof::Script(tactics));
        }
    }
    lower_outcome_simp_proof_direct(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_outcome_simp_proof_direct(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proof, ClickError> {
    if let (ClickProposition::And(surface_left, surface_right), Proposition::And(left, right)) =
        (surface_goal, goal)
        && !available.contains(goal)
    {
        let left_proof = lower_outcome_simp_proof(
            replay,
            surface_left,
            left,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        )?;
        let mut right_available = available.to_vec();
        if !right_available.contains(left) {
            right_available.push(left.as_ref().clone());
        }
        let right_proof = lower_outcome_simp_proof(
            replay,
            surface_right,
            right,
            &right_available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        )?;
        return Ok(Proof::Script(vec![
            ProofTactic::Have(ProofHave {
                proposition: surface_left.as_ref().clone(),
                proof: left_proof,
            }),
            ProofTactic::Have(ProofHave {
                proposition: surface_right.as_ref().clone(),
                proof: right_proof,
            }),
            ProofTactic::Conjunction,
        ]));
    }
    Ok(Proof::Script(vec![lower_outcome_simp_tactic(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?]))
}

#[allow(clippy::too_many_arguments)]
fn certify_outcome_simp_have(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    claim_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    let initial_proof = lower_outcome_simp_proof(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?;
    let mut goal_lowering_facts = available.to_vec();
    if let Proof::Script(tactics) = &initial_proof
        && let Some(ProofTactic::Derive(derive) | ProofTactic::Calculate(derive)) = tactics.first()
    {
        goal_lowering_facts = facts_for_direct_derivation_lowering(available);
        for premise in &derive.premises {
            let lowered = replay
                .surface_propositions
                .available_kernel(premise, available)
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    lower_outcome_proposition_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        available,
                        premise,
                        predicate_environment,
                        click_function_environment,
                        &replay.program_point_states,
                    )
                })
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` could not lower a generated explicit premise while certifying its goal context: {error}"
                    ))
                })?;
            if !goal_lowering_facts.contains(&lowered) {
                goal_lowering_facts.push(lowered);
            }
        }
    }
    let lowered = lower_outcome_proposition_with_obligations(
        parameters,
        arguments,
        pre_state,
        post_state,
        Some(result),
        &goal_lowering_facts,
        surface_goal,
        predicate_environment,
        click_function_environment,
        &replay.program_point_states,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` could not structurally lower its surface goal: {error}"
        ))
    })?;
    // The claim goal may have been lowered while `unfold(...)` was active,
    // so compare against the re-lowered goal in the same unfolded spelling.
    let lowered_proposition = if replay.unfolded_predicates.is_empty() {
        lowered.proposition.clone()
    } else {
        unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            &lowered.proposition,
            &assumptions_from_propositions(available),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` could not unfold its re-lowered goal: {message}"
            ))
        })?
    };
    if normalize_direct_atomic_memory_loads(&lowered.proposition)
        != normalize_direct_atomic_memory_loads(goal)
        && normalize_direct_atomic_memory_loads(&lowered_proposition)
            != normalize_direct_atomic_memory_loads(goal)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` surface goal lowered to a different kernel proposition"
        )));
    }

    let mut certified_available = available.to_vec();
    let mut surface_tactics = Vec::new();
    let mut quantified_memory_premises: Vec<(ClickProposition, Proposition)> = Vec::new();
    for obligation in lowered.loadability_obligations {
        let SurfaceLoadabilityObligation {
            proposition: obligation,
            segment,
        } = obligation;
        if exact_fact_is_available(&obligation, &certified_available) {
            continue;
        }
        let recorded_segment = segment.clone();
        let check_surface = |surface: &ClickProposition| {
            lower_outcome_proposition_with_program_points(
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                &certified_available,
                surface,
                predicate_environment,
                click_function_environment,
                &replay.program_point_states,
            )
            .is_ok_and(|lowered| lowered == obligation)
        };
        let mut surface_obligation = segment.map(|segment| ClickProposition::Loadable { segment });
        if surface_obligation
            .as_ref()
            .is_some_and(|surface| !check_surface(surface))
            && let Some(ClickProposition::Loadable { segment }) = &surface_obligation
        {
            let mut old_segment = segment.clone();
            old_segment.state = ContractSegmentState::Old;
            let old = ClickProposition::Loadable {
                segment: old_segment,
            };
            surface_obligation = check_surface(&old).then_some(old);
        }
        let surface_obligation = match surface_obligation.filter(|surface| check_surface(surface)) {
            Some(surface) => surface,
            None => match checked_surface_fact_at_outcome(
                replay,
                &obligation,
                SurfaceFactMatch::CanonicalExact,
                &certified_available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            ) {
                Ok(surface) => surface,
                Err(error) => {
                    // A loadability obligation inside a quantified body can
                    // mention the binder and therefore has no standalone
                    // Surface Click spelling. It is safe to leave implicit
                    // only when ordinary (non-deferred) lowering of the whole
                    // goal proves it from the explicit generated premises.
                    if quantified_memory_premises.is_empty()
                        && matches!(goal, Proposition::ForAll { .. } | Proposition::Exists { .. })
                    {
                        let mut atomic_available = Vec::new();
                        for fact in available {
                            atomic_conjuncts(fact, &mut atomic_available);
                        }
                        for fact in atomic_available {
                            let needed_for_lowering =
                                matches!(fact, Proposition::CMemoryLoadable { .. })
                                    || matches!(fact, Proposition::ConditionIs(_, _))
                                        && c_condition_fact_has_memory(fact);
                            if !needed_for_lowering {
                                continue;
                            }
                            if let Ok(surface) = checked_surface_fact_at_outcome(
                                replay,
                                fact,
                                SurfaceFactMatch::CanonicalExact,
                                available,
                                parameters,
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                predicate_environment,
                                click_function_environment,
                            ) && !quantified_memory_premises
                                .iter()
                                .any(|(recorded, _)| recorded == &surface)
                            {
                                quantified_memory_premises.push((surface, fact.clone()));
                            }
                        }
                    }
                    for (_, fact) in &quantified_memory_premises {
                        if !goal_lowering_facts.contains(fact) {
                            goal_lowering_facts.push(fact.clone());
                        }
                    }
                    let implicit_lowering = lower_outcome_proposition_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        &goal_lowering_facts,
                        surface_goal,
                        predicate_environment,
                        click_function_environment,
                        &replay.program_point_states,
                    );
                    let implicit_in_goal = implicit_lowering.is_ok_and(|lowered_goal| {
                        normalize_direct_atomic_memory_loads(&lowered_goal)
                            == normalize_direct_atomic_memory_loads(goal)
                    });
                    if implicit_in_goal {
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` loadability obligation has no exact surface spelling: {}\n  recorded segment: {recorded_segment:?}\n  obligation: {obligation:?}",
                        error.message(),
                    )));
                }
            },
        };
        let obligation_memory = match &obligation {
            Proposition::CMemoryLoadable { memory, .. } => memory,
            _ => unreachable!("surface lowering obligations are loadability propositions"),
        };
        let has_current_loadability_context = certified_available.iter().any(|fact| {
            matches!(fact, Proposition::CMemoryLoadable { memory, .. }
                if memory.has_same_snapshot_markers(obligation_memory))
        });
        let direct = has_current_loadability_context
            .then(|| {
                lower_outcome_simp_proof(
                    replay,
                    &surface_obligation,
                    &obligation,
                    &certified_available,
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    result,
                    predicate_environment,
                    click_function_environment,
                )
            })
            .transpose()
            .and_then(|proof| {
                proof.ok_or_else(|| {
                    ClickError::new("loadability obligation requires memory transport")
                })
            })
            .and_then(|proof| {
                let surface_have = ProofHave {
                    proposition: surface_obligation.clone(),
                    proof,
                };
                let replayed = prove_have_at_point(
                    &surface_have,
                    theorem_environment,
                    claim_label,
                    tactic_index,
                    &certified_available,
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    Some(result),
                    &replay.program_point_states,
                    Some(&replay.surface_propositions),
                    predicate_environment,
                    click_function_environment,
                    function_requires,
                    Some(path_index),
                )?;
                if replayed != obligation {
                    return Err(ClickError::new(
                        "loadability certificate replayed a different proposition",
                    ));
                }
                Ok(surface_have)
            });
        if let Ok(surface_have) = direct {
            certified_available.push(obligation);
            surface_tactics.push(ProofTactic::Have(surface_have));
            continue;
        }

        let Proposition::CMemoryLoadable { .. } = &obligation else {
            unreachable!("surface lowering obligations are loadability propositions")
        };
        let source_selectors = std::iter::once(VisitSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }))
        .chain(
            replay
                .program_point_states
                .keys()
                .rev()
                .cloned()
                .map(VisitSelector::ProgramPoint),
        );
        let source_candidates = source_selectors
            .filter_map(|selector| {
                let surface = ClickProposition::At {
                    selector,
                    proposition: Box::new(surface_obligation.clone()),
                };
                let source = lower_outcome_proposition_with_program_points(
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    result,
                    &certified_available,
                    &surface,
                    predicate_environment,
                    click_function_environment,
                    &replay.program_point_states,
                )
                .ok()?;
                matches!(source, Proposition::CMemoryLoadable { .. }).then_some((source, surface))
            })
            .fold(Vec::new(), |mut candidates, candidate| {
                if !candidates.iter().any(|(source, _)| source == &candidate.0) {
                    candidates.push(candidate);
                }
                candidates
            });
        let source_candidate_count = source_candidates.len();
        let mut derivable_source_count = 0;
        let mut transportable_source_count = 0;
        let transported = source_candidates
            .into_iter()
            .find_map(|(source, surface_source)| {
                let Proposition::CMemoryLoadable {
                    memory: source_memory,
                    ..
                } = &source
                else {
                    unreachable!("loadability source candidates are loadability propositions")
                };
                let derivation = if exact_fact_is_available(&source, &certified_available) {
                    None
                } else {
                    let source_context = certified_available
                        .iter()
                        .filter(|fact| {
                            matches!(fact, Proposition::ConditionIs(_, _))
                                || matches!(fact, Proposition::CMemoryLoadable { memory, .. }
                                if memory.has_same_snapshot_markers(source_memory))
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    Some(
                        assumptions_from_propositions(&source_context)
                            .derive_atomic_proposition(&source)
                            .or_else(|| {
                                // The marker filter can starve the context;
                                // retry over everything available plus the
                                // path's effect facts, which connect the
                                // snapshots loadability transports across.
                                let mut context = certified_available.clone();
                                for fact in &replay.effect_facts {
                                    if !context.contains(fact.proposition()) {
                                        context.push(fact.proposition().clone());
                                    }
                                }
                                assumptions_from_propositions(&context)
                                    .derive_atomic_proposition(&source)
                            })?,
                    )
                };
                derivable_source_count += 1;
                let transition_facts =
                    fact_transport_transition_facts(&replay.effect_facts, &source);
                let transport_assumptions = transition_facts
                    .iter()
                    .fold(
                        assumptions_from_propositions(&certified_available),
                        |assumptions, fact| {
                            assumptions.assume_proposition(fact.proposition().clone())
                        },
                    )
                    .assume_proposition(source.clone());
                let reaches = certified_fact_transport_reaches(
                    &source,
                    &obligation,
                    post_state.memory(),
                    &transport_assumptions,
                );
                transportable_source_count += usize::from(reaches);
                reaches.then(|| (source, surface_source, derivation, transition_facts))
            });
        let Some((source, surface_source, source_derivation, transition_facts)) = transported
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: loadability obligation has neither a direct proof nor a certified transport\n  surface obligation: {}\n  source candidates: {source_candidate_count}, derivable: {derivable_source_count}, transportable: {transportable_source_count}\n  obligation: {obligation:?}",
                describe_click_proposition(&surface_obligation),
            )));
        };
        if !exact_fact_is_available(&source, &certified_available) {
            let source_derivation = source_derivation.expect(
                "a non-exact loadability transport source must carry its checked derivation",
            );
            let (_, source_proof) = lower_surface_atomic_derivation(
                replay,
                &source_derivation,
                Some(&surface_source),
                &certified_available,
                parameters,
                arguments,
                post_state,
                predicate_environment,
                click_function_environment,
            )?;
            let source_have = ProofHave {
                proposition: surface_source.clone(),
                proof: source_proof,
            };
            let replayed = prove_have_at_point(
                &source_have,
                theorem_environment,
                claim_label,
                tactic_index,
                &certified_available,
                parameters,
                arguments,
                pre_state,
                post_state,
                Some(result),
                &replay.program_point_states,
                Some(&replay.surface_propositions),
                predicate_environment,
                click_function_environment,
                function_requires,
                Some(path_index),
            )?;
            if replayed != source {
                return Err(ClickError::new(
                    "loadability transport source replayed a different proposition",
                ));
            }
            certified_available.push(source.clone());
            surface_tactics.push(ProofTactic::Have(source_have));
        }
        let explicit_assumptions = assumptions_from_propositions(std::slice::from_ref(&source));
        let resource_facts = post_state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let transport_assumptions = certified_available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        let transport_assumptions = transition_facts
            .iter()
            .fold(transport_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        if !certified_fact_transport_reaches(
            &source,
            &obligation,
            post_state.memory(),
            &transport_assumptions,
        ) {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: explicit loadability source does not replay its certified transport"
            )));
        }
        surface_tactics.push(ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_obligation,
            premises: vec![surface_source],
        });
        certified_available.push(obligation);
    }

    let mut proof = lower_outcome_simp_proof(
        replay,
        surface_goal,
        goal,
        &certified_available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?;
    if !quantified_memory_premises.is_empty()
        && let Proof::Script(tactics) = &mut proof
        && let Some(ProofTactic::Derive(derive) | ProofTactic::Calculate(derive)) =
            tactics.first_mut()
    {
        for (surface, _) in quantified_memory_premises {
            if !derive.premises.contains(&surface) {
                derive.premises.push(surface);
            }
        }
    }
    let surface_have = ProofHave {
        proposition: surface_goal.clone(),
        proof,
    };
    let surface_tactic = ProofTactic::Have(surface_have.clone());
    let certificate = TacticCertificate::from_proof_tactics(std::slice::from_ref(&surface_tactic))
        .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` produced an invalid certificate: {error:?}"
        ))
    })?;
    // Replay may frame loads across recorded effects; a fresh replay
    // recomputes the same effect facts from execution, so including them
    // keeps in-place and standalone replays aligned.
    let mut replay_available = certified_available.clone();
    for fact in &replay.effect_facts {
        if !replay_available.contains(fact.proposition()) {
            replay_available.push(fact.proposition().clone());
        }
    }
    for equation in crate::kernel::certified_store_equations(&replay.effect_facts) {
        if !replay_available.contains(&equation) {
            replay_available.push(equation);
        }
    }
    let replayed_goal = prove_have_at_point(
        &surface_have,
        theorem_environment,
        claim_label,
        tactic_index,
        &replay_available,
        parameters,
        arguments,
        pre_state,
        post_state,
        Some(result),
        &replay.program_point_states,
        Some(&replay.surface_propositions),
        predicate_environment,
        click_function_environment,
        function_requires,
        Some(path_index),
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` certificate failed replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message(),
        ))
    })?;
    if replayed_goal != *goal {
        // The claim goal may be spelled with `unfold(...)` active while the
        // replay produces the folded predicate; both name one proposition by
        // the predicate's definition.
        let replayed_unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            &replayed_goal,
            &assumptions_from_propositions(&replay_available),
        );
        if replay.unfolded_predicates.is_empty()
            || replayed_unfolded.as_ref() != Ok(goal)
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` certificate replayed a different goal"
            )));
        }
    }
    surface_tactics.push(surface_tactic);
    Ok(surface_tactics)
}

#[allow(clippy::too_many_arguments)]
fn certify_outcome_simp(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    claim_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<TacticCertificate, ClickError> {
    let mut surface_tactics = certify_outcome_simp_have(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        function_requires,
        claim_label,
        tactic_index,
        path_index,
    )?;
    surface_tactics.push(ProofTactic::Assumption);
    let certificate = TacticCertificate::from_proof_tactics(&surface_tactics).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` produced an invalid certificate: {error:?}"
        ))
    })?;
    Ok(certificate)
}

/// Lower an exit-claim `simp` that closed under pending `witness`/`choose`
/// tactics.
///
/// `witness` and `choose` are simple tactics, and a `have` proof admits
/// them (`prove_pure_proposition_case_at_point` runs both). So the closer
/// lowers to `have <claim goal> by { <existence tactics>, <simple closer> }`
/// followed by `assumption`: the have re-derives the existential inside its
/// own scope, and `assumption` discharges the claim from the fact the have
/// established. The have's proposition is the claim's own surface goal, so
/// no new surface spelling has to be synthesized for the instantiated body.
///
/// Every candidate is accepted only if `prove_have_at_point` — the replay
/// judgment itself — proves it and yields the claim's kernel goal, so this
/// emits exactly what replay accepts.
#[allow(clippy::too_many_arguments)]
fn certify_outcome_existential_simp(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    existence_tactics: &[ProofTactic],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    claim_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<TacticCertificate, ClickError> {
    // Replay may frame loads across recorded effects; a fresh replay
    // recomputes the same effect facts from execution, so including them
    // keeps in-place and standalone replays aligned.
    let mut replay_available = available.to_vec();
    for fact in &replay.effect_facts {
        if !replay_available.contains(fact.proposition()) {
            replay_available.push(fact.proposition().clone());
        }
    }
    for equation in crate::kernel::certified_store_equations(&replay.effect_facts) {
        if !replay_available.contains(&equation) {
            replay_available.push(equation);
        }
    }
    let mut unfolds = replay.unfolded_predicates.clone();
    unfolds.retain(|name| predicate_environment.get(name).is_some());
    // A `calculate` whose surface proposition is the have's own goal takes
    // the *current* goal as its target (`prove_pure_proposition_case_at_point`
    // short-circuits the re-lowering when the spellings are identical), so it
    // discharges the witness-instantiated goal without needing a surface
    // spelling for it. Its premises are the ambient facts that have one.
    let mut derivation_premises = Vec::new();
    for fact in available {
        if let Ok(surface) = checked_surface_fact_at_outcome(
            replay,
            fact,
            SurfaceFactMatch::CanonicalExact,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        ) && !derivation_premises.contains(&surface)
        {
            derivation_premises.push(surface);
        }
    }
    let try_closer = |closer: ProofTactic| -> Result<TacticCertificate, String> {
        let mut tactics = unfolds
            .iter()
            .cloned()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(existence_tactics.iter().cloned());
        tactics.push(closer);
        let surface_have = ProofHave {
            proposition: surface_goal.clone(),
            proof: Proof::Script(tactics),
        };
        let surface_tactics =
            vec![ProofTactic::Have(surface_have.clone()), ProofTactic::Assumption];
        let certificate = TacticCertificate::from_proof_tactics(&surface_tactics)
            .map_err(|error| format!("produced an invalid certificate: {error:?}"))?;
        let replayed_goal = prove_have_at_point(
            &surface_have,
            theorem_environment,
            claim_label,
            tactic_index,
            &replay_available,
            parameters,
            arguments,
            pre_state,
            post_state,
            Some(result),
            &replay.program_point_states,
            Some(&replay.surface_propositions),
            predicate_environment,
            click_function_environment,
            function_requires,
            Some(path_index),
        )
        .map_err(|error| error.message().to_string())?;
        // `assumption` closes the claim by an exact match against the fact
        // the have just recorded, so the two must agree. The claim goal may
        // be spelled with `unfold(...)` active while the replay produces the
        // folded predicate; both name one proposition by the predicate's
        // definition.
        let replayed_matches = replayed_goal == *goal
            || (!unfolds.is_empty()
                && unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolds,
                    &replayed_goal,
                    &assumptions_from_propositions(&replay_available),
                )
                .as_ref()
                    == Ok(goal));
        if replayed_matches {
            Ok(certificate)
        } else {
            Err(format!(
                "proved a different proposition than the claim goal: {replayed_goal:?}"
            ))
        }
    };
    let mut last_error = None;
    for closer in [ProofTactic::Assumption, ProofTactic::Normalize] {
        match try_closer(closer) {
            Ok(certificate) => return Ok(certificate),
            Err(message) => last_error = Some(message),
        }
    }
    if !derivation_premises.is_empty() {
        let calculate = |premises: &[ClickProposition]| {
            ProofTactic::Calculate(ProofDerive {
                proposition: surface_goal.clone(),
                premises: premises.to_vec(),
            })
        };
        match try_closer(calculate(&derivation_premises)) {
            Ok(certificate) => {
                // Emit the premises the derivation actually needs rather
                // than every ambient fact: drop one at a time and keep the
                // reduction whenever replay still accepts it.
                let mut index = 0;
                while index < derivation_premises.len() {
                    let mut reduced = derivation_premises.clone();
                    reduced.remove(index);
                    if !reduced.is_empty() && try_closer(calculate(&reduced)).is_ok() {
                        derivation_premises = reduced;
                    } else {
                        index += 1;
                    }
                }
                return try_closer(calculate(&derivation_premises)).or(Ok(certificate));
            }
            Err(message) => last_error = Some(message),
        }
    }
    Err(ClickError::new(format!(
        "`{claim_label}` path {path_index}, tactic {tactic_index}: existential `simp` certificate failed replay: {}",
        last_error.unwrap_or_else(|| "no closer candidate applied".to_string())
    )))
}

struct GroupedOutcomeSimpGoal {
    claim_index: usize,
    claim_label: String,
    surface_goal: ClickProposition,
    goal: Proposition,
}

#[allow(clippy::too_many_arguments)]
fn certify_grouped_outcome_simp_transition(
    replay: &TacticReplayState,
    goals: Vec<GroupedOutcomeSimpGoal>,
    newly_closed_claim_count: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    proof_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<TacticCertificate, ClickError> {
    let mut replay = replay.clone();
    let mut available = available.to_vec();
    let mut pending = goals;
    let mut tactics = Vec::new();
    let mut last_errors = BTreeMap::new();

    while !pending.is_empty() {
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for goal in pending {
            match certify_outcome_simp_have(
                &replay,
                &goal.surface_goal,
                &goal.goal,
                &available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                function_requires,
                &goal.claim_label,
                tactic_index,
                path_index,
            ) {
                Ok(surface_haves) => {
                    replay
                        .surface_propositions
                        .record_lowering(&goal.surface_goal, &goal.goal)?;
                    available.push(goal.goal);
                    tactics.extend(surface_haves);
                    made_progress = true;
                }
                Err(error) => {
                    last_errors.insert(goal.claim_index, error.message().to_string());
                    next_pending.push(goal);
                }
            }
        }
        if !made_progress {
            let details = next_pending
                .iter()
                .map(|goal| {
                    format!(
                        "claim {} (`{}`): {}",
                        goal.claim_index,
                        goal.claim_label,
                        last_errors
                            .get(&goal.claim_index)
                            .map(String::as_str)
                            .unwrap_or("no certificate was produced")
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            return Err(ClickError::new(format!(
                "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped `simp` could not certify its complete claim transition\n{details}"
            )));
        }
        pending = next_pending;
    }

    tactics.extend(std::iter::repeat_n(
        ProofTactic::Assumption,
        newly_closed_claim_count,
    ));
    TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
        ClickError::new(format!(
            "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped `simp` produced an invalid transition certificate: {error:?}"
        ))
    })
}

#[allow(clippy::too_many_arguments)]
fn frame_certified_ensure_goals(
    claims: &[FunctionClaimRef<'_>],
    path_execution_facts: &[ExecutionPureFact],
    path_requirements: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Vec<(usize, Proposition)> {
    let mut reasoning_facts = path_requirements.to_vec();
    reasoning_facts.extend(
        path_execution_facts
            .iter()
            .filter(|fact| {
                matches!(
                    fact.proposition(),
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                )
            })
            .map(|fact| fact.proposition().clone()),
    );
    let assumptions = assumptions_from_propositions(&reasoning_facts);
    claims
        .iter()
        .enumerate()
        .filter_map(|(claim_index, claim)| {
            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                return None;
            };
            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
                return None;
            };
            let goal = lower_ensure_proposition_goal(
                path_requirements,
                surface_goal,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                program_point_states,
                unfolded_predicates,
            )
            .ok()?;
            plan_simp_certificate(&goal, &assumptions)
                .is_some()
                .then_some((claim_index, goal))
        })
        .collect()
}

fn comparison_program_point_variants(
    proposition: &ClickProposition,
    points: &[ProgramPointRef],
) -> Option<Vec<ClickProposition>> {
    if let ClickProposition::Not(body) = proposition {
        return Some(
            comparison_program_point_variants(body, points)?
                .into_iter()
                .map(|variant| ClickProposition::Not(Box::new(variant)))
                .collect(),
        );
    }
    if let ClickProposition::ForAll { c_type, name, body } = proposition {
        return Some(
            comparison_program_point_variants(body, points)?
                .into_iter()
                .map(|body| ClickProposition::ForAll {
                    c_type: c_type.clone(),
                    name: name.clone(),
                    body: Box::new(body),
                })
                .collect(),
        );
    }
    if let ClickProposition::Implies(left, right) = proposition {
        let mut variants = comparison_program_point_variants(right, points)?
            .into_iter()
            .map(|right| ClickProposition::Implies(left.clone(), Box::new(right)))
            .collect::<Vec<_>>();
        if let Some(left_variants) = comparison_program_point_variants(left, points) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::Implies(Box::new(left), right.clone())),
            );
        }
        return Some(variants);
    }
    if let ClickProposition::And(left, right) = proposition {
        let mut variants = Vec::new();
        if let Some(right_variants) = comparison_program_point_variants(right, points) {
            variants.extend(
                right_variants
                    .into_iter()
                    .map(|right| ClickProposition::And(left.clone(), Box::new(right))),
            );
        }
        if let Some(left_variants) = comparison_program_point_variants(left, points) {
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
    // uniformly, the way the recorded-spelling search in
    // `checked_surface_fact_at_point` already does. Wrapping a value argument
    // is harmless: it evaluates to the same value at every point it is
    // spellable at, and a wrapping that does not lower is discarded by the
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
        for point in points.iter().rev() {
            let candidate = call(&|argument| ContractExpression::At {
                selector: VisitSelector::ProgramPoint(point.clone()),
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
    let at_point =
        |expression: &ContractExpression, point: &ProgramPointRef| ContractExpression::At {
            selector: VisitSelector::ProgramPoint(point.clone()),
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
    let point_pairs = points
        .iter()
        .rev()
        .map(|point| (at_point(left, point), at_point(right, point)))
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
    for (point_left, point_right) in &point_pairs {
        push(point_left.clone(), right.clone());
        push(left.clone(), point_right.clone());
        push(point_left.clone(), point_right.clone());
    }

    let mut left_variants = vec![left.clone()];
    let mut right_variants = vec![right.clone()];
    if let Some(old_left) = old_left {
        left_variants.push(old_left);
    }
    if let Some(old_right) = old_right {
        right_variants.push(old_right);
    }
    for (point_left, point_right) in point_pairs {
        left_variants.push(point_left);
        right_variants.push(point_right);
    }
    for left in left_variants {
        for right in &right_variants {
            push(left.clone(), right.clone());
        }
    }
    Some(variants)
}

#[allow(clippy::too_many_arguments)]
fn lower_surface_candidate_at_point(
    replay: &TacticReplayState,
    candidate: &ClickProposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let values = parameter_values(parameters, arguments)?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (mut values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let assumptions = assumptions_from_propositions(available).allow_symbolic_contract_loads();
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        replay.old_reference_state(state),
        state,
        None,
        &assumptions,
        candidate,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &replay.program_point_states,
        &mut active_functions,
    )
    .map_err(ClickError::new)
}

#[allow(clippy::too_many_arguments)]
fn record_surface_replay_tactic(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    tactic: &ProofTactic,
    statement_uses_memory_context: Option<bool>,
) {
    if replay.surface_replay.blocker.is_some() {
        return;
    }
    match tactic {
        ProofTactic::CertifiedStatementReplay(evidence) => {
            record_surface_replay_tactic(
                replay,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                &ProofTactic::CertifiedStatementStep {
                    prerequisite_derivations: evidence.transition.prerequisite_derivations.clone(),
                    // Planning reasons from the whole ambient context, so a
                    // condition it consulted leaves no trace in the transition
                    // and cannot be recovered from it afterwards. A statement
                    // whose execution can consult conditions therefore carries
                    // them all; one that only moves a variable or a constant,
                    // in a context that cannot turn a condition into a memory
                    // conclusion, carries none.
                    exact_premises: evidence
                        .transition
                        .consults_conditions
                        .then(|| ambient_condition_facts(available))
                        .unwrap_or_default(),
                },
                None,
            );
            let post_state = match &evidence.transition.outcome {
                CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
                    Some(state)
                }
                CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => {
                    None
                }
            };
            for transport in &evidence.transition.fact_transports {
                if !transport.statement_local
                    || !is_internal_snapshot_frame_witness(&transport.source)
                {
                    continue;
                }
                let surface = replay
                    .surface_propositions
                    .surface(&transport.target)
                    .ok()
                    .cloned()
                    .or_else(|| {
                        post_state.and_then(|state| {
                            synthesize_surface_proposition(
                                &transport.target,
                                parameters,
                                arguments,
                                state,
                            )
                        })
                    });
                let Some(surface) = surface else {
                    replay.surface_replay.block(format!(
                        "statement-local frame witness has no checked Click spelling: {:?}",
                        transport.target
                    ));
                    continue;
                };
                replay.surface_replay.push(ProofTactic::Have(ProofHave {
                    proposition: surface,
                    proof: Proof::Script(vec![ProofTactic::Normalize]),
                }));
            }
        }
        ProofTactic::CertifiedLoopSummaryReplay(evidence) => {
            let exact_premises = theorem_implication_premises(&evidence.transition.theorem)
                .into_iter()
                .filter(|premise| {
                    !evidence
                        .transition
                        .execution_facts
                        .iter()
                        .any(|fact| fact.is_certified() && fact.proposition() == premise)
                })
                .collect();
            record_surface_replay_tactic(
                replay,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                &ProofTactic::CertifiedLoopSummaryStep {
                    prerequisite_derivations: evidence.transition.prerequisite_derivations.clone(),
                    exact_premises,
                },
                statement_uses_memory_context,
            );
        }
        ProofTactic::CertifiedStatementStep {
            prerequisite_derivations: derivations,
            exact_premises,
        } => {
            replay.surface_replay.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            });
            let premises = Ok::<_, ClickError>({
                let mut premises = Vec::new();
                let derivation_context = derivations
                    .iter()
                    .flat_map(PropositionDerivation::context_premises)
                    .collect::<BTreeSet<_>>();
                let explicit_dependency_facts = derivation_context
                    .iter()
                    .map(|fact| (*fact).clone())
                    .chain(exact_premises.iter().cloned())
                    .collect::<Vec<_>>();
                let projected_resource_facts = state.resources().observable_facts_assuming_valid(
                    &assumptions_from_propositions(&explicit_dependency_facts),
                );
                // Preserve exactly the facts selected by prerequisite
                // derivations or explicitly tracked by the transition.
                // Resource/loadability facts are projected deterministically
                // from the current resource state after these premises are
                // installed.
                //
                // Do not copy every implication premise from the execution
                // theorem: it contains the transitive ambient context,
                // including internal call identities and verifier variables.
                // Ordinary replay below remains the authority on whether this
                // explicit, source-expressible subset is sufficient.
                let mut available_conjuncts = Vec::new();
                for fact in available {
                    atomic_conjuncts(fact, &mut available_conjuncts);
                }
                // Source-spelled memory-range separation facts (for example
                // a resource body's canonical
                // `separate(memory(object(owner)), ...)` aggregate) that can
                // re-fold a decomposed per-field separation back to its
                // declared spelling below. Entailment assumptions are built
                // lazily, at most once per candidate.
                let memory_separation_bases = |fact: &Proposition| {
                    let Proposition::CResourceSeparate { left, right } = fact else {
                        return None;
                    };
                    let (CResource::Memory(left), CResource::Memory(right)) = (left, right) else {
                        return None;
                    };
                    Some((left.base().clone(), right.base().clone()))
                };
                let mut spelled_separations = available_conjuncts
                    .iter()
                    .copied()
                    .filter_map(|candidate| {
                        let bases = memory_separation_bases(candidate)?;
                        replay
                            .surface_propositions
                            .surfaces(candidate)
                            .next()
                            .is_some()
                            .then_some((candidate, bases, None::<Assumptions>))
                    })
                    .collect::<Vec<_>>();
                for fact in &available_conjuncts {
                    let fact = *fact;
                    let selected_by_derivation = derivation_context.iter().any(|required| {
                        (*required).eq(fact)
                            || normalize_direct_atomic_memory_loads(required)
                                == normalize_direct_atomic_memory_loads(fact)
                    }) || exact_premises.iter().any(|required| {
                        required == fact
                            || normalize_direct_atomic_memory_loads(required)
                                == normalize_direct_atomic_memory_loads(fact)
                    });
                    // A permission the resource projection reproduces is
                    // reconstructed by the replay for itself. One it does not
                    // reproduce is only available because the ambient context
                    // carried it, so the certificate has to spell it.
                    let non_reconstructible_permission = matches!(
                        fact,
                        Proposition::CMemoryDisjoint { .. }
                            | Proposition::CResourceSeparate { .. }
                            | Proposition::CMemoryLoadable { .. }
                    ) && !exact_fact_is_available(fact, &projected_resource_facts);
                    if !selected_by_derivation && !non_reconstructible_permission {
                        continue;
                    }
                    // A separation carried only as an ambient permission may
                    // be one piece of a source-spelled aggregate (`unfold`
                    // decomposes `separate(memory(object(owner)), ...)` into
                    // per-field separations). Re-fold it: emit the strictly
                    // stronger declared fact, whose canonical spelling the
                    // replay derives the per-field pieces from, instead of
                    // the decomposed piece.
                    let fact = 'fold: {
                        let fact_bases = if selected_by_derivation {
                            None
                        } else {
                            memory_separation_bases(fact)
                        };
                        let Some((fact_left, fact_right)) = fact_bases else {
                            break 'fold fact;
                        };
                        let mut fact_is_foldable = None;
                        for (candidate, (left, right), cached) in &mut spelled_separations {
                            if *candidate == fact
                                || !(*left == fact_left && *right == fact_right
                                    || *left == fact_right && *right == fact_left)
                            {
                                continue;
                            }
                            // An arithmetically true separation (same base,
                            // disjoint constant ranges) is derivable from
                            // any premise set, so entailment cannot pick a
                            // fold target for it; keep its own spelling.
                            let foldable = *fact_is_foldable.get_or_insert_with(|| {
                                assumptions_from_propositions(&[])
                                    .derive_atomic_proposition(fact)
                                    .is_none()
                            });
                            if !foldable {
                                break;
                            }
                            let assumptions = cached.get_or_insert_with(|| {
                                assumptions_from_propositions(std::slice::from_ref(*candidate))
                            });
                            if assumptions.derive_atomic_proposition(fact).is_some()
                                && assumptions_from_propositions(std::slice::from_ref(fact))
                                    .derive_atomic_proposition(candidate)
                                    .is_none()
                            {
                                break 'fold *candidate;
                            }
                        }
                        fact
                    };
                    // A certified statement prerequisite may be represented by
                    // a source fact whose lowering differs only by canonical
                    // load materialization. Keep that checked equivalence here:
                    // the generated `step using` certificate is subsequently
                    // replayed by the ordinary executor, which remains the
                    // authority on whether the selected premise is sufficient.
                    let Ok(surface) = checked_surface_comparison_fact_at_point(
                        replay,
                        fact,
                        SurfaceFactMatch::ReplayEquivalent,
                        available,
                        parameters,
                        arguments,
                        state,
                        predicate_environment,
                        click_function_environment,
                    ) else {
                        continue;
                    };
                    if !premises.contains(&surface) {
                        premises.push(surface);
                    }
                }
                premises
            });
            match premises {
                Ok(premises) if premises.is_empty() => {
                    replay.surface_replay.push(ProofTactic::Step)
                }
                Ok(premises) => replay.surface_replay.push(ProofTactic::StepUsing(premises)),
                Err(error) => replay.surface_replay.block(format!(
                    "could not express a statement-step premise at the current proof point: {}",
                    error.message()
                )),
            }
        }
        ProofTactic::CertifiedLoopSummaryStep {
            prerequisite_derivations: derivations,
            exact_premises,
        } => {
            let loop_index = replay
                .source_layout
                .statement(replay.frontier.next_statement_index)
                .and_then(|region| match region.kind {
                    SourceStatementKind::Loop { loop_index } => Some(loop_index),
                    SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                });
            let Some(loop_index) = loop_index else {
                replay
                    .surface_replay
                    .block("certified loop-summary replay is not at a source loop entry");
                return;
            };
            replay.surface_replay.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            });
            let mut surface_available = available.to_vec();
            let mut loop_summary_premises: Vec<(Proposition, ClickProposition)> = Vec::new();
            if let Some(loop_clause) = function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            {
                let mut unfold_names = Vec::new();
                for proof in [loop_clause.initialize_proof(), loop_clause.preserve_proof()]
                    .into_iter()
                    .flatten()
                {
                    for tactic in proof.tactics().unwrap_or_default() {
                        if let ProofTactic::UnfoldPredicate(name) = tactic
                            && !unfold_names.contains(name)
                        {
                            unfold_names.push(name.clone());
                        }
                    }
                }
                for name in unfold_names {
                    let assumptions = assumptions_from_propositions(&surface_available);
                    let surface_unfoldings = surface_available
                        .iter()
                        .flat_map(|kernel| {
                            let Proposition::Predicate {
                                name: kernel_name, ..
                            } = kernel
                            else {
                                return Vec::new();
                            };
                            if kernel_name != &name {
                                return Vec::new();
                            }
                            let Some(unfolded) = unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                std::slice::from_ref(&name),
                                kernel,
                                &assumptions,
                            )
                            .ok() else {
                                return Vec::new();
                            };
                            replay
                                .surface_propositions
                                .surfaces(kernel)
                                .filter_map(|surface| {
                                    let ClickProposition::PredicateCall {
                                        name: surface_name,
                                        arguments: surface_arguments,
                                    } = surface
                                    else {
                                        return None;
                                    };
                                    let source_point = predicate_call_source_site(surface);
                                    let definition = predicate_environment.get(surface_name)?;
                                    let mut surface = instantiate_click_predicate_definition(
                                        definition,
                                        surface_arguments,
                                    )
                                    .ok()?;
                                    if let Some(point) = source_point {
                                        surface =
                                            surface_with_source_site(&surface, &point).ok()?;
                                    }
                                    Some((surface, unfolded.clone()))
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    match unfold_available_predicate_facts(
                        predicate_environment,
                        click_function_environment,
                        std::slice::from_ref(&name),
                        &surface_available,
                    ) {
                        Ok(unfolded) => surface_available = unfolded,
                        Err(_) => continue,
                    }
                    for (surface, kernel) in surface_unfoldings {
                        if replay
                            .surface_propositions
                            .record_lowering(&surface, &kernel)
                            .is_err()
                        {
                            continue;
                        }
                    }
                    replay
                        .surface_replay
                        .push(ProofTactic::UnfoldPredicate(name));
                }
                let current_loadable_haves = surface_available
                    .iter()
                    .filter_map(|kernel| {
                        if !matches!(kernel, Proposition::CMemoryLoadable { .. }) {
                            return None;
                        }
                        let ClickProposition::Loadable { segment } =
                            replay.surface_propositions.surface(kernel).ok()?
                        else {
                            return None;
                        };
                        let mut current_segment = segment.clone();
                        current_segment.state = ContractSegmentState::Current;
                        Some(ProofHave {
                            proposition: ClickProposition::Loadable {
                                segment: current_segment,
                            },
                            proof: Proof::Tactic(SmartTactic::Simp),
                        })
                    })
                    .collect::<Vec<_>>();
                for have in current_loadable_haves {
                    let Ok((fact, plan)) = plan_smart_have_at_current_point(
                        &have,
                        "surface loop-summary certificate",
                        0,
                        &surface_available,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &[],
                        None,
                    ) else {
                        continue;
                    };
                    if replay
                        .surface_propositions
                        .record_lowering(&have.proposition, &fact)
                        .is_err()
                    {
                        continue;
                    }
                    if !loop_summary_premises
                        .iter()
                        .any(|(kernel, _)| kernel == &fact)
                    {
                        loop_summary_premises.push((fact.clone(), have.proposition.clone()));
                    }
                    if surface_available.contains(&fact) {
                        continue;
                    }
                    match surface_smart_have_certificate(
                        replay,
                        state,
                        &surface_available,
                        parameters,
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        &have,
                        &plan,
                        &[],
                    ) {
                        Ok(certificate) => replay
                            .surface_replay
                            .tactics
                            .extend_from_slice(certificate.tactics()),
                        Err(error) => replay.surface_replay.block(error.message()),
                    }
                    surface_available.push(fact);
                }
                fn append_surface_conjuncts(
                    proposition: &ClickProposition,
                    conjuncts: &mut Vec<ClickProposition>,
                ) {
                    if let ClickProposition::And(left, right) = proposition {
                        append_surface_conjuncts(left, conjuncts);
                        append_surface_conjuncts(right, conjuncts);
                    } else {
                        conjuncts.push(proposition.clone());
                    }
                }
                let mut invariants = Vec::new();
                for invariant in loop_clause
                    .items()
                    .iter()
                    .filter(|item| item.kind() == StructuralItemKind::Invariant)
                    .filter_map(StructuralItem::proposition)
                {
                    append_surface_conjuncts(invariant, &mut invariants);
                }
                for invariant in invariants {
                    let have = ProofHave {
                        proposition: invariant,
                        proof: Proof::Tactic(SmartTactic::Simp),
                    };
                    let planned = plan_smart_have_at_current_point(
                        &have,
                        "surface loop-summary certificate",
                        0,
                        &surface_available,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &[],
                        None,
                    );
                    let (fact, plan) = match planned {
                        Ok(planned) => planned,
                        Err(_) => continue,
                    };
                    if !loop_summary_premises
                        .iter()
                        .any(|(kernel, _)| kernel == &fact)
                    {
                        loop_summary_premises.push((fact.clone(), have.proposition.clone()));
                    }
                    if !surface_available.contains(&fact) {
                        if let Err(error) = replay
                            .surface_propositions
                            .record_lowering(&have.proposition, &fact)
                        {
                            replay.surface_replay.block(format!(
                                "could not record a loop invariant for its surface certificate: {}",
                                error.message()
                            ));
                            return;
                        }
                        match surface_smart_have_certificate(
                            replay,
                            state,
                            &surface_available,
                            parameters,
                            arguments,
                            predicate_environment,
                            click_function_environment,
                            &have,
                            &plan,
                            &[],
                        ) {
                            Ok(certificate) => replay
                                .surface_replay
                                .tactics
                                .extend_from_slice(certificate.tactics()),
                            Err(error) => replay.surface_replay.block(error.message()),
                        }
                        surface_available.push(fact);
                    }
                }
            }
            for derivation in derivations {
                if surface_available.contains(derivation.conclusion()) {
                    continue;
                }
                match lower_surface_atomic_derivation(
                    replay,
                    derivation,
                    None,
                    &surface_available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                ) {
                    Ok((conclusion, proof)) => {
                        replay.surface_replay.push(ProofTactic::Have(ProofHave {
                            proposition: conclusion,
                            proof,
                        }));
                        surface_available.push(derivation.conclusion().clone());
                    }
                    Err(_) => {}
                }
            }
            let needed = exact_premises
                .iter()
                .cloned()
                .chain(
                    loop_summary_premises
                        .iter()
                        .map(|(kernel, _)| kernel.clone()),
                )
                .chain(
                    derivations
                        .iter()
                        .flat_map(PropositionDerivation::context_premises),
                )
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let contextual_step = |replay: &TacticReplayState, needed: &[Proposition]| {
                let normalized_needed = needed
                    .iter()
                    .map(|fact| {
                        (
                            fact,
                            normalize_proposition(fact),
                            normalize_direct_atomic_memory_loads(fact),
                        )
                    })
                    .collect::<Vec<_>>();
                let mut premises = Vec::new();
                for (fact, normalized, materialized) in normalized_needed {
                    let candidates = surface_available.iter().filter(|available| {
                        *available == fact
                            || normalize_proposition(available) == normalized
                            || normalize_direct_atomic_memory_loads(available) == materialized
                            || assumptions_from_propositions(std::slice::from_ref(*available))
                                .proves(fact)
                    });
                    if let Some(surface) = candidates
                        .filter_map(|available_fact| {
                            checked_surface_comparison_fact_at_point(
                                replay,
                                available_fact,
                                SurfaceFactMatch::CanonicalExact,
                                &surface_available,
                                parameters,
                                arguments,
                                state,
                                predicate_environment,
                                click_function_environment,
                            )
                            .ok()
                        })
                        .next()
                        && !premises.contains(&surface)
                    {
                        premises.push(surface);
                    }
                }
                Ok::<_, ClickError>(premises)
            };
            let premises = contextual_step(replay, &needed).map(|mut premises| {
                for (_, surface) in &loop_summary_premises {
                    if !premises.contains(surface) {
                        premises.push(surface.clone());
                    }
                }
                premises
            });
            match premises {
                Ok(premises) if premises.is_empty() => {
                    replay
                        .surface_replay
                        .push(ProofTactic::ApplyLoopSummary(CodeRegionRef::Loop(
                            loop_index,
                        )))
                }
                Ok(premises) => replay
                    .surface_replay
                    .push(ProofTactic::ApplyLoopSummaryUsing {
                        region: CodeRegionRef::Loop(loop_index),
                        premises,
                    }),
                Err(error) => replay.surface_replay.block(format!(
                    "could not express a loop-summary premise at the current proof point: {}",
                    error.message()
                )),
            }
        }
        ProofTactic::CertifiedFactTransport { source, target, .. } => {
            let Some(step_entry) = replay.surface_replay.last_step_entry.clone() else {
                replay
                    .surface_replay
                    .block("fact transport has no preceding statement-entry snapshot");
                return;
            };
            let transport_assumptions = assumptions_from_propositions(available);
            let mut base_surfaces = Vec::new();
            for proposition in [source, target] {
                for surface in replay.surface_propositions.surfaces(proposition) {
                    if !base_surfaces.contains(surface) {
                        base_surfaces.push(surface.clone());
                    }
                }
                if let Some(surface) =
                    synthesize_surface_proposition(proposition, parameters, arguments, state)
                    && !base_surfaces.contains(&surface)
                {
                    base_surfaces.push(surface);
                }
                let normalized = normalize_direct_atomic_memory_loads(proposition);
                for recorded in replay.surface_propositions.kernel_facts() {
    let matches = normalize_direct_atomic_memory_loads(recorded) == normalized
                        || (memory_erased_comparison(recorded).is_some()
                            && memory_erased_comparison(recorded)
                                == memory_erased_comparison(proposition)
                            && proposition_outer_load_memory(proposition).is_some_and(|after| {
                                certified_fact_transport_reaches_through(
                                    recorded,
                                    proposition,
                                    after,
                                    &transport_assumptions,
                                    &replay.effect_facts,
                                )
                            }));
                    if !matches {
                        continue;
                    }
                    for surface in replay.surface_propositions.surfaces(recorded) {
                        if !base_surfaces.contains(surface) {
                            base_surfaces.push(surface.clone());
                        }
                    }
                }
            }
            if base_surfaces.is_empty() {
                replay.surface_replay.block(format!(
                    "fact transport has no recorded or synthesized Click comparison spelling\n  source: {source:?}\n  target: {target:?}"
                ));
                return;
            }
            let mut points = replay
                .program_point_states
                .keys()
                .cloned()
                .collect::<Vec<_>>();
            if !points.contains(&step_entry) {
                points.push(step_entry);
            }
            let mut candidates = Vec::new();
            for base_surface in base_surfaces {
                let Some(variants) = comparison_program_point_variants(&base_surface, &points)
                else {
                    replay.surface_replay.block(
                        "fact transport surface lowering currently supports comparisons only",
                    );
                    return;
                };
                for candidate in variants {
                    if !candidates.contains(&candidate) {
                        candidates.push(candidate);
                    }
                }
            }
            let find_candidate = |expected: &Proposition| {
                let normalized_expected = normalize_direct_atomic_memory_loads(expected);
                let lower = |candidate: &ClickProposition| {
                    lower_surface_candidate_at_point(
                        replay,
                        candidate,
                        available,
                        parameters,
                        arguments,
                        state,
                        predicate_environment,
                        click_function_environment,
                    )
                    .ok()
                };
                candidates.iter().find_map(|candidate| {
                    let actual = lower(candidate)?;
                    if normalize_direct_atomic_memory_loads(&actual) == normalized_expected {
                        return Some((candidate.clone(), actual));
                    }
                    // The certified pair may sit at a snapshot no recorded
                    // point reproduces syntactically; accept a candidate
                    // whose lowering provably transports to the certified
                    // spelling.
                    if memory_erased_comparison(&actual).is_some()
                        && memory_erased_comparison(&actual)
                            == memory_erased_comparison(expected)
                        && let Some(after) = proposition_outer_load_memory(expected)
                        && certified_fact_transport_reaches_through(
                            &actual,
                            expected,
                            after,
                            &transport_assumptions,
                            &replay.effect_facts,
                        )
                    {
                        return Some((candidate.clone(), actual));
                    }
                    None
                })
            };
            let selected_by_preceding_step = replay
                .surface_replay
                .tactics
                .iter()
                .rev()
                .find_map(|tactic| match tactic {
                    ProofTactic::StepUsing(premises)
                    | ProofTactic::ApplyLoopSummaryUsing { premises, .. } => Some(Some(premises)),
                    ProofTactic::Step | ProofTactic::ApplyLoopSummary(_) => Some(None),
                    _ => None,
                })
                .flatten()
                .is_some_and(|premises| {
                    premises.iter().any(|premise| {
                        replay
                            .surface_propositions
                            .surfaces(source)
                            .any(|surface| surface == premise)
                    })
                });
            match (find_candidate(source), find_candidate(target)) {
                (
                    Some((_surface_source, _)),
                    Some((surface_target, lowered_surface_target)),
                ) if selected_by_preceding_step => {
                    // `step using` replays with Selected fact transport, so a
                    // listed statement-entry source is already carried by the
                    // certified statement transition. Do not ask the
                    // post-state context to independently reconstruct the
                    // same frame proof.
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_target, &lowered_surface_target)
                    {
                        replay.surface_replay.block(format!(
                            "could not retain the certified fact transport target spelling: {}",
                            error.message()
                        ));
                    }
                }
                (
                    Some((surface_source, _)),
                    Some((surface_target, lowered_surface_target)),
                )
                    if surface_source == surface_target =>
                {
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_target, &lowered_surface_target)
                    {
                        replay.surface_replay.block(format!(
                            "could not retain the certified fact transport target spelling: {}",
                            error.message()
                        ));
                    }
                    return;
                }
                (
                    Some((surface_source, lowered_surface_source)),
                    Some((surface_target, lowered_surface_target)),
                ) => {
                    let transition_facts =
                        fact_transport_transition_facts(&replay.effect_facts, &lowered_surface_source);
                    match plan_explicit_fact_transport(
                        &surface_source,
                        &lowered_surface_source,
                        &lowered_surface_target,
                        available,
                        &transition_facts,
                        parameters,
                        arguments,
                        replay,
                        state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.surface_replay.push(ProofTactic::TransportUsing {
                                source: surface_source,
                                target: surface_target.clone(),
                                premises,
                            });
                            if let Err(error) = replay
                                .surface_propositions
                                .record_lowering(&surface_target, &lowered_surface_target)
                            {
                                replay.surface_replay.block(format!(
                                    "could not retain the certified fact transport target spelling: {}",
                                    error.message()
                                ));
                            }
                        }
                        Err(error) => replay.surface_replay.block(format!(
                            "could not make fact transport premises explicit: {}",
                            error.message()
                        )),
                    }
                }
                _ => replay.surface_replay.block(format!(
                    "no placement of the comparison operands at the {} recorded program points lowered to the certified fact transport\n  certified source: {source:?}\n  certified target: {target:?}",
                    points.len()
                )),
            }
        }
        ProofTactic::FinishCertifiedFactTransports(_) => {}
        ProofTactic::CertifiedPathAssumption {
            occurrence,
            condition,
            value,
            facts,
            ..
        } => {
            let surface_fact = if *value {
                condition.clone()
            } else {
                ClickProposition::Not(Box::new(condition.clone()))
            };
            let lowered = lower_surface_candidate_at_point(
                replay,
                &surface_fact,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            );
            match lowered {
                Ok(kernel_fact) if facts.contains(&kernel_fact) => {
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_fact, &kernel_fact)
                    {
                        replay.surface_replay.block(format!(
                            "could not retain the certified path-condition spelling: {}",
                            error.message()
                        ));
                        return;
                    }
                }
                Ok(kernel_fact) => {
                    replay.surface_replay.block(format!(
                        "surface branch condition did not lower to a certified path fact\n  lowered: {kernel_fact:?}\n  certified facts: {facts:?}"
                    ));
                    return;
                }
                Err(error) => {
                    replay.surface_replay.block(format!(
                        "could not lower the certified path condition: {}",
                        error.message()
                    ));
                    return;
                }
            }
            replay.surface_replay.path_choices.push(SurfacePathChoice {
                occurrence: *occurrence,
                condition: condition.clone(),
                value: *value,
                tactic_offset: replay.surface_replay.tactics.len(),
            });
        }
        ProofTactic::CertifiedAlternatives(_) => {}
        ProofTactic::Have(have) => {
            match TacticCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                Ok(_) => replay.surface_replay.push(tactic.clone()),
                Err(_)
                    if smart_simp_unfold_prefix(&have.proof).is_some()
                        || have_proof_contains_smart_apply(&have.proof) =>
                {
                    // The successful smart proof is lowered after it has
                    // produced its checked kernel fact.
                }
                Err(error) => replay
                    .surface_replay
                    .block(format!("could not lower control-flow tactic: {error:?}")),
            }
        }
        ProofTactic::ExactPropositionDerivation(derivation) => {
            match lower_surface_atomic_derivation(
                replay,
                derivation,
                None,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            ) {
                Ok((conclusion, proof)) => {
                    replay.surface_replay.push(ProofTactic::Have(ProofHave {
                        proposition: conclusion,
                        proof,
                    }));
                }
                Err(error) => replay.surface_replay.block(format!(
                    "could not lower exact proposition derivation: {}",
                    error.message()
                )),
            }
        }
        ProofTactic::CertifiedFrame(path_derivations) => {
            let lowered = path_derivations
                .iter()
                .map(|derivations| {
                    let mut tactics = Vec::new();
                    for derivation in derivations {
                        let (conclusion, proof) = lower_surface_atomic_derivation(
                            replay,
                            derivation,
                            None,
                            available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        )?;
                        tactics.push(ProofTactic::Have(ProofHave {
                            proposition: conclusion,
                            proof,
                        }));
                    }
                    tactics.push(ProofTactic::Frame(None));
                    Ok::<_, ClickError>(tactics)
                })
                .collect::<Result<Vec<_>, _>>();
            match lowered {
                Ok(path_tactics) => {
                    if let Err(message) = append_surface_tactics_by_leaf(
                        &mut replay.surface_replay.tactics,
                        &path_tactics,
                    ) {
                        replay.surface_replay.block(message);
                    }
                }
                Err(error) => replay.surface_replay.block(format!(
                    "could not lower contextual frame certificate: {}",
                    error.message()
                )),
            }
        }
        _ => match tactic.class() {
            TacticClass::Simple(simple) if simple.is_surface_expressible() => {
                replay.surface_replay.push(tactic.clone())
            }
            TacticClass::ControlFlow(_) => {
                match TacticCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                    Ok(_) => replay.surface_replay.push(tactic.clone()),
                    Err(error) => replay
                        .surface_replay
                        .block(format!("could not lower control-flow tactic: {error:?}")),
                }
            }
            TacticClass::Smart(_) | TacticClass::Simple(_) => {}
        },
    }
}

fn have_proof_is_smart_simp(proof: &Proof) -> bool {
    match proof {
        Proof::Default | Proof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        Proof::Script(tactics) => matches!(tactics.as_slice(), [ProofTactic::Simp]),
        Proof::Tactic(SmartTactic::Frame) => false,
    }
}

fn smart_simp_unfold_prefix(proof: &Proof) -> Option<Vec<String>> {
    if have_proof_is_smart_simp(proof) {
        return Some(Vec::new());
    }
    let Proof::Script(tactics) = proof else {
        return None;
    };
    let (last, prefix) = tactics.split_last()?;
    if !matches!(last, ProofTactic::Simp) {
        return None;
    }
    prefix
        .iter()
        .map(|tactic| match tactic {
            ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// Replace the trailing smart `simp` of a post-execution `have` script whose
/// prefix is already certificate-expressible with a simple closer.
///
/// This covers the shapes the `[unfold*, simp]` lowering misses — notably a
/// `witness`/`choose` prefix, which is how an existential `have` is written.
/// The candidate script is accepted only when `prove_have_at_point` (the
/// replay judgment) proves it AND yields exactly the fact the smart script
/// established, so this emits only what replay accepts.
#[allow(clippy::too_many_arguments)]
fn lower_smart_simp_suffix_have(
    have: &ProofHave,
    fact: &Proposition,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_requires: &[Requirement],
    path_index: usize,
) -> Option<ProofHave> {
    let Proof::Script(tactics) = &have.proof else {
        return None;
    };
    let (last, prefix) = tactics.split_last()?;
    if !matches!(last, ProofTactic::Simp) {
        return None;
    }
    for closer in [ProofTactic::Assumption, ProofTactic::Normalize] {
        let mut candidate_tactics = prefix.to_vec();
        candidate_tactics.push(closer);
        let candidate = ProofHave {
            proposition: have.proposition.clone(),
            proof: Proof::Script(candidate_tactics),
        };
        if TacticCertificate::from_proof_tactics(std::slice::from_ref(&ProofTactic::Have(
            candidate.clone(),
        )))
        .is_err()
        {
            continue;
        }
        let replayed = prove_have_at_point(
            &candidate,
            theorem_environment,
            claim_label,
            tactic_index,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            Some(result),
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            function_requires,
            Some(path_index),
        );
        if replayed.is_ok_and(|replayed| replayed == *fact) {
            return Some(candidate);
        }
    }
    None
}

fn have_proof_contains_smart_apply(proof: &Proof) -> bool {
    let Proof::Script(tactics) = proof else {
        return false;
    };
    tactics
        .iter()
        .any(|tactic| matches!(tactic, ProofTactic::ApplyTheorem(_)))
}

#[allow(clippy::too_many_arguments)]
fn surface_simp_plan_proof(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    surface_goal: &ClickProposition,
    plan: &ProofReplayPlan,
    unfolded_predicates: &[String],
) -> Result<Proof, ClickError> {
    let active_surface_goal = if unfolded_predicates.is_empty() {
        surface_goal.clone()
    } else {
        unfold_structural_invariant_proposition(
            predicate_environment,
            surface_goal,
            unfolded_predicates,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "could not express the smart proof goal after predicate unfolding: {message}"
            ))
        })?
    };
    let proof = match plan.tactics() {
        [ProofTactic::Assumption] => Proof::Script(vec![ProofTactic::Assumption]),
        [ProofTactic::Normalize] => Proof::Script(vec![ProofTactic::Normalize]),
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
            let (_, proof) = lower_surface_atomic_derivation(
                replay,
                derivation,
                Some(&active_surface_goal),
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "could not lower the planned smart proof certificate: {}",
                    error.message()
                ))
            })?;
            proof
        }
        _ => {
            return Err(ClickError::new(
                "smart proof planned an unexpected simp certificate",
            ));
        }
    };
    if unfolded_predicates.is_empty() {
        return Ok(proof);
    }
    let mut tactics = unfolded_predicates
        .iter()
        .cloned()
        .map(ProofTactic::UnfoldPredicate)
        .collect::<Vec<_>>();
    let Proof::Script(suffix) = proof else {
        return Err(ClickError::new(
            "planned smart proof certificate was not a tactic script",
        ));
    };
    tactics.extend(suffix);
    Ok(Proof::Script(tactics))
}

#[allow(clippy::too_many_arguments)]
fn surface_smart_have_certificate(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
    plan: &ProofReplayPlan,
    unfolded_predicates: &[String],
) -> Result<TacticCertificate, ClickError> {
    let proof = surface_simp_plan_proof(
        replay,
        state,
        available,
        parameters,
        arguments,
        predicate_environment,
        click_function_environment,
        &have.proposition,
        plan,
        unfolded_predicates,
    )?;
    let tactic = ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof,
    });
    TacticCertificate::from_proof_tactics(&[tactic]).map_err(|error| {
        ClickError::new(format!(
            "smart `have` produced an invalid certificate: {error:?}"
        ))
    })
}

#[allow(clippy::too_many_arguments)]
fn surface_smart_apply_have_certificate(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
    have: &ProofHave,
    goal: &Proposition,
) -> Result<Option<TacticCertificate>, ClickError> {
    if !have_proof_contains_smart_apply(&have.proof) {
        return Ok(None);
    }
    let Proof::Script(tactics) = &have.proof else {
        unreachable!("smart apply is represented by a proof script")
    };
    let mut planning_replay = replay.clone();
    let mut planning_available = available.to_vec();
    let mut surface_tactics = Vec::with_capacity(tactics.len());
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(name) => {
                planning_available = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &planning_available,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not plan smart `apply` after `unfold`: {message}"
                    ))
                })?;
                if !planning_replay.unfolded_predicates.contains(name) {
                    planning_replay.unfolded_predicates.push(name.clone());
                }
                surface_tactics.push(tactic.clone());
            }
            ProofTactic::ApplyTheorem(application) => {
                let premises = plan_explicit_theorem_application(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    &planning_available,
                    parameters,
                    arguments,
                    &planning_replay,
                    state,
                    predicate_environment,
                    click_function_environment,
                )?;
                planning_available = apply_theorem_at_current_point(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    planning_available,
                    parameters,
                    arguments,
                    planning_replay.old_reference_state(state),
                    state,
                    &planning_replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                    &planning_replay.unfolded_predicates,
                    None,
                )?;
                surface_tactics.push(ProofTactic::ApplyTheoremUsing {
                    application: application.clone(),
                    premises,
                });
            }
            ProofTactic::Simp => {
                let assumptions = assumptions_from_propositions(&planning_available);
                let plan = plan_simp_certificate(goal, &assumptions).ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not plan the `simp` suffix after smart `apply`"
                    ))
                })?;
                let Proof::Script(lowered) = surface_simp_plan_proof(
                    &mut planning_replay,
                    state,
                    &planning_available,
                    parameters,
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    &have.proposition,
                    &plan,
                    &[],
                )?
                else {
                    unreachable!("surface simp lowering always returns a script")
                };
                surface_tactics.extend(lowered);
            }
            _ => surface_tactics.push(tactic.clone()),
        }
    }
    let tactic = ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof: Proof::Script(surface_tactics),
    });
    let certificate = TacticCertificate::from_proof_tactics(&[tactic]).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart `apply` inside `have` produced an invalid certificate: {error:?}"
        ))
    })?;
    Ok(Some(certificate))
}

/// Track, in the certificate-generation fact set, the facts a recorded
/// post-execution surface tactic just added to the drain's requirements.
///
/// `surface_certificate_facts` is snapshotted before the drain runs, but
/// the certificate a claim ends up with is `[recorded post tactics ...,
/// closer tactics ...]`. Facts produced by replaying a recorded tactic are
/// therefore in scope when the closer replays; withholding them from
/// generation only makes generation plan against strictly less than the
/// replay judgment accepts.
fn record_certificate_facts_from_replay(
    before: &[Proposition],
    after: &[Proposition],
    surface_certificate_facts: &mut Vec<Proposition>,
) {
    for fact in after {
        if !before.contains(fact) && !surface_certificate_facts.contains(fact) {
            surface_certificate_facts.push(fact.clone());
        }
    }
}

fn tactic_is_deferred_post_execution(tactic: &ProofTactic) -> bool {
    matches!(
        tactic,
        ProofTactic::FoldResource(_)
            | ProofTactic::UnfoldPredicate(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Have(_)
            | ProofTactic::Transport { .. }
            | ProofTactic::TransportUsing { .. }
            | ProofTactic::Witness(_)
            | ProofTactic::Choose(_)
            | ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Rewrite(_)
            | ProofTactic::Simp
            | ProofTactic::Frame(None | Some(CodeRegionRef::Function))
    )
}

struct TacticTiming {
    claim_label: String,
    tactic_index: usize,
    source_index: usize,
    tactic_name: String,
    tactic_class: &'static str,
    statement_index: usize,
    start: std::time::Instant,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceTacticClass {
    Simple,
    Smart,
    Control,
}

impl SourceTacticClass {
    fn label(self) -> &'static str {
        match self {
            Self::Simple => "simple",
            Self::Smart => "smart",
            Self::Control => "control",
        }
    }
}

pub(super) fn source_tactic_class(tactic: &ProofTactic) -> SourceTacticClass {
    if let ProofTactic::Have(have) = tactic {
        if smart_simp_unfold_prefix(&have.proof).is_some() {
            return SourceTacticClass::Smart;
        }
        if let Proof::Script(tactics) = &have.proof
            && !tactics.is_empty()
            && tactics
                .iter()
                .all(|tactic| matches!(tactic.class(), TacticClass::Simple(_)))
        {
            return SourceTacticClass::Simple;
        }
    }
    match tactic.class() {
        TacticClass::Simple(_) => SourceTacticClass::Simple,
        TacticClass::Smart(_) => SourceTacticClass::Smart,
        TacticClass::ControlFlow(_) => SourceTacticClass::Control,
    }
}

impl TacticTiming {
    fn new(
        claim_label: &str,
        tactic_index: usize,
        source_index: usize,
        tactic: &ProofTactic,
        statement_index: usize,
    ) -> Option<Self> {
        Self::named_for_tactic(
            claim_label,
            tactic_name(tactic),
            tactic,
            tactic_index,
            source_index,
            statement_index,
        )
    }

    /// Times work that is not itself a surface tactic replay — a planner
    /// searching for a certificate, or a kernel re-derivation that a replayed
    /// tactic defers to its caller — under an explicit `name`, taking the
    /// class from the tactic the work belongs to rather than inventing one.
    fn named_for_tactic(
        claim_label: &str,
        name: &str,
        tactic: &ProofTactic,
        tactic_index: usize,
        source_index: usize,
        statement_index: usize,
    ) -> Option<Self> {
        std::env::var_os("CLICK_TIMINGS").is_some().then(|| {
            let tactic_class = source_tactic_class(tactic).label();
            if std::env::var_os("CLICK_TIMING_STARTS").is_some() {
                eprintln!(
                    "click timing: started tactic {} {} {} class {} statement {} source {}",
                    claim_label, tactic_index, name, tactic_class, statement_index, source_index
                );
            }
            Self {
                claim_label: claim_label.to_string(),
                tactic_index,
                source_index,
                tactic_name: name.to_string(),
                tactic_class,
                statement_index,
                start: std::time::Instant::now(),
            }
        })
    }
}

impl Drop for TacticTiming {
    fn drop(&mut self) {
        eprintln!(
            "click timing: tactic {} {} {} class {} statement {} source {} {:.6}s",
            self.claim_label,
            self.tactic_index,
            self.tactic_name,
            self.tactic_class,
            self.statement_index,
            self.source_index,
            self.start.elapsed().as_secs_f64()
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn replay_linear_tactics(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    let ProofReplayContext {
        mut state,
        pure_facts: mut requirement_pure_facts,
        mut replay,
        mut branch_path,
    } = context;
    let mut assumptions = assumptions_from_propositions(&requirement_pure_facts);

    for indexed_tactic in tactics {
        let tactic_index = indexed_tactic.index;
        let source_index = indexed_tactic.source_index;
        let tactic = &indexed_tactic.tactic;
        let deferred_post_execution = replay.ordered_finalization
            && replay.is_at_function_exit()
            && tactic_is_deferred_post_execution(tactic);
        let deferred_region_simp = replay.region_proof && matches!(tactic, ProofTactic::Simp);
        let pre_capture_branch_skeleton =
            begin_tactic_expansion_capture(source_index, tactic, &mut replay);
        let capture_this_tactic = pre_capture_branch_skeleton.is_some();
        if let Some(branch_skeleton) = pre_capture_branch_skeleton
            && deferred_post_execution
        {
            replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                branch_skeleton,
            });
        }
        if !deferred_post_execution {
            record_surface_replay_tactic(
                &mut replay,
                &state,
                &requirement_pure_facts,
                function_block,
                parsed_function.parameters(),
                arguments,
                predicate_environment,
                click_function_environment,
                tactic,
                None,
            );
        }
        let _timing = (!deferred_post_execution
            && !(replay.region_proof && matches!(tactic, ProofTactic::Simp)))
        .then(|| {
            TacticTiming::new(
                claim_label,
                tactic_index,
                source_index,
                tactic,
                replay.frontier.next_statement_index,
            )
        })
        .flatten();
        if let ProofTactic::Transport {
            source: surface_source,
            target: surface_target,
        } = tactic
            && !replay.is_at_function_exit()
        {
            if replay.is_at_function_entry() || replay.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                )));
            }
            let pre_state = replay.old_reference_state(&state);
            let source = lower_point_proposition(
                surface_source,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                pre_state,
                &state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if assumptions.derive_proposition(&source).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        &requirement_pure_facts,
                        state.resources().facts(),
                        parsed_function.parameters(),
                        arguments,
                        &replay.effect_facts,
                    )
                )));
            }
            let target = lower_point_proposition(
                surface_target,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                pre_state,
                &state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = fact_transport_transition_facts(&replay.effect_facts, &source);
            let premises = plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                &requirement_pure_facts,
                &transition_facts,
                parsed_function.parameters(),
                arguments,
                &replay,
                &state,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not make fact transport premises explicit: {}",
                    error.message()
                ))
            })?;
            let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::TransportUsing {
                source: surface_source.clone(),
                target: surface_target.clone(),
                premises,
            }])
            .expect("explicit fact transport is a simple tactic");
            let result = replay_smart_plan(
                ProofReplayContext {
                    state,
                    pure_facts: requirement_pure_facts,
                    replay,
                    branch_path,
                },
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactic_index,
                source_index,
                &plan,
            )?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            if capture_this_tactic {
                return Err(finish_tactic_expansion_capture(&replay.surface_replay, false));
            }
            continue;
        }
        if let ProofTactic::ApplyTheorem(application) = tactic
            && !replay.is_at_function_exit()
        {
            if theorem_environment.get(&application.name).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                    application.name
                )));
            }
            let premises = plan_explicit_theorem_application(
                theorem_environment,
                application,
                claim_label,
                tactic_index,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                &replay,
                &state,
                predicate_environment,
                click_function_environment,
            )?;
            let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::ApplyTheoremUsing {
                application: application.clone(),
                premises,
            }])
            .expect("explicit theorem application is a simple tactic");
            let result = replay_smart_plan(
                ProofReplayContext {
                    state,
                    pure_facts: requirement_pure_facts,
                    replay,
                    branch_path,
                },
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactic_index,
                source_index,
                &plan,
            )?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            if capture_this_tactic {
                return Err(finish_tactic_expansion_capture(&replay.surface_replay, false));
            }
            continue;
        }
        match tactic {
            ProofTactic::UnfoldResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold` must run before execution reaches function exit"
                    )));
                }
                state = unfold_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    arguments,
                    state,
                    &mut requirement_pure_facts,
                    &mut replay.surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ObserveResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `observe` must run before execution reaches function exit"
                    )));
                }
                state = observe_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    arguments,
                    state,
                    &mut requirement_pure_facts,
                    &mut replay.surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Transport {
                source: surface_source,
                target: surface_target,
            }
            | ProofTactic::TransportUsing {
                source: surface_source,
                target: surface_target,
                ..
            } => {
                if replay.is_at_function_exit() {
                    let premises = match tactic {
                        ProofTactic::TransportUsing { premises, .. } => Some(premises.clone()),
                        ProofTactic::Transport { .. } => None,
                        _ => unreachable!(),
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Transport {
                            source: surface_source.clone(),
                            target: surface_target.clone(),
                            premises,
                        },
                    );
                    continue;
                }
                if replay.is_at_function_entry() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires at least one completed execution step"
                    )));
                }
                let pre_state = replay.old_reference_state(&state).clone();
                let surface_premises = match tactic {
                    ProofTactic::TransportUsing { premises, .. } => Some(premises),
                    ProofTactic::Transport { .. } => None,
                    _ => unreachable!(),
                };
                let mut explicit_premises = Vec::new();
                if let Some(surface_premises) = surface_premises {
                    for surface_premise in surface_premises {
                        let premise = if let Some(recorded) = replay
                            .surface_propositions
                            .available_kernel(surface_premise, &requirement_pure_facts)
                        {
                            recorded.clone()
                        } else {
                            lower_point_proposition(
                                surface_premise,
                                &requirement_pure_facts,
                                parsed_function.parameters(),
                                arguments,
                                &pre_state,
                                &state,
                                None,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` tactic {tactic_index}: could not lower `transport using` premise: {message}"
                                ))
                            })?
                        };
                        if !exact_fact_is_available(&premise, &requirement_pure_facts) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `transport using` requires an exact premise: {}",
                                describe_missing_pure_fact(
                                    &premise,
                                    &requirement_pure_facts,
                                    state.resources().facts(),
                                    parsed_function.parameters(),
                                    arguments,
                                    &replay.effect_facts,
                                )
                            )));
                        }
                        if !explicit_premises.contains(&premise) {
                            explicit_premises.push(premise);
                        }
                    }
                }
                // Lowering memory expressions uses the already-validated
                // ambient resource/loadability context. The proof search
                // below is still restricted to explicit premises plus
                // certified frame context.
                let lowering_facts = requirement_pure_facts.as_slice();
                let mut direct_lowering_facts =
                    facts_for_direct_surface_lowering(&requirement_pure_facts);
                for premise in &explicit_premises {
                    if !direct_lowering_facts.contains(premise) {
                        direct_lowering_facts.push(premise.clone());
                    }
                }
                let source = if let Some(recorded) = replay
                    .surface_propositions
                    .available_kernel(surface_source, &requirement_pure_facts)
                {
                    recorded.clone()
                } else {
                    lower_point_proposition(
                        surface_source,
                        lowering_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        &state,
                        None,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                        ))
                    })?
                };
                replay
                    .surface_propositions
                    .record_lowering(surface_source, &source)?;
                let selected_assumptions = if surface_premises.is_some() {
                    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                    let resource_facts = state
                        .resources()
                        .observable_facts_assuming_valid(&explicit_assumptions);
                    requirement_pure_facts
                        .iter()
                        .filter(|fact| is_implicit_fact_transport_context(fact))
                        .cloned()
                        .chain(resource_facts)
                        .fold(explicit_assumptions, |assumptions, fact| {
                            assumptions.assume_proposition(fact)
                        })
                } else {
                    assumptions.clone()
                };
                // A transport source spelled at a later program point than
                // its listed fact is the same fact when the kernel proves the
                // snapshots agree at the loaded pointers. Candidates still
                // come only from the explicit premises, so the transport must
                // still list the fact; the recorded effects and the selected
                // assumptions only supply the frame evidence.
                if !exact_fact_is_available(&source, &explicit_premises)
                    && !snapshot_bridged_fact_is_available_under(
                        &source,
                        &explicit_premises,
                        &selected_assumptions,
                        &replay.effect_facts,
                    )
                    && selected_assumptions
                        .derive_atomic_proposition(&source)
                        .is_none()
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport{}` requires a source derivable from its {}facts: {}",
                        if surface_premises.is_some() {
                            " using"
                        } else {
                            ""
                        },
                        if surface_premises.is_some() {
                            "explicit "
                        } else {
                            "ambient "
                        },
                        describe_missing_pure_fact(
                            &source,
                            &requirement_pure_facts,
                            state.resources().facts(),
                            parsed_function.parameters(),
                            arguments,
                            &replay.effect_facts,
                        )
                    )));
                }
                let target = lower_point_proposition(
                    surface_target,
                    &direct_lowering_facts,
                    parsed_function.parameters(),
                    arguments,
                    &pre_state,
                    &state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                    ))
                })?;
                replay
                    .surface_propositions
                    .record_lowering(surface_target, &target)?;
                // The target can already be present under a different snapshot
                // spelling; candidates come from the ambient facts, so the
                // bridge only re-spells a fact that is genuinely available.
                if exact_fact_is_available_across_effects(
                    &target,
                    &requirement_pure_facts,
                    &replay.effect_facts,
                ) || materialization_equivalent_available_fact(&target, &requirement_pure_facts)
                    .is_some()
                {
                    if !requirement_pure_facts.contains(&target) {
                        requirement_pure_facts.push(target.clone());
                        assumptions = assumptions.assume_proposition(target);
                    }
                    continue;
                }
                let transition_facts =
                    fact_transport_transition_facts(&replay.effect_facts, &source);
                if surface_premises.is_none() {
                    match plan_explicit_fact_transport(
                        surface_source,
                        &source,
                        &target,
                        &requirement_pure_facts,
                        &transition_facts,
                        parsed_function.parameters(),
                        arguments,
                        &replay,
                        &state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.surface_replay.push(ProofTactic::TransportUsing {
                                source: surface_source.clone(),
                                target: surface_target.clone(),
                                premises,
                            });
                        }
                        Err(error) => replay.surface_replay.block(format!(
                            "could not make fact transport premises explicit: {}",
                            error.message()
                        )),
                    }
                }
                let transport_assumptions = transition_facts
                    .iter()
                    .fold(selected_assumptions, |assumptions, fact| {
                        assumptions.assume_proposition(fact.proposition().clone())
                    })
                    .assume_proposition(source.clone());
                if !certified_fact_transport_reaches_through(
                    &source,
                    &target,
                    state.memory(),
                    &transport_assumptions,
                    &transition_facts,
                ) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: no certified frame transport applies to the exact source fact\n  source: {source:?}\n  current memory: {:?}\n  effect facts: {:?}",
                        state.memory(),
                        replay.effect_facts
                    )));
                }
                if !requirement_pure_facts.contains(&target) {
                    requirement_pure_facts.push(target.clone());
                    assumptions = assumptions.assume_proposition(target);
                }
            }
            ProofTactic::StepUsing(premises)
            | ProofTactic::ApplyLoopSummaryUsing { premises, .. } => {
                let all_pure_facts = requirement_pure_facts.clone();
                let (tactic_name, prerequisite_policy, loop_step_policy) = match tactic {
                    ProofTactic::StepUsing(_) => (
                        "step using",
                        StatementPrerequisitePolicy::Explicit,
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::ApplyLoopSummaryUsing { region, .. } => {
                        let CodeRegion::Loop(expected_loop) = resolve_code_region_ref(
                            function_block,
                            region,
                            claim_label,
                            tactic_index,
                        )?
                        else {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `apply_loop_summary` expects a loop region"
                            )));
                        };
                        let current_loop = replay
                            .source_layout
                            .statement(replay.frontier.next_statement_index)
                            .and_then(|region| match region.kind {
                                SourceStatementKind::Loop { loop_index } => Some(loop_index),
                                SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                            });
                        if current_loop != Some(expected_loop) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `apply_loop_summary(loop({expected_loop}))` is not at that loop's entry; current statement is statement({})",
                                replay.frontier.next_statement_index
                            )));
                        }
                        (
                            "apply_loop_summary using",
                            StatementPrerequisitePolicy::Explicit,
                            LoopStepPolicy::ApplyVerifiedRule,
                        )
                    }
                    _ => unreachable!(),
                };
                let pre_state = replay.old_reference_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let premise = if let Some(recorded) = replay
                        .surface_propositions
                        .available_kernel(surface_premise, &all_pure_facts)
                    {
                        recorded.clone()
                    } else {
                        lower_point_proposition(
                            surface_premise,
                            &all_pure_facts,
                            parsed_function.parameters(),
                            arguments,
                            &pre_state,
                            &state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower `{tactic_name}` premise `{}`: {message}",
                                super::printing::source_click_proposition(surface_premise)
                            ))
                        })?
                    };
                    replay
                        .surface_propositions
                        .record_lowering(surface_premise, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise: {}",
                                error.message()
                            ))
                        })?;
                    let entry_point = ProgramPointRef {
                        region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                        kind: ProgramPointKind::Entry,
                    };
                    let source_surface = surface_with_source_site(surface_premise, &entry_point)?;
                    replay
                        .surface_propositions
                        .record_lowering(&source_surface, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise source site: {}",
                                error.message()
                            ))
                        })?;
                    // Loadability premises additionally transport across
                    // snapshot spellings and recorded effects: the recorded
                    // fact and the premise print identically but embed
                    // different memory snapshots.
                    let premise_is_available = exact_fact_is_available_across_effects(
                        &premise,
                        &all_pure_facts,
                        &replay.effect_facts,
                    ) || materialization_equivalent_available_fact(&premise, &all_pure_facts)
                        .is_some()
                        || crate::kernel::loadable_covered_by_fact(&assumptions, &premise);
                    if !premise_is_available {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires an exact premise: {}",
                            describe_missing_pure_fact(
                                &premise,
                                &all_pure_facts,
                                state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                &replay.effect_facts,
                            )
                        )));
                    }
                    if !explicit_premises.contains(&premise) {
                        explicit_premises.push(premise);
                    }
                }
                for case in &replay.case_assumptions {
                    let branch_fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let proposition = lower_point_proposition(
                            &case.condition,
                            &all_pure_facts,
                            parsed_function.parameters(),
                            arguments,
                            &pre_state,
                            &state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower enclosing proof-branch condition: {message}"
                            ))
                        })?;
                        if case.value {
                            proposition
                        } else {
                            match proposition {
                                Proposition::ConditionIs(condition, value) => {
                                    Proposition::ConditionIs(condition, !value)
                                }
                                Proposition::Not(body) => *body,
                                proposition => Proposition::Not(Box::new(proposition)),
                            }
                        }
                    };
                    if exact_fact_is_available(&branch_fact, &all_pure_facts)
                        && !explicit_premises.contains(&branch_fact)
                    {
                        explicit_premises.push(branch_fact);
                    }
                }
                if matches!(tactic, ProofTactic::ApplyLoopSummaryUsing { .. })
                    && !replay.unfolded_predicates.is_empty()
                {
                    for fact in &all_pure_facts {
                        if !explicit_premises.contains(fact) {
                            explicit_premises.push(fact.clone());
                        }
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                for resource_fact in state
                    .resources()
                    .observable_facts_assuming_valid(&explicit_assumptions)
                {
                    if !explicit_premises.contains(&resource_fact) {
                        explicit_premises.push(resource_fact);
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut explicit_premises,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &explicit_assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name,
                    &[],
                    None,
                    prerequisite_policy,
                    // `using` deliberately selects the exact context that may
                    // cross this statement boundary. Transport only those
                    // listed facts through the certified statement effect;
                    // ambient facts are restored below at their original
                    // snapshots.
                    StatementFactTransportPolicy::Selected,
                    loop_step_policy,
                )?;
                for fact in all_pure_facts {
                    if !explicit_premises.contains(&fact) {
                        explicit_premises.push(fact);
                    }
                }
                requirement_pure_facts = explicit_premises;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Step
            | ProofTactic::ApplyLoopSummary(_)
            | ProofTactic::CertifiedStatementStep { .. }
            | ProofTactic::CertifiedLoopSummaryStep { .. }
            | ProofTactic::CertifiedStatementReplay(_)
            | ProofTactic::CertifiedLoopSummaryReplay(_) => {
                let (
                    prerequisite_policy,
                    certified_prerequisites,
                    certified_replay,
                    loop_step_policy,
                ) = match tactic {
                    ProofTactic::Step => (
                        StatementPrerequisitePolicy::Exact,
                        &[][..],
                        None,
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::ApplyLoopSummary(region_ref) => {
                        let CodeRegion::Loop(expected_loop) = resolve_code_region_ref(
                            function_block,
                            region_ref,
                            claim_label,
                            tactic_index,
                        )?
                        else {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `apply_loop_summary` expects a loop region"
                            )));
                        };
                        let current_loop = replay
                            .source_layout
                            .statement(replay.frontier.next_statement_index)
                            .and_then(|region| match region.kind {
                                SourceStatementKind::Loop { loop_index } => Some(loop_index),
                                SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                            });
                        if current_loop != Some(expected_loop) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `apply_loop_summary(loop({expected_loop}))` is not at that loop's entry; current statement is statement({})",
                                replay.frontier.next_statement_index
                            )));
                        }
                        (
                            StatementPrerequisitePolicy::Exact,
                            &[][..],
                            None,
                            LoopStepPolicy::ApplyVerifiedRule,
                        )
                    }
                    ProofTactic::CertifiedStatementStep {
                        prerequisite_derivations,
                        ..
                    } => (
                        StatementPrerequisitePolicy::Certified,
                        prerequisite_derivations.as_slice(),
                        None,
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedLoopSummaryStep {
                        prerequisite_derivations,
                        ..
                    } => (
                        StatementPrerequisitePolicy::Certified,
                        prerequisite_derivations.as_slice(),
                        None,
                        LoopStepPolicy::ApplyVerifiedRule,
                    ),
                    ProofTactic::CertifiedStatementReplay(evidence) => (
                        StatementPrerequisitePolicy::Certified,
                        evidence.transition.prerequisite_derivations.as_slice(),
                        Some(evidence.as_ref()),
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedLoopSummaryReplay(evidence) => (
                        StatementPrerequisitePolicy::Certified,
                        evidence.transition.prerequisite_derivations.as_slice(),
                        Some(evidence.as_ref()),
                        LoopStepPolicy::ApplyVerifiedRule,
                    ),
                    _ => unreachable!(),
                };
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name(tactic),
                    certified_prerequisites,
                    certified_replay,
                    prerequisite_policy,
                    StatementFactTransportPolicy::None,
                    loop_step_policy,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CertifiedPathAssumption { facts, theorem, .. } => {
                if !matches!(
                    implication_body(theorem.proposition()),
                    Proposition::CConditionEvaluates { .. }
                ) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified path assumption is not backed by a condition-evaluation theorem"
                    )));
                }
                for fact in facts {
                    if !requirement_pure_facts.contains(fact) {
                        requirement_pure_facts.push(fact.clone());
                    }
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CertifiedAlternatives(alternatives) => {
                let outer_surface_replay = replay.surface_replay.clone();
                let base = ProofReplayContext {
                    state: state.clone(),
                    pure_facts: requirement_pure_facts.clone(),
                    replay: replay.clone(),
                    branch_path: branch_path.clone(),
                };
                let mut completed = Vec::new();
                let mut surface_paths = Vec::new();
                for alternative in alternatives {
                    let mut alternative_base = base.clone();
                    alternative_base.replay.surface_replay = SurfaceReplay::default();
                    let result = replay_internal_plan(
                        alternative_base,
                        function_block,
                        parsed_function,
                        claims,
                        claim_label,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        theorem_environment,
                        function,
                        arguments,
                        tactic_index,
                        source_index,
                        alternative,
                    )?;
                    surface_paths.push(result.replay.surface_replay.clone());
                    completed.push(BoundedProofFrontier {
                        replay: result.replay,
                        state: result.state,
                        pure_facts: result.pure_facts,
                    });
                }
                merge_bounded_execution_frontiers(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function,
                    arguments,
                    completed,
                    claim_label,
                    tactic_index,
                )?;
                replay.surface_replay = outer_surface_replay;
                match synthesize_surface_alternatives(surface_paths) {
                    Ok(tactics) => {
                        for tactic in tactics {
                            replay.surface_replay.push(tactic);
                        }
                    }
                    Err(message) => replay.surface_replay.block(format!(
                        "could not lower certified branch alternatives: {message}"
                    )),
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteStep => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_step_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    "execute_step",
                    &[],
                    None,
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    LoopStepPolicy::EnterBody,
                )?;
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_step` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteThenStep => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                let entered = execute_branch_step_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                    Some(true),
                    &[],
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    BranchStepPolicy::RequireProven,
                )?;
                debug_assert!(entered);
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_then_step` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteElseStep => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                let entered = execute_branch_step_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                    Some(false),
                    &[],
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    BranchStepPolicy::RequireProven,
                )?;
                debug_assert!(entered);
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_else_step` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteRest => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_rest_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                )?;
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_rest` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteUntil(region_ref) => {
                let code_region =
                    resolve_code_region_ref(function_block, region_ref, claim_label, tactic_index)?;
                let CodeRegion::Statement(statement_index) = code_region else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `execute_until` expects a statement region"
                    )));
                };
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_until_statement(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    statement_index,
                    claim_label,
                    tactic_index,
                    StatementPrerequisitePolicy::Planning,
                )?;
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_until` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::BoundedExecute => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                bounded_execute_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                    StatementPrerequisitePolicy::Planning,
                )?;
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `bounded_execute` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ContextualFrame => {
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                let Some(effect_claim) = claims
                    .iter()
                    .find(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `frame` has no effect claim to prove"
                    )));
                };
                let FunctionClaimRef::Effect(_, effect_clause) = effect_claim else {
                    unreachable!("selected claim must be an effect claim")
                };
                let execution = replay
                    .execution()
                    .expect("function-exit replay should contain an execution");
                let pre_state = replay.old_reference_state(&state);
                let mut path_derivations = Vec::with_capacity(execution.paths().len());
                for (path_index, path) in execution.paths().iter().enumerate() {
                    if !path.obligations().is_empty() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame` cannot plan from an execution path with unresolved obligations"
                        )));
                    }
                    let mut path_facts = requirement_pure_facts.clone();
                    path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                    path_derivations.push(plan_effect_clause_derivations(
                        claim_label,
                        path_index,
                        &path.execution_facts(),
                        &path_facts,
                        effect_clause.effect(),
                        parsed_function.parameters(),
                        arguments,
                        pre_state,
                        path.outcome(),
                    )?);
                }
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&[ProofTactic::CertifiedFrame(
                        path_derivations,
                    )])
                    .expect("certified frame is a simple tactic");
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Frame(region_ref) => {
                if let Some(goal) = replay.loop_effect_goal.as_mut() {
                    if region_ref.is_some() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: a structural effect proof must use unqualified `frame()`"
                        )));
                    }
                    if goal.closed {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: the structural effect goal was closed more than once"
                        )));
                    }
                    c_loop_effects_hold_at_back_edge(
                        &goal.before_state,
                        &state,
                        std::slice::from_ref(&goal.check),
                        &requirement_pure_facts,
                        &assumptions,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame()` failed: {message}"
                        ))
                    })?;
                    goal.closed = true;
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                let code_region = region_ref
                    .as_ref()
                    .map(|region_ref| {
                        resolve_code_region_ref(
                            function_block,
                            region_ref,
                            claim_label,
                            tactic_index,
                        )
                    })
                    .transpose()?;
                if replay.ordered_finalization
                    && replay.is_at_function_exit()
                    && matches!(code_region, None | Some(CodeRegion::Function))
                {
                    if !replay.grouped_contract {
                        validate_frame_code_region(
                            function_block,
                            parsed_function,
                            code_region,
                            &claims[0],
                            claim_label,
                            tactic_index,
                        )?;
                    }
                    let Some(effect_claim) = claims
                        .iter()
                        .find(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame()` has no effect claim to prove"
                        )));
                    };
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        effect_claim,
                        claim_label,
                        tactic_index,
                    )?;
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Frame,
                    );
                    replay.frames.insert(region_ref.clone());
                    continue;
                }
                let effect_claims = claims
                    .iter()
                    .filter(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    .collect::<Vec<_>>();
                if effect_claims.is_empty() {
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        &claims[0],
                        claim_label,
                        tactic_index,
                    )?;
                }
                for claim in effect_claims {
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        claim,
                        claim_label,
                        tactic_index,
                    )?;
                    match code_region {
                        None | Some(CodeRegion::Function) => {
                            validate_function_frame_tactic(
                                replay.execution().expect("execution should exist"),
                                claim,
                                claim_label,
                                tactic_index,
                                parsed_function.parameters(),
                                arguments,
                                &state,
                                &requirement_pure_facts,
                            )?;
                        }
                        Some(CodeRegion::Loop(_)) => {}
                        Some(CodeRegion::Statement(_)) => {}
                    }
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let region = region_ref.clone().ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: contextual function `frame()` should have been deferred earlier"
                        ))
                    })?;
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::FrameRegion(region),
                    );
                }
                replay.frames.insert(region_ref.clone());
            }
            ProofTactic::CertifiedFrame(path_derivations) => {
                require_function_exit(&replay, claim_label, tactic_index, "certified_frame")?;
                replay.defer_post_execution(
                    tactic_index,
                    source_index,
                    PostExecutionTactic::CertifiedFrame(path_derivations.clone()),
                );
            }
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::UnfoldPredicate(name.clone()),
                    );
                    continue;
                }
                if !replay.unfolded_predicates.contains(name) {
                    replay.unfolded_predicates.push(name.clone());
                }
                let surface_unfoldings = requirement_pure_facts
                    .iter()
                    .filter_map(|kernel| {
                        let Proposition::Predicate {
                            name: kernel_name, ..
                        } = kernel
                        else {
                            return None;
                        };
                        if kernel_name != name {
                            return None;
                        }
                        let ClickProposition::PredicateCall {
                            name: surface_name,
                            arguments: surface_arguments,
                        } = replay.surface_propositions.surface(kernel).ok()?
                        else {
                            return None;
                        };
                        let definition = predicate_environment.get(surface_name)?;
                        let surface =
                            instantiate_click_predicate_definition(definition, surface_arguments)
                                .ok()?;
                        let unfolded = unfold_predicates_in_proposition(
                            predicate_environment,
                            click_function_environment,
                            std::slice::from_ref(name),
                            kernel,
                            &assumptions,
                        )
                        .ok()?;
                        Some((surface, unfolded))
                    })
                    .collect::<Vec<_>>();
                requirement_pure_facts = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &requirement_pure_facts,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
                for (surface, kernel) in surface_unfoldings {
                    replay
                        .surface_propositions
                        .record_lowering(&surface, &kernel)?;
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ApplyTheorem(application) => {
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Apply(application.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `apply` is not available in this region proof"
                        )));
                    }
                } else {
                    match plan_explicit_theorem_application(
                        theorem_environment,
                        application,
                        claim_label,
                        tactic_index,
                        &requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &replay,
                        &state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.surface_replay.push(ProofTactic::ApplyTheoremUsing {
                                application: application.clone(),
                                premises,
                            });
                        }
                        Err(error) => replay.surface_replay.block(format!(
                            "could not make theorem application premises explicit: {}",
                            error.message()
                        )),
                    }
                    requirement_pure_facts = apply_theorem_at_current_point(
                        theorem_environment,
                        application,
                        claim_label,
                        tactic_index,
                        requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &replay.unfolded_predicates,
                        None,
                    )?;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                }
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => {
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::ApplyUsing {
                                application: application.clone(),
                                premises: premises.clone(),
                            },
                        );
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply using` is not available in this region proof"
                    )));
                }
                let all_pure_facts = requirement_pure_facts.clone();
                let mut lowering_facts = all_pure_facts.clone();
                append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
                let pre_state = replay.old_reference_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let premise = if let Some(recorded) = replay
                        .surface_propositions
                        .available_kernel(surface_premise, &all_pure_facts)
                    {
                        recorded.clone()
                    } else {
                        lower_point_proposition(
                            surface_premise,
                            &lowering_facts,
                            parsed_function.parameters(),
                            arguments,
                            &pre_state,
                            &state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                            ))
                        })?
                    };
                    if !exact_fact_is_available(&premise, &all_pure_facts)
                        && materialization_equivalent_available_fact(&premise, &all_pure_facts)
                            .is_none()
                    {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `apply using` requires an exact premise: {}",
                            describe_missing_pure_fact(
                                &premise,
                                &all_pure_facts,
                                state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                &replay.effect_facts,
                            )
                        )));
                    }
                    if !explicit_premises.contains(&premise) {
                        explicit_premises.push(premise);
                    }
                }
                let mut applied = apply_theorem_at_current_point(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    explicit_premises,
                    parsed_function.parameters(),
                    arguments,
                    &pre_state,
                    &state,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                    &replay.unfolded_predicates,
                    Some(&lowering_facts),
                )?;
                for fact in all_pure_facts {
                    if !applied.contains(&fact) {
                        applied.push(fact);
                    }
                }
                requirement_pure_facts = applied;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FoldResource(resource) => {
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Fold(resource.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `fold` is not available in this region proof"
                        )));
                    }
                } else {
                    let pre_state = replay.old_reference_state(&state).clone();
                    state = fold_composite_resource_at_current_point(
                        resource_environment,
                        resource,
                        claim_label,
                        tactic_index,
                        &requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        state,
                        predicate_environment,
                        click_function_environment,
                        &replay.unfolded_predicates,
                    )?;
                }
            }
            ProofTactic::Have(have) => {
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Have(have.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `have` is not available in this region proof"
                        )));
                    }
                    continue;
                }
                let mut have_facts = requirement_pure_facts.clone();
                have_facts.extend(
                    replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                for fact in replay.surface_propositions.kernel_facts() {
                    if !have_facts.contains(fact) {
                        have_facts.push(fact.clone());
                    }
                }
                let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                let smart_plan = if let Some(unfolded_predicates) = &smart_unfolds {
                    let (fact, plan) = plan_smart_have_at_current_point(
                        have,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        unfolded_predicates,
                        None,
                    )?;
                    Some((fact, plan))
                } else {
                    None
                };
                let fact = match &smart_plan {
                    Some((fact, _)) => fact.clone(),
                    None => prove_have_at_current_point(
                        have,
                        theorem_environment,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        &replay.surface_propositions,
                        predicate_environment,
                        click_function_environment,
                        function_block.requires(),
                    )?,
                };
                replay
                    .surface_propositions
                    .record_lowering(&have.proposition, &fact)?;
                let surface_certificate = if let Some((_, plan)) = &smart_plan {
                    Some(surface_smart_have_certificate(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        have,
                        plan,
                        smart_unfolds.as_deref().unwrap_or(&[]),
                    )?)
                } else {
                    surface_smart_apply_have_certificate(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                        claim_label,
                        tactic_index,
                        have,
                        &fact,
                    )?
                };
                if let Some(certificate) = surface_certificate {
                    let (_, _) = pure_goal_certificate_gateway(
                        claim_label,
                        || Ok(certificate.clone()),
                        |certificate| {
                            verify_surface_certificate(
                                ProofReplayContext {
                                    state: state.clone(),
                                    pure_facts: requirement_pure_facts.clone(),
                                    replay: replay.clone(),
                                    branch_path: branch_path.clone(),
                                },
                                function_block,
                                parsed_function,
                                claims,
                                claim_label,
                                function_environment,
                                predicate_environment,
                                click_function_environment,
                                resource_environment,
                                theorem_environment,
                                function,
                                arguments,
                                tactic_index,
                                source_index,
                                certificate,
                            )
                        },
                    )?;
                    replay
                        .surface_replay
                        .tactics
                        .extend_from_slice(certificate.tactics());
                }
                if !requirement_pure_facts.contains(&fact) {
                    requirement_pure_facts.push(fact.clone());
                    assumptions = assumptions.assume_proposition(fact);
                }
            }
            ProofTactic::If(_) | ProofTactic::Advance(_) => {
                unreachable!("structured tactics are represented by internal proof nodes")
            }
            ProofTactic::Witness(_) => {
                if replay.grouped_contract {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: top-level `witness` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let ProofTactic::Witness(witness) = tactic else {
                        unreachable!()
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Witness(witness.clone()),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "witness")?;
            }
            ProofTactic::Choose(_) => {
                if replay.grouped_contract {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: top-level `choose` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let ProofTactic::Choose(choice) = tactic else {
                        unreachable!()
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Choose(choice.clone()),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "choose")?;
            }
            ProofTactic::Assumption | ProofTactic::Normalize | ProofTactic::Rewrite(_) => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, tactic_name(tactic))?;
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let post_tactic = match tactic {
                        ProofTactic::Assumption => PostExecutionTactic::Assumption,
                        ProofTactic::Normalize => PostExecutionTactic::Normalize,
                        ProofTactic::Rewrite(equality) => {
                            PostExecutionTactic::Rewrite(equality.clone())
                        }
                        _ => unreachable!(),
                    };
                    replay.defer_post_execution(tactic_index, source_index, post_tactic);
                }
            }
            ProofTactic::Intro
            | ProofTactic::Conjunction
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::DoubleNegation
            | ProofTactic::Vacuous
            | ProofTactic::Contradiction(_)
            | ProofTactic::Derive(_)
            | ProofTactic::Calculate(_) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{}` is only available while proving a pure goal, such as inside `have ... by`",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::ExactPropositionDerivation(derivation) => {
                if !derivation.replay(&assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: proposition derivation did not replay"
                    )));
                }
                if !requirement_pure_facts.contains(derivation.conclusion()) {
                    requirement_pure_facts.push(derivation.conclusion().clone());
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                }
            }
            ProofTactic::CertifiedFactTransport {
                source,
                target,
                theorem,
            } => {
                let Some(available_source) =
                    materialization_equivalent_available_fact(source, &requirement_pure_facts)
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport is missing exact source {source:?}"
                    )));
                };
                if available_source != *source && !requirement_pure_facts.contains(source) {
                    requirement_pure_facts.retain(|fact| fact != &available_source);
                    requirement_pure_facts.push(source.clone());
                }
                let Proposition::Implies(theorem_source, theorem_target) = theorem.proposition()
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport theorem is not an implication"
                    )));
                };
                if theorem_source.as_ref() != source || theorem_target.as_ref() != target {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport theorem does not match its source and target"
                    )));
                }
                if !requirement_pure_facts.contains(target) {
                    requirement_pure_facts.push(target.clone());
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FinishCertifiedFactTransports(sources) => {
                requirement_pure_facts.retain(|fact| !sources.contains(fact));
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CloseInvariants => {
                if !replay.loop_invariant_region {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `close_invariants` is only available in a loop-region proof"
                    )));
                }
                if replay.region_invariants_closed {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: the invariant bundle was closed more than once on one path"
                    )));
                }
                replay.region_invariants_closed = true;
                replay.invariant_closer_step = Some(InvariantCloserStep {
                    tactic_index,
                    source_index,
                    statement_index: replay.frontier.next_statement_index,
                });
            }
            ProofTactic::Simp => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, "simp")?;
                }
                if replay.region_proof {
                    replay.region_simp = Some((tactic_index, source_index));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Simp,
                    );
                }
            }
        }
        if capture_this_tactic && !deferred_post_execution && !deferred_region_simp {
            return Err(finish_tactic_expansion_capture(&replay.surface_replay, false));
        }
    }

    Ok(ProofReplayContext {
        state,
        pure_facts: requirement_pure_facts,
        replay,
        branch_path,
    })
}

#[allow(clippy::too_many_arguments)]
fn replay_internal_plan(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    certificate: &ProofReplayPlan,
) -> Result<ProofReplayContext, ClickError> {
    let tactics = certificate
        .tactics()
        .iter()
        .cloned()
        .map(|tactic| IndexedTactic {
            index: tactic_index,
            source_index,
            tactic,
        })
        .collect::<Vec<_>>();
    replay_linear_tactics(
        context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        &tactics,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_internal_plan_to_surface_certificate(
    context: &ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    plan: &ProofReplayPlan,
) -> Result<(TacticCertificate, ProofReplayContext), ClickError> {
    let mut lowering_context = context.clone();
    let tactics = matches!(plan.tactics(), [ProofTactic::CertifiedFrame(_)])
        .then(|| surface_branch_skeleton(&context.replay.surface_replay.tactics))
        .unwrap_or_default();
    lowering_context.replay.surface_replay = SurfaceReplay {
        tactics,
        last_step_entry: context.replay.surface_replay.last_step_entry.clone(),
        ..SurfaceReplay::default()
    };
    let lowered = replay_internal_plan(
        lowering_context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        plan,
    )?;
    if let Some(blocker) = &lowered.replay.surface_replay.blocker {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart tactic could not produce a surface certificate: {blocker}"
        )));
    }
    if lowered.replay.surface_replay.tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart tactic produced an empty surface certificate"
        )));
    }
    let certificate =
        TacticCertificate::from_proof_tactics(&lowered.replay.surface_replay.tactics).map_err(
            |error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart tactic produced a non-surface certificate at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            ))
            },
        )?;
    Ok((certificate, lowered))
}

#[allow(clippy::too_many_arguments)]
fn verify_surface_certificate(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    certificate: &TacticCertificate,
) -> Result<ProofReplayContext, ClickError> {
    let enclosing_branch_path = context.branch_path.clone();
    let enclosing_case_assumptions = context.replay.case_assumptions.clone();
    let program =
        build_generated_certificate_proof(certificate.tactics(), claim_label, source_index)?;
    let completed = SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(|suppressed| {
        let previous = suppressed.replace(true);
        let result = execute_internal_proof(
            &program,
            context,
            function_block,
            parsed_function,
            claims,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function,
            arguments,
        );
        suppressed.set(previous);
        result
    })?;
    merge_surface_certificate_contexts(
        completed,
        function,
        arguments,
        claim_label,
        tactic_index,
        source_index,
        &enclosing_branch_path,
        &enclosing_case_assumptions,
    )
}

fn merge_surface_certificate_contexts(
    mut completed: Vec<ProofReplayContext>,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    source_index: usize,
    enclosing_branch_path: &[String],
    enclosing_case_assumptions: &[ReplayCaseAssumption],
) -> Result<ProofReplayContext, ClickError> {
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: surface certificate at source tactic {source_index} produced no replay contexts"
        )));
    }
    if completed.len() == 1 {
        return Ok(completed.pop().expect("one completed context exists"));
    }
    if completed
        .iter()
        .any(|context| !context.replay.is_at_function_exit())
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: branched surface certificate at source tactic {source_index} did not finish every branch at function exit"
        )));
    }
    let execution_start_state = completed[0]
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: branched surface certificate has no execution start state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|context| context.pure_facts.contains(fact))
    });
    let mut common_program_points = completed[0].replay.program_point_states.clone();
    common_program_points.retain(|point, point_state| {
        completed
            .iter()
            .skip(1)
            .all(|context| context.replay.program_point_states.get(point) == Some(point_state))
    });
    let mut paths = Vec::new();
    for context in &completed {
        let execution = context
            .replay
            .execution()
            .expect("every completed surface branch is at function exit");
        for path in execution.paths() {
            let mut facts = path.execution_facts();
            for fact in &context.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            let obligations = path.obligations().to_vec();
            if !paths
                .iter()
                .any(|(existing_outcome, existing_facts, existing_obligations)| {
                    existing_outcome == path.outcome()
                        && existing_facts == &facts
                        && existing_obligations == &obligations
                })
            {
                paths.push((path.outcome().clone(), facts, obligations));
            }
        }
    }
    let execution = c_function_execution_candidates_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        paths,
    );
    let mut merged = completed.remove(0);
    merged.replay.program_point_states = common_program_points;
    merged.replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    merged.replay.case_assumptions = enclosing_case_assumptions.to_vec();
    merged.state = execution_start_state;
    merged.pure_facts = common_pure_facts;
    merged.branch_path = enclosing_branch_path.to_vec();
    Ok(merged)
}

#[allow(clippy::too_many_arguments)]
fn replay_smart_plan(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    plan: &ProofReplayPlan,
) -> Result<ProofReplayContext, ClickError> {
    let outer_surface_replay = context.replay.surface_replay.clone();
    let (certificate, mut internal_result) = lower_internal_plan_to_surface_certificate(
        &context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        plan,
    )?;
    let mut verified_result = verify_surface_certificate(
        context.clone(),
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        &certificate,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: generated surface certificate failed replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    let last_step_entry = internal_result
        .replay
        .surface_replay
        .last_step_entry
        .clone();
    internal_result.replay.surface_replay = outer_surface_replay;
    let replaces_existing_branch = matches!(plan.tactics(), [ProofTactic::CertifiedFrame(_)])
        && matches!(certificate.tactics(), [ProofTactic::If(_)])
        && internal_result
            .replay
            .surface_replay
            .tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::If(_)));
    if replaces_existing_branch {
        let branch_index = internal_result
            .replay
            .surface_replay
            .tactics
            .iter()
            .rposition(|tactic| matches!(tactic, ProofTactic::If(_)))
            .expect("an existing surface branch was checked above");
        internal_result
            .replay
            .surface_replay
            .tactics
            .truncate(branch_index);
        internal_result
            .replay
            .surface_replay
            .tactics
            .extend(certificate.tactics().iter().cloned());
    } else {
        for tactic in certificate.tactics() {
            internal_result.replay.surface_replay.push(tactic.clone());
        }
    }
    internal_result.replay.surface_replay.last_step_entry = last_step_entry;
    verified_result.replay.surface_replay = internal_result.replay.surface_replay;
    Ok(verified_result)
}

#[allow(clippy::too_many_arguments)]
fn execute_internal_proof(
    node: &InternalProofNode,
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
) -> Result<Vec<ProofReplayContext>, ClickError> {
    match node {
        InternalProofNode::Done => Ok(vec![context]),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            let branch_path = context.branch_path.clone();
            let context = replay_linear_tactics(
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactics,
            )
            .map_err(|error| add_proof_branch_path(error, &branch_path))?;
            execute_internal_proof(
                continuation,
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )
        }
        InternalProofNode::If {
            index,
            condition,
            then_branch,
            else_branch,
            continuation,
        } => {
            let condition_text = describe_click_proposition(condition);
            let mut contexts = Vec::new();
            for (branch_name, value, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                let branch_description =
                    format!("{branch_name} branch of proof `if {condition_text}`");
                branch_context.branch_path.push(branch_description);
                introduce_proof_case_assumption(
                    &mut branch_context,
                    condition,
                    value,
                    *index,
                    parsed_function.parameters(),
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                )?;
                for branch_context in branch_contexts {
                    let mut continued = execute_internal_proof(
                        continuation,
                        branch_context,
                        function_block,
                        parsed_function,
                        claims,
                        claim_label,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        theorem_environment,
                        function,
                        arguments,
                    )?;
                    contexts.append(&mut continued);
                }
            }
            Ok(contexts)
        }
        InternalProofNode::Advance {
            index,
            _join_id: _,
            target,
            assertions,
            body,
            continuation,
        } => {
            let body_contexts = execute_internal_proof(
                body,
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )?;
            let mut stable_join_locals = parameter_values(parsed_function.parameters(), arguments)?;
            stable_join_locals.retain(|name, value| {
                body_contexts
                    .iter()
                    .all(|context| context.state.locals().get(name) == Some(value))
            });
            let mut joined_context: Option<ProofReplayContext> = None;
            for mut branch_context in body_contexts {
                let result = apply_advance_interface(
                    target,
                    assertions,
                    *index,
                    &mut branch_context.replay,
                    &mut branch_context.state,
                    &mut branch_context.pure_facts,
                    function_block,
                    parsed_function.parameters(),
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    claim_label,
                    &stable_join_locals,
                );
                if let Err(error) = result {
                    return Err(add_proof_branch_path(error, &branch_context.branch_path));
                }
                // Every branch has established the same declared interface against
                // the shared abstraction. Its remaining branch-local state is hidden.
                if let Some(joined) = &mut joined_context {
                    append_execution_effect_facts(
                        &mut joined.replay.effect_facts,
                        &branch_context.replay.effect_facts,
                    );
                } else {
                    branch_context.branch_path.clear();
                    joined_context = Some(branch_context);
                }
            }
            let joined_context = joined_context.ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `advance` body produced no proof frontier"
                ))
            })?;
            execute_internal_proof(
                continuation,
                joined_context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn introduce_proof_case_assumption(
    context: &mut ProofReplayContext,
    condition: &ClickProposition,
    value: bool,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<(), ClickError> {
    if context.replay.is_at_function_exit() {
        context.replay.case_assumptions.push(ReplayCaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: None,
        });
        return Ok(());
    }
    let proposition = lower_point_proposition(
        condition,
        &context.pure_facts,
        parameters,
        arguments,
        context.replay.old_reference_state(&context.state),
        &context.state,
        None,
        &context.replay.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
        ))
    })?;
    let surface_fact = if value {
        condition.clone()
    } else {
        match condition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: left.clone(),
                operator: match operator {
                    ComparisonOperator::Equal => ComparisonOperator::NotEqual,
                    ComparisonOperator::NotEqual => ComparisonOperator::Equal,
                    ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
                    ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
                    ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
                    ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
                },
                right: right.clone(),
            },
            ClickProposition::Not(body) => body.as_ref().clone(),
            condition => ClickProposition::Not(Box::new(condition.clone())),
        }
    };
    let kernel_fact = if value {
        proposition
    } else {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition, !value)
            }
            Proposition::Not(body) => *body,
            proposition => Proposition::Not(Box::new(proposition)),
        }
    };
    context
        .replay
        .surface_propositions
        .record_lowering(&surface_fact, &kernel_fact)?;
    context.pure_facts.push(kernel_fact.clone());
    context.replay.case_assumptions.push(ReplayCaseAssumption {
        tactic_index,
        condition: condition.clone(),
        value,
        fact: Some(kernel_fact),
    });
    Ok(())
}

fn add_proof_branch_context(error: ClickError, branch: &str) -> ClickError {
    ClickError::new(format!("in {branch}:\n{}", error.message()))
}

fn add_proof_branch_path(mut error: ClickError, branch_path: &[String]) -> ClickError {
    for branch in branch_path.iter().rev() {
        error = add_proof_branch_context(error, branch);
    }
    error
}

fn apply_advance_interface(
    target: &ProgramPointRef,
    assertions: &[ProofAssertion],
    tactic_index: usize,
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    stable_join_locals: &BTreeMap<String, CValue>,
) -> Result<(), ClickError> {
    let region =
        resolve_code_region_ref(function_block, &target.region, claim_label, tactic_index)?;
    let at_target = !replay.frontier.inside_branch()
        && match (region, &replay.frontier.point, target.kind) {
            (
                CodeRegion::Statement(statement_index),
                ProofExecutionPoint::StatementEntry { .. },
                ProgramPointKind::Entry,
            ) => replay.frontier.next_statement_index == statement_index,
            (
                CodeRegion::Statement(statement_index),
                ProofExecutionPoint::StatementEntry { .. },
                ProgramPointKind::Exit,
            ) => {
                replay.frontier.next_statement_index
                    == replay
                        .source_layout
                        .statement(statement_index)
                        .map(|region| region.continuation_node)
                        .unwrap_or(usize::MAX)
                    && replay.program_point_states.contains_key(target)
            }
            (CodeRegion::Loop(loop_index), ProofExecutionPoint::StatementEntry { .. }, kind) => {
                let loop_node = replay
                    .source_layout
                    .loop_statement(loop_index)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `advance` could not resolve source loop({loop_index})"
                        ))
                    })?;
                let continuation_node = replay
                    .source_layout
                    .statement(loop_node)
                    .expect("source loop node should have a region")
                    .continuation_node;
                let expected_node = match kind {
                    ProgramPointKind::Entry => loop_node,
                    ProgramPointKind::Exit => continuation_node,
                };
                replay.frontier.next_statement_index == expected_node
                    && replay.program_point_states.contains_key(target)
            }
            (CodeRegion::Function, _, _) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `advance` requires a statement or loop entry or exit target"
                )));
            }
            _ => false,
        };
    if !at_target {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `advance` branch did not reach `{}.{}`",
            describe_code_region_ref(&target.region),
            match target.kind {
                ProgramPointKind::Entry => "entry",
                ProgramPointKind::Exit => "exit",
            }
        )));
    }

    let mut concrete_facts = available_pure_facts.clone();
    let mut established_interface_resources = Vec::new();
    for assertion in assertions {
        match assertion {
            ProofAssertion::Fact(surface_fact) => {
                let fact = lower_point_proposition(
                        surface_fact,
                        &concrete_facts,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        None,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `advance` fact: {message}"
                        ))
                })?;
                replay
                    .surface_propositions
                    .record_lowering(surface_fact, &fact)?;
                let assumptions = assumptions_from_propositions(&concrete_facts);
                if !concrete_facts.contains(&fact) && !assumptions.proves(&fact) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `advance` did not establish fact: {}",
                        describe_missing_pure_fact(
                            &fact,
                            &concrete_facts,
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                if !concrete_facts.contains(&fact) {
                    concrete_facts.push(fact);
                }
            }
            ProofAssertion::Resource(resource) => {
                let expected =
                    lower_resource_clause_at_state(resource, parameters, arguments, state)?;
                let assumptions = assumptions_from_propositions(&concrete_facts);
                let is_observed_core = resource_is_direct_observed_core(
                    resource,
                    &established_interface_resources,
                    resource_environment,
                    claim_label,
                    tactic_index,
                )?;
                if !is_observed_core && !state.resources().satisfies_fact(&expected, &assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `advance` did not establish resource fact: {}",
                        describe_missing_resource_fact(
                            &expected,
                            &concrete_facts,
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                established_interface_resources.push(resource.clone());
            }
        }
    }
    let entry_state = replay.execution_start_state(state).clone();
    let mut abstract_state =
        abstract_c_state_for_join(state, stable_join_locals).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not abstract `advance` target state: {message}"
            ))
        })?;

    replay.program_point_states.clear();
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());
    replay.unfolded_predicates.clear();
    replay.case_assumptions.clear();
    replay.execution_abstraction = true;

    let mut exported_resources = ResourceContext::new();
    let mut exported_pure_facts = Vec::new();
    for assertion in assertions {
        if let ProofAssertion::Resource(resource) = assertion {
            let fact =
                lower_resource_clause_at_state(resource, parameters, arguments, &abstract_state)?;
            exported_resources = exported_resources.unchecked_with_fact(fact);
            append_lowered_resource_clause_loadable_fact(
                resource,
                parameters,
                exported_resources
                    .facts()
                    .last()
                    .expect("exported resource was just appended"),
                &abstract_state,
                &mut exported_pure_facts,
            );
            // An `old(...)`-interface ensure needs the exported view's
            // loadability in its entry-memory spelling. Export it exactly
            // when the clause lowers at entry at all and the pre-advance
            // proof state establishes it, the same gate `fact` assertions
            // pass through.
            let mut entry_loadables = Vec::new();
            if let Ok(entry_lowered) =
                lower_resource_clause_at_state(resource, parameters, arguments, &entry_state)
            {
                append_lowered_resource_clause_loadable_fact(
                    resource,
                    parameters,
                    &entry_lowered,
                    &entry_state,
                    &mut entry_loadables,
                );
            }
            if !entry_loadables.is_empty() {
                let mut pre_advance_facts = concrete_facts.clone();
                for fact in &replay.effect_facts {
                    if !pre_advance_facts.contains(fact.proposition()) {
                        pre_advance_facts.push(fact.proposition().clone());
                    }
                }
                let pre_advance = assumptions_from_propositions(&pre_advance_facts);
                for fact in entry_loadables {
                    if pre_advance.proves(&fact) && !exported_pure_facts.contains(&fact) {
                        exported_pure_facts.push(fact);
                    }
                }
            }
            if let ResourceClause::Declared {
                kind: ResourceKind::Composite,
                name,
                ..
            } = resource
            {
                let definition = resource_environment.get(name).ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown resource `{name}`"
                    ))
                })?;
                let CResource::Composite {
                    arguments: resource_arguments,
                    ..
                } = exported_resources
                    .facts()
                    .last()
                    .expect("exported composite resource was just appended")
                    .resource()
                else {
                    unreachable!("composite resource clause lowered to another resource family")
                };
                let (memory, _) = apply_composite_observation_law(
                    definition,
                    resource_arguments,
                    parameters,
                    arguments,
                    &entry_state,
                    abstract_state.memory().clone(),
                    &CValue::Int32(Bitvector32Term::Constant(0)),
                    &mut exported_pure_facts,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not project `advance` resource `{name}`: {message}"
                    ))
                })?;
                abstract_state = abstract_state.with_memory(memory);
            }
        }
    }
    abstract_state = abstract_state.with_resource_context(exported_resources.clone());
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());

    for assertion in assertions {
        if let ProofAssertion::Fact(surface_fact) = assertion {
            let fact = lower_point_proposition(
                    surface_fact,
                    &exported_pure_facts,
                    parameters,
                    arguments,
                    &entry_state,
                    &abstract_state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not abstract `advance` fact: {message}"
                    ))
                })?;
            if !exported_pure_facts.contains(&fact) {
                exported_pure_facts.push(fact);
            }
        }
    }

    let exported_assumptions = assumptions_from_propositions(&exported_pure_facts);
    exported_resources = ResourceContext::new()
            .try_compose_with_facts(exported_resources.facts().iter().cloned(), &exported_assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: invalid `advance` resource interface: {error:?}"
                ))
            })?;
    abstract_state = abstract_state.with_resource_context(exported_resources);
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());
    *state = abstract_state;
    *available_pure_facts = exported_pure_facts;
    Ok(())
}

fn append_execution_effect_facts(
    target: &mut Vec<ExecutionPureFact>,
    source: &[ExecutionPureFact],
) {
    for fact in source {
        // Verified-call rule results are kernel-certified transition facts,
        // just like memory-effect summaries. Keep them available to later
        // explicit replay without making the surface certificate restate
        // opaque call identities or intermediate-memory equalities.
        if (is_memory_effect_proposition(fact.proposition()) || fact.is_certified())
            && !target.contains(fact)
        {
            target.push(fact.clone());
        }
    }
}

fn fact_transport_transition_facts(
    facts: &[ExecutionPureFact],
    source: &Proposition,
) -> Vec<ExecutionPureFact> {
    let source_memories = c_condition_fact_memories(source);
    let matching_effect = facts.iter().position(|fact| {
        let before = match fact.proposition() {
            Proposition::CMemoryMutatesOnly { before, .. }
            | Proposition::CMemoryEffectSummary { before, .. } => before,
            _ => return false,
        };
        source_memories.contains(before)
    });
    let Some(start) = matching_effect else {
        return facts.to_vec();
    };
    let end = facts[start + 1..]
        .iter()
        .position(|fact| is_memory_effect_proposition(fact.proposition()))
        .map(|offset| start + 1 + offset)
        .unwrap_or(facts.len());
    facts[start..end].to_vec()
}

fn is_memory_effect_proposition(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. } | Proposition::CMemoryEffectSummary { .. }
    )
}

fn is_implicit_fact_transport_context(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
    )
}

fn resource_is_direct_observed_core(
    required: &ResourceClause,
    established: &[ResourceClause],
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<bool, ClickError> {
    for parent in established {
        let ResourceClause::Declared {
            kind: ResourceKind::Composite,
            name,
            ..
        } = parent
        else {
            continue;
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_argument_substitutions(definition, parent, claim_label, tactic_index)?;
        for child in body.contains() {
            let child = instantiate_resource_clause(child, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate observed child of `{name}`: {message}"
                ))
            })?;
            let core = match child {
                ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
                    ResourceClause::Read(segment)
                }
                ResourceClause::Declared {
                    kind,
                    name,
                    arguments,
                    parameter_types,
                    ..
                } => ResourceClause::Declared {
                    access: ResourceAccessMode::View,
                    kind,
                    name,
                    arguments,
                    parameter_types,
                },
            };
            if &core == required {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
fn execute_branch_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    requested_branch: Option<bool>,
    certified_prerequisites: &[PropositionDerivation],
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    branch_step_policy: BranchStepPolicy,
) -> Result<bool, ClickError> {
    let tactic_name = match requested_branch {
        Some(true) => "execute_then_step",
        Some(false) => "execute_else_step",
        None if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) => "step",
        None => "execute_step",
    };
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    let assertion_prefix_count =
        source_assertion_prefix_count(function_block, statement_index, None);
    let (execution_start_state, mut current_state, assertion_prefix, statement, remaining) =
        next_top_level_statement_from_execution_point(
            replay,
            state,
            function,
            arguments,
            assertion_prefix_count,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    let CStatement::If {
        condition,
        then_branch,
        else_branch,
    } = statement
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires the next C statement to be an `if`"
        )));
    };
    let SourceStatementKind::If {
        then_statement_index,
        else_statement_index,
    } = source_region.kind
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` found a C `if` outside its source region"
        )));
    };

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    if let Some(assertion_prefix) = assertion_prefix {
        let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
        let (transitions, _) = certified_statement_transitions(
            &current_state,
            available_pure_facts,
            &assertion_prefix,
            function_environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut replay.next_opaque_call,
            &mut replay.next_verification_variable,
            prerequisite_policy,
            fact_transport_policy,
            certified_prerequisites,
        )?;
        let [transition] = transitions.as_slice() else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` assertion prefix requires exactly one successor, got {}",
                transitions.len()
            )));
        };
        let CStatementOutcome::Normal(next_state) = &transition.outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` assertion prefix did not complete normally"
            )));
        };
        current_state = next_state.clone();
        *available_pure_facts = transition.pure_facts.clone();
    }
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        certified_prerequisites,
        true,
    )?;
    let condition_was_proven = condition_transitions.len() == 1;
    if matches!(branch_step_policy, BranchStepPolicy::RequireProven)
        && condition_transitions.len() != 1
    {
        let expected = requested_branch.map_or("one exact truth value", |take_then| {
            if take_then { "true" } else { "false" }
        });
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove that the next C `if` condition `{}` is {expected}; got {} feasible condition paths\n  condition path facts: {:?}\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            condition_transitions
                .iter()
                .map(|transition| &transition.path_facts)
                .collect::<Vec<_>>(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let condition_transition = match branch_step_policy {
        BranchStepPolicy::RequireProven => condition_transitions
            .into_iter()
            .next()
            .expect("one condition transition was required"),
        BranchStepPolicy::Explore => {
            let requested_branch = requested_branch.expect("branch exploration selects an arm");
            let Some(transition) = condition_transitions
                .into_iter()
                .find(|transition| transition.is_true == requested_branch)
            else {
                return Ok(false);
            };
            transition
        }
    };
    let selected_then = condition_transition.is_true;
    if requested_branch.is_some_and(|take_then| selected_then != take_then) {
        let actual = if selected_then { "then" } else { "else" };
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requested the {} branch, but current pure facts prove the {actual} branch",
            if requested_branch == Some(true) {
                "then"
            } else {
                "else"
            }
        )));
    }

    if matches!(branch_step_policy, BranchStepPolicy::Explore)
        && !condition_was_proven
        && matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
    {
        let occurrence = replay.next_path_choice;
        replay.next_path_choice += 1;
        replay
            .planned_tactics
            .push(ProofTactic::CertifiedPathAssumption {
                occurrence,
                condition: surface_c_condition(&condition),
                value: condition_transition.is_true,
                facts: condition_transition.path_facts.clone(),
                theorem: condition_transition.theorem.clone(),
            });
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_condition_transition_certificate(
            replay,
            &condition_transition,
            condition_was_proven || matches!(branch_step_policy, BranchStepPolicy::RequireProven),
        );
    }
    *available_pure_facts = condition_transition.pure_facts;
    let selected_branch = if selected_then {
        *then_branch
    } else {
        *else_branch
    };
    replay
        .frontier
        .continuations
        .push(ProofExecutionContinuation {
            remaining,
            next_statement_index: source_region.continuation_node,
            kind: ProofExecutionContinuationKind::Branch { statement_index },
        });
    replay.frontier.next_statement_index = if selected_then {
        then_statement_index
    } else {
        else_statement_index
    };
    replay.frontier.execution_start_state = Some(execution_start_state);
    replay.frontier.point = ProofExecutionPoint::StatementEntry {
        remaining: selected_branch,
    };
    *state = current_state;
    record_current_statement_entry(
        replay,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn execute_concrete_loop_head_step(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    certified_prerequisites: &[PropositionDerivation],
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    statement_index: usize,
    loop_index: usize,
    continuation_node: usize,
    execution_start_state: CState,
    mut current_state: CState,
    assertion_prefix: Option<CStatement>,
    loop_statement: CStatement,
    remaining: Option<CStatement>,
) -> Result<(), ClickError> {
    replay.concrete_loop_execution = true;
    let CStatement::While {
        condition, body, ..
    } = loop_statement.clone()
    else {
        unreachable!("concrete loop stepping requires a while statement");
    };

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    record_loop_program_point_state(
        replay,
        function_block,
        loop_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );

    if let Some(assertion_prefix) = assertion_prefix {
        let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
        let (transitions, _) = certified_statement_transitions(
            &current_state,
            available_pure_facts,
            &assertion_prefix,
            function_environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut replay.next_opaque_call,
            &mut replay.next_verification_variable,
            prerequisite_policy,
            fact_transport_policy,
            certified_prerequisites,
        )?;
        let [transition] = transitions.as_slice() else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` loop assertion prefix requires exactly one successor, got {}",
                transitions.len()
            )));
        };
        let CStatementOutcome::Normal(next_state) = &transition.outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` loop assertion prefix did not complete normally"
            )));
        };
        append_execution_effect_facts(&mut replay.effect_facts, &transition.execution_facts);
        current_state = next_state.clone();
        *available_pure_facts = transition.pure_facts.clone();
    }

    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        certified_prerequisites,
        true,
    )?;
    if condition_transitions.len() != 1 {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove one exact truth value for loop({loop_index}) condition `{}`; got {} feasible condition paths\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let condition_transition = condition_transitions
        .into_iter()
        .next()
        .expect("one condition transition was required");
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_condition_transition_certificate(replay, &condition_transition, true);
    }
    *available_pure_facts = condition_transition.pure_facts;
    replay.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state.clone();

    if condition_transition.is_true {
        let loop_head = match remaining {
            Some(remaining) => c_seq(loop_statement, remaining),
            None => loop_statement,
        };
        replay
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: Some(loop_head),
                next_statement_index: statement_index,
                kind: ProofExecutionContinuationKind::LoopIteration,
            });
        replay.frontier.next_statement_index = replay
            .source_layout
            .loop_body_entry(loop_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source body of loop({loop_index})"
                ))
            })?;
        replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining: *body };
        record_statement_program_point_state(
            replay,
            function_block,
            replay.frontier.next_statement_index,
            ProgramPointKind::Entry,
            current_state,
        );
        return Ok(());
    }

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    record_loop_program_point_state(
        replay,
        function_block,
        loop_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    let next = if let Some(remaining) = remaining {
        replay.frontier.next_statement_index = continuation_node;
        Some(remaining)
    } else {
        resume_after_completed_region(replay, function_block, &current_state)
    };
    let Some(remaining) = next else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
        )));
    };
    replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
    record_statement_program_point_state(
        replay,
        function_block,
        replay.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn next_top_level_statement_from_execution_point(
    replay: &TacticReplayState,
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assertion_prefix_count: usize,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<NextTopLevelStatement, ClickError> {
    match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => {
            let execution_start_state = state.clone();
            let current_state = c_function_entry_state(&execution_start_state, function, arguments)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                    ))
                })?;
            let (assertion_prefix, statement, remaining) = split_next_source_operation(
                function.body(),
                assertion_prefix_count,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                ))
            })?;
            Ok((
                execution_start_state,
                current_state,
                assertion_prefix,
                statement,
                remaining,
            ))
        }
        ProofExecutionPoint::StatementEntry { remaining } => {
            let execution_start_state = replay
                .frontier
                .execution_start_state
                .clone()
                .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` has no execution start state"
                ))
            })?;
            let (assertion_prefix, statement, remaining) = split_next_source_operation(
                remaining,
                assertion_prefix_count,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                ))
            })?;
            Ok((
                execution_start_state,
                state.clone(),
                assertion_prefix,
                statement,
                remaining,
            ))
        }
        ProofExecutionPoint::FunctionExit { .. } => Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        ))),
    }
}

fn record_loop_program_point_state(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    loop_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    replay.program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind,
        },
        state.clone(),
    );
    for label in function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .filter_map(StructuralClause::label)
    {
        replay.program_point_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind,
            },
            state.clone(),
        );
    }
}

fn record_statement_program_point_state(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    statement_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    replay.program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Statement(statement_index),
            kind,
        },
        state.clone(),
    );
    for label in function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Statement(statement_index))
        .filter_map(StructuralClause::label)
    {
        replay.program_point_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind,
            },
            state.clone(),
        );
    }
}

fn replay_certified_statement_transition(
    evidence: &CertifiedStatementReplay,
    current_state: &CState,
    statement: &CStatement,
    available_pure_facts: &[Proposition],
    context_label: &str,
) -> Result<CertifiedStatementTransition, ClickError> {
    let mut replay_facts = available_pure_facts.to_vec();
    for fact in evidence
        .transition
        .execution_facts
        .iter()
        .filter(|fact| fact.is_certified())
    {
        if !replay_facts.contains(fact.proposition()) {
            replay_facts.push(fact.proposition().clone());
        }
    }
    let mut proposition = evidence.transition.theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        let certified = exact_fact_is_available(premise, available_pure_facts)
            || materialization_equivalent_available_fact(premise, available_pure_facts).is_some()
            || matches!(normalize_proposition(premise), SimpProposition::True)
            || evidence
                .transition
                .execution_facts
                .iter()
                .any(|fact| fact.is_certified() && fact.proposition() == premise.as_ref())
            || evidence
                .transition
                .prerequisite_derivations
                .iter()
                .any(|derivation| {
                    derivation.conclusion() == premise.as_ref()
                        && derivation_replays_with_materialized_context(derivation, &replay_facts)
                });
        if !certified {
            return Err(ClickError::new(format!(
                "{context_label} certificate is missing prerequisite {premise:?}"
            )));
        }
        proposition = body;
    }
    let Proposition::CStatementExecutes {
        state: theorem_state,
        statement: theorem_statement,
        outcome,
    } = proposition
    else {
        return Err(ClickError::new(format!(
            "{context_label} certificate has an unexpected theorem body: {proposition:?}"
        )));
    };
    if theorem_state != current_state || theorem_statement != statement {
        return Err(ClickError::new(format!(
            "{context_label} certificate does not match the current statement execution"
        )));
    }
    if outcome != &evidence.transition.outcome {
        return Err(ClickError::new(format!(
            "{context_label} certificate outcome does not match its execution theorem"
        )));
    }

    let mut transition = evidence.transition.clone();
    transition.pure_facts = available_pure_facts.to_vec();
    for fact in &transition.path_facts {
        if !transition.pure_facts.contains(fact) {
            transition.pure_facts.push(fact.clone());
        }
    }
    let internal_transports = transition
        .fact_transports
        .iter()
        .filter(|transport| transport.statement_local)
        .collect::<Vec<_>>();
    for transport in &internal_transports {
        if !exact_fact_is_available(&transport.source, &transition.pure_facts) {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport is missing exact statement-produced source {:?}",
                transport.source
            )));
        }
        let Proposition::Implies(theorem_source, theorem_target) = transport.theorem.proposition()
        else {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport theorem is not an implication"
            )));
        };
        if theorem_source.as_ref() != &transport.source
            || theorem_target.as_ref() != &transport.target
        {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport theorem does not match its source and target"
            )));
        }
    }
    let internal_sources = internal_transports
        .iter()
        .map(|transport| &transport.source)
        .collect::<Vec<_>>();
    transition
        .pure_facts
        .retain(|fact| !internal_sources.contains(&fact));
    for transport in internal_transports {
        if !transition.pure_facts.contains(&transport.target) {
            transition.pure_facts.push(transport.target.clone());
        }
    }
    transition.fact_transports.clear();
    Ok(transition)
}

fn surface_with_source_site(
    surface: &ClickProposition,
    point: &ProgramPointRef,
) -> Result<ClickProposition, ClickError> {
    if matches!(
        surface,
        ClickProposition::Loadable { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
    ) {
        return Ok(ClickProposition::At {
            selector: VisitSelector::ProgramPoint(point.clone()),
            proposition: Box::new(surface.clone()),
        });
    }
    let expression_at_source = |expression: &ContractExpression| {
        if matches!(expression, ContractExpression::Old(_)) {
            expression.clone()
        } else {
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(point.clone()),
                expression: Box::new(match expression {
                    ContractExpression::At { expression, .. } => expression.as_ref().clone(),
                    expression => expression.clone(),
                }),
            }
        }
    };
    fn annotate(
        proposition: &ClickProposition,
        expression_at_source: &impl Fn(&ContractExpression) -> ContractExpression,
    ) -> ClickProposition {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: expression_at_source(left),
                operator: *operator,
                right: expression_at_source(right),
            },
            ClickProposition::Defined { expression } => ClickProposition::Defined {
                expression: expression_at_source(expression),
            },
            ClickProposition::At { .. } => proposition.clone(),
            ClickProposition::And(left, right) => ClickProposition::And(
                Box::new(annotate(left, expression_at_source)),
                Box::new(annotate(right, expression_at_source)),
            ),
            ClickProposition::Or(left, right) => ClickProposition::Or(
                Box::new(annotate(left, expression_at_source)),
                Box::new(annotate(right, expression_at_source)),
            ),
            ClickProposition::Not(body) => {
                ClickProposition::Not(Box::new(annotate(body, expression_at_source)))
            }
            ClickProposition::Implies(left, right) => ClickProposition::Implies(
                Box::new(annotate(left, expression_at_source)),
                Box::new(annotate(right, expression_at_source)),
            ),
            ClickProposition::ForAll { c_type, name, body } => ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_source)),
            },
            ClickProposition::Exists { c_type, name, body } => ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_source)),
            },
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAll {
                start: expression_at_source(start),
                end: expression_at_source(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_source)),
            },
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAny {
                start: expression_at_source(start),
                end: expression_at_source(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_source)),
            },
            ClickProposition::PredicateCall { name, arguments } => {
                ClickProposition::PredicateCall {
                    name: name.clone(),
                    arguments: arguments.iter().map(expression_at_source).collect(),
                }
            }
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => proposition.clone(),
        }
    }
    Ok(annotate(surface, &expression_at_source))
}

fn predicate_call_source_site(surface: &ClickProposition) -> Option<ProgramPointRef> {
    let ClickProposition::PredicateCall { arguments, .. } = surface else {
        return None;
    };
    arguments.iter().find_map(|argument| {
        let ContractExpression::At {
            selector: VisitSelector::ProgramPoint(point),
            ..
        } = argument
        else {
            return None;
        };
        Some(point.clone())
    })
}

#[allow(clippy::too_many_arguments)]
fn execute_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    _assumptions: &Assumptions,
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    certified_prerequisites: &[PropositionDerivation],
    certified_replay: Option<&CertifiedStatementReplay>,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
) -> Result<(), ClickError> {
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    if matches!(source_region.kind, SourceStatementKind::If { .. }) {
        let entered = execute_branch_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            function_environment,
            claim_label,
            tactic_index,
            None,
            certified_prerequisites,
            prerequisite_policy,
            fact_transport_policy,
            BranchStepPolicy::RequireProven,
        )?;
        debug_assert!(entered);
        return Ok(());
    }
    let loop_index = match source_region.kind {
        SourceStatementKind::Loop { loop_index } => Some(loop_index),
        SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
    };
    let assertion_prefix_count =
        source_assertion_prefix_count(function_block, statement_index, loop_index);
    let (execution_start_state, current_state, assertion_prefix, source_statement, remaining) =
        next_top_level_statement_from_execution_point(
            replay,
            state,
            function,
            arguments,
            assertion_prefix_count,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    if matches!(source_statement, CStatement::While { .. }) && loop_index.is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source loop at statement({statement_index})"
        )));
    }
    if let (Some(loop_index), CStatement::While { .. }) = (loop_index, &source_statement)
        && matches!(loop_step_policy, LoopStepPolicy::EnterBody)
    {
        return execute_concrete_loop_head_step(
            replay,
            state,
            available_pure_facts,
            function_block,
            parameters,
            arguments,
            function_environment,
            claim_label,
            tactic_index,
            tactic_name,
            certified_prerequisites,
            prerequisite_policy,
            fact_transport_policy,
            statement_index,
            loop_index,
            source_region.continuation_node,
            execution_start_state,
            current_state,
            assertion_prefix,
            source_statement,
            remaining,
        );
    }
    let step_statement = assertion_prefix
        .map(|prefix| c_seq(prefix, source_statement.clone()))
        .unwrap_or(source_statement);

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    if let Some(loop_index) = loop_index {
        record_loop_program_point_state(
            replay,
            function_block,
            loop_index,
            ProgramPointKind::Entry,
            current_state.clone(),
        );
    }
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let direct_transition = certified_replay
        .map(|evidence| {
            replay_certified_statement_transition(
                evidence,
                &current_state,
                &step_statement,
                available_pure_facts,
                &transition_label,
            )
        })
        .transpose()?;
    let transitions = if let Some(transition) = direct_transition {
        replay.next_opaque_call = certified_replay
            .expect("a direct transition requires replay evidence")
            .next_opaque_call;
        replay.next_verification_variable = certified_replay
            .expect("a direct transition requires replay evidence")
            .next_verification_variable;
        vec![transition]
    } else {
        certified_statement_transitions(
            &current_state,
            available_pure_facts,
            &step_statement,
            function_environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut replay.next_opaque_call,
            &mut replay.next_verification_variable,
            prerequisite_policy,
            fact_transport_policy,
            certified_prerequisites,
        )?
        .0
    };
    if transitions.len() != 1 {
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
            let safe = transitions
                .iter()
                .filter(|transition| {
                    matches!(
                        transition.outcome,
                        CStatementOutcome::Normal(_) | CStatementOutcome::Return { .. }
                    )
                })
                .collect::<Vec<_>>();
            if let [safe] = safe.as_slice()
                && let Some(required) = safe
                    .pure_facts
                    .iter()
                    .find(|fact| !exact_fact_is_available(fact, available_pure_facts))
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` is missing exact prerequisite needed to select the safe statement transition: {required:?}"
                )));
            }
        }
        if let Some(kind) = transitions
            .iter()
            .find_map(|transition| match &transition.outcome {
                CStatementOutcome::UndefinedBehavior(kind) => Some(kind.clone()),
                _ => None,
            })
        {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            )));
        }
        if let Some(error) = transitions
            .iter()
            .find_map(|transition| match &transition.outcome {
                CStatementOutcome::RuntimeError(error) => Some(error),
                _ => None,
            })
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced runtime error: {}\n{}",
                describe_runtime_error(error, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            )));
        }
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires exactly one statement successor for {step_statement:?}, got {}\n{}",
            transitions.len(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let transition = transitions
        .into_iter()
        .next()
        .expect("one statement transition was required");
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(loop_index) = loop_index
        && matches!(transition.outcome, CStatementOutcome::Normal(_))
        && let Some(loop_clause) = function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        // The verified loop rule exports its effect summaries first, followed
        // by one lowered fact for each invariant check in declaration order,
        // followed by facts from the false loop-condition path. Preserve that
        // structural association instead of searching the ambient context for
        // a proposition that happens to match.
        let mut invariant_targets = transition.pure_facts.iter().filter(|fact| {
            !available_pure_facts.contains(fact)
                && !matches!(
                    fact,
                    Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CMemoryMutatesOnly { .. }
                )
        });
        let mut mapped_invariants = Vec::new();
        for surface in loop_clause
            .items()
            .iter()
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .filter_map(StructuralItem::proposition)
        {
            let target = if let Some((_, target)) = mapped_invariants
                .iter()
                .find(|(mapped_surface, _)| *mapped_surface == surface)
            {
                *target
            } else {
                invariant_targets.next().ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: verified loop summary omitted an exported fact for an invariant"
                    ))
                })?
            };
            mapped_invariants.push((surface, target));
            let exit_point = ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            };
            let exit_surface = surface_with_source_site(surface, &exit_point)?;
            replay
                .surface_propositions
                .record_lowering(&exit_surface, target)?;
        }
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_statement_transition_certificate(
            replay,
            &transition,
            if loop_index.is_some() {
                loop_step_policy
            } else {
                LoopStepPolicy::EnterBody
            },
        );
    }
    let execution_pure_facts = transition.execution_facts;
    append_execution_effect_facts(&mut replay.effect_facts, &execution_pure_facts);
    let transition_obligations = transition.obligations;
    let successor_pure_facts = transition.pure_facts;
    let outcome = transition.outcome;
    if let Some(statement_exit_state) = match &outcome {
        CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
            Some(state.clone())
        }
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => None,
    } {
        record_statement_program_point_state(
            replay,
            function_block,
            statement_index,
            ProgramPointKind::Exit,
            statement_exit_state,
        );
        if let Some(loop_index) = loop_index {
            record_loop_program_point_state(
                replay,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                match &outcome {
                    CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
                        state.clone()
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => unreachable!(),
                },
            );
        }
    }

    match outcome {
        CStatementOutcome::Normal(next_state) => {
            let remaining = if let Some(remaining) = remaining {
                replay.frontier.next_statement_index = source_region.continuation_node;
                remaining
            } else if let Some(remaining) =
                resume_after_completed_region(replay, function_block, &next_state)
            {
                remaining
            } else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                )));
            };
            *available_pure_facts = successor_pure_facts;
            replay.frontier.execution_start_state = Some(execution_start_state);
            replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
            *state = next_state.clone();
            record_statement_program_point_state(
                replay,
                function_block,
                replay.frontier.next_statement_index,
                ProgramPointKind::Entry,
                next_state,
            );
        }
        CStatementOutcome::Return { .. } => {
            if let CStatementOutcome::Return {
                state: return_state,
                ..
            } = &outcome
            {
                record_completed_continuation_exits(replay, function_block, return_state);
            }
            let return_assumptions = assumptions_from_propositions(&successor_pure_facts);
            let (outcome, obligations) = c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                outcome,
                transition_obligations,
                &return_assumptions,
            );
            let mut completed_execution_facts = execution_pure_facts;
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
            let completed = c_function_execution_candidates_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                vec![(outcome, completed_execution_facts, obligations)],
            );
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            replay.frontier.next_statement_index = source_region.continuation_node;
            *state = replay_state;
        }
        CStatementOutcome::UndefinedBehavior(kind) => {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
        CStatementOutcome::RuntimeError(error) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced runtime error: {}\n{}",
                describe_runtime_error(&error, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
    }
    Ok(())
}

fn resume_after_completed_region(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    state: &CState,
) -> Option<CStatement> {
    while let Some(continuation) = replay.frontier.continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            record_statement_program_point_state(
                replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
        replay.frontier.next_statement_index = continuation.next_statement_index;
        if let Some(remaining) = continuation.remaining {
            return Some(remaining);
        }
    }
    None
}

fn record_completed_continuation_exits(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    state: &CState,
) {
    while let Some(continuation) = replay.frontier.continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            record_statement_program_point_state(
                replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn record_current_statement_entry(
    replay: &mut TacticReplayState,
    state: &CState,
    function_block: &FunctionBlock,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    let current_state = match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => c_function_entry_state(state, function, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                ))
            })?,
        ProofExecutionPoint::StatementEntry { .. } => state.clone(),
        ProofExecutionPoint::FunctionExit { .. } => return Ok(()),
    };
    record_statement_program_point_state(
        replay,
        function_block,
        replay.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

const BOUNDED_EXECUTE_STEP_LIMIT: usize = 10_000;

#[derive(Clone)]
struct BoundedProofFrontier {
    replay: TacticReplayState,
    state: CState,
    pure_facts: Vec<Proposition>,
}

#[allow(clippy::too_many_arguments)]
fn bounded_execute_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<(), ClickError> {
    let mut pending = vec![BoundedProofFrontier {
        replay: replay.clone(),
        state: state.clone(),
        pure_facts: available_pure_facts.clone(),
    }];
    let mut completed = Vec::new();
    let mut executed_steps = 0;

    while let Some(mut frontier) = pending.pop() {
        if frontier.replay.is_at_function_exit() {
            completed.push(frontier);
            continue;
        }
        if executed_steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `bounded_execute` exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget at statement({})",
                frontier.replay.frontier.next_statement_index
            )));
        }
        executed_steps += 1;

        let source_region = frontier
            .replay
            .source_layout
            .statement(frontier.replay.frontier.next_statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `bounded_execute` could not resolve source statement({})",
                    frontier.replay.frontier.next_statement_index
                ))
            })?;
        if matches!(source_region.kind, SourceStatementKind::If { .. }) {
            for take_then in [false, true] {
                let mut branch = frontier.clone();
                let entered = execute_branch_step_from_execution_point(
                    &mut branch.replay,
                    &mut branch.state,
                    &mut branch.pure_facts,
                    function_block,
                    function,
                    parameters,
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                    Some(take_then),
                    &[],
                    prerequisite_policy,
                    StatementFactTransportPolicy::Automatic,
                    BranchStepPolicy::Explore,
                )?;
                if entered {
                    pending.push(branch);
                }
            }
            continue;
        }

        let assumptions = assumptions_from_propositions(&frontier.pure_facts);
        execute_step_from_execution_point(
            &mut frontier.replay,
            &mut frontier.state,
            &mut frontier.pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "bounded_execute",
            &[],
            None,
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `bounded_execute` failed after {executed_steps} small execution steps: {}",
                error.message()
            ))
        })?;
        pending.push(frontier);
    }

    let alternatives = if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        Some(
            completed
                .iter()
                .map(|frontier| {
                    ProofReplayPlan::from_planned_tactics(&frontier.replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `bounded_execute` path planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
    } else {
        None
    };
    merge_bounded_execution_frontiers(
        replay,
        state,
        available_pure_facts,
        function,
        arguments,
        completed,
        claim_label,
        tactic_index,
    )?;
    if let Some(alternatives) = alternatives {
        replay.planned_tactics = vec![ProofTactic::CertifiedAlternatives(alternatives)];
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn merge_bounded_execution_frontiers(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function: &CFunction,
    arguments: &[CExpression],
    mut completed: Vec<BoundedProofFrontier>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `bounded_execute` produced no complete execution paths"
        )));
    }

    let execution_start_state = completed[0]
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `bounded_execute` has no execution start state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.pure_facts.contains(fact))
    });
    let mut common_program_points = completed[0].replay.program_point_states.clone();
    common_program_points.retain(|point, point_state| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.replay.program_point_states.get(point) == Some(point_state))
    });

    let mut paths = Vec::new();
    for frontier in &completed {
        let execution = frontier
            .replay
            .execution()
            .expect("completed bounded frontier should have an execution");
        for path in execution.paths() {
            let mut facts = path.execution_facts();
            for fact in &frontier.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            paths.push((path.outcome().clone(), facts, path.obligations().to_vec()));
        }
    }
    let execution = c_function_execution_candidates_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        paths,
    );

    let mut merged = completed.remove(0);
    merged.replay.program_point_states = common_program_points;
    merged.replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    merged.state = execution_start_state;
    merged.pure_facts = common_pure_facts;
    *replay = merged.replay;
    *state = merged.state;
    *available_pure_facts = merged.pure_facts;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_rest_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    loop {
        let assertion_prefix_count = replay
            .source_layout
            .statement(replay.frontier.next_statement_index)
            .map(|region| {
                let loop_index = match region.kind {
                    SourceStatementKind::Loop { loop_index } => Some(loop_index),
                    SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                };
                source_assertion_prefix_count(
                    function_block,
                    replay.frontier.next_statement_index,
                    loop_index,
                )
            })
            .unwrap_or(0);
        let can_execute_one_step = match &replay.frontier.point {
            ProofExecutionPoint::FunctionEntry => {
                split_next_execution_step(function.body(), assertion_prefix_count).is_ok()
            }
            ProofExecutionPoint::StatementEntry { remaining } => {
                split_next_execution_step(remaining, assertion_prefix_count).is_ok()
            }
            ProofExecutionPoint::FunctionExit { .. } => return Ok(()),
        };
        if !can_execute_one_step {
            break;
        }

        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute_rest",
            &[],
            None,
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
        )?;
    }

    if !replay.is_at_function_exit() {
        bounded_execute_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            function_environment,
            claim_label,
            tactic_index,
            StatementPrerequisitePolicy::Planning,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_until_statement(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    statement_index: usize,
    claim_label: &str,
    tactic_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<(), ClickError> {
    if replay.source_layout.statement(statement_index).is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: function has no source statement({statement_index}); it contains {} statement regions",
            replay.source_layout.statement_count()
        )));
    }

    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot run after execution already reached function exit"
        )));
    }
    if statement_index < replay.frontier.next_statement_index {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot move backward from statement({})",
            replay.frontier.next_statement_index
        )));
    }

    while replay.frontier.next_statement_index != statement_index {
        let region_start = replay.frontier.next_statement_index;
        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute_until",
            &[],
            None,
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
        )?;
        if replay.is_at_function_exit() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` reached function exit before its target"
            )));
        }
        if replay.frontier.next_statement_index > statement_index {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` target is not reachable from the current execution path; advancing statement({region_start}) moved the frontier to statement({})",
                replay.frontier.next_statement_index
            )));
        }
    }
    Ok(())
}

fn source_assertion_prefix_count(
    function_block: &FunctionBlock,
    source_node: usize,
    loop_index: Option<usize>,
) -> usize {
    let statement_assertions = function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Statement(source_node))
        .flat_map(StructuralClause::items)
        .filter(|item| item.kind() == StructuralItemKind::Assert)
        .count();
    let loop_assertions = loop_index.map_or(0, |loop_index| {
        function_block
            .structural_clauses()
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Assert)
            .count()
    });
    statement_assertions + loop_assertions
}

fn split_next_execution_step(
    statement: &CStatement,
    assertion_prefix_count: usize,
) -> Result<(CStatement, Option<CStatement>), String> {
    let (assertion_prefix, source_statement, remaining) =
        split_next_source_operation(statement, assertion_prefix_count)?;
    if matches!(source_statement, CStatement::If { .. }) {
        return Err(
            "next statement is an `if`; use `execute_then_step()` or `execute_else_step()`"
                .to_string(),
        );
    }
    let step_statement = assertion_prefix
        .map(|prefix| c_seq(prefix, source_statement.clone()))
        .unwrap_or(source_statement);
    Ok((step_statement, remaining))
}

fn split_next_source_operation(
    statement: &CStatement,
    assertion_prefix_count: usize,
) -> Result<(Option<CStatement>, CStatement, Option<CStatement>), String> {
    let mut statements = Vec::new();
    flatten_top_level_sequence(statement, &mut statements)
        .map_err(|message| format!("could not flatten the lowered statement sequence: {message}"))?;
    let source_statement_offset = assertion_prefix_count;
    let Some(source_statement) = statements.get(source_statement_offset) else {
        return Err("lowered statement is missing its source operation".to_string());
    };
    let assertion_prefix = sequence_from_statements(&statements[..source_statement_offset]);
    let remaining = sequence_from_statements(&statements[source_statement_offset + 1..]);
    Ok((assertion_prefix, source_statement.clone(), remaining))
}

fn flatten_top_level_sequence(
    statement: &CStatement,
    statements: &mut Vec<CStatement>,
) -> Result<(), String> {
    match statement {
        CStatement::Seq(first, second) => {
            flatten_top_level_sequence(first, statements)?;
            flatten_top_level_sequence(second, statements)
        }
        statement => {
            statements.push(statement.clone());
            Ok(())
        }
    }
}

fn sequence_from_statements(statements: &[CStatement]) -> Option<CStatement> {
    let (first, rest) = statements.split_first()?;
    Some(rest.iter().cloned().fold(first.clone(), c_seq))
}

fn set_replay_execution(
    replay: &mut TacticReplayState,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    execution_start_state: CState,
    execution: CFunctionExecutionCandidates,
) -> Result<(), ClickError> {
    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        )));
    }
    replay.frontier.execution_start_state = Some(execution_start_state);
    replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    Ok(())
}

fn require_function_exit(
    replay: &TacticReplayState,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    if !replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires execution to reach function exit first"
        )));
    }
    Ok(())
}

fn materialize_folded_composite_resource_cells(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    claim_label: &str,
) -> Result<CState, ClickError> {
    let memory = materialize_folded_composite_resource_memory(
        resource_environment,
        parameters,
        arguments,
        &state,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    Ok(state.with_memory(memory))
}

fn materialize_folded_composite_resource_memory(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Result<CMemory, String> {
    let mut memory = state.memory().clone();
    for resource in state.resources().facts() {
        let (name, resource_arguments) = match resource.resource() {
            CResource::Composite { name, arguments } => (name, arguments),
            CResource::Memory(_) | CResource::Token { .. } => {
                continue;
            }
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_value_substitutions(definition, resource_arguments).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        memory = materialize_composite_resource_memory(
            name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            memory,
        )?;
    }
    Ok(memory)
}

fn project_initial_composite_resource_cores(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &[Proposition],
    claim_label: &str,
    include_owned: bool,
) -> Result<CState, ClickError> {
    let assumptions = assumptions_from_propositions(available_pure_facts);
    for resource in state.resources().facts().to_vec() {
        let (name, resource_arguments) = match resource {
            CResourceFact::View(CResource::Composite { name, arguments }) => (name, arguments),
            CResourceFact::Own(CResource::Composite { name, arguments }) if include_owned => {
                (name, arguments)
            }
            _ => continue,
        };
        let Some(definition) = resource_environment.get(&name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_value_substitutions(definition, &resource_arguments).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` setup failed: could not project composite resource core `{name}`: {message}"
                ))
            })?;
        let (memory, contained_resources) = instantiate_composite_resource_body_resources(
            &name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            state.memory().clone(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not project composite resource core `{name}`: {message}"
            ))
        })?;
        let viewed_contained_resources = contained_resources
            .facts()
            .iter()
            .filter_map(CResourceFact::core)
            .collect::<Vec<_>>();
        let resources = state
            .resources()
            .clone()
            .try_compose_with_facts(viewed_contained_resources, &assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` setup failed: projecting composite resource core `{name}` produced {}",
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        state = state.with_memory(memory).with_resource_context(resources);
    }
    Ok(state)
}

fn project_initial_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let result = CValue::Int32(Bitvector32Term::Constant(0));
    let projected_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        &format!("`{claim_label}` setup"),
    )?;
    project_folded_resource_observable_facts(
        resource_environment,
        parameters,
        arguments,
        state,
        state,
        &result,
        &projected_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))
}

fn project_outcome_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    path_index: usize,
) -> Result<Vec<Proposition>, ClickError> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Ok(available_pure_facts.to_vec());
    };
    let projected_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        &format!("`{claim_label}` path {path_index}"),
    )?;
    project_folded_resource_observable_facts(
        resource_environment,
        parameters,
        arguments,
        pre_state,
        state,
        value,
        &projected_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}: could not project folded resource facts: {message}"
        ))
    })
}

fn project_resource_context_observable_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    resources: &ResourceContext,
    available_pure_facts: &[Proposition],
    context: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut propositions = available_pure_facts.to_vec();
    let facts = resources.observable_facts(&assumptions).map_err(|error| {
        ClickError::new(format!(
            "{context}: {}",
            describe_resource_context_validity_error(error, parameters, arguments)
        ))
    })?;
    for proposition in facts {
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
    Ok(propositions)
}

fn append_state_resource_context_observable_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &mut Vec<Proposition>,
    context: &str,
) -> Result<(), ClickError> {
    *available_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        context,
    )?;
    Ok(())
}

fn project_folded_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, String> {
    let mut propositions = available_pure_facts.to_vec();
    for resource in state.resources().facts() {
        project_held_resource_observable_facts(
            resource_environment,
            resource,
            parameters,
            arguments,
            pre_state,
            state.memory().clone(),
            result,
            &mut propositions,
            predicate_environment,
            click_function_environment,
        )?;
    }
    Ok(propositions)
}

fn observe_composite_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    available_pure_facts: &mut Vec<Proposition>,
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CState, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "observe",
        claim_label,
        tactic_index,
    )?;
    let abstract_resource = lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    if !state
        .resources()
        .satisfies_fact(&abstract_resource, &assumptions)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `observe({})` failed: {}",
            describe_resource_clause(resource),
            describe_missing_resource_fact(
                &abstract_resource,
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let CResource::Composite {
        arguments: resource_arguments,
        ..
    } = abstract_resource.resource()
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `observe` expects a composite resource"
        )));
    };
    let surface_substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    let observation_pre_state = state.clone();
    let (memory, contained_resources) = apply_composite_observation_law(
        definition,
        resource_arguments,
        parameters,
        arguments,
        &state,
        state.memory().clone(),
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not observe `{}`: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let fact_state = observation_pre_state.clone().with_memory(memory.clone());
    record_observed_composite_surface_facts(
        definition,
        resource,
        &surface_substitutions,
        parameters,
        arguments,
        &observation_pre_state,
        &fact_state,
        available_pure_facts,
        surface_propositions,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not record observed `{}` facts: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let viewed_contained_resources = contained_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::core)
        .collect::<Vec<_>>();
    // Holding the folded composite certifies its instantiated body. Observation
    // only adds the body's duplicable cores, so it must not revalidate ownership.
    let resources = state
        .resources()
        .clone()
        .unchecked_with_facts(viewed_contained_resources);
    Ok(state.with_memory(memory).with_resource_context(resources))
}

#[allow(clippy::too_many_arguments)]
fn record_observed_composite_surface_facts(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    available_pure_facts: &[Proposition],
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    let composite_body = definition
        .composite_body()
        .expect("observing a composite resource requires a composite body");
    let parent = lower_resource_clause(resource, parameters, arguments, fact_state.memory())
        .map_err(|error| error.message().to_string())?;
    let parent_subject = resource_clause_subject(resource);
    let mut owned_children = Vec::new();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!(
                    "could not instantiate resource `{}` contained resource: {message}",
                    definition.name()
                )
            })?;
        let lowered = lower_resource_clause(&contained, parameters, arguments, fact_state.memory())
            .map_err(|error| error.message().to_string())?;
        if let Some(child) = lowered.owned_resource() {
            let child_subject = resource_clause_subject(&contained);
            surface_propositions
                .record_lowering(
                    &ClickProposition::Contains {
                        parent: parent_subject.clone(),
                        child: child_subject.clone(),
                    },
                    &Proposition::CResourceContains {
                        parent: parent.resource().clone(),
                        child: child.clone(),
                    },
                )
                .map_err(|error| error.message().to_string())?;
            owned_children.push((child.clone(), child_subject));
        }
        let (ResourceClause::Read(segment) | ResourceClause::Write(segment)) = &contained else {
            continue;
        };
        if let Some(kernel) =
            resource_clause_loadable_prop(&contained, parameters, arguments, fact_state.memory())
                .map_err(|error| error.message().to_string())?
        {
            surface_propositions
                .record_lowering(
                    &ClickProposition::Loadable {
                        segment: segment.clone(),
                    },
                    &kernel,
                )
                .map_err(|error| error.message().to_string())?;
        }
    }
    for left_index in 0..owned_children.len() {
        for (right, right_subject) in &owned_children[left_index + 1..] {
            let (left, left_subject) = &owned_children[left_index];
            surface_propositions
                .record_lowering(
                    &ClickProposition::Separate {
                        left: left_subject.clone(),
                        right: right_subject.clone(),
                    },
                    &Proposition::CResourceSeparate {
                        left: left.clone(),
                        right: right.clone(),
                    },
                )
                .map_err(|error| error.message().to_string())?;
        }
    }
    for fact in composite_body.facts() {
        let surface = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        let kernel = lower_outcome_proposition(
            parameters,
            arguments,
            pre_state,
            fact_state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            &surface,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            format!(
                "could not lower resource `{}` fact `{}`: {message}",
                definition.name(),
                describe_click_proposition(&surface)
            )
        })?;
        surface_propositions
            .record_lowering(&surface, &kernel)
            .map_err(|error| error.message().to_string())?;
    }
    Ok(())
}

fn resource_clause_subject(resource: &ResourceClause) -> ResourceSubject {
    match resource {
        ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
            ResourceSubject::Memory(segment.clone())
        }
        ResourceClause::Declared {
            kind,
            name,
            arguments,
            parameter_types,
            ..
        } => ResourceSubject::Declared {
            kind: *kind,
            name: name.clone(),
            arguments: arguments.clone(),
            parameter_types: parameter_types.clone(),
        },
    }
}

#[allow(clippy::too_many_arguments)]
fn record_initial_composite_surface_facts(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &[Proposition],
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_resources: &mut BTreeSet<String>,
) -> Result<(), String> {
    let ResourceClause::Declared { name, .. } = resource else {
        return Ok(());
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(());
    };
    let Some(composite_body) = definition.composite_body() else {
        return Ok(());
    };
    if !active_resources.insert(name.clone()) {
        return Ok(());
    }
    let result = (|| {
        let substitutions =
            resource_argument_substitutions(definition, resource, "initial resource projection", 0)
                .map_err(|error| error.message().to_string())?;
        record_observed_composite_surface_facts(
            definition,
            resource,
            &substitutions,
            parameters,
            arguments,
            state,
            state,
            available_pure_facts,
            surface_propositions,
            predicate_environment,
            click_function_environment,
        )?;
        for contained in composite_body.contains() {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    format!(
                        "could not instantiate resource `{}` child: {message}",
                        definition.name()
                    )
                })?;
            record_initial_composite_surface_facts(
                resource_environment,
                &contained,
                parameters,
                arguments,
                state,
                available_pure_facts,
                surface_propositions,
                predicate_environment,
                click_function_environment,
                active_resources,
            )?;
        }
        Ok(())
    })();
    active_resources.remove(name);
    result
}

fn project_held_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    memory: CMemory,
    result: &CValue,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CMemory, String> {
    let (name, resource_arguments) = match resource.resource() {
        CResource::Composite { name, arguments } => (name, arguments),
        CResource::Memory(_) | CResource::Token { .. } => {
            return Ok(memory);
        }
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(memory);
    };
    apply_composite_observation_law(
        definition,
        resource_arguments,
        parameters,
        arguments,
        pre_state,
        memory,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map(|(memory, _)| memory)
}

/// Applies the non-consuming observation law declared by a composite body.
/// The kernel algebra handles the folded resource fact itself; Click owns this
/// definitional layer because it requires source-level substitution and fact
/// lowering.
fn apply_composite_observation_law(
    definition: &ResourceDefinition,
    resource_arguments: &[CValue],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    memory: CMemory,
    result: &CValue,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(CMemory, ResourceContext), String> {
    let Some(composite_body) = definition.composite_body() else {
        return Ok((memory, ResourceContext::new()));
    };

    let substitutions =
        resource_value_substitutions(definition, resource_arguments).map_err(|message| {
            format!(
                "could not instantiate resource `{}` facts: {message}",
                definition.name()
            )
        })?;
    let (memory, contained_resources) = instantiate_composite_resource_body_resources(
        definition.name(),
        composite_body,
        &substitutions,
        parameters,
        arguments,
        memory,
    )?;
    let fact_state = pre_state.clone().with_memory(memory.clone());

    append_composite_definition_observable_facts(
        definition,
        composite_body,
        &CResource::Composite {
            name: definition.name().to_string(),
            arguments: resource_arguments.to_vec(),
        },
        &substitutions,
        &contained_resources,
        parameters,
        arguments,
        pre_state,
        &fact_state,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )?;
    Ok((memory, contained_resources))
}

fn append_composite_definition_observable_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    parent_resource: &CResource,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
    propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    append_resource_context_observable_facts(contained_resources, propositions);

    append_composite_resource_relation_facts(parent_resource, contained_resources, propositions);

    append_composite_resource_loadable_facts(
        definition,
        composite_body,
        substitutions,
        parameters,
        arguments,
        fact_state.memory(),
        propositions,
    )?;

    append_composite_resource_declared_facts(
        definition,
        composite_body,
        substitutions,
        contained_resources,
        parameters,
        arguments,
        pre_state,
        fact_state,
        result,
        propositions,
        predicate_environment,
        click_function_environment,
    )
}

fn append_composite_resource_relation_facts(
    parent_resource: &CResource,
    contained_resources: &ResourceContext,
    propositions: &mut Vec<Proposition>,
) {
    let owned_children = contained_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::owned_resource)
        .cloned()
        .collect::<Vec<_>>();
    for child in &owned_children {
        let proposition = Proposition::CResourceContains {
            parent: parent_resource.clone(),
            child: child.clone(),
        };
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
    for i in 0..owned_children.len() {
        for right in &owned_children[i + 1..] {
            let proposition = Proposition::CResourceSeparate {
                left: owned_children[i].clone(),
                right: right.clone(),
            };
            if !propositions.contains(&proposition) {
                propositions.push(proposition);
            }
        }
    }
}

fn append_composite_resource_loadable_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    propositions: &mut Vec<Proposition>,
) -> Result<(), String> {
    for contained in composite_body.contains() {
        let contained = instantiate_resource_clause(contained, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` contained resource for loadability: {message}",
                definition.name()
            )
        })?;
        append_resource_clause_loadable_fact(
            &contained,
            parameters,
            arguments,
            memory,
            propositions,
        )
        .map_err(|error| {
            format!(
                "could not project resource `{}` contained `{}` loadability: {}",
                definition.name(),
                describe_resource_clause(&contained),
                error.message()
            )
        })?;
    }
    Ok(())
}

fn append_resource_clause_loadable_fact(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    propositions: &mut Vec<Proposition>,
) -> Result<(), ClickError> {
    let Some(proposition) = resource_clause_loadable_prop(resource, parameters, arguments, memory)?
    else {
        return Ok(());
    };
    if !propositions.contains(&proposition) {
        propositions.push(proposition);
    }
    Ok(())
}

fn append_lowered_resource_clause_loadable_fact(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    lowered: &CResourceFact,
    state: &CState,
    propositions: &mut Vec<Proposition>,
) {
    let (ResourceClause::Read(segment) | ResourceClause::Write(segment)) = resource else {
        return;
    };
    let Some(range) = lowered
        .memory_view_range()
        .or_else(|| lowered.memory_own_range())
    else {
        return;
    };
    let proposition = memory_range_loadable_prop(
        state.memory(),
        range,
        contract_segment_element_width(parameters, segment),
    );
    if !propositions.contains(&proposition) {
        propositions.push(proposition);
    }
}

fn append_composite_resource_declared_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
    propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    for fact in composite_body.facts() {
        let fact = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        let lowered = lower_outcome_proposition(
            parameters,
            arguments,
            pre_state,
            fact_state,
            result,
            propositions,
            &fact,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            format!(
                "could not lower resource `{}` pure fact `{}`: {message}\n  pure facts: {}\n  resource facts: {}",
                definition.name(),
                describe_click_proposition(&fact),
                describe_pure_facts(propositions),
                describe_resource_facts(contained_resources.facts(), parameters, arguments)
            )
        })?;
        if !propositions.contains(&lowered) {
            propositions.push(lowered);
        }
    }
    Ok(())
}

fn append_resource_context_observable_facts(
    resources: &ResourceContext,
    propositions: &mut Vec<Proposition>,
) {
    let assumptions = assumptions_from_propositions(propositions);
    let facts = resources.observable_facts_assuming_valid(&assumptions);
    for proposition in facts {
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
}

fn describe_resource_context_validity_error(
    error: ResourceContextValidityError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            format!(
                "duplicate resource fact `{}`",
                describe_resource_fact(&resource, parameters, arguments)
            )
        }
        ResourceContextValidityError::OverlappingWriteResources { left, right } => {
            format!(
                "overlapping owned memory resource facts `owns {}` and `owns {}`",
                describe_memory_range(&left, parameters, arguments),
                describe_memory_range(&right, parameters, arguments)
            )
        }
    }
}

fn materialize_composite_resource_memory(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: CMemory,
) -> Result<CMemory, String> {
    let (memory, _) = instantiate_composite_resource_body_resources(
        name,
        composite_body,
        substitutions,
        parameters,
        arguments,
        memory,
    )?;
    Ok(memory)
}

/// Instantiates the resource-state side of a composite definition. The result
/// is provisional until the caller composes it with assumptions and checks
/// validity through `ResourceContext`.
pub(super) fn instantiate_composite_resource_body_resources(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut memory: CMemory,
) -> Result<(CMemory, ResourceContext), String> {
    let mut resources = ResourceContext::new();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        let lowered =
            lower_resource_clause(&contained, parameters, arguments, &memory).map_err(|error| {
                format!(
                    "could not lower resource `{name}` contained `{}`: {}\n  {}",
                    describe_resource_clause(&contained),
                    error.message(),
                    describe_available_facts(&[], resources.facts(), parameters, arguments, &[])
                )
            })?;
        memory = materialize_composite_resource_cells(memory, &contained, &lowered, parameters);
        // This composite-body instantiation path has no fact assumptions yet.
        // Projection/packing paths check composition once assumptions are
        // available.
        resources = resources.unchecked_with_fact(lowered);
    }
    Ok((memory, resources))
}

fn resource_value_substitutions(
    definition: &ResourceDefinition,
    arguments: &[CValue],
) -> Result<BTreeMap<String, ContractExpression>, String> {
    if definition.parameters().len() != arguments.len() {
        return Err(format!(
            "resource `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            (
                parameter.name().to_string(),
                ContractExpression::CFragment(CExpression::Value(argument.clone())),
            )
        })
        .collect())
}

/// Applies the owned-composite equivalence from the folded fact to one
/// instantiated body. This is a definition law, not primitive consumption
/// behavior of the kernel's folded composite fact.
fn unfold_composite_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &mut Vec<Proposition>,
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CState, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "unfold",
        claim_label,
        tactic_index,
    )?;
    let composite_body = definition
        .composite_body()
        .expect("composite_resource_law_definition should require a composite body");
    let substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    let abstract_resource = lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let folded_resources = state
        .resources()
        .clone()
        .without_fact(&abstract_resource, &assumptions);
    let already_unfolded = folded_resources.is_none();
    let resources = if let Some(resources) = folded_resources {
        resources
    } else {
        let mut remaining = state.resources().clone();
        for contained in composite_body.contains() {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not inspect canonical `unfold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let lowered = lower_resource_clause(&contained, parameters, arguments, state.memory())?;
            let Some(next) = remaining.without_fact(&lowered, &assumptions) else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
                    describe_resource_clause(resource),
                    describe_missing_resource_fact(
                        &abstract_resource,
                        available_pure_facts,
                        state.resources().facts(),
                        parameters,
                        arguments,
                        &[]
                    )
                )));
            };
            remaining = next;
        }
        state.resources().clone()
    };
    state = state.with_resource_context(resources);

    if already_unfolded && composite_body.contains().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
            describe_resource_clause(resource),
            describe_missing_resource_fact(
                &abstract_resource,
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                &[]
            )
        )));
    }

    let mut unfolded_facts = Vec::new();
    for contained in composite_body.contains() {
        let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})`: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let lowered = lower_resource_clause(&contained, parameters, arguments, state.memory())?;
        unfolded_facts.push(lowered.clone());
        let memory = materialize_composite_resource_cells(
            state.memory().clone(),
            &contained,
            &lowered,
            parameters,
        );
        let resources = if already_unfolded {
            state.resources().clone()
        } else {
            state
                .resources()
                .clone()
                .try_compose_with_fact(lowered, &assumptions)
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                        describe_resource_clause(resource),
                        describe_resource_context_validity_error(error, parameters, arguments)
                    ))
                })?
        };
        state = state.with_memory(memory).with_resource_context(resources);
        append_resource_clause_loadable_fact(
            &contained,
            parameters,
            arguments,
            state.memory(),
            available_pure_facts,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not project `unfold({})` loadability: {}",
                describe_resource_clause(resource),
                error.message()
            ))
        })?;
    }

    let unfolded_resources = ResourceContext::new().unchecked_with_facts(unfolded_facts);
    append_composite_resource_relation_facts(
        abstract_resource.resource(),
        &unfolded_resources,
        available_pure_facts,
    );

    for fact in composite_body.facts() {
        let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})` fact: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
        let lowered_fact = lower_outcome_proposition(
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            &fact,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower `unfold({})` pure fact `{}`: {message}\n{}",
                describe_resource_clause(resource),
                describe_click_proposition(&fact),
                describe_proof_context(
                    available_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    &[]
                )
            ))
        })?;
        surface_propositions.record_lowering(&fact, &lowered_fact)?;
        available_pure_facts.push(lowered_fact);
    }

    append_state_resource_context_observable_facts(
        parameters,
        arguments,
        &state,
        available_pure_facts,
        &format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})`",
            describe_resource_clause(resource)
        ),
    )?;

    Ok(state)
}

/// Applies the reverse composite definition law after proving the body's pure
/// facts and consuming its immediate contained resource state.
fn fold_composite_resources_on_outcome(
    resource_environment: &ResourceEnvironment,
    resource_folds: &[ResourceClause],
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[ExecutionPureFact],
    available_pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    mut outcome: CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<CFunctionOutcome, ClickError> {
    for resource in resource_folds {
        let definition = composite_resource_law_definition(
            resource_environment,
            resource,
            "fold",
            claim_label,
            path_index,
        )?;
        let composite_body = definition
            .composite_body()
            .expect("composite_resource_law_definition should require a composite body");
        let substitutions =
            resource_argument_substitutions(definition, resource, claim_label, path_index)?;

        for fact in composite_body.facts() {
            let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let program_point_states = ProgramPointStates::new();
            let required = lower_ensure_proposition_goal(
                available_pure_facts,
                &fact,
                parameters,
                arguments,
                pre_state,
                &outcome,
                predicate_environment,
                click_function_environment,
                &program_point_states,
                unfolded_predicates,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: could not lower exact `fold({})` fact: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
            if !exact_fact_is_available(&required, available_pure_facts)
                && !matches!(normalize_proposition(&required), SimpProposition::True)
                // An available fact may spell the same body fact through
                // loads at an earlier snapshot; the bounded derivation
                // prover bridges those spellings deterministically.
                && assumptions_from_propositions(available_pure_facts)
                    .derive_atomic_proposition(&required)
                    .is_none()
            {
                let resources = match &outcome {
                    CFunctionOutcome::Return { state, .. } => state.resources().facts(),
                    _ => pre_state.resources().facts(),
                };
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires an exact body fact: {}",
                    describe_resource_clause(resource),
                    describe_missing_pure_fact(
                        &required,
                        available_pure_facts,
                        resources,
                        parameters,
                        arguments,
                        execution_pure_facts,
                    )
                )));
            }
        }

        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}\n  execution pure facts: {}",
                describe_resource_clause(resource),
                describe_function_outcome(&outcome, parameters, arguments),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        };
        let mut post_state = state;
        // Range spellings in held resource facts embed loads at their
        // creation snapshot; carrying them to the fold point needs the
        // execution's store effect facts alongside the pure facts.
        let mut fold_facts = available_pure_facts.to_vec();
        fold_facts.extend(
            execution_pure_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        let assumptions = assumptions_from_propositions(&fold_facts);
        let mut lowered_contained = Vec::new();
        for contained in composite_body.contains() {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let lowered =
                lower_resource_clause(&contained, parameters, arguments, post_state.memory())?;
            lowered_contained.push(lowered);
        }
        let resources = if let Some(resources) = post_state
            .resources()
            .clone()
            .without_facts(&lowered_contained, &assumptions)
        {
            resources
        } else {
            // Preserve the precise missing-resource diagnostic on the slow
            // failure path.
            let mut diagnostic_resources = post_state.resources().clone();
            for lowered in &lowered_contained {
                let diagnostic_facts = diagnostic_resources.facts().to_vec();
                let Some(resources) = diagnostic_resources.without_fact(lowered, &assumptions)
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` failed: {}",
                        describe_resource_clause(resource),
                        describe_missing_resource_fact(
                            lowered,
                            available_pure_facts,
                            &diagnostic_facts,
                            parameters,
                            arguments,
                            execution_pure_facts
                        )
                    )));
                };
                diagnostic_resources = resources;
            }
            // The batch consumption above refused a body the one-at-a-time
            // walk accepted; report that rather than crashing.
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `fold({})` could not consume the body layer as a whole, though each contained resource is held individually",
                describe_resource_clause(resource)
            )));
        };
        post_state = post_state.with_resource_context(resources);

        let abstract_resource =
            lower_resource_clause(resource, parameters, arguments, post_state.memory())?;
        let resources = post_state
            .resources()
            .clone()
            .try_compose_with_fact(abstract_resource.clone(), &assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` produced {}",
                    describe_resource_clause(resource),
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        post_state = post_state.with_resource_context(resources);
        outcome = CFunctionOutcome::Return {
            value,
            state: post_state,
        };
    }

    Ok(outcome)
}

/// Resolves the source declaration that supplies fold, unfold, and observation
/// laws for a composite resource fact.
fn composite_resource_law_definition<'a>(
    resource_environment: &'a ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    claim_label: &str,
    tactic_index: usize,
) -> Result<&'a ResourceDefinition, ClickError> {
    let ResourceClause::Declared { name, .. } = resource else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects a composite resource"
        )));
    };
    if matches!(action, "fold" | "unfold")
        && !matches!(
            resource,
            ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                ..
            }
        )
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects an owned composite resource"
        )));
    }
    if !matches!(
        resource,
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            ..
        }
    ) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects composite resource `{name}` to have a body"
        )));
    }
    let definition = resource_environment.get(name).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown resource `{name}`"
        ))
    })?;
    if definition.composite_body().is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects composite resource `{name}` to have a body"
        )));
    }
    Ok(definition)
}

fn resource_argument_substitutions(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    let ResourceClause::Declared {
        name,
        arguments,
        parameter_types,
        ..
    } = resource
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: expected declared resource"
        )));
    };
    if definition.name() != name {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource definition mismatch for `{name}`"
        )));
    }
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource `{name}` expects {} argument(s), got {}",
            definition.parameters().len(),
            arguments.len()
        )));
    }
    let expected_types = definition
        .parameters()
        .iter()
        .map(FunctionParameter::c_type)
        .collect::<Vec<_>>();
    if parameter_types != &expected_types {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource `{name}` has malformed argument type metadata"
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

fn instantiate_resource_clause(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

fn instantiate_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(base, substitutions)?,
            start: substitute_contract_expression(start, substitutions)?,
            end: substitute_contract_expression(end, substitutions)?,
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
        surface,
    })
}

fn materialize_composite_resource_cells(
    mut memory: CMemory,
    resource_clause: &ResourceClause,
    lowered: &CResourceFact,
    parameters: &[syntax::C0Parameter],
) -> CMemory {
    let Some((segment, range)) = (match resource_clause {
        ResourceClause::Read(segment) => lowered.memory_view_range().map(|range| (segment, range)),
        ResourceClause::Write(segment) => lowered.memory_own_range().map(|range| (segment, range)),
        ResourceClause::Declared { .. } => None,
    }) else {
        return memory;
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (range.start(), range.end())
    else {
        return memory;
    };
    if end < start {
        return memory;
    }

    let element_width = contract_segment_element_width(parameters, segment);
    let base_memory = memory.clone();
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            range.base().clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        let load =
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(base_memory.clone()), Box::new(pointer.clone()));
        let value = match element_width {
            1 => CValue::UInt8(load),
            _ => CValue::Int32(load),
        };
        memory = memory.store(pointer, value);
    }
    memory
}

fn resolve_code_region_ref(
    function_block: &FunctionBlock,
    region_ref: &CodeRegionRef,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CodeRegion, ClickError> {
    Ok(match region_ref {
        CodeRegionRef::Function => CodeRegion::Function,
        CodeRegionRef::Loop(index) => CodeRegion::Loop(*index),
        CodeRegionRef::Statement(index) => CodeRegion::Statement(*index),
        CodeRegionRef::Label(label) => *function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.label() == Some(label.as_str()))
            .map(StructuralClause::region)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: unknown code region label `{label}`"
                ))
            })?,
    })
}

fn validate_loop_code_region(
    parsed_function: &syntax::C0Function,
    loop_index: usize,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    if loop_index >= loop_count {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: function has no `loop({loop_index})` code region; it contains {loop_count} loop(s)"
        )));
    }
    Ok(())
}

fn validate_frame_code_region(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    code_region: Option<CodeRegion>,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    match code_region {
        None | Some(CodeRegion::Function) => {
            if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `frame()` proves function-level effect claims; use `frame(loop(N))` or a code region label to use loop effect summaries in an `ensures` proof"
                )));
            }
            Ok(())
        }
        Some(CodeRegion::Loop(loop_index)) => {
            validate_loop_code_region(parsed_function, loop_index, claim_label, tactic_index)?;
            if !function_block.structural_clauses().iter().any(|clause| {
                clause.region() == &CodeRegion::Loop(loop_index)
                    && clause.items().iter().any(StructuralItem::is_effect_kind)
            }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `frame(loop({loop_index}))` needs a loop effect clause such as `mutable` or `immutable`"
                )));
            }
            Ok(())
        }
        Some(CodeRegion::Statement(statement_index)) => {
            let statement_count = count_statements(parsed_function.body());
            if statement_index >= statement_count {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: function has no `statement({statement_index})` code region; it contains {statement_count} statement(s)"
                )));
            }
            Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `frame(statement({statement_index}))` is not supported yet"
            )))
        }
    }
}

fn validate_function_frame_tactic(
    execution: &CFunctionExecutionCandidates,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    requirement_pure_facts: &[Proposition],
) -> Result<(), ClickError> {
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `frame()` had no complete execution path"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `frame()` failed on path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    requirement_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    path.facts()
                )
            )));
        }
        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_effect_claim_exact(
            claim_label,
            path_index,
            &path.execution_facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            path.outcome(),
        )?;
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_effect_claim_exact(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[ExecutionPureFact],
    available_pure_facts: &[Proposition],
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let FunctionClaimRef::Effect(_, effect_clause) = claim else {
        return Err(ClickError::new(format!(
            "`frame()` requires an effect claim for `{claim_label}`"
        )));
    };
    prove_effect_clause_exact(
        claim_label,
        path_index,
        execution_pure_facts,
        available_pure_facts,
        effect_clause.effect(),
        parameters,
        arguments,
        pre_state,
        outcome,
    )
}

fn requirements_with_structural_unfolds(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_block: &FunctionBlock,
    requirement_pure_facts: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    let unfolded_predicates = structural_unfold_tactic_names(function_block);
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        requirement_pure_facts,
    )
}

fn structural_unfold_tactic_names(function_block: &FunctionBlock) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for clause in function_block.structural_clauses() {
        for proof in [clause.initialize_proof(), clause.preserve_proof()]
            .into_iter()
            .flatten()
        {
            for name in proof.unfold_tactic_names() {
                if seen.insert(name.clone()) {
                    names.push(name);
                }
            }
        }
        for item in clause.items() {
            for name in item.proof().unfold_tactic_names() {
                if seen.insert(name.clone()) {
                    names.push(name);
                }
            }
        }
    }
    names
}

fn bounded_execution_tactic_candidates(claim: &FunctionClaimRef<'_>) -> Vec<Vec<ProofTactic>> {
    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            vec![vec![ProofTactic::BoundedExecute, ProofTactic::Simp]]
        }
        FunctionClaimRef::Effect(_, _) => vec![vec![
            ProofTactic::BoundedExecute,
            ProofTactic::ContextualFrame,
        ]],
    }
}

fn auto_loop_verification_tactic_candidates(
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
) -> Vec<Vec<ProofTactic>> {
    let mut base = vec![ProofTactic::ExecuteRest];
    base.extend(
        loop_effect_summary_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofTactic::Frame(Some(CodeRegionRef::Loop(loop_index)))),
    );

    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            let mut simp = base;
            simp.push(ProofTactic::Simp);
            vec![simp]
        }
        FunctionClaimRef::Effect(_, _) => {
            base.push(ProofTactic::ContextualFrame);
            vec![base]
        }
    }
}

fn loop_effect_summary_regions(function_block: &FunctionBlock) -> BTreeSet<usize> {
    function_block
        .structural_clauses()
        .iter()
        .filter_map(|clause| match clause.region() {
            CodeRegion::Loop(index)
                if clause.items().iter().any(StructuralItem::is_effect_kind) =>
            {
                Some(*index)
            }
            _ => None,
        })
        .collect()
}
