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

fn check_atomic_derivation_goal(
    tactic: &ProofTactic,
    target: Proposition,
    premises: Vec<Proposition>,
    goal: &Proposition,
    available: &[Proposition],
) -> Result<(), String> {
    if &target != goal {
        return Err(format!(
            "`{}` target does not match the current goal\n  target: {target:?}\n  goal: {goal:?}",
            tactic_name(tactic)
        ));
    }
    if let Some(missing) = premises.iter().find(|premise| {
        let normalized = normalize_direct_atomic_memory_loads(premise);
        !available
            .iter()
            .any(|available| normalize_direct_atomic_memory_loads(available) == normalized)
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
    let assumptions = assumptions_from_propositions(&normalized_premises);
    let derivation = match tactic {
        ProofTactic::Derive(_) => assumptions
            .derive_atomic_proposition(&normalized_target)
            .or_else(|| assumptions.derive_proposition(&normalized_target)),
        ProofTactic::Calculate(_) => assumptions
            .derive_simp_atomic_proposition(&normalized_target)
            .or_else(|| assumptions.derive_simp_proposition(&normalized_target)),
        _ => return Err("not a derivation tactic".to_string()),
    };
    if derivation.is_none() {
        return Err(format!(
            "`{}` could not check the target from exactly the listed premises: {target:?}",
            tactic_name(tactic)
        ));
    }
    Ok(())
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
                ProofTactic::Derive(ProofDerive {
                    proposition: surface_goal.clone(),
                    premises,
                })
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

    match ensure_clause.proof() {
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
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::Pure,
                proof_tactics: None,
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
        Proof::Tactic(SmartTactic::Simp) => {
            let assumptions = assumptions_from_propositions(&context.requires);
            let certificate = plan_simp_certificate(&goal, &assumptions)
                .ok_or_else(|| ClickError::new(format!("`simp` failed for `{claim_label}`")))?;
            replay_pure_theorem_certificate(
                claim_label,
                &context.requires,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                context,
                &certificate,
            )?;
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::Simp,
                proof_tactics: lower_pure_simp_certificate(
                    theorem,
                    surface_goal,
                    context,
                    &certificate,
                ),
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
        Proof::Tactic(SmartTactic::Frame) => Err(ClickError::new(format!(
            "`frame` is not available in the pure proof for theorem `{claim_label}`"
        ))),
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
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::TacticScript,
                proof_tactics: Some(tactics.to_vec()),
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
    }
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
    certificate: &ProofReplayPlan,
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

        assert_eq!(timing_tactic_class(&have), "simple");
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
        let failing = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple tactic");
        let succeeding = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Normalize])
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
        join_id: usize,
        target: ProgramPointRef,
        assertions: Vec<ProofAssertion>,
        body: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
}

fn build_internal_proof(
    tactics: &[ProofTactic],
    claim_label: &str,
) -> Result<InternalProofNode, ClickError> {
    let mut next_join_id = 0;
    build_internal_proof_at(tactics, claim_label, &mut next_join_id, 0, 0)
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
                join_id,
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
                if !available.contains(&goal) {
                    return Err(ClickError::new(format!(
                        "`assumption` failed for `{claim_label}`: {}",
                        describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                    )));
                }
                closed = true;
            }
            ProofTactic::Normalize => {
                if !matches!(normalize_proposition(&goal), SimpProposition::True) {
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
        if !available.contains(&lowered)
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
        conclusions.push(conclusion);
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

fn initial_claim_context(
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
        ) {
            Ok(mut theorems) => {
                for theorem in &mut theorems {
                    theorem.proof_kind = ProofKind::LoopVerification;
                }
                return Ok(theorems);
            }
            Err(error) => loop_verification_error = Some(error),
        }
    }

    let mut bounded_error = None;
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
        ) {
            Ok(theorems) => return Ok(theorems),
            Err(error) => bounded_error = Some(error),
        }
    }
    Err(loop_verification_error
        .or(bounded_error)
        .expect("auto should attempt at least one certificate candidate"))
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
    )?;
    for theorem in &mut theorems {
        theorem.proof_kind = ProofKind::Simp;
    }
    Ok(theorems)
}

#[derive(Clone, Default)]
struct TacticReplayState {
    frontier: ExecutionFrontier,
    source_layout: SourceExecutionLayout,
    program_point_states: ProgramPointStates,
    frames: BTreeSet<Option<CodeRegionRef>>,
    unfolded_predicates: Vec<String>,
    post_execution_tactics: Vec<(usize, PostExecutionTactic)>,
    case_assumptions: Vec<ReplayCaseAssumption>,
    effect_facts: Vec<ExecutionPureFact>,
    region_proof: bool,
    ordered_finalization: bool,
    grouped_contract: bool,
    next_opaque_call: u64,
    next_verification_variable: u64,
    next_path_choice: usize,
    planned_tactics: Vec<ProofTactic>,
    surface_propositions: SurfacePropositionMap,
    surface_replay: SurfaceReplay,
    deferred_tactic_capture: Option<DeferredTacticCapture>,
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

const TACTIC_EXPANSION_COMPLETE: &str = "internal: selected tactic expansion complete";

struct TacticExpansionProbe {
    function_name: String,
    claim: CProofClaim,
    source_index: usize,
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
    function_name: &str,
    claim: CProofClaim,
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
            function_name: function_name.to_string(),
            claim,
            source_index,
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
        Err(error) if error.message() != TACTIC_EXPANSION_COMPLETE => Err(error),
        Err(_) => Err(ClickError::new(
            "selected tactic completed without recording an expansion",
        )),
        Ok(_) => Err(ClickError::new(format!(
            "function `{function_name}` has no source tactic {source_index} in the selected {claim:?} proof"
        ))),
    }
}

pub(super) fn active_c0_tactic_expansion_request() -> Option<(String, CProofClaim, usize)> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .map(|probe| (probe.function_name.clone(), probe.claim, probe.source_index))
    })
}

fn probe_matches_claim(
    probe: &TacticExpansionProbe,
    function_block: &FunctionBlock,
    claims: &[FunctionClaimRef<'_>],
    grouped_contract: bool,
) -> bool {
    if function_block.signature().name() != probe.function_name {
        return false;
    }
    match probe.claim {
        CProofClaim::Grouped => grouped_contract,
        CProofClaim::Ensure(wanted) if !grouped_contract => matches!(
            claims,
            [FunctionClaimRef::Ensure(found, _)] if *found == wanted
        ),
        CProofClaim::Effect(wanted) if !grouped_contract => matches!(
            claims,
            [FunctionClaimRef::Effect(found, _)] if *found == wanted
        ),
        CProofClaim::Ensure(_) | CProofClaim::Effect(_) => false,
    }
}

fn begin_tactic_expansion_capture(
    function_block: &FunctionBlock,
    claims: &[FunctionClaimRef<'_>],
    source_index: usize,
    _tactic: &ProofTactic,
    replay: &mut TacticReplayState,
) -> bool {
    if SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(std::cell::Cell::get) {
        return false;
    }
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return false;
        };
        if probe.active
            || probe.source_index != source_index
            || !probe_matches_claim(probe, function_block, claims, replay.grouped_contract)
        {
            return false;
        }
        probe.active = true;
        let last_step_entry = replay.surface_replay.last_step_entry.clone();
        replay.surface_replay = SurfaceReplay {
            last_step_entry,
            ..SurfaceReplay::default()
        };
        true
    })
}

fn finish_tactic_expansion_capture(surface_replay: &SurfaceReplay) -> ClickError {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let probe = slot
            .as_mut()
            .expect("finishing a selected tactic requires an active probe");
        probe.result = Some(match &surface_replay.blocker {
            Some(blocker) => Err(format!("could not expand selected tactic: {blocker}")),
            None if surface_replay.tactics.is_empty() => {
                Err("selected tactic produced no standalone surface expansion".to_string())
            }
            None => Ok(surface_replay.tactics.clone()),
        });
    });
    ClickError::new(TACTIC_EXPANSION_COMPLETE)
}

fn tactic_expansion_capture_is_active() -> bool {
    TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow().as_ref().is_some_and(|probe| probe.active))
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
    Choose(ProofChoice),
    Witness(ProofWitness),
    Assumption,
    Normalize,
    Rewrite(ClickProposition),
    Frame,
    CertifiedFrame(Vec<Vec<PropositionDerivation>>),
    Simp,
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
        execution: crate::kernel::SymbolicCExecution,
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

    fn execution(&self) -> Option<&crate::kernel::SymbolicCExecution> {
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
    let has_structural_loops = function_block
        .structural_clauses()
        .iter()
        .any(|clause| matches!(clause.region(), CodeRegion::Loop(_)));
    if !has_structural_loops {
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
    )?;

    let entry_state = c_function_entry_state(&initial_state, &function, &arguments)
        .ok_or_else(|| ClickError::new(format!("`{label}` could not bind function arguments")))?;
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
    let mut next_loop_index = 0;
    let mut verified_loop_rules = Vec::new();
    verify_execution_proofs_forward(
        function.body(),
        vec![ExecutionProofContext {
            state: entry_state,
            pure_facts: requirement_facts,
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
    next_opaque_call: u64,
    next_verification_variable: u64,
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
    available
        .iter()
        .any(|fact| exact_fact_contains_conjunct(fact, required))
}

fn exact_fact_contains_conjunct(fact: &Proposition, required: &Proposition) -> bool {
    fact == required
        || matches!(fact, Proposition::And(left, right)
            if exact_fact_contains_conjunct(left, required)
                || exact_fact_contains_conjunct(right, required))
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

fn minimal_proposition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Option<PropositionDerivation> {
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
            let opposite = Proposition::ConditionIs(condition.clone(), !value);
            assumptions.proves(&opposite)
                || assumptions.derive_simp_proposition(&opposite).is_some()
        }
        Proposition::Not(body) => {
            assumptions.proves(body) || assumptions.derive_simp_proposition(body).is_some()
        }
        fact => {
            let opposite = Proposition::Not(Box::new(fact.clone()));
            assumptions.proves(&opposite)
                || assumptions.derive_simp_proposition(&opposite).is_some()
        }
    }
}

fn assumptions_from_exact_conditions(propositions: &[Proposition]) -> Assumptions {
    fn collect(proposition: &Proposition, conditions: &mut Vec<Proposition>) {
        match proposition {
            Proposition::ConditionIs(_, _) => conditions.push(proposition.clone()),
            Proposition::And(left, right) => {
                collect(left, conditions);
                collect(right, conditions);
            }
            _ => {}
        }
    }

    let mut conditions = Vec::new();
    for proposition in propositions {
        collect(proposition, &mut conditions);
    }
    assumptions_from_propositions(&conditions)
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
    *next_opaque_call = budget.next_opaque_call();
    *next_verification_variable = budget.next_verification_variable();
    certified_transitions_from_execution(
        execution,
        loop_rule,
        &transition_pure_facts,
        context_label,
        prerequisite_policy,
        fact_transport_policy,
        certified_prerequisites,
        statement_contains_call_assign(statement),
    )
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
        CStatement::Declare { .. }
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
                }) || matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
                    && fact_conflicts_with_assumptions(
                        path_fact.proposition(),
                        &assumptions_from_propositions(pure_facts),
                    )
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
            let transport_assumptions = assumptions_from_propositions(&transport_facts);
            let prerequisite_assumptions = assumptions_from_propositions(&successor_facts);
            let planning_assumptions = assumptions_from_propositions(pure_facts);
            let planning_condition_assumptions =
                assumptions_from_exact_conditions(pure_facts);
            let mut prerequisite_derivations = Vec::new();
            if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
                let mut seen_prerequisites = BTreeSet::new();
                let mut theorem_context = pure_facts.to_vec();
                for premise in theorem_implication_premises(path.theorem()) {
                    let already_certified = exact_fact_is_available(&premise, &theorem_context)
                        || materialization_equivalent_available_fact(
                            &premise,
                            &theorem_context,
                        )
                        .is_some()
                        || matches!(normalize_proposition(&premise), SimpProposition::True)
                        || execution_facts
                            .iter()
                            .any(|fact| fact.is_certified() && fact.proposition() == &premise)
                        || path
                            .obligations()
                            .iter()
                            .any(|obligation| obligation.proposition() == &premise);
                    if !already_certified {
                        let derivation =
                            minimal_proposition_derivation(&premise, &theorem_context);
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
                    } else if planning_assumptions.proves(proposition) {
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
                            let exact_assumptions = if matches!(
                                proposition,
                                Proposition::ConditionIs(_, _)
                            ) {
                                &planning_condition_assumptions
                            } else {
                                &planning_assumptions
                            };
                            exact_assumptions
                                .derive_atomic_proposition(proposition)
                                .or_else(|| {
                                    exact_assumptions
                                        .derive_simp_atomic_proposition(proposition)
                                })
                                .ok_or_else(|| {
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
                            Some(
                                assumptions_from_propositions(
                                    &successor_facts
                                        .iter()
                                        .filter(|fact| *fact != proposition)
                                        .cloned()
                                        .collect::<Vec<_>>(),
                                )
                                .derive_proposition(proposition)
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
                        let Some(theorem) = prove_c_condition_fact_transport(
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
                        if c_condition_fact_memories(&fact).is_empty() {
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
                                prove_c_condition_fact_transport(
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
        CStatement::While {
            condition,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            let loop_clause = environment
                .function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index));
            let explicit_tactics = loop_clause.and_then(explicit_loop_preservation_tactics);
            let explicit_initialization = loop_clause
                .and_then(StructuralClause::initialize_proof)
                .filter(|proof| !proof.is_auto_tactic());
            let mut iteration_contexts = Vec::new();
            for (path_index, context) in contexts.iter().enumerate() {
                let assumptions = assumptions_from_propositions(&context.pure_facts);
                if let (Some(clause), Some(proof)) = (loop_clause, explicit_initialization) {
                    verify_loop_initialization_pure_proof(
                        loop_index,
                        proof,
                        clause,
                        context,
                        invariant_checks,
                        environment,
                    )?;
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
                    11_000_000_000 + loop_index as u64 * 1_000_000 + path_index as u64 * 10_000,
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
                    if let Some(tactics) = explicit_tactics {
                        verify_one_loop_preservation_proof(
                            loop_index,
                            tactics,
                            &preservation,
                            &pure_facts,
                            invariant_checks,
                            effect_checks,
                            body,
                            environment,
                        )?;
                    }
                    iteration_contexts.push(ExecutionProofContext {
                        state: preservation.state().clone(),
                        pure_facts,
                        next_opaque_call: context.next_opaque_call,
                        next_verification_variable: context.next_verification_variable,
                    });
                }
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
                if explicit_tactics.is_some() {
                    LoopPreservationSource::ExecutionProof
                } else {
                    LoopPreservationSource::Automatic
                },
                explicit_initialization.is_some(),
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
        CStatement::Declare { .. }
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
            match transition.outcome {
                CStatementOutcome::Normal(state) => advanced.push(ExecutionProofContext {
                    state,
                    pure_facts: transition.pure_facts,
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
                        "execution proof traversal produced runtime error: {error:?}"
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
) -> Result<(), ClickError> {
    let claim_label = format!(
        "{}.loop({loop_index}).initialize",
        environment.function_block.signature().name()
    );
    let mut program_point_states = ProgramPointStates::new();
    program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        context.state.clone(),
    );
    let mut available = context.pure_facts.clone();
    for (invariant_index, item) in clause
        .items()
        .iter()
        .filter(|item| item.kind() == StructuralItemKind::Invariant)
        .enumerate()
    {
        let proposition = item
            .proposition()
            .expect("invariant region proof item should contain a proposition");
        let fact = prove_pure_proposition_at_point(
            proposition,
            proof,
            "initialize",
            environment.theorem_environment,
            &claim_label,
            invariant_index,
            &available,
            environment.parsed_function.parameters(),
            environment.arguments,
            environment.initial_state,
            &context.state,
            None,
            &program_point_states,
            environment.predicate_environment,
            environment.click_function_environment,
            environment.function_block.requires(),
            None,
        )?;
        if !available.contains(&fact) {
            available.push(fact);
        }
    }
    let assumptions = assumptions_from_propositions(&available);
    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))
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
) -> Result<(), ClickError> {
    let claim_label = format!(
        "{}.loop({loop_index}).preserve",
        environment.function_block.signature().name()
    );

    let dummy_ensure = EnsureClause {
        name: None,
        ensure: Ensure::Proposition(ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        }),
        proof: Proof::Tactic(SmartTactic::Auto),
    };
    let dummy_claim = FunctionClaimRef::Ensure(0, &dummy_ensure);
    let proof_claims = [dummy_claim];
    let program = build_internal_proof(tactics, &claim_label)?;
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
    for context in contexts {
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if !at_back_edge {
            return Err(ClickError::new(format!(
                "`{claim_label}` must execute exactly one complete loop-body iteration"
            )));
        }
        let assumptions = assumptions_from_propositions(&context.pure_facts);
        c_loop_invariants_hold_at_back_edge(
            &context.state,
            preservation.loop_entry_state(),
            invariant_checks,
            &assumptions,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        c_loop_effects_hold_at_back_edge(
            preservation.state(),
            &context.state,
            effect_checks,
            &context.pure_facts,
            &assumptions,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    }
    Ok(())
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
    let candidates = available
        .iter()
        .filter_map(|kernel| {
            checked_surface_fact_at_point(
                replay,
                kernel,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .ok()
            .map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    let pre_state = replay.execution_start_state(state);
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
    let application_replays = |selected: &[(Proposition, ClickProposition)]| {
        apply_theorem_at_current_point(
            theorem_environment,
            application,
            claim_label,
            tactic_index,
            selected.iter().map(|(kernel, _)| kernel.clone()).collect(),
            parameters,
            arguments,
            pre_state,
            state,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            None,
        )
        .is_ok()
    };
    let is_loadability = |proposition: &Proposition| {
        matches!(
            proposition,
            Proposition::CMemoryLoadable { .. } | Proposition::CMemoryCanStore { .. }
        )
    };
    let is_memory_effect = |proposition: &Proposition| {
        matches!(
            proposition,
            Proposition::CMemoryMutatesOnly { .. } | Proposition::CMemoryEffectSummary { .. }
        )
    };
    let is_condition =
        |proposition: &Proposition| matches!(proposition, Proposition::ConditionIs(_, _));

    let mut selected = None;
    for tier in 0..4 {
        let mut tier_candidates = candidates
            .iter()
            .filter(|(kernel, _)| match tier {
                0 => is_loadability(kernel),
                1 => is_loadability(kernel) || is_memory_effect(kernel),
                2 => is_loadability(kernel) || is_memory_effect(kernel) || is_condition(kernel),
                _ => true,
            })
            .cloned()
            .collect::<Vec<_>>();
        let Ok(requirements) = lower_theorem_application_requirements(
            theorem_environment,
            application,
            &context,
            &tier_candidates
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>(),
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
        ) else {
            continue;
        };
        let mut complete = true;
        for requirement in requirements {
            if matches!(normalize_proposition(&requirement), SimpProposition::True) {
                continue;
            }
            let Some(pair) = candidates
                .iter()
                .find(|(kernel, _)| kernel == &requirement)
                .cloned()
            else {
                complete = false;
                break;
            };
            if !tier_candidates.contains(&pair) {
                tier_candidates.push(pair);
            }
        }
        if complete && application_replays(&tier_candidates) {
            selected = Some(tier_candidates);
            break;
        }
    }
    let mut selected = selected.ok_or_else(|| {
        ClickError::new(
            "theorem application depends on an ambient fact with no checked Click spelling",
        )
    })?;
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
fn checked_surface_fact_at_outcome(
    replay: &TacticReplayState,
    kernel: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
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
        .map_err(ClickError::new)
    };
    if let Ok(surface) = replay.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    let mut bases = Vec::new();
    if let Ok(surface) = replay.surface_propositions.surface(kernel) {
        bases.push(surface.clone());
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
            if check(&candidate).is_ok_and(|lowered| {
                normalize_direct_atomic_memory_loads(&lowered)
                    == normalize_direct_atomic_memory_loads(kernel)
            }) {
                return Ok(candidate);
            }
        }
    }
    let surface = synthesize_surface_proposition(kernel, parameters, arguments, post_state)
        .ok_or_else(|| {
            ClickError::new(format!(
                "no checked Click spelling for post-execution fact {kernel:?}"
            ))
        })?;
    if check(&surface)?.eq(kernel) {
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
        if !exact_fact_is_available(&premise, &available) {
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
            });
        let Some(theorem) =
            prove_c_condition_fact_transport(source, state.memory(), &transport_assumptions)
        else {
            return false;
        };
        let Proposition::Implies(_, conclusion) = theorem.proposition() else {
            unreachable!("condition transport must produce an implication")
        };
        normalize_direct_atomic_memory_loads(conclusion)
            == normalize_direct_atomic_memory_loads(target)
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
            .count();
        return Err(ClickError::new(format!(
            "transport depends on an ambient fact with no checked Click spelling\n  selected surface premises: {}\n  unspellable ambient facts: {unavailable}",
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
) -> Result<(Proposition, ProofReplayPlan), ClickError> {
    // Plan and replay this proof once. Surface expansion must lower this exact
    // plan; it must not search for a different proof if lowering is incomplete.
    // Snapshot transport belongs to the statement transition that changed the
    // memory and reaches a later `have` as an exact current-state assumption.
    let fact = lower_point_proposition(
        &have.proposition,
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
            "`{claim_label}` have proof {outer_tactic_index}: could not lower pure goal: {message}"
        ))
    })?;
    if available.contains(&fact) {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }

    let assumptions = assumptions_from_propositions(available);
    let Some(plan) = plan_simp_certificate(&fact, &assumptions) else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {}",
            describe_missing_pure_fact(
                &fact,
                available,
                state.resources().facts(),
                parameters,
                arguments,
                &[],
            )
        )));
    };
    if !replay_simp_certificate(&fact, &assumptions, &plan) {
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
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    prove_pure_proposition_at_point(
        &have.proposition,
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
        predicate_environment,
        click_function_environment,
        original_requirements,
        path_index,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_proposition_at_point(
    proposition: &ClickProposition,
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
                    let lowered = lower_point_proposition_with_values(
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
                    })?;
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
                if goal.is_none() {
                    let lowered = lower_point_proposition_with_values(
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
                    })?;
                    fact = Some(lowered.clone());
                    goal = Some(lowered);
                }
                let assumptions = assumptions_from_propositions(&available);
                let unfolded_goal = unfold_predicates_in_proposition(
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
                })?;
                match tactic {
                    ProofTactic::Assumption => {
                        if !available.contains(&unfolded_goal) {
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
                        if !matches!(normalize_proposition(&unfolded_goal), SimpProposition::True) {
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
                        let target = lower_point_proposition_with_values(
                            &derive.proposition,
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
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `{}` target: {message}",
                                tactic_name(tactic)
                            ))
                        })?;
                        let premises = derive
                            .premises
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
        None => lower_point_proposition_with_values(
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
        })?,
    };
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
    if goal_closed
        || available.contains(&goal)
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
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty explicit proof script"
        )));
    }
    let program = build_internal_proof(tactics, claim_label)?;
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
    )?;
    let proof_claims = [*claim];
    let mut replay = TacticReplayState {
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        ordered_finalization: true,
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
    let program = build_internal_proof(tactics, &proof_label)?;
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
    )?;
    let mut replay = TacticReplayState {
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        ordered_finalization: true,
        grouped_contract: true,
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

    prove_claims_by_grouped_tactics(
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
    )
}

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
        if let Some(limit) = execution.limit() {
            return Err(ClickError::new(format!(
                "execution proof hit execution limit {limit:?} for `{proof_label}`"
            )));
        }
        if execution.paths().is_empty() {
            return Err(ClickError::new(format!(
                "execution proof could not prove any complete execution path for `{proof_label}`"
            )));
        }
        let pre_state = replay.execution_start_state(&state);
        let mut verified = Vec::new();
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_closer_blockers = vec![None; claims.len()];
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_tactics_by_path = Vec::with_capacity(execution.paths().len());

        for (path_index, path) in execution.paths().iter().enumerate() {
            let mut path_surface_closers = vec![Vec::new(); claims.len()];
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
            let mut outcome = match implication_body(path.theorem().proposition()) {
                Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
                proposition => {
                    return Err(ClickError::new(format!(
                        "execution proof failed for `{proof_label}` path {path_index}: unexpected theorem body {proposition:?}"
                    )));
                }
            };
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

            let mut closed_claims = vec![false; claims.len()];
            let mut closer_errors = vec![None; claims.len()];
            let mut rewritten_claim_goals: Vec<Option<Proposition>> = vec![None; claims.len()];
            let mut existence_tactics = Vec::new();
            for (tactic_index, post_tactic) in &replay.post_execution_tactics {
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
                        TacticCertificate::from_proof_tactics(std::slice::from_ref(
                            &surface_tactic,
                        ))
                        .expect("post-execution smart apply must lower to a simple tactic");
                        let ProofTactic::ApplyTheoremUsing { premises, .. } = &surface_tactic
                        else {
                            unreachable!()
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
                            surface_tactic,
                        );
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
                        let (surface_have, fact) = if have_proof_is_smart_simp(&have.proof) {
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
                            let proof_tactic = lower_outcome_simp_tactic(
                                &replay,
                                &have.proposition,
                                &fact,
                                &path_requirements,
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
                            let surface_have = ProofHave {
                                proposition: have.proposition.clone(),
                                proof: Proof::Script(vec![proof_tactic]),
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
                                predicate_environment,
                                click_function_environment,
                                function_block.requires(),
                                Some(path_index),
                            )?;
                            (ProofTactic::Have(have.clone()), fact)
                        };
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
                            if closed_claims[claim_index] {
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
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` could not lower goal: {message}"
                                    ))
                                })?,
                            };
                            if path_requirements.contains(&goal) {
                                closed_claims[claim_index] = true;
                                closed_any = true;
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
                            if closed_claims[claim_index] {
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
                                closed_claims[claim_index] = true;
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
                            if closed_claims[claim_index] {
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
                            closed_claims[claim_index] = true;
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
                            closed_claims[claim_index] = true;
                        }
                    }
                    PostExecutionTactic::Simp => {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closed_claims[claim_index] {
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
                                    closed_claims[claim_index] = true;
                                    closer_errors[claim_index] = None;
                                    if existence_tactics.is_empty() {
                                        let surface_tactic = match (
                                            &rewritten_claim_goals[claim_index],
                                            ensure_clause.ensure(),
                                            &outcome,
                                        ) {
                                            (
                                                None,
                                                Ensure::Proposition(surface_goal),
                                                CFunctionOutcome::Return {
                                                    value: result,
                                                    state: post_state,
                                                },
                                            ) => {
                                                let goal = lower_ensure_proposition_goal(
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
                                                .and_then(|goal| {
                                                    lower_outcome_simp_tactic(
                                                        &replay,
                                                        surface_goal,
                                                        &goal,
                                                        &path_requirements,
                                                        parsed_function.parameters(),
                                                        arguments,
                                                        pre_state,
                                                        post_state,
                                                        result,
                                                        predicate_environment,
                                                        click_function_environment,
                                                    )
                                                    .map_err(|error| {
                                                        error.message().to_string()
                                                    })
                                                });
                                                goal
                                            }
                                            (Some(_), _, _) => Err(
                                                "surface lowering after `rewrite` is not implemented"
                                                    .to_string(),
                                            ),
                                            _ => Err(
                                                "surface `simp` lowering requires a proposition return goal"
                                                    .to_string(),
                                            ),
                                        };
                                        match surface_tactic {
                                            Ok(tactic) => {
                                                if replay
                                                    .deferred_tactic_capture
                                                    .as_ref()
                                                    .is_some_and(|capture| {
                                                        capture.tactic_index == *tactic_index
                                                    })
                                                    && !path_deferred_capture_tactics
                                                        .contains(&tactic)
                                                {
                                                    path_deferred_capture_tactics
                                                        .push(tactic.clone());
                                                }
                                                path_surface_closers[claim_index].push(tactic)
                                            }
                                            Err(message) => {
                                                surface_closer_blockers[claim_index]
                                                    .get_or_insert(message);
                                            }
                                        }
                                    } else {
                                        surface_closer_blockers[claim_index].get_or_insert_with(
                                            || {
                                                "surface `simp` lowering with existential tactics is not implemented"
                                                    .to_string()
                                            },
                                        );
                                    }
                                }
                                Err(error) => {
                                    closer_errors[claim_index] = Some(error.message().to_string());
                                }
                            }
                        }
                    }
                }
            }

            if !require_explicit_closers {
                for (claim_index, claim) in claims.iter().enumerate() {
                    if closed_claims[claim_index] {
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
                        Ok(()) => closed_claims[claim_index] = true,
                        Err(error) => {
                            closer_errors[claim_index] = Some(error.message().to_string())
                        }
                    }
                }
            }

            if let Some((claim_index, claim)) = claims
                .iter()
                .enumerate()
                .find(|(claim_index, _)| !closed_claims[*claim_index])
            {
                let claim_label = function_claim_label(function_block.signature().name(), claim);
                let closer = match claim {
                    FunctionClaimRef::Effect(_, _) => "`frame()`",
                    FunctionClaimRef::Ensure(_, _) => "`simp()`",
                };
                let detail = closer_errors[claim_index]
                    .as_deref()
                    .map(|message| format!("\nlast closing attempt:\n{message}"))
                    .unwrap_or_default();
                return Err(ClickError::new(format!(
                    "`{proof_label}` path {path_index} left `{claim_label}` unproved; use {closer} after establishing the facts and resources it needs (claim index {claim_index}){detail}"
                )));
            }

            let specification = c_function_specification(
                pre_state.clone(),
                arguments.to_vec(),
                path_requirements,
                outcome,
            );
            let theorem = prove_c_function_satisfies_specification_from_symbolic_path(
                function.clone(),
                specification.clone(),
                Assumptions::new(),
                path.facts(),
                path.obligations(),
            );
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
                });
            }
            for (claim_index, closers) in path_surface_closers.into_iter().enumerate() {
                surface_closers_by_claim[claim_index].push(closers);
            }
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
            if let Some(blocker) = surface_closer_blockers.iter().flatten().next() {
                expanded.block(format!("could not lower post-execution `simp`: {blocker}"));
            } else {
                let mut combined = vec![Vec::new(); execution.paths().len()];
                for claim_paths in &surface_closers_by_claim {
                    for (path_index, tactics) in claim_paths.iter().enumerate() {
                        for tactic in tactics {
                            if !combined[path_index].contains(tactic) {
                                combined[path_index].push(tactic.clone());
                            }
                        }
                    }
                }
                if combined.iter().any(|tactics| !tactics.is_empty())
                    && let Err(message) =
                        append_surface_tactics_by_leaf(&mut expanded.tactics, &combined)
                {
                    expanded.block(message);
                }
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
                if let Some(blocker) = &surface_closer_blockers[claim_index] {
                    expanded.block(format!("could not lower post-execution `simp`: {blocker}"));
                } else if surface_closers_by_claim[claim_index]
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
            let mut capture = SurfaceReplay {
                tactics: deferred.branch_skeleton.clone(),
                ..SurfaceReplay::default()
            };
            if let Err(message) = append_surface_tactics_by_leaf(
                &mut capture.tactics,
                &deferred_capture_tactics_by_path,
            ) {
                capture.block(message);
            }
            return Err(finish_tactic_expansion_capture(&capture));
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
            replay.execution_start_state(state),
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

#[allow(clippy::too_many_arguments)]
fn checked_surface_comparison_fact_at_point(
    replay: &TacticReplayState,
    kernel: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
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
    if let Ok(surface) = replay.surface_propositions.surface(kernel)
        && !bases.contains(surface)
    {
        bases.push(surface.clone());
    }
    if let Some(surface) = synthesize_surface_proposition(kernel, parameters, arguments, state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    let kernel_memories = c_condition_fact_memories(kernel);
    let matching_points = replay
        .program_point_states
        .iter()
        .rev()
        .filter(|(_, state)| {
            kernel_memories
                .iter()
                .any(|memory| memory.has_same_snapshot_markers(state.memory()))
        })
        .collect::<Vec<_>>();
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
                if lowered.is_ok_and(|lowered| {
                    normalize_direct_atomic_memory_loads(&lowered)
                        == normalize_direct_atomic_memory_loads(kernel)
                }) {
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
            .is_ok_and(|lowered| {
                normalize_direct_atomic_memory_loads(&lowered)
                    == normalize_direct_atomic_memory_loads(kernel)
            }) {
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
        return Some(ClickProposition::Loadable {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: synthesize_surface_pointer(base, parameters, arguments, state)?,
                start: CExpression::Value(int32(0)),
                end: element_count,
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
    Some(ResourceSubject::Memory(ContractSegment {
        state: ContractSegmentState::Current,
        base: synthesize_surface_pointer(range.base(), parameters, arguments, state)?,
        start: contract_expression_to_c_fragment(&synthesize_surface_bitvector(
            range.start(),
            parameters,
            arguments,
            state,
        )?)?,
        end: contract_expression_to_c_fragment(&synthesize_surface_bitvector(
            range.end(),
            parameters,
            arguments,
            state,
        )?)?,
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
            Some(ContractExpression::CFragment(CExpression::TypedLoad {
                pointer: Box::new(synthesize_surface_pointer(
                    pointer, parameters, arguments, state,
                )?),
                value_type: CType::Int32Pointer,
            }))
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
        return Some(ContractExpression::CFragment(CExpression::Variable(
            name.to_string(),
        )));
    }
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return Some(ContractExpression::CFragment(CExpression::Variable(name)));
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
            let pointer = synthesize_surface_pointer(pointer, parameters, arguments, state)?;
            Some(ContractExpression::CFragment(CExpression::Load(Box::new(
                pointer,
            ))))
        }
        Bitvector32Term::Variable(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. } => None,
    }
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
    let mut premise_pairs = derivation
        .context_premises()
        .into_iter()
        .filter_map(|premise| {
            checked_surface_comparison_fact_at_point(
                replay,
                &premise,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .ok()
            .map(|surface| (premise, surface))
        })
        .collect::<Vec<_>>();
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
            "surface premises do not replay the atomic derivation of {:?}",
            derivation.conclusion(),
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
    let mut premise_pairs = Vec::new();
    for fact in available {
        let Ok(surface) = checked_surface_fact_at_outcome(
            replay,
            fact,
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
        if check(&surface).is_ok_and(|lowered| {
            normalize_direct_atomic_memory_loads(&lowered)
                == normalize_direct_atomic_memory_loads(fact)
        }) {
            premise_pairs.push((fact.clone(), surface));
        }
    }
    if premise_pairs.iter().any(|(fact, _)| fact == goal) {
        return Ok(ProofTactic::Assumption);
    }
    let kernel_premises = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let surface_premises = premise_pairs
        .into_iter()
        .map(|(_, surface)| surface)
        .collect::<Vec<_>>();
    if surface_premises.is_empty() {
        return Err(ClickError::new(format!(
            "postcondition has no expressible premises for surface `simp` lowering: {goal:?}"
        )));
    }
    let assumptions = assumptions_from_propositions(&kernel_premises);
    if assumptions
        .derive_atomic_proposition(goal)
        .or_else(|| assumptions.derive_proposition(goal))
        .is_some()
    {
        Ok(ProofTactic::Derive(ProofDerive {
            proposition: surface_goal.clone(),
            premises: surface_premises,
        }))
    } else if assumptions
        .derive_simp_atomic_proposition(goal)
        .or_else(|| assumptions.derive_simp_proposition(goal))
        .is_some()
    {
        Ok(ProofTactic::Calculate(ProofDerive {
            proposition: surface_goal.clone(),
            premises: surface_premises,
        }))
    } else {
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

fn comparison_program_point_variants(
    proposition: &ClickProposition,
    points: &[ProgramPointRef],
) -> Option<Vec<ClickProposition>> {
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
        replay.execution_start_state(state),
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

fn expression_reads_memory(expression: &CExpression) -> bool {
    match expression {
        CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(_, _) => true,
        CExpression::Value(_) | CExpression::Variable(_) => false,
        CExpression::AddressOf(inner)
        | CExpression::Not(inner)
        | CExpression::BitwiseNot(inner) => expression_reads_memory(inner),
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            expression_reads_memory(left) || expression_reads_memory(right)
        }
    }
}

fn statement_uses_ambient_memory_context(statement: &CStatement) -> bool {
    match statement {
        CStatement::Declare { .. } => false,
        CStatement::Assign { expression, .. }
        | CStatement::Assert {
            condition: expression,
            ..
        }
        | CStatement::Return(expression) => expression_reads_memory(expression),
        CStatement::CallAssign { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::If { .. }
        | CStatement::While { .. } => true,
        CStatement::Seq(first, second) => {
            statement_uses_ambient_memory_context(first)
                || statement_uses_ambient_memory_context(second)
        }
    }
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
            let statement_uses_memory_context =
                match implication_body(evidence.transition.theorem.proposition()) {
                    Proposition::CStatementExecutes { statement, .. } => {
                        statement_uses_ambient_memory_context(statement)
                    }
                    _ => true,
                };
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
                &ProofTactic::CertifiedStatementStep {
                    prerequisite_derivations: evidence.transition.prerequisite_derivations.clone(),
                    exact_premises,
                },
                Some(statement_uses_memory_context),
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
                // Preserve the facts selected by prerequisite derivations,
                // plus exact condition facts that can affect arithmetic,
                // access-range, or alias selection. Resource/loadability facts
                // are projected deterministically from the current resource
                // state after these explicit conditions are installed.
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
                for fact in available_conjuncts {
                    let selected_by_derivation = derivation_context.iter().any(|required| {
                        (*required).eq(fact)
                            || normalize_direct_atomic_memory_loads(required)
                                == normalize_direct_atomic_memory_loads(fact)
                    }) || exact_premises.iter().any(|required| {
                        required == fact
                            || normalize_direct_atomic_memory_loads(required)
                                == normalize_direct_atomic_memory_loads(fact)
                    });
                    let structural_context = statement_uses_memory_context.unwrap_or(true)
                        && matches!(
                            fact,
                            Proposition::ConditionIs(_, _)
                                | Proposition::CMemoryLoadable { .. }
                                | Proposition::CMemoryCanStore { .. }
                                | Proposition::CMemoryDisjoint { .. }
                                | Proposition::CResourceSeparate { .. }
                                | Proposition::CResourceContains { .. }
                        );
                    if !selected_by_derivation && !structural_context {
                        continue;
                    }
                    let Ok(surface) = checked_surface_comparison_fact_at_point(
                        replay,
                        fact,
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
                        .filter_map(|kernel| {
                            let Proposition::Predicate {
                                name: kernel_name, ..
                            } = kernel
                            else {
                                return None;
                            };
                            if kernel_name != &name {
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
                            let surface = instantiate_click_predicate_definition(
                                definition,
                                surface_arguments,
                            )
                            .ok()?;
                            let unfolded = unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                std::slice::from_ref(&name),
                                kernel,
                                &assumptions,
                            )
                            .ok()?;
                            Some((surface, unfolded))
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
                        replay.execution_start_state(state),
                        state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
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
                    record_surface_smart_have(
                        replay,
                        state,
                        &surface_available,
                        parameters,
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        &have,
                        &plan,
                    );
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
                        replay.execution_start_state(state),
                        state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
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
                        record_surface_smart_have(
                            replay,
                            state,
                            &surface_available,
                            parameters,
                            arguments,
                            predicate_environment,
                            click_function_environment,
                            &have,
                            &plan,
                        );
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
            if normalize_direct_atomic_memory_loads(source)
                == normalize_direct_atomic_memory_loads(target)
            {
                return;
            }
            let is_reflexive = |proposition: &Proposition| {
                matches!(
                    proposition,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
                        if left == right
                )
            };
            if is_reflexive(source) && is_reflexive(target) {
                return;
            }
            let Some(step_entry) = replay.surface_replay.last_step_entry.clone() else {
                replay
                    .surface_replay
                    .block("fact transport has no preceding statement-entry snapshot");
                return;
            };
            let mut base_surfaces = Vec::new();
            for proposition in [source, target] {
                if let Ok(surface) = replay.surface_propositions.surface(proposition)
                    && !base_surfaces.contains(surface)
                {
                    base_surfaces.push(surface.clone());
                }
                if let Some(surface) =
                    synthesize_surface_proposition(proposition, parameters, arguments, state)
                    && !base_surfaces.contains(&surface)
                {
                    base_surfaces.push(surface);
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
                    (&actual == expected).then(|| candidate.clone())
                })
            };
            match (find_candidate(source), find_candidate(target)) {
                (Some(surface_source), Some(surface_target))
                    if surface_source == surface_target =>
                {
                    return;
                }
                (Some(surface_source), Some(surface_target)) => {
                    let transition_facts =
                        fact_transport_transition_facts(&replay.effect_facts, source);
                    match plan_explicit_fact_transport(
                        &surface_source,
                        source,
                        target,
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
                                target: surface_target,
                                premises,
                            });
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
            ..
        } => replay.surface_replay.path_choices.push(SurfacePathChoice {
            occurrence: *occurrence,
            condition: condition.clone(),
            value: *value,
            tactic_offset: replay.surface_replay.tactics.len(),
        }),
        ProofTactic::CertifiedAlternatives(_) => {}
        ProofTactic::Have(have) => {
            match TacticCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                Ok(_) => replay.surface_replay.push(tactic.clone()),
                Err(_) if have_proof_is_smart_simp(&have.proof) => {
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

#[allow(clippy::too_many_arguments)]
fn record_surface_smart_have(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
    certificate: &ProofReplayPlan,
) {
    if replay.surface_replay.blocker.is_some() {
        return;
    }
    let proof = match certificate.tactics() {
        [ProofTactic::Assumption] => Proof::Script(vec![ProofTactic::Assumption]),
        [ProofTactic::Normalize] => Proof::Script(vec![ProofTactic::Normalize]),
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
            match lower_surface_atomic_derivation(
                replay,
                derivation,
                Some(&have.proposition),
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            ) {
                Ok((_, proof)) => proof,
                Err(error) => {
                    replay.surface_replay.block(format!(
                        "could not lower the planned smart `have` certificate: {}",
                        error.message()
                    ));
                    return;
                }
            }
        }
        _ => {
            replay
                .surface_replay
                .block("smart `have` planned an unexpected simp certificate");
            return;
        }
    };
    let tactic = ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof,
    });
    match TacticCertificate::from_proof_tactics(std::slice::from_ref(&tactic)) {
        Ok(_) => replay.surface_replay.push(tactic),
        Err(error) => replay.surface_replay.block(format!(
            "smart `have` produced an invalid certificate: {error:?}"
        )),
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

fn timing_tactic_class(tactic: &ProofTactic) -> &'static str {
    if let ProofTactic::Have(have) = tactic {
        if have_proof_is_smart_simp(&have.proof) {
            return "smart";
        }
        if let Proof::Script(tactics) = &have.proof
            && !tactics.is_empty()
            && tactics
                .iter()
                .all(|tactic| matches!(tactic.class(), TacticClass::Simple(_)))
        {
            return "simple";
        }
    }
    match tactic.class() {
        TacticClass::Simple(_) => "simple",
        TacticClass::Smart(_) => "smart",
        TacticClass::ControlFlow(_) => "control",
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
        std::env::var_os("CLICK_TIMINGS").is_some().then(|| {
            let tactic_class = timing_tactic_class(tactic);
            if std::env::var_os("CLICK_TIMING_STARTS").is_some() {
                eprintln!(
                    "click timing: started tactic {} {} {} class {} statement {} source {}",
                    claim_label,
                    tactic_index,
                    tactic_name(tactic),
                    tactic_class,
                    statement_index,
                    source_index
                );
            }
            Self {
                claim_label: claim_label.to_string(),
                tactic_index,
                source_index,
                tactic_name: tactic_name(tactic).to_string(),
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
        let pre_capture_branch_skeleton = surface_branch_skeleton(&replay.surface_replay.tactics);
        let capture_this_tactic = begin_tactic_expansion_capture(
            function_block,
            claims,
            source_index,
            tactic,
            &mut replay,
        );
        if capture_this_tactic && deferred_post_execution {
            replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                branch_skeleton: pre_capture_branch_skeleton,
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
        let _timing = TacticTiming::new(
            claim_label,
            tactic_index,
            source_index,
            tactic,
            replay.frontier.next_statement_index,
        );
        if let ProofTactic::Transport {
            source: surface_source,
            target: surface_target,
        } = tactic
        {
            if replay.is_at_function_entry() || replay.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                )));
            }
            let pre_state = replay.execution_start_state(&state).clone();
            let source = lower_point_proposition(
                surface_source,
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
                return Err(finish_tactic_expansion_capture(&replay.surface_replay));
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
                return Err(finish_tactic_expansion_capture(&replay.surface_replay));
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
                if replay.is_at_function_entry() || replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                    )));
                }
                let pre_state = replay.execution_start_state(&state).clone();
                let surface_premises = match tactic {
                    ProofTactic::TransportUsing { premises, .. } => Some(premises),
                    ProofTactic::Transport { .. } => None,
                    _ => unreachable!(),
                };
                let mut explicit_premises = Vec::new();
                if let Some(surface_premises) = surface_premises {
                    for surface_premise in surface_premises {
                        let premise = lower_point_proposition(
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
                        })?;
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
                let source = lower_point_proposition(
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
                })?;
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
                if selected_assumptions.derive_proposition(&source).is_none() {
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
                        "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                    ))
                })?;
                replay
                    .surface_propositions
                    .record_lowering(surface_target, &target)?;
                if selected_assumptions.derive_proposition(&target).is_some() {
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
                    });
                let theorem = prove_c_condition_fact_transport(
                    &source,
                    state.memory(),
                    &transport_assumptions,
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: no certified frame transport applies to the exact source fact\n  source: {source:?}\n  current memory: {:?}\n  effect facts: {:?}",
                        state.memory(), replay.effect_facts
                    ))
                })?;
                let Proposition::Implies(_, conclusion) = theorem.proposition() else {
                    unreachable!("condition transport must produce an implication")
                };
                let transported = normalize_direct_atomic_memory_loads(conclusion);
                let requested = normalize_direct_atomic_memory_loads(&target);
                if transported != requested {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: transported fact does not equal the requested target\n  transported: {:?}\n  requested: {:?}",
                        transported, requested
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
                let all_pure_assumptions = assumptions_from_propositions(&all_pure_facts);
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
                let pre_state = replay.execution_start_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let premise = lower_point_proposition(
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
                            "`{claim_label}` tactic {tactic_index}: could not lower `{tactic_name}` premise: {message}"
                        ))
                    })?;
                    replay
                        .surface_propositions
                        .record_lowering(surface_premise, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise: {}",
                                error.message()
                            ))
                        })?;
                    let premise_is_available =
                        materialization_equivalent_available_fact(&premise, &all_pure_facts)
                            .is_some()
                            || all_pure_assumptions
                                .derive_atomic_proposition(&premise)
                                .or_else(|| {
                                    all_pure_assumptions.derive_simp_atomic_proposition(&premise)
                                })
                                .is_some();
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
                for effect in &replay.effect_facts {
                    if effect.is_certified()
                        && exact_fact_is_available(effect.proposition(), &all_pure_facts)
                        && !explicit_premises.contains(effect.proposition())
                    {
                        explicit_premises.push(effect.proposition().clone());
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
                let pre_state = replay.execution_start_state(&state);
                let mut path_derivations = Vec::with_capacity(execution.paths().len());
                for (path_index, path) in execution.paths().iter().enumerate() {
                    if !path.obligations().is_empty() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame` cannot plan from an execution path with unresolved obligations"
                        )));
                    }
                    let Proposition::CFunctionExecutes { outcome, .. } =
                        implication_body(path.theorem().proposition())
                    else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame` saw an unexpected execution theorem"
                        )));
                    };
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
                        outcome,
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
                    replay
                        .post_execution_tactics
                        .push((tactic_index, PostExecutionTactic::Frame));
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
                replay.frames.insert(region_ref.clone());
            }
            ProofTactic::CertifiedFrame(path_derivations) => {
                require_function_exit(&replay, claim_label, tactic_index, "certified_frame")?;
                replay.post_execution_tactics.push((
                    tactic_index,
                    PostExecutionTactic::CertifiedFrame(path_derivations.clone()),
                ));
            }
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.post_execution_tactics.push((
                        tactic_index,
                        PostExecutionTactic::UnfoldPredicate(name.clone()),
                    ));
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
                        replay.post_execution_tactics.push((
                            tactic_index,
                            PostExecutionTactic::Apply(application.clone()),
                        ));
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
                        replay.execution_start_state(&state),
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
                        replay.post_execution_tactics.push((
                            tactic_index,
                            PostExecutionTactic::ApplyUsing {
                                application: application.clone(),
                                premises: premises.clone(),
                            },
                        ));
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply using` is not available in this region proof"
                    )));
                }
                let all_pure_facts = requirement_pure_facts.clone();
                let mut lowering_facts = all_pure_facts.clone();
                append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
                let pre_state = replay.execution_start_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let premise = lower_point_proposition(
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
                    })?;
                    if !exact_fact_is_available(&premise, &all_pure_facts) {
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
                        replay
                            .post_execution_tactics
                            .push((tactic_index, PostExecutionTactic::Fold(resource.clone())));
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `fold` is not available in this region proof"
                        )));
                    }
                } else {
                    let pre_state = replay.execution_start_state(&state).clone();
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
                        replay
                            .post_execution_tactics
                            .push((tactic_index, PostExecutionTactic::Have(have.clone())));
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
                let smart_plan = if have_proof_is_smart_simp(&have.proof) {
                    let (fact, plan) = plan_smart_have_at_current_point(
                        have,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.execution_start_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
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
                        replay.execution_start_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        function_block.requires(),
                    )?,
                };
                replay
                    .surface_propositions
                    .record_lowering(&have.proposition, &fact)?;
                if let Some((_, plan)) = &smart_plan {
                    record_surface_smart_have(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        have,
                        plan,
                    );
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
                    replay
                        .post_execution_tactics
                        .push((tactic_index, PostExecutionTactic::Witness(witness.clone())));
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
                    replay
                        .post_execution_tactics
                        .push((tactic_index, PostExecutionTactic::Choose(choice.clone())));
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
                    replay
                        .post_execution_tactics
                        .push((tactic_index, post_tactic));
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
            ProofTactic::Simp => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, "simp")?;
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay
                        .post_execution_tactics
                        .push((tactic_index, PostExecutionTactic::Simp));
                }
            }
        }
        if capture_this_tactic && !deferred_post_execution {
            return Err(finish_tactic_expansion_capture(&replay.surface_replay));
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
) -> Result<(), ClickError> {
    let program = build_internal_proof(certificate.tactics(), claim_label)?;
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
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: surface certificate at source tactic {source_index} produced no replay contexts"
        )));
    }
    Ok(())
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
    verify_surface_certificate(
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
    Ok(internal_result)
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
            join_id,
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
                    *join_id,
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
        context.replay.execution_start_state(&context.state),
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
    join_id: usize,
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
                        replay.execution_start_state(state),
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
    let variable_start = (join_id as u64)
        .checked_mul(1_000_000)
        .and_then(|offset| 10_000_000_000u64.checked_add(offset))
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: too many nested `advance` joins"
            ))
        })?;
    let mut abstract_state =
        abstract_c_state_for_join(state, stable_join_locals, variable_start).map_err(|message| {
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
            .expect("source loop should have a body entry");
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

#[allow(clippy::too_many_arguments)]
fn execute_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    assumptions: &Assumptions,
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
            let completed = certify_c_function_execution_paths_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                assumptions.clone(),
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
            let Proposition::CFunctionExecutes { outcome, .. } =
                implication_body(path.theorem().proposition())
            else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `bounded_execute` saw an unexpected completed theorem"
                )));
            };
            let mut facts = path.execution_facts();
            for fact in &frontier.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            paths.push((outcome.clone(), facts, path.obligations().to_vec()));
        }
    }
    let execution = certify_c_function_execution_paths_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        Assumptions::new(),
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
        .expect("flattening a C statement sequence should succeed");
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
    execution: crate::kernel::SymbolicCExecution,
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
    let resources = state
        .resources()
        .clone()
        .without_fact(&abstract_resource, &assumptions)
        .ok_or_else(|| {
            ClickError::new(format!(
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
            ))
        })?;
    state = state.with_resource_context(resources);

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
        let resources = state
            .resources()
            .clone()
            .try_compose_with_fact(lowered, &assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                    describe_resource_clause(resource),
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
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
        let assumptions = assumptions_from_propositions(available_pure_facts);
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
            unreachable!("batch and sequential resource consumption disagreed")
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
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
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
            Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(pointer.clone()));
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
    execution: &crate::kernel::SymbolicCExecution,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    requirement_pure_facts: &[Proposition],
) -> Result<(), ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `frame()` hit execution limit {limit:?}"
        )));
    }
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
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `frame()` saw unexpected theorem body {proposition:?}\n  execution pure facts: {}",
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };
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
            &outcome,
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
