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
                proof_tactics: Some(certificate.tactics().to_vec()),
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
            if control_index + 1 != tactics.len() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {control_index}: proof-level `if` must be the final tactic because both branches prove the current claim; use `advance(...)` to join C execution before a shared suffix"
                )));
            }
            let mut cases = Vec::new();
            for (value, branch_tactics) in [
                (true, proof_if.then_tactics.as_slice()),
                (false, proof_if.else_tactics.as_slice()),
            ] {
                for mut branch in
                    expand_structured_proof_cases(branch_tactics, claim_label, next_join_id)?
                {
                    let mut linear = prefix.to_vec();
                    linear.append(&mut branch.tactics);
                    let mut assumptions = vec![ProofCaseAssumption {
                        tactic_index: prefix.len(),
                        proposition: proof_if.condition.clone(),
                        value,
                    }];
                    assumptions.extend(branch.assumptions.into_iter().map(|assumption| {
                        ProofCaseAssumption {
                            tactic_index: prefix.len() + assumption.tactic_index,
                            ..assumption
                        }
                    }));
                    let advance_checks = branch
                        .advance_checks
                        .into_iter()
                        .map(|check| ProofAdvanceCheck {
                            tactic_index: prefix.len() + check.tactic_index,
                            ..check
                        })
                        .collect();
                    cases.push(ExpandedProofCase {
                        tactics: linear,
                        assumptions,
                        advance_checks,
                    });
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
    build_internal_proof_at(tactics, claim_label, &mut next_join_id, 0)
}

fn build_internal_proof_at(
    tactics: &[ProofTactic],
    claim_label: &str,
    next_join_id: &mut usize,
    index_offset: usize,
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
                    tactic,
                })
                .collect(),
            continuation: Box::new(InternalProofNode::Done),
        });
    };

    let index = index_offset + control_index;
    let control = match control_tactic {
        ProofTactic::If(proof_if) => {
            if control_index + 1 != tactics.len() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: proof-level `if` must be the final tactic because both branches prove the current claim; use `advance(...)` to join C execution before a shared suffix"
                )));
            }
            InternalProofNode::If {
                index,
                condition: proof_if.condition.clone(),
                then_branch: Box::new(build_internal_proof_at(
                    &proof_if.then_tactics,
                    claim_label,
                    next_join_id,
                    index + 1,
                )?),
                else_branch: Box::new(build_internal_proof_at(
                    &proof_if.else_tactics,
                    claim_label,
                    next_join_id,
                    index + 1,
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
                )?),
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    claim_label,
                    next_join_id,
                    index + 1,
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
                    tactic,
                })
                .collect(),
            continuation: Box::new(control),
        })
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
    mut available: Vec<Proposition>,
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
        let conclusions = instantiate_theorem_application(
            theorem_environment,
            application,
            claim_label,
            path_index,
            *tactic_index,
            &available,
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
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        &assumptions,
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
) -> Result<(CState, Vec<CExpression>, Vec<Proposition>), ClickError> {
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
    Ok((state, arguments, requirement_pure_facts))
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
    let (state, arguments, requirement_pure_facts) = initial_claim_context(
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
    let assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let vc_execution = prove_symbolic_c_function_verification_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions.clone(),
        function_environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    if let Some(error) = execution_obligation_error(
        &vc_execution,
        claim_label,
        &requirement_pure_facts,
        state.resources().facts(),
        parsed_function.parameters(),
        &arguments,
    ) {
        return Err(error);
    }
    let loop_verification_error = match prove_claim_from_execution(
        &vc_execution,
        AutoExecutionKind::LoopVerification,
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        resource_environment,
    ) {
        Ok(theorems) => {
            let proof_tactics = certified_proof_tactics(
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
                auto_loop_verification_tactic_candidates(function_block, claim),
            );
            return Ok(with_proof_tactics(theorems, proof_tactics));
        }
        Err(error) => Some(error),
    };
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
        .expect("auto should attempt at least one bounded execution proof"))
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

    let (state, arguments, requirement_pure_facts) = initial_claim_context(
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
    let assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let execution = prove_symbolic_c_function_verification_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    if let Some(error) = execution_obligation_error_for_tactic(
        "frame",
        &execution,
        claim_label,
        &requirement_pure_facts,
        state.resources().facts(),
        parsed_function.parameters(),
        &arguments,
    ) {
        return Err(error);
    }

    let theorems = prove_claim_from_execution(
        &execution,
        AutoExecutionKind::Frame,
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let proof_tactics = certified_proof_tactics(
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
        frame_tactic_candidates(),
    );
    Ok(with_proof_tactics(theorems, proof_tactics))
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
    if count_loops(parsed_function.body()) != 0 {
        return Err(ClickError::new(format!(
            "`simp` does not prove loop-backed claims for `{claim_label}`; use `by auto;`"
        )));
    }

    let (state, arguments, requirement_pure_facts) = initial_claim_context(
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
    let proof_tactics = certified_proof_tactics(
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
        vec![vec![ProofTactic::ExecuteRest, ProofTactic::Simp]],
    );
    let assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let execution = prove_symbolic_c_function_execution_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`simp` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`simp` could not establish a direct execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`simp` failed for `{claim_label}` path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    &requirement_pure_facts,
                    state.resources().facts(),
                    parsed_function.parameters(),
                    &arguments,
                    path.facts()
                )
            )));
        }

        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`simp` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  pure facts: {}\n  execution pure facts: {}",
                    describe_pure_facts(&requirement_pure_facts),
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        path_requirements = project_outcome_resource_facts(
            resource_environment,
            parsed_function.parameters(),
            &arguments,
            &state,
            &outcome,
            &path_requirements,
            predicate_environment,
            click_function_environment,
            claim_label,
            path_index,
        )?;
        let program_point_states = ProgramPointStates::new();
        check_function_claim_by_simp(
            claim_label,
            path_index,
            &path.execution_facts(),
            &path_requirements,
            claim,
            parsed_function.parameters(),
            &arguments,
            &state,
            &outcome,
            predicate_environment,
            click_function_environment,
            &program_point_states,
            &[],
        )?;
        let specification = c_function_specification(
            state.clone(),
            arguments.clone(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = prove_c_function_satisfies_specification_with_environment(
            function.clone(),
            specification.clone(),
            Assumptions::new(),
            function_environment.clone(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`simp` failed for `{claim_label}` path {path_index}: execution did not satisfy the packaged specification\n  execution pure facts: {}",
                describe_execution_pure_facts(path.facts())
            ))
        })?;

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind: ProofKind::Simp,
            proof_tactics: proof_tactics.clone(),
            specification,
            theorem,
        });
    }

    Ok(verified)
}

#[derive(Clone, Default)]
struct TacticReplayState {
    frontier: ExecutionFrontier,
    source_layout: SourceExecutionLayout,
    program_point_states: ProgramPointStates,
    frames: BTreeSet<Option<CodeRegionRef>>,
    unfolded_predicates: Vec<String>,
    post_execution_tactics: Vec<(usize, PostExecutionTactic)>,
    case_assumptions: Vec<(usize, ClickProposition, bool)>,
    effect_facts: Vec<ExecutionPureFact>,
    region_proof: bool,
    ordered_finalization: bool,
    grouped_contract: bool,
    next_opaque_call: u64,
    planned_tactics: Vec<ProofTactic>,
}

#[derive(Clone)]
enum PostExecutionTactic {
    Fold(ResourceClause),
    UnfoldPredicate(String),
    Apply(TheoremApplication),
    Have(ProofHave),
    Choose(ProofChoice),
    Witness(ProofWitness),
    Assumption,
    Normalize,
    Rewrite(ClickProposition),
    Frame,
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
    let (initial_state, arguments, requirement_facts) = initial_claim_context(
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
    };
    let mut next_loop_index = 0;
    let mut verified_loop_rules = Vec::new();
    verify_execution_proofs_forward(
        function.body(),
        vec![ExecutionProofContext {
            state: entry_state,
            pure_facts: requirement_facts,
            next_opaque_call: 0,
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
}

#[derive(Clone)]
struct ExecutionProofContext {
    state: CState,
    pure_facts: Vec<Proposition>,
    next_opaque_call: u64,
}

#[derive(Clone)]
struct CertifiedConditionTransition {
    is_true: bool,
    pure_facts: Vec<Proposition>,
    prerequisite_derivations: Vec<PropositionDerivation>,
}

#[derive(Clone)]
pub(super) struct CertifiedStatementTransition {
    pub(super) outcome: CStatementOutcome,
    pub(super) execution_facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) pure_facts: Vec<Proposition>,
    pub(super) prerequisite_derivations: Vec<PropositionDerivation>,
    pub(super) fact_transports: Vec<CertifiedFactTransport>,
}

#[derive(Clone)]
pub(super) struct CertifiedFactTransport {
    pub(super) source: Proposition,
    pub(super) target: Proposition,
    pub(super) theorem: Theorem,
}

fn append_statement_transition_certificate(
    replay: &mut TacticReplayState,
    transition: &CertifiedStatementTransition,
) {
    replay
        .planned_tactics
        .push(ProofTactic::CertifiedStatementStep(
            transition.prerequisite_derivations.clone(),
        ));
    replay
        .planned_tactics
        .extend(transition.fact_transports.iter().map(|transport| {
            ProofTactic::CertifiedFactTransport {
                source: transport.source.clone(),
                target: transport.target.clone(),
                theorem: transport.theorem.clone(),
            }
        }));
}

fn append_condition_transition_certificate(
    replay: &mut TacticReplayState,
    transition: &CertifiedConditionTransition,
) {
    replay
        .planned_tactics
        .push(ProofTactic::CertifiedStatementStep(
            transition.prerequisite_derivations.clone(),
        ));
}

#[derive(Clone, Copy)]
pub(super) enum StatementPrerequisitePolicy {
    Exact,
    Certified,
    Contextual,
    Planning,
}

#[derive(Clone, Copy)]
pub(super) enum StatementFactTransportPolicy {
    None,
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

fn exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (Proposition::And(first, second), _) => {
            exact_facts_directly_conflict(first, right)
                || exact_facts_directly_conflict(second, right)
        }
        (_, Proposition::And(first, second)) => {
            exact_facts_directly_conflict(left, first)
                || exact_facts_directly_conflict(left, second)
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
) -> Result<Vec<CertifiedConditionTransition>, ClickError> {
    let assumptions = match prerequisite_policy {
        StatementPrerequisitePolicy::Exact => Assumptions::new(),
        StatementPrerequisitePolicy::Certified
        | StatementPrerequisitePolicy::Contextual
        | StatementPrerequisitePolicy::Planning => assumptions_from_propositions(pure_facts),
    };
    let evaluation =
        prove_symbolic_c_condition_evaluation(state.clone(), condition.clone(), assumptions);
    if let Some(limit) = evaluation.limit() {
        return Err(ClickError::new(format!(
            "{context_label} hit condition execution limit {limit:?}"
        )));
    }
    evaluation
        .paths()
        .iter()
        .filter(|path| {
            matches!(
                prerequisite_policy,
                StatementPrerequisitePolicy::Contextual | StatementPrerequisitePolicy::Planning
            )
                || !path.facts().iter().any(|path_fact| {
                    pure_facts.iter().any(|available| {
                        exact_facts_directly_conflict(available, path_fact.proposition())
                    })
                })
        })
        .map(|path| {
            let mut successor_facts = pure_facts.to_vec();
            successor_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let prerequisite_assumptions = assumptions_from_propositions(&successor_facts);
            let mut prerequisite_derivations = Vec::new();
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
                    StatementPrerequisitePolicy::Contextual => {
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
                    prerequisite_derivations,
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
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    certified_prerequisites: &[PropositionDerivation],
) -> Result<(Vec<CertifiedStatementTransition>, Option<CVerifiedLoopRule>), ClickError> {
    let assumptions = match prerequisite_policy {
        StatementPrerequisitePolicy::Exact => Assumptions::new(),
        StatementPrerequisitePolicy::Certified
        | StatementPrerequisitePolicy::Contextual
        | StatementPrerequisitePolicy::Planning => assumptions_from_propositions(pure_facts),
    };
    let mut budget = ExecutionBudget::default().with_next_opaque_call(*next_opaque_call);
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
    certified_transitions_from_execution(
        execution,
        loop_rule,
        pure_facts,
        context_label,
        prerequisite_policy,
        fact_transport_policy,
        certified_prerequisites,
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
) -> Result<(Vec<CertifiedStatementTransition>, Option<CVerifiedLoopRule>), ClickError> {
    let assumptions = assumptions_from_propositions(pure_facts);
    let mut budget = ExecutionBudget::default().with_next_opaque_call(*next_opaque_call);
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
    certified_transitions_from_execution(
        execution,
        loop_rule,
        pure_facts,
        context_label,
        StatementPrerequisitePolicy::Contextual,
        StatementFactTransportPolicy::Automatic,
        &[],
    )
}

fn certified_transitions_from_execution(
    execution: SymbolicCExecution,
    loop_rule: Option<CVerifiedLoopRule>,
    pure_facts: &[Proposition],
    context_label: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    certified_prerequisites: &[PropositionDerivation],
) -> Result<(Vec<CertifiedStatementTransition>, Option<CVerifiedLoopRule>), ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "{context_label} hit execution limit {limit:?}"
        )));
    }
    let transitions = execution
        .paths()
        .iter()
        .filter(|path| {
            matches!(
                prerequisite_policy,
                StatementPrerequisitePolicy::Contextual | StatementPrerequisitePolicy::Planning
            ) || !path.facts().iter().any(|path_fact| {
                pure_facts.iter().any(|available| {
                    exact_facts_directly_conflict(available, path_fact.proposition())
                })
            })
        })
        .map(|path| {
            let mut successor_facts = pure_facts.to_vec();
            successor_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let execution_facts = path.execution_facts();
            let mut transport_facts = successor_facts.clone();
            transport_facts.extend(
                execution_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            let transport_assumptions = assumptions_from_propositions(&transport_facts);
            let prerequisite_assumptions = assumptions_from_propositions(&successor_facts);
            let mut prerequisite_derivations = Vec::new();
            for obligation in path.obligations() {
                let proposition = obligation.proposition();
                let derivation = match prerequisite_policy {
                    StatementPrerequisitePolicy::Exact | StatementPrerequisitePolicy::Certified => {
                        if exact_fact_is_available(proposition, pure_facts)
                            || matches!(normalize_proposition(proposition), SimpProposition::True)
                            || matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified)
                                && certified_prerequisites.iter().any(|derivation| {
                                    derivation.conclusion() == proposition
                                        && derivation.replay(&prerequisite_assumptions)
                                })
                        {
                            None
                        } else {
                            let requirement = match prerequisite_policy {
                                StatementPrerequisitePolicy::Exact => "exact prerequisite",
                                StatementPrerequisitePolicy::Certified => "certified prerequisite",
                                StatementPrerequisitePolicy::Contextual
                                | StatementPrerequisitePolicy::Planning => unreachable!(),
                            };
                            return Err(ClickError::new(format!(
                                "{context_label} is missing {requirement}{}: {:?}",
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
                    StatementPrerequisitePolicy::Planning => Some(
                        prerequisite_assumptions
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
                    ),
                };
                if let Some(derivation) = derivation {
                    prerequisite_derivations.push(derivation);
                }
            }
            let Proposition::CStatementExecutes { outcome, .. } =
                implication_body(path.theorem().proposition())
            else {
                return Err(ClickError::new(format!(
                    "{context_label} saw an unexpected execution theorem"
                )));
            };
            if matches!(
                fact_transport_policy,
                StatementFactTransportPolicy::Automatic
            ) && let CStatementOutcome::Normal(post_state)
            | CStatementOutcome::Return {
                state: post_state, ..
            } = outcome
            {
                let mut transported_facts = Vec::new();
                for fact in successor_facts.clone() {
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
                    transported_facts.push(CertifiedFactTransport {
                        source: fact,
                        target: conclusion.as_ref().clone(),
                        theorem,
                    });
                }
                for transport in &transported_facts {
                    successor_facts.retain(|fact| fact != &transport.source);
                    if !successor_facts.contains(&transport.target) {
                        successor_facts.push(transport.target.clone());
                    }
                }
                return Ok(CertifiedStatementTransition {
                    outcome: outcome.clone(),
                    execution_facts,
                    obligations: path.obligations().to_vec(),
                    pure_facts: successor_facts,
                    prerequisite_derivations,
                    fact_transports: transported_facts,
                });
            }
            Ok(CertifiedStatementTransition {
                outcome: outcome.clone(),
                execution_facts,
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
        )? {
            let next = ExecutionProofContext {
                state: context.state.clone(),
                pure_facts: transition.pure_facts,
                next_opaque_call: context.next_opaque_call,
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
            )?,
        };
        if matches!(statement, CStatement::While { .. }) {
            let loop_rule = loop_rule.ok_or_else(|| {
                ClickError::new(format!(
                    "`{}` loop({region_index}) did not produce an obligation-free verified loop rule",
                    environment.function_block.signature().name()
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
        ..TacticReplayState::default()
    };
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
    let available = apply_theorem_applications_to_available(
        theorem_environment,
        &[(tactic_index, application.clone())],
        claim_label,
        None,
        available,
        &context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    Ok(available)
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
            ProofTactic::Assumption | ProofTactic::Normalize | ProofTactic::Rewrite(_) => {
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
    let (state, arguments, pure_facts) = initial_claim_context(
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
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state,
            pure_facts,
            replay: TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ordered_finalization: true,
                ..TacticReplayState::default()
            },
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
    let (state, arguments, pure_facts) = initial_claim_context(
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
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state,
            pure_facts,
            replay: TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ordered_finalization: true,
                grouped_contract: true,
                ..TacticReplayState::default()
            },
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

        for (path_index, path) in execution.paths().iter().enumerate() {
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
                for (tactic_index, condition, value) in &replay.case_assumptions {
                    let condition = lower_outcome_proposition_with_program_points(
                        parsed_function.parameters(),
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        &path_requirements,
                        condition,
                        predicate_environment,
                        click_function_environment,
                        &replay.program_point_states,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{proof_label}` path {path_index}, tactic {tactic_index}: could not lower `if` condition: {message}"
                        ))
                    })?;
                    path_requirements.push(if *value {
                        condition
                    } else {
                        Proposition::Not(Box::new(condition))
                    });
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
                        let values = parameter_values(parsed_function.parameters(), arguments)
                            .map_err(|error| ClickError::new(error.message))?;
                        let array_refs = array_refs_for_parameters(
                            parsed_function.parameters(),
                            &values,
                            post_state.memory(),
                        );
                        let application_context = TheoremApplicationContext {
                            values: &values,
                            array_refs: &array_refs,
                            pre_state,
                            post_state,
                            result: Some(result),
                            program_point_states: &replay.program_point_states,
                        };
                        path_requirements = apply_theorem_applications_to_available(
                            theorem_environment,
                            &[(*tactic_index, application.clone())],
                            &proof_label,
                            Some(path_index),
                            path_requirements,
                            &application_context,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
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
                        if !path_requirements.contains(&fact) {
                            path_requirements.push(fact);
                        }
                    }
                    PostExecutionTactic::Choose(choice) => {
                        existence_tactics.push(ProofTactic::Choose(choice.clone()));
                    }
                    PostExecutionTactic::Witness(witness) => {
                        existence_tactics.push(ProofTactic::Witness(witness.clone()));
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
                    }
                    PostExecutionTactic::Simp => {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closed_claims[claim_index]
                                || !matches!(claim, FunctionClaimRef::Ensure(_, _))
                            {
                                continue;
                            }
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
                    specification: specification.clone(),
                    theorem: theorem.clone(),
                });
            }
        }
        Ok(verified)
    })();
    result.map_err(|error| add_proof_branch_path(error, &branch_path))
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
        let tactic = &indexed_tactic.tactic;
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
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Transport { source, target } => {
                if replay.is_at_function_entry() || replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                    )));
                }
                let pre_state = replay.execution_start_state(&state);
                let source = lower_point_proposition(
                    source,
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
                if !requirement_pure_facts.contains(&source) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires an exact source fact: {}",
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
                    target,
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
                let mut transport_facts = requirement_pure_facts.clone();
                transport_facts.extend(
                    replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                let transport_assumptions = assumptions_from_propositions(&transport_facts);
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
                    requirement_pure_facts.push(target);
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Step | ProofTactic::CertifiedStatementStep(_) => {
                let (prerequisite_policy, certified_prerequisites) = match tactic {
                    ProofTactic::Step => (StatementPrerequisitePolicy::Exact, &[][..]),
                    ProofTactic::CertifiedStatementStep(derivations) => (
                        StatementPrerequisitePolicy::Certified,
                        derivations.as_slice(),
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
                    prerequisite_policy,
                    StatementFactTransportPolicy::None,
                    LoopStepPolicy::EnterBody,
                )?;
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
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    LoopStepPolicy::EnterBody,
                )?;
                let certificate =
                    TacticCertificate::from_proof_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_step` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let certificate_tactics = certificate
                    .tactics()
                    .iter()
                    .cloned()
                    .map(|tactic| IndexedTactic {
                        index: tactic_index,
                        tactic,
                    })
                    .collect::<Vec<_>>();
                let result = replay_linear_tactics(
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
                    &certificate_tactics,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteThenStep | ProofTactic::ExecuteElseStep => {
                let entered = execute_branch_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                    Some(matches!(tactic, ProofTactic::ExecuteThenStep)),
                    &[],
                    StatementPrerequisitePolicy::Contextual,
                    StatementFactTransportPolicy::Automatic,
                    BranchStepPolicy::RequireProven,
                )?;
                debug_assert!(entered);
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteRest => {
                execute_rest_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name(tactic),
                    matches!(tactic, ProofTactic::ExecuteRest),
                )?;
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
                execute_until_statement(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    statement_index,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::BoundedExecute => {
                bounded_execute_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    claim_label,
                    tactic_index,
                )?;
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
                requirement_pure_facts = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &requirement_pure_facts,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
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
                    )?;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                }
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
                let fact = prove_have_at_current_point(
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
                )?;
                if !requirement_pure_facts.contains(&fact) {
                    requirement_pure_facts.push(fact);
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
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
                if !exact_fact_is_available(source, &requirement_pure_facts) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport is missing exact source {source:?}"
                    )));
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
    }

    Ok(ProofReplayContext {
        state,
        pure_facts: requirement_pure_facts,
        replay,
        branch_path,
    })
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
                let mut branch_contexts = execute_internal_proof(
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
                contexts.append(&mut branch_contexts);
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
        context
            .replay
            .case_assumptions
            .push((tactic_index, condition.clone(), value));
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
    context.pure_facts.push(if value {
        proposition
    } else {
        Proposition::Not(Box::new(proposition))
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
        if is_memory_effect_proposition(fact.proposition()) && !target.contains(fact) {
            target.push(fact.clone());
        }
    }
}

fn is_memory_effect_proposition(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. } | Proposition::CMemoryEffectSummary { .. }
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
    )?;
    if matches!(branch_step_policy, BranchStepPolicy::RequireProven)
        && condition_transitions.len() != 1
    {
        let expected = requested_branch.map_or("one exact truth value", |take_then| {
            if take_then { "true" } else { "false" }
        });
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove that the next C `if` condition `{}` is {expected}; got {} feasible condition paths\n{}",
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

    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_condition_transition_certificate(replay, &condition_transition);
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
        append_condition_transition_certificate(replay, &condition_transition);
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
    let (transitions, _) = certified_statement_transitions(
        &current_state,
        available_pure_facts,
        &step_statement,
        function_environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &transition_label,
        &mut replay.next_opaque_call,
        prerequisite_policy,
        fact_transport_policy,
        certified_prerequisites,
    )?;
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
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires exactly one statement successor, got {}",
            transitions.len()
        )));
    }
    let transition = transitions
        .into_iter()
        .next()
        .expect("one statement transition was required");
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_statement_transition_certificate(replay, &transition);
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
            *state = next_state;
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
                    StatementPrerequisitePolicy::Contextual,
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
            StatementPrerequisitePolicy::Contextual,
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

    merge_bounded_execution_frontiers(
        replay,
        state,
        available_pure_facts,
        function,
        arguments,
        completed,
        claim_label,
        tactic_index,
    )
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
    tactic_name: &str,
    record_straight_line_snapshots: bool,
) -> Result<(), ClickError> {
    if record_straight_line_snapshots {
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
            replay.next_opaque_call = 0;
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
                tactic_name,
                &[],
                StatementPrerequisitePolicy::Contextual,
                StatementFactTransportPolicy::Automatic,
                LoopStepPolicy::ApplyVerifiedRule,
            )?;
        }
    }

    if record_straight_line_snapshots {
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
    }
    let assumptions = assumptions_from_propositions(available_pure_facts);
    match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => {
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                state.clone(),
                prove_symbolic_c_function_verification_paths_with_environment(
                    state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    assumptions.clone(),
                    function_environment.clone(),
                    CExecutionSemantics::APPLY_VERIFIED_RULES,
                ),
            )?;
        }
        ProofExecutionPoint::StatementEntry { remaining, .. } => {
            let remaining = remaining_with_execution_continuations(replay, remaining);
            let execution = prove_symbolic_c_execution_paths_with_environment(
                state.clone(),
                remaining,
                assumptions.clone(),
                function_environment.clone(),
                CExecutionSemantics::APPLY_VERIFIED_RULES,
            );
            let Some(execution_start_state) = replay.frontier.execution_start_state.clone() else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` has no execution start state"
                )));
            };
            let completed = complete_segmented_function_execution(
                execution,
                &execution_start_state,
                function,
                arguments,
                available_pure_facts,
                &assumptions,
                claim_label,
                tactic_index,
                tactic_name,
            )?;
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            *state = replay_state;
        }
        ProofExecutionPoint::FunctionExit { .. } => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
            )));
        }
    }
    Ok(())
}

fn remaining_with_execution_continuations(
    replay: &TacticReplayState,
    current: &CStatement,
) -> CStatement {
    replay
        .frontier
        .continuations
        .iter()
        .rev()
        .filter_map(|continuation| continuation.remaining.as_ref())
        .fold(current.clone(), |body, continuation| {
            c_seq(body, continuation.clone())
        })
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
        replay.next_opaque_call = 0;
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
            StatementPrerequisitePolicy::Contextual,
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
    replay.next_opaque_call = 0;
    record_current_statement_entry(
        replay,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        "execute_until",
    )?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn complete_segmented_function_execution(
    execution: crate::kernel::SymbolicCExecution,
    execution_start_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    available_pure_facts: &[Proposition],
    assumptions: &Assumptions,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<crate::kernel::SymbolicCExecution, ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` hit execution limit {limit:?}"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced no suffix execution paths"
        )));
    }
    let mut completed_paths = Vec::new();
    for path in execution.paths() {
        let Proposition::CStatementExecutes { outcome, .. } =
            implication_body(path.theorem().proposition())
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` saw unexpected suffix theorem"
            )));
        };
        let mut path_pure_facts = available_pure_facts.to_vec();
        path_pure_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        let return_assumptions = assumptions_from_propositions(&path_pure_facts);
        let (outcome, obligations) = c_function_outcome_from_statement_outcome(
            execution_start_state,
            function,
            outcome.clone(),
            path.obligations().to_vec(),
            &return_assumptions,
        );
        completed_paths.push((outcome, path.facts().to_vec(), obligations));
    }
    Ok(certify_c_function_execution_paths_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        assumptions.clone(),
        completed_paths,
    ))
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
            let resources = post_state
                .resources()
                .clone()
                .without_fact(&lowered, &assumptions)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` failed: {}",
                        describe_resource_clause(resource),
                        describe_missing_resource_fact(
                            &lowered,
                            available_pure_facts,
                            post_state.resources().facts(),
                            parameters,
                            arguments,
                            execution_pure_facts
                        )
                    ))
                })?;
            post_state = post_state.with_resource_context(resources);
        }

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

enum AutoExecutionKind {
    Frame,
    LoopVerification,
}

impl AutoExecutionKind {
    fn proof_kind(&self) -> ProofKind {
        match self {
            Self::Frame => ProofKind::Frame,
            Self::LoopVerification => ProofKind::LoopVerification,
        }
    }

    fn tactic_name(&self) -> &'static str {
        match self {
            Self::Frame => "frame",
            Self::LoopVerification => "auto",
        }
    }
}

fn with_proof_tactics(
    mut theorems: Vec<VerifiedCTheorem>,
    proof_tactics: Option<Vec<ProofTactic>>,
) -> Vec<VerifiedCTheorem> {
    if let Some(proof_tactics) = proof_tactics {
        for theorem in &mut theorems {
            theorem.proof_tactics = Some(proof_tactics.clone());
        }
    }
    theorems
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

fn certified_proof_tactics(
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
    candidates: Vec<Vec<ProofTactic>>,
) -> Option<Vec<ProofTactic>> {
    candidates.into_iter().find(|tactics| {
        prove_claim_by_tactics(
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
            tactics,
        )
        .is_ok()
    })
}

fn frame_tactic_candidates() -> Vec<Vec<ProofTactic>> {
    vec![vec![ProofTactic::ExecuteRest, ProofTactic::Frame(None)]]
}

fn bounded_execution_tactic_candidates(claim: &FunctionClaimRef<'_>) -> Vec<Vec<ProofTactic>> {
    match claim {
        FunctionClaimRef::Ensure(_, _) => vec![
            vec![ProofTactic::BoundedExecute, ProofTactic::Simp],
            vec![ProofTactic::BoundedExecute],
        ],
        FunctionClaimRef::Effect(_, _) => {
            vec![vec![ProofTactic::BoundedExecute, ProofTactic::Frame(None)]]
        }
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
            let mut simp = base.clone();
            simp.push(ProofTactic::Simp);

            let direct = base;
            vec![simp, direct]
        }
        FunctionClaimRef::Effect(_, _) => {
            let mut frame = base.clone();
            frame.push(ProofTactic::Frame(None));

            let direct = base;
            vec![frame, direct]
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

fn execution_obligation_error(
    execution: &crate::kernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ClickError> {
    execution_obligation_error_for_tactic(
        "auto",
        execution,
        ensure_label,
        requirement_pure_facts,
        resource_facts,
        parameters,
        arguments,
    )
}

fn execution_obligation_error_for_tactic(
    tactic_name: &str,
    execution: &crate::kernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ClickError> {
    if let Some(limit) = execution.limit() {
        return Some(ClickError::new(format!(
            "`{tactic_name}` hit execution limit {limit:?} for `{ensure_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Some(ClickError::new(format!(
            "`{tactic_name}` could not prove any complete execution path for `{ensure_label}`"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Some(ClickError::new(format!(
                "`{tactic_name}` failed for `{ensure_label}` path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    requirement_pure_facts,
                    resource_facts,
                    parameters,
                    arguments,
                    path.facts()
                )
            )));
        }
    }

    None
}

fn prove_claim_from_execution(
    execution: &crate::kernel::SymbolicCExecution,
    execution_kind: AutoExecutionKind,
    source_path: &str,
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let proof_kind = execution_kind.proof_kind();
    let tactic_name = execution_kind.tactic_name();
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{tactic_name}` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{tactic_name}` could not prove any complete execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`{tactic_name}` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  pure facts: {}\n  execution pure facts: {}",
                    describe_pure_facts(requirement_pure_facts),
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        path_requirements = project_outcome_resource_facts(
            resource_environment,
            parameters,
            arguments,
            state,
            &outcome,
            &path_requirements,
            predicate_environment,
            click_function_environment,
            claim_label,
            path_index,
        )?;
        let program_point_states = ProgramPointStates::new();
        check_function_claim(
            claim_label,
            path_index,
            &path.execution_facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            &outcome,
            predicate_environment,
            click_function_environment,
            &program_point_states,
            &[],
        )?;
        let specification = c_function_specification(
            state.clone(),
            arguments.to_vec(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = match execution_kind {
            AutoExecutionKind::Frame | AutoExecutionKind::LoopVerification => {
                prove_c_function_satisfies_specification_from_symbolic_path(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    path.facts(),
                    path.obligations(),
                )
            }
        };

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind,
            proof_tactics: None,
            specification,
            theorem,
        });
    }

    Ok(verified)
}
