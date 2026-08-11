use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn fold_composite_resource_at_current_point(
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
    close_or_initialize_composite_resource_at_current_point(
        resource_environment,
        resource,
        claim_label,
        tactic_index,
        available_pure_facts,
        parameters,
        arguments,
        pre_state,
        state,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        ResourceBodyClosure::Initialize,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn close_open_resource_at_current_point(
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
    preserve_exposed_body: bool,
) -> Result<CState, ClickError> {
    close_or_initialize_composite_resource_at_current_point(
        resource_environment,
        resource,
        claim_label,
        tactic_index,
        available_pure_facts,
        parameters,
        arguments,
        pre_state,
        state,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        ResourceBodyClosure::CloseOpen {
            preserve_exposed_body,
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn close_or_initialize_composite_resource_at_current_point(
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
    closure: ResourceBodyClosure,
) -> Result<CState, ClickError> {
    let surface_propositions = SurfacePropositionMap::default();
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
        &surface_propositions,
        parameters,
        arguments,
        pre_state,
        outcome,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        closure,
    )?;
    let CFunctionOutcome::Return { state, .. } = outcome else {
        unreachable!("folding a synthetic return outcome preserves its outcome kind")
    };
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn lower_point_proposition(
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
fn lower_point_proposition_with_memory_resolution(
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
    let assumptions =
        assumptions_from_propositions(available).defer_non_exact_loadability_obligations();
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

fn reverse_surface_equality(proposition: &ClickProposition) -> Option<ClickProposition> {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = proposition
    else {
        return None;
    };
    Some(ClickProposition::Comparison {
        left: right.clone(),
        operator: ComparisonOperator::Equal,
        right: left.clone(),
    })
}

fn reverse_kernel_equality(proposition: Proposition) -> Option<Proposition> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(right, left), true),
        ),
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::PointerEqual(right, left), true),
        ),
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(right, left), true),
        ),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn prove_have_at_current_point(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
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
        transition_facts,
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
pub(in crate::lang::click::proof) fn plan_smart_have_at_current_point(
    have: &ProofHave,
    claim_label: &str,
    outer_tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    prelowered_goal: Option<&Proposition>,
) -> Result<(Proposition, InternalProofPlan), ClickError> {
    // Plan and replay this proof once. Surface expansion must lower this exact
    // plan; it must not search for a different proof if lowering is incomplete.
    // Snapshot transport belongs to the statement transition that changed the
    // memory and reaches a later `have` as an exact current-state assumption.
    let restricted_simp = matches!(
        &have.proof,
        Proof::Script(tactics)
            if matches!(tactics.last(), Some(ProofTactic::SimpUsing(_)))
    );
    // Restricted simplification must reason from its named equalities; goal
    // lowering must not silently apply those (or other ambient equalities)
    // before the smart plan is recorded, or expansion loses a required proof
    // step. Keep only the facts needed to spell direct program values.
    let direct_lowering_facts = if restricted_simp {
        facts_for_restricted_simp_lowering(available)
    } else {
        facts_for_smart_have_lowering(available)
    };
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
        Err(message) if restricted_simp => {
            return Err(ClickError::new(format!(
                "`{claim_label}` have proof {outer_tactic_index}: could not lower restricted `simp` goal without applying an ambient equality: {message}"
            )));
        }
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
            Err(fallback_message) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: could not lower pure goal: {fallback_message}\n  direct lowering also failed: {message}"
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
    let restricted_surfaces = match &have.proof {
        Proof::Script(tactics) => tactics.last().and_then(|tactic| match tactic {
            ProofTactic::SimpUsing(simp) => Some(&simp.premises),
            _ => None,
        }),
        _ => None,
    };
    let reasoning_available = if let Some(surfaces) = restricted_surfaces {
        // Restricted simplification limits which facts may prove the goal,
        // not which certified bounds may establish that a named premise's
        // memory expressions are defined. Keep scalar/order facts for that
        // lowering step; the `exact` vector below remains the entire
        // simplifier context.
        let lowering_facts = facts_for_restricted_simp_lowering(&available);
        let mut exact = Vec::new();
        for surface in surfaces {
            if let Some(recorded) = surface_propositions.available_kernel(surface, &available) {
                exact.push(recorded.clone());
                continue;
            }
            let lowered = lower_point_proposition(
                surface,
                &lowering_facts,
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
                    "`{claim_label}` have proof {outer_tactic_index}: could not lower `simp` premise: {message}"
                ))
            })?;
            let exact_available = available
                .iter()
                .find(|fact| *fact == &lowered || condition_polarity_equivalent(fact, &lowered))
                .cloned()
                .or_else(|| {
                    exact_proper_conjunct_is_available(&lowered, &available)
                        .then_some(lowered.clone())
                })
                .or_else(|| materialization_equivalent_available_fact(&lowered, &available))
                .or_else(|| {
                    // A listed `at(...)` fact can denote an available kernel
                    // fact whose load atoms carry another certified snapshot.
                    // Bridging establishes identity of that one premise; it
                    // does not add the rest of `available` to simp's context.
                    snapshot_bridged_fact_is_available(&lowered, &available, &[])
                        .then_some(lowered.clone())
                });
            let Some(exact_fact) = exact_available else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: `simp` listed a premise that is not exactly available\n  Click: {}\n  lowered: {}",
                    describe_click_proposition(surface),
                    describe_pure_fact(&lowered, parameters, arguments),
                )));
            };
            exact.push(exact_fact);
        }
        exact
    } else {
        available.clone()
    };
    let assumptions = assumptions_from_propositions(&reasoning_available);
    if reasoning_available.contains(&goal) {
        let plan = InternalProofPlan::from_surface_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    if matches!(normalize_proposition(&goal), SimpProposition::True) {
        let plan = InternalProofPlan::from_surface_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a simple replay tactic");
        return Ok((fact, plan));
    }
    if quantified_replay_equivalent_available_fact(&goal, &reasoning_available).is_some() {
        let plan = InternalProofPlan::from_surface_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    let normalized_fact = normalize_direct_atomic_memory_loads(&goal);
    if let Some(equivalent) = reasoning_available
        .iter()
        .find(|available| normalize_direct_atomic_memory_loads(available) == normalized_fact)
        && let Some(derivation) =
            minimal_proposition_derivation(&goal, std::slice::from_ref(equivalent))?
    {
        let plan = InternalProofPlan::from_operations(vec![
            InternalProofOperation::ExactPropositionDerivation(derivation),
        ]);
        return Ok((fact, plan));
    }
    if let Some(derivation) = search_condition_derivation(&goal, &reasoning_available)? {
        let plan = InternalProofPlan::from_operations(vec![
            InternalProofOperation::ExactPropositionDerivation(derivation),
        ]);
        return Ok((fact, plan));
    }

    let Some(plan) = plan_simp_certificate(&goal, &assumptions) else {
        let mut message = format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {}",
            describe_missing_pure_fact(
                &goal,
                &reasoning_available,
                state.resources().facts(),
                parameters,
                arguments,
                &[],
            )
        );
        if matches!(goal, Proposition::ConditionIs(_, _)) {
            message.push_str("\n  ");
            message.push_str(&describe_condition_search_miss(
                &goal,
                &reasoning_available,
                parameters,
                arguments,
            ));
        }
        return Err(ClickError::new(message));
    };
    if !replay_simp_certificate(&goal, &assumptions, &plan) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: planned smart `have` certificate did not replay"
        )));
    }
    Ok((fact, plan))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn prove_have_at_point(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
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
        transition_facts,
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
pub(in crate::lang::click::proof) fn prove_pure_proposition_at_point(
    proposition: &ClickProposition,
    prelowered_goal: Option<&Proposition>,
    proof: &Proof,
    proof_name: &str,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
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
        Proof::Script(tactics) => (expand_proof_if_cases(tactics)?, false),
        Proof::Default | Proof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => (
            vec![ExpandedProofCase {
                tactics: Vec::new(),
                assumptions: Vec::new(),
            }],
            true,
        ),
        Proof::Tactic(SmartTactic::Frame) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `frame` is not available in a pure proof"
            )));
        }
    };
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
            transition_facts,
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
pub(in crate::lang::click::proof) fn prove_pure_proposition_case_at_point(
    proposition: &ClickProposition,
    prelowered_goal: Option<&Proposition>,
    proof_case: &ExpandedProofCase,
    tactic_simp: bool,
    proof_name: &str,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
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
    let mut surface_logical_goal = proposition.clone();
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
                // Later `intro` tactics track the surface goal to bind a
                // universal binder's Click name; a goal that is itself the
                // unfolded predicate call must expose its definition here.
                if let Ok(unfolded) = unfold_structural_invariant_proposition(
                    predicate_environment,
                    &surface_logical_goal,
                    std::slice::from_ref(name),
                ) {
                    surface_logical_goal = unfolded;
                }
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
                    transition_facts,
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
            ProofTactic::TransportUsing {
                source: surface_source,
                target: surface_target,
                premises: surface_premises,
            } => {
                let lower = |surface: &ClickProposition, facts: &[Proposition]| {
                    surface_propositions
                        .and_then(|propositions| {
                            propositions.available_kernel(surface, facts).cloned()
                        })
                        .map(Ok)
                        .unwrap_or_else(|| {
                            lower_point_proposition_with_values(
                                surface,
                                facts,
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
                };
                let mut explicit_premises = surface_premises
                    .iter()
                    .map(|premise| lower(premise, &available))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `transport using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `transport using` requires an exact available premise"
                        )));
                    }
                }

                let ordinary_source = lower(surface_source, &available).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `transport` source: {message}"
                    ))
                })?;
                let source = if matches!(normalize_proposition(&ordinary_source), SimpProposition::True)
                    && (proposition_contains_at_expression(surface_source)
                        || proposition_contains_old_expression(surface_source))
                    && let Some(result) = result
                {
                    lower_outcome_proposition_symbolically_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        result,
                        &available,
                        surface_source,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                    )
                    .unwrap_or_else(|_| ordinary_source.clone())
                } else {
                    ordinary_source.clone()
                };
                // Materialization proved the surface source, while the
                // symbolic spelling retains the load identity required by
                // the explicit frame transport. This is the same checked
                // source fact, not an additional ambient premise.
                if source != ordinary_source
                    && matches!(normalize_proposition(&ordinary_source), SimpProposition::True)
                {
                    if !available.contains(&source) {
                        available.push(source.clone());
                    }
                    if !explicit_premises.contains(&source) {
                        explicit_premises.push(source.clone());
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
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
                if !exact_fact_is_available(&source, &explicit_premises)
                    && selected_assumptions
                        .derive_atomic_proposition(&source)
                        .is_none()
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `transport using` source is not derivable from its explicit premises"
                    )));
                }

                // A source spelling may intentionally identify a retained
                // fact from an older snapshot. The target, however, denotes
                // the fact being established at this proof frontier. Looking
                // it up in the recorded-surface map can silently select the
                // older source again when the two surface spellings coincide.
                let target = lower_point_proposition_with_values(
                    surface_target,
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
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `transport` target: {message}"
                    ))
                })?;
                if !exact_fact_is_available(&target, &available)
                    && materialization_equivalent_available_fact(&target, &available).is_none()
                {
                    let transition_facts =
                        fact_transport_transition_facts(transition_facts, &source);
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
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: no certified transport connects `{}` to `{}` using {} explicit premise(s)",
                            describe_click_proposition(surface_source),
                            describe_click_proposition(surface_target),
                            surface_premises.len(),
                        )));
                    }
                }
                if !available.contains(&target) {
                    available.push(target);
                }
            }
            ProofTactic::InstantiateUsing {
                quantified: surface_quantified,
                argument,
                premises: surface_premises,
            } => {
                let lower = |surface: &ClickProposition, facts: &[Proposition]| {
                    surface_propositions
                        .and_then(|propositions| {
                            propositions.available_kernel(surface, facts).cloned()
                        })
                        .map(Ok)
                        .unwrap_or_else(|| {
                            lower_point_proposition_with_values(
                                surface,
                                facts,
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
                };
                let explicit_premises = surface_premises
                    .iter()
                    .map(|premise| lower(premise, &available))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `instantiate using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `instantiate using` requires an exact available premise"
                        )));
                    }
                }
                let lowered_quantified =
                    lower(surface_quantified, &available).map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `instantiate` quantified fact: {message}"
                        ))
                    })?;
                let quantified_fact = if exact_fact_is_available(&lowered_quantified, &available)
                {
                    lowered_quantified
                } else if let Some(matched) =
                    quantified_replay_equivalent_available_fact(&lowered_quantified, &available)
                {
                    matched
                } else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `instantiate` quantified fact is not exactly available: {}",
                        describe_click_proposition(surface_quantified)
                    )));
                };
                let assumptions = assumptions_from_propositions(&available);
                let mut active_functions = BTreeSet::new();
                let argument_value = evaluate_contract_expression_with_environment(
                    &values,
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    &assumptions,
                    argument,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    &mut active_functions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not evaluate `instantiate` argument: {message}"
                    ))
                })?;
                let CValue::Int32(argument_term) = argument_value else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `instantiate` argument did not evaluate to int32"
                    )));
                };
                let Proposition::ForAll { var, sort, body } = &quantified_fact else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `instantiate` requires a universally quantified fact"
                    )));
                };
                if *sort != Sort::CInt32 {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `instantiate` supports only int32 universals"
                    )));
                }
                let instantiated = substitute_int32_variable_in_proposition(
                    body,
                    *var,
                    argument_term.clone(),
                );
                let (guards, conclusion) =
                    discharge_instantiated_guards(instantiated, &explicit_premises).map_err(
                        |message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `instantiate` failed: {message}"
                            ))
                        },
                    )?;
                let theorem =
                    prove_forall_int32_application(&quantified_fact, argument_term, &guards)
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: kernel rejected the `instantiate` application"
                            ))
                        })?;
                let Proposition::Implies(theorem_quantified, mut theorem_body) =
                    theorem.proposition().clone()
                else {
                    return Err(ClickError::new(
                        "invalid universal instantiation theorem",
                    ));
                };
                if theorem_quantified.as_ref() != &quantified_fact {
                    return Err(ClickError::new(
                        "universal instantiation changed its quantified premise",
                    ));
                }
                for guard in &guards {
                    let Proposition::Implies(theorem_guard, next) = theorem_body.as_ref() else {
                        return Err(ClickError::new(
                            "universal instantiation omitted a discharged premise",
                        ));
                    };
                    if theorem_guard.as_ref() != guard {
                        return Err(ClickError::new(
                            "universal instantiation changed a discharged premise",
                        ));
                    }
                    theorem_body = next.clone();
                }
                if theorem_body.as_ref() != &conclusion {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: universal instantiation produced an unexpected conclusion"
                    )));
                }
                if !available.contains(&conclusion) {
                    available.push(conclusion);
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
            ProofTactic::Extract(surface_proposition) => {
                let proposition = lower_point_proposition_with_values(
                    surface_proposition,
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
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: `extract` could not lower proposition: {message}"
                    ))
                })?;
                if !exact_proper_conjunct_is_available(&proposition, &available) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: `extract` proposition is not a proper conjunct of an exact available fact: {}",
                        describe_pure_fact(&proposition, parameters, arguments)
                    )));
                }
                if !available.contains(&proposition) {
                    available.push(proposition);
                }
            }
            ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Contradiction(_)
            | ProofTactic::SimpUsing(_)
            | ProofTactic::Rewrite(_) => {
                let mut prepared_derivation_lowering_facts = None;
                let direct_goal_lowering_facts =
                    matches!(tactic, ProofTactic::Assumption | ProofTactic::Normalize)
                        .then(|| facts_for_simple_goal_lowering(&available));
                let explicit_premises = match tactic {
                    ProofTactic::SimpUsing(simp) => Some(&simp.premises),
                    _ => None,
                };
                if let Some(explicit_premises) = explicit_premises {
                    let mut lowering_facts = facts_for_direct_derivation_lowering(&available);
                    let mut unresolved = explicit_premises.iter().collect::<Vec<_>>();
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
                        let lowering_facts = prepared_derivation_lowering_facts
                            .as_deref()
                            .or(direct_goal_lowering_facts.as_deref())
                            .unwrap_or(&available);
                        lower_point_proposition_with_values(
                            proposition,
                            lowering_facts,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .or_else(|_| {
                            lower_point_proposition_with_memory_resolution(
                                proposition,
                                lowering_facts,
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
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `normalize` failed because the goal did not normalize to true: {}",
                                describe_pure_fact(&unfolded_goal, parameters, arguments)
                            )));
                        }
                        goal_closed = true;
                    }
                    ProofTactic::Intro
                    | ProofTactic::Split
                    | ProofTactic::Left
                    | ProofTactic::Right
                    | ProofTactic::Contradiction(_) => {
                        let contradiction_fact = match tactic {
                            ProofTactic::Contradiction(surface_fact) => Some(
                                if let Some(recorded) =
                                    surface_propositions.and_then(|propositions| {
                                        propositions.available_kernel(surface_fact, &available)
                                    })
                                {
                                    recorded.clone()
                                } else {
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
                                    })?
                                },
                            ),
                            _ => None,
                        };
                        let mut logical_goal = unfolded_goal;
                        if matches!(tactic, ProofTactic::Intro) {
                            match (&surface_logical_goal, &logical_goal) {
                                (
                                    ClickProposition::ForAll {
                                        c_type: C0Type::Int32,
                                        name,
                                        body,
                                    },
                                    Proposition::ForAll {
                                        var,
                                        sort: Sort::CInt32,
                                        ..
                                    },
                                ) => {
                                    values.insert(
                                        name.clone(),
                                        CValue::Int32(Bitvector32Term::Variable(*var)),
                                    );
                                    surface_logical_goal = body.as_ref().clone();
                                }
                                (
                                    ClickProposition::Implies(_, body),
                                    Proposition::Implies(_, _),
                                )
                                | (ClickProposition::Not(body), Proposition::Not(_)) => {
                                    surface_logical_goal = body.as_ref().clone();
                                }
                                _ => {}
                            }
                        }
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
                    ProofTactic::SimpUsing(simp) => {
                        let derivation_lowering_facts = prepared_derivation_lowering_facts
                            .as_ref()
                            .expect("simp using lowering facts should be prepared");
                        let premises = simp
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
                                        derivation_lowering_facts,
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
                                    "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `simp` premise: {message}"
                                ))
                            })?;
                        plan_restricted_simp_goal(
                            &unfolded_goal,
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
                        let equality = surface_propositions
                            .and_then(|propositions| {
                                propositions
                                    .available_kernel(surface_equality, &available)
                                    .cloned()
                                    .or_else(|| {
                                        let reverse =
                                            reverse_surface_equality(surface_equality)?;
                                        let kernel = propositions
                                            .available_kernel(&reverse, &available)?
                                            .clone();
                                        reverse_kernel_equality(kernel)
                                    })
                            })
                            .map(Ok)
                            .unwrap_or_else(|| {
                                lower_point_proposition_with_values(
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
                            })
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
                    values.clone(),
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .or_else(|_| {
                    lower_point_proposition_with_memory_resolution(
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
                })
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

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn finish_ordered_proof_contexts(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    contexts: Vec<ProofReplayContext>,
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
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut certification_cache = Vec::new();
    let mut captured_paths = Vec::new();
    for context in contexts {
        let path_choices = context.replay.deferred_expansion_path_choices.clone();
        resume_deferred_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            &context.replay,
        )?;
        let path_had_deferred_capture = context.replay.deferred_tactic_capture.is_some();
        let result_before = expansion_capture
            .as_deref()
            .is_some_and(|capture| capture.result.is_some());
        let theorems = finish_ordered_proof_replay(
            expansion_capture.as_deref_mut(),
            context,
            source_path,
            function_block,
            parsed_function,
            claims,
            require_explicit_closers,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function_environment,
            function,
            arguments,
            tactics,
            &mut certification_cache,
        )?;
        for theorem in theorems {
            if !verified.contains(&theorem) {
                verified.push(theorem);
            }
        }
        let path_finished_capture = path_had_deferred_capture
            && !result_before
            && expansion_capture
                .as_deref()
                .is_some_and(|capture| capture.result.is_some());
        if path_finished_capture {
            let captured = take_path_tactic_expansion_capture(expansion_capture.as_deref_mut())?;
            captured_paths.push(SimpleProofBuilder {
                steps: SimpleProof::from_proof_tactics(&captured)
                    .map_err(|error| {
                        ClickError::new(format!(
                            "captured branch expansion was not a simple proof: {error:?}"
                        ))
                    })?
                    .steps()
                    .to_vec(),
                path_choices,
                ..SimpleProofBuilder::default()
            });
        }
    }
    if !captured_paths.is_empty() {
        let tactics = if captured_paths
            .iter()
            .all(|path| path.steps == captured_paths[0].steps)
        {
            captured_paths[0].steps.clone()
        } else {
            synthesize_surface_alternatives(captured_paths).map_err(|message| {
                ClickError::new(format!(
                    "could not merge selected deferred tactic across branch contexts: {message}"
                ))
            })?
        };
        let allow_empty = tactics.is_empty();
        finish_tactic_expansion_capture(
            expansion_capture,
            &SimpleProofBuilder {
                steps: tactics,
                ..SimpleProofBuilder::default()
            },
            allow_empty,
        );
    }
    Ok(verified)
}
