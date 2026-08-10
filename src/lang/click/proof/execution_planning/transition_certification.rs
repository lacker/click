use super::*;

pub(in crate::lang::click::proof) fn certified_condition_transitions(
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
            if derivation_replays_with_materialized_context(derivation, pure_facts)? {
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
    } else if matches!(
        prerequisite_policy,
        StatementPrerequisitePolicy::Certified | StatementPrerequisitePolicy::Explicit
    ) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
    }
    let evaluation = prove_symbolic_c_condition_evaluation(
        state.clone(),
        condition.clone(),
        assumptions.clone(),
    );
    if let Some(limit) = evaluation.limit() {
        if matches!(limit, crate::kernel::ExecutionLimit::Deadline) {
            return Err(ClickError::new(format!(
                "verification budget exhausted inside {}",
                crate::instrumentation::deadline_context()
            )));
        }
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
                        minimal_proposition_derivation(proposition, pure_facts)?
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

pub(in crate::lang::click) fn certified_statement_transitions(
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
    let mut assumptions = assumptions_from_propositions(pure_facts);
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Certified) {
        for derivation in certified_prerequisites {
            if derivation_replays_with_materialized_context(derivation, pure_facts)? {
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
    let execute = || {
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            state.clone(),
            statement.clone(),
            assumptions,
            function_environment.clone(),
            execution_semantics,
            &mut budget,
        )
    };
    let precise_call_provenance =
        matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
            && statement_contains_call(statement);
    let ((execution, loop_rule), mut planning_premises) = if precise_call_provenance {
        crate::kernel::collect_reasoning_provenance(execute)
    } else {
        let planning_premises =
            (matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
                && (statement_consults_conditions(state, statement)
                    || context_reasons_about_memory(state, &transition_pure_facts)))
            .then(|| ambient_condition_facts(pure_facts))
            .unwrap_or_default();
        (execute(), planning_premises)
    };
    if precise_call_provenance {
        planning_premises.retain(|premise| exact_fact_is_available(premise, pure_facts));
        let mut leaf_premises = Vec::new();
        for premise in planning_premises {
            // An exact consumed premise is already the smallest stable
            // certificate dependency. Do not replace it with a different
            // ambient fact that can re-derive it: that would turn a simple
            // statement step back into heuristic reasoning during replay.
            if pure_facts.contains(&premise) {
                if !leaf_premises.contains(&premise) {
                    leaf_premises.push(premise);
                }
                continue;
            }
            let alternatives = pure_facts
                .iter()
                .filter(|available| *available != &premise)
                .cloned()
                .collect::<Vec<_>>();
            if let Some(derivation) = minimal_proposition_derivation(&premise, &alternatives)? {
                for dependency in derivation.context_premises() {
                    if exact_fact_is_available(&dependency, pure_facts)
                        && !leaf_premises.contains(&dependency)
                    {
                        leaf_premises.push(dependency);
                    }
                }
            } else if !leaf_premises.contains(&premise) {
                leaf_premises.push(premise);
            }
        }
        planning_premises = leaf_premises;
    }
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
        statement_contains_call(statement),
    )?;
    for transition in &mut transitions {
        transition.planning_premises = planning_premises.clone();
    }
    Ok((transitions, loop_rule))
}

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

/// Whether anything in this proof context can turn a condition into a memory or
/// resource conclusion.
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

/// Whether executing this non-call statement can consult ambient conditions.
fn statement_consults_conditions(state: &CState, statement: &CStatement) -> bool {
    fn expression_consults(expression: &CExpression) -> bool {
        !matches!(expression, CExpression::Value(_) | CExpression::Variable(_))
    }
    match statement {
        CStatement::Skip | CStatement::Declare { .. } => false,
        CStatement::Assign { name, expression } => {
            state.local_object_type(name) == Some(CType::UInt8) || expression_consults(expression)
        }
        CStatement::Return(expression) => expression_consults(expression),
        CStatement::Seq(first, second) => {
            statement_consults_conditions(state, first)
                || statement_consults_conditions(state, second)
        }
        CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::If { .. }
        | CStatement::While { .. } => true,
    }
}

pub(in crate::lang::click::proof) fn certified_loop_exit_transitions_with_proven_phases(
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
        statement_contains_call(statement),
    )
}

fn statement_contains_call(statement: &CStatement) -> bool {
    match statement {
        CStatement::CallAssign { .. } | CStatement::Call { .. } => true,
        CStatement::Seq(first, second) => {
            statement_contains_call(first) || statement_contains_call(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => statement_contains_call(then_branch) || statement_contains_call(else_branch),
        CStatement::While { body, .. } => statement_contains_call(body),
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => false,
        CStatement::HeapAllocate { .. } | CStatement::HeapFree { .. } => false,
    }
}

pub(in crate::lang::click::proof) fn is_internal_snapshot_frame_witness(
    fact: &Proposition,
) -> bool {
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
        if matches!(limit, crate::kernel::ExecutionLimit::Deadline) {
            return Err(ClickError::new(format!(
                "verification budget exhausted inside {}",
                crate::instrumentation::deadline_context()
            )));
        }
        return Err(ClickError::new(format!(
            "{context_label} hit execution limit {limit:?}"
        )));
    }
    let has_failure_path = execution.paths().iter().any(|path| {
        matches!(
            implication_body(path.theorem().proposition()),
            Proposition::CStatementVerifies {
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
                            search_condition_derivation(&premise, pure_facts)?
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
                            minimal_proposition_derivation(&premise, &theorem_context)?;
                        let Some(derivation) = derivation else {
                            if has_failure_path {
                                if !theorem_context.contains(&premise) {
                                    theorem_context.push(premise);
                                }
                                continue;
                            }
                            return Err(ClickError::new(format!(
                                "{context_label} used an assumption-derived theorem premise without a replayable derivation: {}",
                                describe_derivation_failure(&premise, &theorem_context),
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
                        minimal_proposition_derivation(proposition, pure_facts)?
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
                            "{context_label} used an assumption-derived execution fact without a replayable derivation: {}",
                            describe_derivation_failure(proposition, pure_facts),
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
                            // `step() using` exposes a deliberately small premise
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
                                search_condition_derivation(proposition, pure_facts)?
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
                                        "{context_label} is missing exact prerequisite{}: {}",
                                        obligation
                                            .context()
                                            .map(|context| format!(" ({context})"))
                                            .unwrap_or_default(),
                                        describe_derivation_failure(proposition, pure_facts),
                                    ))
                                })
                                .map(Some)?
                        } else {
                            return Err(ClickError::new(format!(
                                "{context_label} is missing certified prerequisite{}: {}",
                                obligation
                                    .context()
                                    .map(|context| format!(" ({context})"))
                                    .unwrap_or_default(),
                                describe_derivation_failure(proposition, pure_facts),
                            )));
                        }
                    }
                    StatementPrerequisitePolicy::Contextual => {
                        if prerequisite_assumptions.proves(proposition) {
                            None
                        } else {
                            return Err(ClickError::new(format!(
                                "{context_label} is missing prerequisite{}: {}",
                                obligation
                                    .context()
                                    .map(|context| format!(" ({context})"))
                                    .unwrap_or_default(),
                                describe_derivation_failure(proposition, pure_facts),
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
                                minimal_proposition_derivation(proposition, &derivation_facts)?
                                    .ok_or_else(|| {
                                    ClickError::new(format!(
                                        "{context_label} is missing prerequisite{}: {}",
                                        obligation
                                            .context()
                                            .map(|context| format!(" ({context})"))
                                            .unwrap_or_default(),
                                        describe_derivation_failure(
                                            proposition,
                                            &derivation_facts,
                                        ),
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
            let Proposition::CStatementVerifies {
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
                    planning_premises: Vec::new(),
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
                planning_premises: Vec::new(),
                fact_transports: Vec::new(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((transitions, loop_rule))
}
