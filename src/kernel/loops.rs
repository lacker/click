use super::prelude::*;

pub(super) fn execute_c_call_assign_paths(
    state: &CState,
    target: &str,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let Some(function) = environment.get_function(function_name) else {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    };

    let paths = execute_c_function_call_paths(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )?
    .into_iter()
    .map(|path| {
        let outcome = match path.outcome {
            CFunctionOutcome::Return { value, mut state } => {
                if value == CValue::Void {
                    return CStatementExecutionPath {
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    };
                }
                if state.locals.is_array_object(target) {
                    return CStatementExecutionPath {
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    };
                }
                sync_stack_local(&mut state, target, &value);
                let c_type = state
                    .locals
                    .object_type(target)
                    .unwrap_or_else(|| value.c_type());
                state.locals.set_typed(target.to_string(), value, c_type);
                CStatementOutcome::Normal(state)
            }
            CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
            CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                CStatementOutcome::UndefinedBehavior(undefined_behavior)
            }
            CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        };

        CStatementExecutionPath {
            outcome,
            facts: path.facts,
            obligations: path.obligations,
        }
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_call_paths(
    state: &CState,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let Some(function) = environment.get_function(function_name) else {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    };

    let paths = execute_c_function_call_paths(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )?
    .into_iter()
    .map(|path| CStatementExecutionPath {
        outcome: match path.outcome {
            CFunctionOutcome::Return { state, .. } => CStatementOutcome::Normal(state),
            CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
            CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                CStatementOutcome::UndefinedBehavior(undefined_behavior)
            }
            CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        },
        facts: path.facts,
        obligations: path.obligations,
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement_paths_with_prefix(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_c_statement_paths(
        state,
        statement,
        &effective_assumptions,
        environment,
        execution_semantics,
        budget,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(CStatementExecutionPath {
            outcome: path.outcome,
            facts,
            obligations,
        })
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement_verification_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    // `Seq` only groups source statements; it is not another statement step.
    if !matches!(statement, CStatement::Seq(_, _)) {
        budget.consume_statement_step()?;
    }
    if execution_semantics.loops == CLoopSemantics::ApplyVerifiedRules
        && matches!(
            statement,
            CStatement::While {
                invariant_checks,
                effect_checks,
                ..
            } if !invariant_checks.is_empty() || !effect_checks.is_empty()
        )
    {
        let Some(rule) = environment.applicable_verified_loop_rule(state, statement, assumptions)
        else {
            return Ok(Vec::new());
        };
        let paths = rule
            .paths
            .iter()
            .cloned()
            .map(|mut path| {
                path.facts = path
                    .facts
                    .into_iter()
                    .map(ExecutionPureFact::into_certified)
                    .collect();
                path
            })
            .collect::<Vec<_>>();
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }
    let paths = match statement {
        CStatement::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in execute_c_statement_verification_paths(
                state,
                first,
                assumptions,
                environment,
                execution_semantics,
                budget,
                variables,
            )? {
                match first_path.outcome {
                    CStatementOutcome::Normal(state) => {
                        paths.extend(execute_c_statement_verification_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            environment,
                            execution_semantics,
                            &first_path.facts,
                            &first_path.obligations,
                            budget,
                            variables,
                        )?);
                    }
                    outcome @ (CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,
                    }),
                }
            }
            paths
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for condition_path in
                evaluate_c_expression_paths(state, condition, assumptions, budget)?
            {
                let CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    CExpressionOutcome::Value(value) => {
                        for truthiness_path in
                            c_truthiness_paths(value, facts, obligations, assumptions)
                        {
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            let branch_assumptions = assumptions_with_path_context(
                                assumptions,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                            );
                            let branch_state =
                                resolve_pending_heap_allocations(state, &branch_assumptions);
                            paths.extend(execute_c_statement_verification_paths_with_prefix(
                                &branch_state,
                                branch,
                                assumptions,
                                environment,
                                execution_semantics,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                                budget,
                                variables,
                            )?);
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        })
                    }
                }
            }
            paths
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } if !invariant_checks.is_empty() || !effect_checks.is_empty() => {
            execute_c_while_verification_paths(
                state,
                condition,
                invariant,
                invariant_checks,
                effect_checks,
                body,
                assumptions,
                environment,
                execution_semantics,
                budget,
                variables,
            )?
        }
        _ => {
            // Loop verification and verified-call execution share one symbolic
            // identity stream. The loop paths allocate through `variables`,
            // while ordinary statement execution allocates opaque-call
            // identities through `budget`; synchronize both sides before and
            // after crossing that boundary so neither can reuse an identity.
            budget.next_kernel_variable = budget.next_kernel_variable.max(variables.next);
            let operation = match statement {
                CStatement::Skip => "verification statement: skip",
                CStatement::Declare { .. } => "verification statement: declare",
                CStatement::Assign { .. } => "verification statement: assign",
                CStatement::CallAssign { .. } => "verification statement: call assign",
                CStatement::Call { .. } => "verification statement: call",
                CStatement::HeapAllocate { .. } => "verification statement: heap allocate",
                CStatement::HeapFree { .. } => "verification statement: heap free",
                CStatement::Assert { .. } => "verification statement: assert",
                CStatement::Return(_) => "verification statement: return",
                CStatement::Store { .. } => "verification statement: store",
                CStatement::TypedStore { .. } => "verification statement: typed store",
                CStatement::While { .. } => "verification statement: while",
                CStatement::Seq(_, _) | CStatement::If { .. } => unreachable!(),
            };
            let paths = crate::instrumentation::measure_operation(
                "kernel",
                "independent kernel execution",
                operation,
                || {
                    execute_c_statement_paths(
                        state,
                        statement,
                        assumptions,
                        environment,
                        execution_semantics,
                        budget,
                    )
                },
            );
            variables.next = variables.next.max(budget.next_kernel_variable);
            paths?
        }
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement_verification_paths_with_prefix(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_c_statement_verification_paths(
        state,
        statement,
        &effective_assumptions,
        environment,
        execution_semantics,
        budget,
        variables,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(CStatementExecutionPath {
            outcome: path.outcome,
            facts,
            obligations,
        })
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_while_verification_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    execute_c_while_exit_paths(
        state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
        assumptions,
        Some(environment),
        execution_semantics,
        false,
        budget,
        variables,
    )
}

/// Checks the state components that a loop back edge cannot silently reset.
/// Scalar locals and ordinary memory cells are handled by the existing loop
/// abstraction and effect checks; heap lifetime, resource ownership, and
/// counted resource populations are separate semantic state and must either
/// be unchanged at the loop-state join.
pub(crate) fn c_loop_state_components_match_at_back_edge(
    top_state: &CState,
    next_state: &CState,
    assumptions: &PureFactContext,
    composite_resource_definitions: &[CCompositeResourceDefinition],
) -> Result<(), String> {
    c_loop_state_components_match_at_back_edge_inner(
        top_state,
        next_state,
        composite_resource_definitions,
        assumptions,
    )
}

fn c_loop_state_components_match_at_back_edge_inner(
    top_state: &CState,
    next_state: &CState,
    composite_resource_definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let mut changed = Vec::new();
    if top_state.memory().heap != next_state.memory().heap {
        changed.push("heap allocation lifetime");
    }
    if !crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
        composite_resource_definitions,
        top_state.memory(),
        top_state.resources(),
        next_state.memory(),
        next_state.resources(),
        assumptions,
    ) {
        changed.push("resource ownership");
    }
    if !crate::kernel::api::counted_populations_definitionally_equal(
        top_state,
        next_state,
        composite_resource_definitions,
        assumptions,
    ) {
        changed.push("counted resource populations");
    }
    if changed.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "loop state join changes {}; the body path does not reach the loop-head state",
            changed.join(", ")
        ))
    }
}

pub(super) fn execute_c_while_exit_paths_with_proven_phases(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    initialization_proven: bool,
    preservation_proven: bool,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    execute_c_while_exit_paths(
        state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
        assumptions,
        (!preservation_proven).then_some(environment),
        execution_semantics,
        initialization_proven,
        budget,
        variables,
    )
}

#[allow(clippy::too_many_arguments)]
fn execute_c_while_exit_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &PureFactContext,
    preservation_environment: Option<&CExecutionEnvironment>,
    execution_semantics: CExecutionSemantics,
    initialization_proven: bool,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut base_obligations = Vec::new();
    for proposition in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, proposition.clone()).is_none() {
            return Ok(Vec::new());
        }
    }

    let entry_obligations = if initialization_proven {
        Vec::new()
    } else {
        collect_invariant_check_obligations(
            state,
            state,
            invariant_checks,
            InvariantPhase::Entry,
            assumptions,
            budget,
        )?
    };
    let (top_state, whole_loop_effect_summaries) =
        prepare_loop_top_state(state, effect_checks, body, assumptions, budget, variables)?;
    let preservation_obligations = if let Some(environment) = preservation_environment {
        collect_loop_preservation_summary(
            state,
            &top_state,
            condition,
            invariant_checks,
            effect_checks,
            &whole_loop_effect_summaries,
            body,
            assumptions,
            environment,
            execution_semantics,
            budget,
            variables,
        )?
        .obligations
    } else {
        Vec::new()
    };
    let mut loop_check_obligations = Vec::new();
    append_required_proof_obligations(&mut loop_check_obligations, assumptions, &entry_obligations);
    append_required_proof_obligations(
        &mut loop_check_obligations,
        assumptions,
        &preservation_obligations,
    );
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();

    let mut paths = Vec::new();
    let invariant_contexts = assume_invariant_checks(
        &top_state,
        state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &base_obligations,
        budget,
    )?;
    let mut has_live_iteration = false;
    for (invariant_facts, invariant_obligations) in &invariant_contexts {
        if !assume_condition_truthiness(
            &top_state,
            condition,
            assumptions,
            invariant_facts,
            invariant_obligations,
            true,
            budget,
        )?
        .is_empty()
        {
            has_live_iteration = true;
            break;
        }
    }
    for (invariant_facts, invariant_obligations) in invariant_contexts {
        let condition_contexts = assume_condition_truthiness(
            &top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            false,
            budget,
        )?;
        for (facts, mut obligations) in condition_contexts {
            append_required_proof_obligations(
                &mut obligations,
                assumptions,
                &loop_check_obligations,
            );
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(top_state.clone()),
                facts,
                obligations,
            });
        }
    }
    if paths.is_empty() {
        let mut obligations = base_obligations;
        append_required_proof_obligations(&mut obligations, assumptions, &loop_check_obligations);
        if !has_live_iteration {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context("loop has neither a safe exit nor a safe iteration"),
            );
        }
        paths.push(CStatementExecutionPath {
            outcome: CStatementOutcome::VerificationDiverges,
            facts: whole_loop_effect_facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InvariantPhase {
    Entry,
    Preservation,
}

pub(super) fn invariant_context(
    check: &CLoopInvariantCheck,
    phase: InvariantPhase,
) -> Option<&str> {
    match phase {
        InvariantPhase::Entry => check.entry_context(),
        InvariantPhase::Preservation => check.preservation_context(),
    }
}

pub(super) fn collect_invariant_check_obligations(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        loop_entry_state,
        invariant_checks,
        phase,
        assumptions,
        budget,
        false,
    )
}

pub(super) fn collect_invariant_check_obligations_without_search(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        loop_entry_state,
        invariant_checks,
        phase,
        assumptions,
        budget,
        true,
    )
}

type VerifiedInvariantPath = (Vec<ExecutionPureFact>, Vec<ProofObligation>);

fn verify_lowered_invariant_path(
    check_index: usize,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
    path: SpecPropositionPath,
    assumptions: &PureFactContext,
) -> Result<Option<VerifiedInvariantPath>, String> {
    let Some((mut merged_facts, merged_obligations)) = merge_execution_pure_facts_and_obligations(
        facts,
        obligations,
        &path.facts,
        &path.obligations,
        assumptions,
    ) else {
        return Ok(None);
    };
    let local = assumptions_with_path_context(assumptions, &merged_facts, &merged_obligations);
    for obligation in merged_obligations
        .iter()
        .filter(|obligation| !obligation.is_assumable())
    {
        let proposition = obligation.proposition();
        let Some(derivation) = local
            .derive_proposition_without_premise_minimization(proposition)
            .or_else(|| local.derive_simp_proposition(proposition))
        else {
            if let Some(context) = crate::instrumentation::exceeded_verification_limit_context() {
                return Err(format!("verification budget exhausted inside {context}"));
            }
            return Err(format!(
                "invariant {check_index} is missing path obligation: {proposition:?}"
            ));
        };
        if !derivation.check(&local) {
            return Err(format!(
                "invariant {check_index} path obligation derivation check failed: {proposition:?}"
            ));
        }
    }
    let Some(derivation) = local
        .derive_proposition_without_premise_minimization(&path.proposition)
        .or_else(|| local.derive_simp_proposition(&path.proposition))
    else {
        if let Some(context) = crate::instrumentation::exceeded_verification_limit_context() {
            return Err(format!("verification budget exhausted inside {context}"));
        }
        return Err(format!(
            "invariant {check_index} is missing path goal: {:?}",
            path.proposition
        ));
    };
    if !derivation.check(&local) {
        return Err(format!(
            "invariant {check_index} path derivation check failed: {:?}",
            path.proposition
        ));
    }
    if !merged_facts
        .iter()
        .any(|fact| fact.proposition() == &path.proposition)
    {
        merged_facts.push(ExecutionPureFact::new(path.proposition));
    }
    Ok(Some((merged_facts, merged_obligations)))
}

pub(super) fn verify_invariant_checks_at_back_edge_using(
    state: &CState,
    loop_entry_state: &CState,
    checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<(), String> {
    let mut contexts = vec![(Vec::new(), Vec::new())];
    for (check_index, check) in checks.iter().enumerate() {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let lowering_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations)
                    .defer_non_exact_condition_reasoning()
                    .defer_non_exact_loadability_obligations();
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &lowering_assumptions,
                budget,
            )
            .map_err(|error| format!("could not lower invariant paths: {error:?}"))?;
            if paths.len() <= 1 {
                for path in paths {
                    if let Some(context) = verify_lowered_invariant_path(
                        check_index,
                        &facts,
                        &obligations,
                        path,
                        assumptions,
                    )? {
                        next_contexts.push(context);
                    }
                }
                continue;
            }
            let worker_count = std::thread::available_parallelism()
                .map(usize::from)
                .unwrap_or(1)
                .min(8)
                .min(paths.len());
            if worker_count == 1 {
                for path in paths {
                    if let Some(context) = verify_lowered_invariant_path(
                        check_index,
                        &facts,
                        &obligations,
                        path,
                        assumptions,
                    )? {
                        next_contexts.push(context);
                    }
                }
                continue;
            }
            let mut work = (0..worker_count).map(|_| Vec::new()).collect::<Vec<_>>();
            for (index, path) in paths.into_iter().enumerate() {
                work[index % worker_count].push((index, path));
            }
            let mut verified = std::thread::scope(|scope| {
                let handles = work
                    .into_iter()
                    .map(|worker_paths| {
                        let facts = &facts;
                        let obligations = &obligations;
                        std::thread::Builder::new()
                            .name(format!("click-invariant-{check_index}"))
                            .stack_size(8 * 1024 * 1024)
                            .spawn_scoped(scope, move || {
                                worker_paths
                                    .into_iter()
                                    .map(|(index, path)| {
                                        Ok((
                                            index,
                                            verify_lowered_invariant_path(
                                                check_index,
                                                facts,
                                                obligations,
                                                path,
                                                assumptions,
                                            )?,
                                        ))
                                    })
                                    .collect::<Result<Vec<_>, String>>()
                            })
                            .map_err(|error| format!("could not start invariant verifier: {error}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                handles
                    .into_iter()
                    .map(|handle| {
                        handle
                            .join()
                            .map_err(|_| "invariant verifier thread panicked".to_string())?
                    })
                    .collect::<Result<Vec<_>, String>>()
            })?;
            let mut verified = verified.drain(..).flatten().collect::<Vec<_>>();
            verified.sort_by_key(|(index, _)| *index);
            next_contexts.extend(verified.into_iter().filter_map(|(_, context)| context));
        }
        contexts = next_contexts;
    }
    if contexts.is_empty() {
        return Err("invariant bundle has no reachable lowering path".to_string());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn collect_invariant_check_obligations_with_mode(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    without_search: bool,
) -> ExecutionResult<Vec<ProofObligation>> {
    let mut contexts = vec![(Vec::new(), Vec::new())];
    let mut all_obligations = Vec::new();
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let effective_assumptions = if without_search {
                assumptions_with_path_context(assumptions, &facts, &obligations)
                    .defer_non_exact_condition_reasoning()
                    .defer_non_exact_loadability_obligations()
            } else {
                assumptions_with_path_context(assumptions, &facts, &obligations)
            };
            for path in lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &effective_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path.facts,
                    &path.obligations,
                    if without_search {
                        &effective_assumptions
                    } else {
                        assumptions
                    },
                ) else {
                    continue;
                };
                let mut obligations = obligations;
                let obligation_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let proposition = wrap_path_context(path.proposition, &facts, &obligations);
                if without_search {
                    add_required_proof_obligation_without_search(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
                    );
                    append_required_proof_obligations_without_search(
                        &mut all_obligations,
                        assumptions,
                        &obligations,
                    );
                } else {
                    add_required_proof_obligation_with_context(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
                    );
                    append_required_proof_obligations(
                        &mut all_obligations,
                        assumptions,
                        &obligations,
                    );
                }
                next_contexts.push((facts, obligations));
            }
        }
        contexts = next_contexts;
    }
    Ok(all_obligations)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LoopPreservationSummary {
    pub(super) obligations: Vec<ProofObligation>,
}

pub(super) fn collect_loop_preservation_summary(
    loop_entry_state: &CState,
    top_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    whole_loop_effect_summaries: &[Proposition],
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<LoopPreservationSummary> {
    let mut obligations = Vec::new();
    let composite_resource_definitions = environment
        .functions
        .values()
        .flat_map(|function| function.composite_resource_definitions().iter().cloned())
        .fold(Vec::new(), |mut definitions, definition| {
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
            definitions
        });
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    for (invariant_facts, invariant_obligations) in assume_invariant_checks(
        top_state,
        loop_entry_state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        budget,
    )? {
        for (condition_facts, condition_obligations) in assume_condition_truthiness(
            top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            budget,
        )? {
            for body_path in execute_c_statement_verification_paths_with_prefix(
                top_state,
                body,
                assumptions,
                environment,
                execution_semantics,
                &condition_facts,
                &condition_obligations,
                budget,
                variables,
            )? {
                match body_path.outcome {
                    CStatementOutcome::Normal(next_state) => {
                        let effect_obligations = collect_loop_effect_check_obligations(
                            top_state,
                            &next_state,
                            effect_checks,
                            &body_path.facts,
                            &body_path.obligations,
                            assumptions,
                            budget,
                        )?;
                        let path_assumptions = assumptions_with_path_context(
                            assumptions,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                        let path_obligations = collect_invariant_check_obligations(
                            &next_state,
                            loop_entry_state,
                            invariant_checks,
                            InvariantPhase::Preservation,
                            &path_assumptions,
                            budget,
                        )?;
                        let mut state_obligations = body_path.obligations.clone();
                        if let Err(message) = c_loop_state_components_match_at_back_edge_inner(
                            top_state,
                            &next_state,
                            &composite_resource_definitions,
                            &path_assumptions,
                        ) {
                            state_obligations.push(
                                ProofObligation::verification_condition(
                                    false_equals_true_proposition(),
                                )
                                .with_context(message),
                            );
                        }
                        append_required_proof_obligations(
                            &mut obligations,
                            assumptions,
                            &state_obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut obligations,
                            assumptions,
                            &effect_obligations,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut obligations,
                            assumptions,
                            &path_obligations,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                    }
                    CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => {
                        let mut path_obligations = body_path.obligations;
                        path_obligations.push(
                            ProofObligation::verification_condition(false_equals_true_proposition())
                                .with_context("loop preservation body safety"),
                        );
                        append_required_proof_obligations(
                            &mut obligations,
                            assumptions,
                            &path_obligations,
                        );
                    }
                }
            }
        }
    }
    Ok(LoopPreservationSummary { obligations })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct EvaluatedMemorySegment {
    pub(super) base: Pointer,
    pub(super) start: Bitvector32Term,
    pub(super) end: Bitvector32Term,
    pub(super) element_width: u32,
}

pub(super) fn collect_whole_loop_effect_summaries(
    before_state: &CState,
    after_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    include_mutable_summaries: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<Proposition>> {
    let mut summaries = Vec::new();
    for check in effect_checks {
        if check.span() != CLoopEffectSpan::Whole {
            continue;
        }

        let ranges = match check.effect() {
            CLoopEffect::Immutable => Vec::new(),
            // A mutable clause is an upper bound. Without a memory-writing
            // body, it is not evidence of mutation and should not block an
            // enclosing immutable claim.
            CLoopEffect::Mutable(_) if !include_mutable_summaries => continue,
            CLoopEffect::Mutable(segments) => {
                let mut ranges = Vec::new();
                let mut failed = false;
                for segment in segments {
                    let element_width = crate::kernel::eval::c_expression_pointer_step_width(
                        before_state,
                        &segment.base,
                    )
                    .unwrap_or(4);
                    match evaluate_loop_effect_segment(before_state, segment, assumptions, budget)?
                    {
                        Ok(segment) => ranges.push(CMemoryRange::new_with_element_width(
                            segment.base,
                            segment.start,
                            segment.end,
                            element_width,
                        )),
                        Err(_) => {
                            failed = true;
                            break;
                        }
                    }
                }
                if failed {
                    continue;
                }
                ranges
            }
        };

        summaries.push(Proposition::CMemoryEffectSummary {
            before: before_state.memory().clone(),
            after: after_state.memory().clone(),
            mutable_ranges: ranges,
        });
    }
    Ok(summaries)
}

pub(super) fn prepare_loop_top_state(
    entry_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<(CState, Vec<Proposition>)> {
    let mut top_state = havoc_loop_modified_locals(entry_state, body, variables);
    let include_mutable_summaries = statement_may_write_memory(body);
    let mut summaries = collect_whole_loop_effect_summaries(
        entry_state,
        &top_state,
        effect_checks,
        include_mutable_summaries,
        assumptions,
        budget,
    )?;

    // Whole-loop effects are part of the induction hypothesis at the abstract
    // head and are checked independently at every back edge.
    let mut framed_memory = top_state.memory().clone();
    if !summaries.is_empty() {
        std::sync::Arc::make_mut(&mut framed_memory.blocks).extend(
            entry_state
                .memory()
                .blocks
                .iter()
                .map(|(key, value)| (key.clone(), value.clone())),
        );
    }
    for (pointer, value) in entry_state.memory().cells.iter() {
        if pointer.block.starts_with("local:") {
            continue;
        }
        let is_stable = summaries.iter().any(|summary| {
            let Proposition::CMemoryEffectSummary { mutable_ranges, .. } = summary else {
                return false;
            };
            assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        if is_stable {
            std::sync::Arc::make_mut(&mut framed_memory.cells)
                .insert(pointer.clone(), value.clone());
        }
    }

    if framed_memory != *top_state.memory() {
        top_state = top_state.with_memory(framed_memory);
        summaries = collect_whole_loop_effect_summaries(
            entry_state,
            &top_state,
            effect_checks,
            include_mutable_summaries,
            assumptions,
            budget,
        )?;
    }
    Ok((top_state, summaries))
}

pub(super) fn collect_loop_effect_check_obligations(
    before_state: &CState,
    after_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    facts: &[ExecutionPureFact],
    path_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    if effect_checks.is_empty() {
        return Ok(Vec::new());
    }

    let effective_assumptions = assumptions_with_path_context(assumptions, facts, path_obligations);
    let mut writes = after_state
        .memory()
        .differing_cell_pointers(before_state.memory())
        .into_iter()
        .filter(is_loop_effect_relevant_pointer)
        .filter(|pointer| {
            let has_disjoint_effect_summary = facts.iter().any(|fact| {
                matches!(
                    fact.proposition(),
                    Proposition::CMemoryEffectSummary { mutable_ranges, .. }
                        if effective_assumptions
                            .ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
                )
            });
            !has_disjoint_effect_summary
                || !c_memory_load_is_unchanged(
                    before_state.memory(),
                    after_state.memory(),
                    pointer,
                    &effective_assumptions,
                )
        })
        .collect::<BTreeSet<_>>();
    writes.extend(
        facts
            .iter()
            .filter_map(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly { pointers, .. } => Some(pointers.as_slice()),
                _ => None,
            })
            .flatten()
            .cloned(),
    );
    let effect_summary_ranges = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
                Some(mutable_ranges.as_slice())
            }
            _ => None,
        })
        .flatten()
        .filter(|range| is_loop_effect_relevant_pointer(range.base()))
        .collect::<Vec<_>>();

    let mut obligations = Vec::new();
    for check in effect_checks {
        let mut segment_evaluation_failed = false;
        let segments = match check.effect() {
            CLoopEffect::Immutable => Vec::new(),
            CLoopEffect::Mutable(segments) => {
                let mut evaluated = Vec::new();
                for (segment_index, segment) in segments.iter().enumerate() {
                    match evaluate_loop_effect_segment(
                        before_state,
                        segment,
                        &effective_assumptions,
                        budget,
                    )? {
                        Ok(segment) => evaluated.push(segment),
                        Err(message) => {
                            segment_evaluation_failed = true;
                            push_false_loop_effect_obligation(
                                &mut obligations,
                                loop_effect_failure_context(
                                    check,
                                    format!(
                                        "could not evaluate mutable segment {segment_index} in {:?}: {message}",
                                        check.effect()
                                    ),
                                ),
                            );
                        }
                    }
                }
                evaluated
            }
        };

        if segment_evaluation_failed {
            continue;
        }

        for pointer in &writes {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_pointer(segment, pointer, &effective_assumptions)
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "write to {pointer:?} is outside the mutable footprint; external writes: {writes:?}; declared effect: {:?}; evaluated segments: {segments:?}",
                            check.effect()
                        ),
                    ),
                );
            }
        }

        for range in &effect_summary_ranges {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_range(segment, range, &effective_assumptions)
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "effect summary range {range:?} is outside the mutable footprint; declared effect: {:?}; evaluated segments: {segments:?}",
                            check.effect()
                        ),
                    ),
                );
            }
        }
    }

    Ok(obligations)
}

pub(super) fn evaluate_loop_effect_segment(
    state: &CState,
    segment: &CMemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<EvaluatedMemorySegment, String>> {
    let base = match evaluate_loop_effect_segment_value(
        state,
        &segment.base,
        assumptions,
        "segment base",
        budget,
    )? {
        Ok(CValue::Pointer(pointer)) => pointer,
        Ok(value) => {
            return Ok(Err(format!(
                "segment base evaluated to {value:?}, not pointer"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let start = match evaluate_loop_effect_segment_value(
        state,
        &segment.start,
        assumptions,
        "segment start",
        budget,
    )? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment start evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let end = match evaluate_loop_effect_segment_value(
        state,
        &segment.end,
        assumptions,
        "segment end",
        budget,
    )? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment end evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let element_width =
        crate::kernel::eval::c_expression_pointer_step_width(state, &segment.base).unwrap_or(4);

    Ok(Ok(EvaluatedMemorySegment {
        base,
        start,
        end,
        element_width,
    }))
}

pub(super) fn evaluate_loop_effect_segment_with_facts(
    state: &CState,
    segment: &CMemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(EvaluatedMemorySegment, Vec<ExecutionPureFact>), String>> {
    let mut facts = Vec::new();
    let mut evaluate = |expression: &CExpression, label: &str| {
        let local_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
        let evaluated = evaluate_loop_effect_segment_value_with_facts(
            state,
            expression,
            &local_assumptions,
            label,
            budget,
        )?;
        let (value, new_facts) = match evaluated {
            Ok(evaluated) => evaluated,
            Err(message) => return Ok(Err(message)),
        };
        for fact in new_facts {
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }
        Ok(Ok(value))
    };
    let base = match evaluate(&segment.base, "segment base")? {
        Ok(CValue::Pointer(pointer)) => pointer,
        Ok(value) => {
            return Ok(Err(format!(
                "segment base evaluated to {value:?}, not pointer"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let start = match evaluate(&segment.start, "segment start")? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment start evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let end = match evaluate(&segment.end, "segment end")? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment end evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let element_width =
        crate::kernel::eval::c_expression_pointer_step_width(state, &segment.base).unwrap_or(4);
    Ok(Ok((
        EvaluatedMemorySegment {
            base,
            start,
            end,
            element_width,
        },
        facts,
    )))
}

pub(super) fn evaluate_loop_effect_segment_value(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CValue, String>> {
    Ok(evaluate_loop_effect_segment_value_with_facts(
        state,
        expression,
        assumptions,
        label,
        budget,
    )?
    .map(|(value, _)| value))
}

fn evaluate_loop_effect_segment_value_with_facts(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(CValue, Vec<ExecutionPureFact>), String>> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget)?;
    if paths.len() != 1 {
        return Ok(Err(format!(
            "{label} evaluated through {} paths, expected exactly one",
            paths.len()
        )));
    }
    let Some(path) = paths.into_iter().next() else {
        return Ok(Err(format!("{label} had no evaluation path")));
    };
    if !path.obligations.is_empty() {
        return Ok(Err(format!(
            "{label} left proof obligations: {:?}",
            path.obligations
        )));
    }
    match path.outcome {
        CExpressionOutcome::Value(value) => Ok(Ok((value, path.facts))),
        CExpressionOutcome::UndefinedBehavior(undefined_behavior) => Ok(Err(format!(
            "{label} produced undefined behavior: {undefined_behavior:?}"
        ))),
        CExpressionOutcome::RuntimeError(error) => {
            Ok(Err(format!("{label} produced runtime error: {error:?}")))
        }
    }
}

pub(super) fn loop_effect_segment_contains_pointer(
    segment: &EvaluatedMemorySegment,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(index) =
        pointer.element_index_from_base_with_width(&segment.base, segment.element_width)
    else {
        return false;
    };
    assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(index, segment.end.clone()),
        true,
    ))
}

pub(super) fn loop_effect_segment_contains_range(
    segment: &EvaluatedMemorySegment,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if range.element_width() != segment.element_width {
        return false;
    }
    let Some(base_index) = range
        .base()
        .element_index_from_base_with_width(&segment.base, segment.element_width)
    else {
        return false;
    };
    let range_start = Bitvector32Term::add(base_index.clone(), range.start().clone());
    let range_end = Bitvector32Term::add(base_index, range.end().clone());
    assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(segment.start.clone(), range_start),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(range_end, segment.end.clone()),
        true,
    ))
}

pub(super) fn is_loop_effect_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

pub(super) fn loop_effect_failure_context(check: &CLoopEffectCheck, message: String) -> String {
    match check.context() {
        Some(context) => format!("{context}: {message}"),
        None => message,
    }
}

pub(super) fn push_false_loop_effect_obligation(
    obligations: &mut Vec<ProofObligation>,
    context: String,
) {
    obligations.push(
        ProofObligation::verification_condition(false_equals_true_proposition())
            .with_context(context),
    );
}

pub(super) fn false_equals_true_proposition() -> Proposition {
    Proposition::Equal(
        Term::Condition(ConditionTerm::Constant(false)),
        Term::Condition(ConditionTerm::Constant(true)),
    )
}

pub(super) fn assume_invariant_checks(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<(Vec<ExecutionPureFact>, Vec<ProofObligation>)>> {
    let mut contexts = vec![(prefix_facts.to_vec(), prefix_obligations.to_vec())];
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for path in lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &effective_assumptions,
                budget,
            )? {
                let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                // A loop invariant is an explicit induction hypothesis at the
                // fresh loop-top snapshot. Even when the entry assumptions can
                // derive it, retain the lowered proposition itself: the facts
                // used for that derivation may belong to an earlier snapshot
                // and are not a substitute for this loop's hypothesis after
                // havoc.
                if assumptions.proves(&path.proposition) {
                    if !facts
                        .iter()
                        .any(|fact| fact.proposition() == &path.proposition)
                    {
                        facts.push(ExecutionPureFact::new(path.proposition));
                    }
                    next_contexts.push((facts, obligations));
                } else if add_path_fact(&mut facts, assumptions, path.proposition).is_some() {
                    next_contexts.push((facts, obligations));
                }
            }
        }
        contexts = next_contexts;
    }
    Ok(contexts)
}

pub(super) fn assume_condition_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    desired_truthiness: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<(Vec<ExecutionPureFact>, Vec<ProofObligation>)>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let mut contexts = Vec::new();
    for condition_path in
        evaluate_c_expression_paths(state, condition, &effective_assumptions, budget)?
    {
        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &condition_path.facts,
            &condition_path.obligations,
            assumptions,
        ) else {
            continue;
        };
        let CExpressionOutcome::Value(value) = condition_path.outcome else {
            continue;
        };
        for truthiness_path in c_truthiness_paths(value, facts, obligations, assumptions) {
            if truthiness_path.is_true == desired_truthiness {
                contexts.push((truthiness_path.facts, truthiness_path.obligations));
            }
        }
    }
    Ok(contexts)
}

pub(super) fn havoc_loop_modified_locals(
    state: &CState,
    body: &CStatement,
    variables: &mut KernelVariableGenerator,
) -> CState {
    let mut state = state.clone();
    let mut names = BTreeSet::new();
    collect_loop_modified_locals(body, &mut names);
    let may_write_memory = statement_may_write_memory(body);
    if may_write_memory {
        // A local whose address escapes can be written by the loop body
        // through a pointer without ever being assigned by name, so treat it
        // as loop-modified too (otherwise its stale value survives the havoc).
        names.extend(address_escaped_scalar_locals(&state, body));
    }
    for name in names {
        let Some(binding) = state.locals.binding(&name) else {
            continue;
        };
        let CLocalBinding::Object { c_type, .. } = binding else {
            continue;
        };
        let c_type = *c_type;
        let value = match c_type {
            CType::Void => continue,
            CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
            CType::UInt8 => uint8(Bitvector32Term::Variable(variables.next())),
            // A pointer local reassigned in the body (`p = p + 1`) must not
            // keep its entry value across the abstract iteration, exactly as
            // the join abstraction treats it; an invariant must relate it.
            CType::Int32Pointer | CType::UInt8Pointer => {
                CValue::Pointer(Pointer::symbolic(variables.next()))
            }
            // Array objects are never assigned by name (C forbids it), and
            // they bind as array objects rather than scalar objects above.
            CType::Int32Array(_) | CType::UInt8Array(_) => continue,
        };
        sync_stack_local(&mut state, &name, &value);
        state.locals.set_typed(name, value, c_type);
    }
    if may_write_memory {
        // Keep only scalar stack local cells (havoced above and re-synced via
        // sync_stack_local); every other concrete cell could have been
        // overwritten by the loop body through a pointer. Address-escaped
        // locals were havoced above, so their preserved cells now hold fresh
        // symbolic values rather than stale ones.
        let preserved_blocks: BTreeSet<PointerBlock> = state
            .locals
            .bindings
            .keys()
            .filter(|name| state.locals.get(name).is_some())
            .filter_map(|name| state.locals.slot(name).map(|slot| slot.block.clone()))
            .collect();
        state.memory = state
            .memory
            .with_loop_memory_havoc(variables.next(), &preserved_blocks);
    }
    state
}

pub(super) fn statement_may_write_memory(statement: &CStatement) -> bool {
    match statement {
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_) => false,
        CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => true,
        CStatement::Seq(first, second) => {
            statement_may_write_memory(first) || statement_may_write_memory(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => statement_may_write_memory(then_branch) || statement_may_write_memory(else_branch),
        CStatement::While { body, .. } => statement_may_write_memory(body),
    }
}

pub(super) fn collect_loop_modified_locals(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => {}
        CStatement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        CStatement::CallAssign { target, .. } => {
            names.insert(target.clone());
        }
        CStatement::Call { .. } => {}
        CStatement::HeapAllocate { target, .. } => {
            names.insert(target.clone());
        }
        CStatement::HeapFree { .. } => {}
        CStatement::Seq(first, second) => {
            collect_loop_modified_locals(first, names);
            collect_loop_modified_locals(second, names);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_modified_locals(then_branch, names);
            collect_loop_modified_locals(else_branch, names);
        }
        CStatement::While { body, .. } => {
            collect_loop_modified_locals(body, names);
        }
    }
}

/// Scalar locals the loop body could write *through a pointer* without ever
/// assigning them by name. `collect_loop_modified_locals` ignores `Store`, so
/// these would otherwise be wrongly preserved across the loop havoc. A local
/// counts as escaped if a live pointer in the pre-loop state already points at
/// its block, or if the body takes its address syntactically.
pub(super) fn address_escaped_scalar_locals(state: &CState, body: &CStatement) -> BTreeSet<String> {
    let mut escaped = BTreeSet::new();
    collect_address_taken_locals(body, &mut escaped);

    let record_pointer = |value: &CValue, escaped: &mut BTreeSet<String>| {
        if let CValue::Pointer(pointer) = value
            && let Some(name) = state.locals.name_for_slot(pointer)
        {
            escaped.insert(name.to_string());
        }
    };
    for name in state.locals.bindings.keys() {
        if let Some(value) = state.locals.get(name) {
            record_pointer(value, &mut escaped);
        }
    }
    for value in state.memory.cells.values() {
        record_pointer(value, &mut escaped);
    }
    escaped
}

pub(crate) fn collect_address_taken_locals(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip | CStatement::Declare { .. } => {}
        CStatement::Assign { expression, .. } => {
            collect_address_taken_in_expression(expression, names)
        }
        CStatement::CallAssign { arguments, .. } => {
            for argument in arguments {
                collect_address_taken_in_expression(argument, names);
            }
        }
        CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_address_taken_in_expression(argument, names);
            }
        }
        CStatement::HeapAllocate { .. } => {}
        CStatement::HeapFree { pointer } => {
            collect_address_taken_in_expression(pointer, names);
        }
        CStatement::Assert { condition, .. } => {
            collect_address_taken_in_expression(condition, names)
        }
        CStatement::Return(expression) => collect_address_taken_in_expression(expression, names),
        CStatement::Store { pointer, value } => {
            collect_address_taken_in_expression(pointer, names);
            collect_address_taken_in_expression(value, names);
        }
        CStatement::TypedStore { pointer, value, .. } => {
            collect_address_taken_in_expression(pointer, names);
            collect_address_taken_in_expression(value, names);
        }
        CStatement::Seq(first, second) => {
            collect_address_taken_locals(first, names);
            collect_address_taken_locals(second, names);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_locals(then_branch, names);
            collect_address_taken_locals(else_branch, names);
        }
        CStatement::While {
            condition, body, ..
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_locals(body, names);
        }
    }
}

pub(super) fn collect_address_taken_in_expression(
    expression: &CExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        // `&target`: any local reachable in the target may have its address
        // escape, so conservatively record every variable it mentions.
        CExpression::AddressOf(target) => collect_variable_names(target, names),
        CExpression::Value(_) | CExpression::Variable(_) => {}
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_address_taken_in_expression(pointer, names)
        }
        CExpression::Not(inner) | CExpression::Load(inner) => {
            collect_address_taken_in_expression(inner, names)
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_address_taken_in_expression(pointer, names)
        }
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
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_address_taken_in_expression(left, names);
            collect_address_taken_in_expression(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_address_taken_in_expression(expression, names);
        }
    }
}

pub(super) fn collect_variable_names(expression: &CExpression, names: &mut BTreeSet<String>) {
    match expression {
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::Value(_) => {}
        CExpression::PointerOffsetBytes { pointer, .. } => collect_variable_names(pointer, names),
        CExpression::AddressOf(inner) | CExpression::Not(inner) | CExpression::Load(inner) => {
            collect_variable_names(inner, names)
        }
        CExpression::TypedLoad { pointer, .. } => collect_variable_names(pointer, names),
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
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_variable_names(left, names);
            collect_variable_names(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_variable_names(expression, names);
        }
    }
}
