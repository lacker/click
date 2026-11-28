use super::*;
use crate::kernel::ExecutionFactSource;
use crate::kernel::proof::{CheckedBranchSplit, CheckedBranchSplitError};

/// Record only associations retained by the loop producer. Missing entries
/// are normal when a break path does not retain an invariant at the exit.
pub(in crate::surface::proof) fn record_loop_exit_invariants(
    presentation: &mut SurfacePropositionMap,
    clause: &StructuralClause,
    correspondence: &[(usize, Proposition)],
    loop_index: usize,
) -> Result<(), ClickError> {
    let exit_point = ProgramPointRef {
        region: CodeRegionRef::Loop(loop_index),
        kind: ProgramPointKind::Exit,
    };
    for (index, target) in correspondence {
        let item = clause
            .items()
            .get(*index)
            .ok_or_else(|| ClickError::new("loop-exit invariant index exceeds declared clauses"))?;
        let surface = surface_at_program_point(item.proposition(), &exit_point)?;
        presentation.record_lowering(&surface, target)?;
    }
    Ok(())
}

fn missing_prerequisite_error(
    message: impl Into<String>,
    obligation: &ProofObligation,
) -> ClickError {
    let error = ClickError::new(message).with_proof_refusal(crate::surface::ProofRefusal::Tactic);
    if obligation.is_assumable() {
        error
    } else {
        error.with_unresolved_requirement(obligation)
    }
}

fn reject_known_undefined_behavior<'a>(
    obligations: &[ProofObligation],
    facts: impl Fn(&ProofObligation) -> &'a PureFactContext,
    context_label: &str,
) -> Result<(), ClickError> {
    if let Some(kind) = obligations
        .iter()
        .find_map(|obligation| obligation.known_undefined_behavior(facts(obligation)))
    {
        return Err(ClickError::new(format!(
            "{context_label} produced {}{}",
            crate::surface::diagnostics::describe_execution_safety_refusal(&kind),
            crate::surface::diagnostics::describe_execution_statement_site()
        ))
        .with_kind(crate::surface::diagnostics::undefined_behavior_refusal_kind(&kind))
        .with_proof_refusal(crate::surface::ProofRefusal::Tactic));
    }
    Ok(())
}

/// A live-view write can use the named goal, its symmetric form, or an exact
/// indexed byte-span witness. Nearby separations are premises for the proof
/// of the requirement, never candidates for execution to try.
fn states_write_separation(proposition: &Proposition, facts: &PureFactContext) -> bool {
    let _checking = crate::instrumentation::CheckingWorkScope::new("stated write separation", 1);
    let Proposition::ResourceSeparate { left, right } = proposition else {
        return false;
    };
    facts.contains_assumed_exact(proposition)
        || facts.contains_assumed_exact(&Proposition::ResourceSeparate {
            left: right.clone(),
            right: left.clone(),
        })
        || facts.states_prepared_memory_separation(proposition)
}

#[cfg(test)]
mod scaling_tests {
    include!(
        "../../../scaling_tests/surface/proof/execution_planning/transition_certification/tests.rs"
    );
}

/// What a probing `Fast` step met while [`probe_open_obligations`] ran.
#[derive(Default)]
pub(in crate::surface) struct OpenObligationProbe {
    /// The open obligations that carry a structured requirement, in order.
    pub(in crate::surface) recorded: Vec<UnresolvedRequirement>,
    /// The refusal each recorded requirement stood for, in the same order.
    pub(in crate::surface) refusals: Vec<ClickError>,
    /// A lowering refusal which has no requirement for the planner to prove.
    pub(in crate::surface) terminal_lowering_refusal: Option<ClickError>,
    collect_step_requirements: bool,
}

thread_local! {
    static OPEN_OBLIGATION_PROBE: std::cell::RefCell<Option<OpenObligationProbe>> =
        const { std::cell::RefCell::new(None) };
}

/// Presentation checks are observations, not execution steps. Their missing
/// prerequisites must reject the candidate, never become debts of a surrounding
/// step probe or let a candidate pass by deferring its prerequisites.
pub(in crate::surface) fn without_open_obligation_probe<R>(operation: impl FnOnce() -> R) -> R {
    struct Restore(Option<OpenObligationProbe>);
    impl Drop for Restore {
        fn drop(&mut self) {
            OPEN_OBLIGATION_PROBE.with(|probe| *probe.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(OPEN_OBLIGATION_PROBE.with(|probe| probe.borrow_mut().take()));
    operation()
}

/// Runs `operation` with every `Fast` refusal that carries a structured
/// requirement recorded instead of returned, and returns what the step met.
/// With recorded obligations, a successful result is a conditional successor,
/// not a checked step. A caller may retain it privately and publish it only
/// after proving every recorded obligation against the original input state.
/// It must never use the candidate's facts to discharge those obligations.
/// Failed preparations have no successor to retain and are final refusals.
pub(in crate::surface) fn probe_open_obligations<R>(
    operation: impl FnOnce() -> R,
) -> (R, OpenObligationProbe) {
    probe_obligations(false, operation)
}

pub(in crate::surface) fn probe_step_obligations<R>(
    operation: impl FnOnce() -> R,
) -> (R, OpenObligationProbe) {
    probe_obligations(true, operation)
}

pub(in crate::surface) fn collecting_step_requirements() -> bool {
    OPEN_OBLIGATION_PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .is_some_and(|probe| probe.collect_step_requirements)
    })
}

fn probe_obligations<R>(
    collect_step_requirements: bool,
    operation: impl FnOnce() -> R,
) -> (R, OpenObligationProbe) {
    struct Restore(Option<OpenObligationProbe>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0.take();
            OPEN_OBLIGATION_PROBE.with(|probe| *probe.borrow_mut() = previous);
        }
    }
    let previous = OPEN_OBLIGATION_PROBE.with(|probe| {
        probe.borrow_mut().replace(OpenObligationProbe {
            collect_step_requirements,
            ..OpenObligationProbe::default()
        })
    });
    let restore = Restore(previous);
    let result = operation();
    let met = OPEN_OBLIGATION_PROBE
        .with(|probe| probe.borrow_mut().take())
        .unwrap_or_default();
    drop(restore);
    (result, met)
}

/// Returns `error`, or, while a `Fast` step is being probed, records its
/// structured requirement and lets checking continue past it.
fn refuse_or_probe(
    policy: StatementPrerequisitePolicy,
    error: ClickError,
) -> Result<(), ClickError> {
    if !matches!(policy, StatementPrerequisitePolicy::Fast) {
        return Err(error);
    }
    let Some(requirement) = error.unresolved_requirement() else {
        return Err(error);
    };
    let recorded = OPEN_OBLIGATION_PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        let probe = probe.as_mut()?;
        probe.recorded.push(requirement.clone());
        probe.refusals.push(error.clone());
        Some(())
    });
    match recorded {
        Some(()) => Ok(()),
        None => Err(error),
    }
}

/// Retains a terminal refusal across a lowering interface that returns text.
pub(in crate::surface) fn record_terminal_lowering_refusal(error: ClickError) {
    OPEN_OBLIGATION_PROBE.with(|probe| {
        if let Some(probe) = probe.borrow_mut().as_mut() {
            probe.terminal_lowering_refusal = Some(error);
        }
    });
}

/// Returns `error`, or, while open obligations are being probed, records its
/// structured requirement and lets the tactic continue past it. A simple
/// tactic other than `step` refuses a requirement it cannot close exactly
/// through this, so a probe can collect them all for the implicit `solve`.
pub(in crate::surface) fn refuse_or_record_open_obligation(
    error: ClickError,
) -> Result<(), ClickError> {
    refuse_or_probe(StatementPrerequisitePolicy::Fast, error)
}

/// A condition's unmet prerequisite, spelled as a proof would state it over
/// `state`'s locals rather than as the kernel's term.
fn missing_condition_prerequisite_error(
    context_label: &str,
    obligation: &ProofObligation,
    state: &ExecutionState,
) -> ClickError {
    missing_prerequisite_error(
        format!(
            "{context_label} is missing condition prerequisite{}: `{}`",
            crate::surface::diagnostics::describe_proof_obligation_context(obligation)
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            crate::surface::diagnostics::describe_stated_fact_over_locals(
                obligation.proposition(),
                state
            ),
        ),
        obligation,
    )
}

fn proof_condition_runtime_error(
    context_label: &str,
    error: &crate::kernel::RuntimeError,
    state: &ExecutionState,
    function: Option<&crate::languages::interface::ImportedFunction>,
) -> ClickError {
    let (parameters, arguments) =
        crate::surface::diagnostics::local_naming_tables_with_source(state, function);
    let (detail, guidance) = match error {
        crate::kernel::RuntimeError::MissingResource { resource }
            if resource.memory_view_range().is_some() =>
        {
            let required =
                crate::surface::proof_diagnostics::render::render_resource_fact_diagnostic(
                    resource,
                    ParameterBinding::new(&parameters, &arguments),
                );
            (
                format!("the read requires `{required}`, which is not available"),
                " The condition's Boolean value does not need to be known in advance: `branch` can split on either value once the field can be read. Unfold the resource that exposes this field before the step that reads it. If a read is valid only under a separate condition, establish that guard before executing the read.",
            )
        }
        _ => (
            crate::surface::diagnostics::describe_runtime_error(
                error,
                ParameterBinding::new(&parameters, &arguments),
            ),
            "",
        ),
    };
    ClickError::new(format!(
        "{context_label} could not evaluate the C condition: {detail}.{guidance}"
    ))
    .with_kind(crate::surface::diagnostics::runtime_refusal_kind(error))
    .with_proof_refusal(crate::surface::diagnostics::runtime_proof_refusal(error))
}

#[derive(Clone)]
pub(in crate::surface::proof) struct CertifiedProofConditionTransition {
    pub(in crate::surface::proof) is_true: bool,
    pub(in crate::surface::proof) pure_facts: PureFactStore,
    pub(in crate::surface::proof) path_facts: Vec<Proposition>,
    pub(in crate::surface::proof) theorem: Theorem,
}

/// Checks a condition split directly against the persistent facts owned by a
/// `Proof`.
///
/// This is the non-planning branch operation: it neither minimizes premises
/// nor reconstructs a certificate. Each feasible path receives only its
/// kernel-issued path facts, appended persistently to the shared ancestor.
#[cfg(test)]
pub(in crate::surface::proof) fn certified_proof_condition_transitions(
    state: &ExecutionState,
    pure_facts: &PureFactStore,
    condition: &ProgramExpression,
    context_label: &str,
) -> Result<Vec<CertifiedProofConditionTransition>, ClickError> {
    let branch = ProgramStatement::If {
        condition: condition.clone(),
        then_branch: Box::new(ProgramStatement::Skip),
        else_branch: Box::new(ProgramStatement::Skip),
    };
    certified_proof_condition_split(state, pure_facts, &branch, None, context_label, None)
        .map(|(_, transitions)| transitions)
}

pub(in crate::surface::proof) fn certified_proof_condition_split(
    state: &ExecutionState,
    pure_facts: &PureFactStore,
    branch_statement: &ProgramStatement,
    continuation: Option<&ProgramStatement>,
    context_label: &str,
    function: Option<&crate::languages::interface::ImportedFunction>,
) -> Result<(CheckedBranchSplit, Vec<CertifiedProofConditionTransition>), ClickError> {
    let split = CheckedBranchSplit::check(
        state.clone(),
        branch_statement.clone(),
        continuation.cloned(),
        pure_facts,
    )
    .map_err(|error| match error {
        CheckedBranchSplitError::Limit(crate::kernel::ExecutionLimit::Deadline) => {
            ClickError::new(format!(
                "verification budget exhausted inside {}",
                crate::instrumentation::deadline_context()
            ))
        }
        CheckedBranchSplitError::Limit(limit) => {
            ClickError::new(format!("{context_label} stopped at {}", limit.describe()))
        }
        CheckedBranchSplitError::InvalidEvidence => ClickError::new(format!(
            "{context_label} received malformed checked condition evidence"
        )),
    })?;
    let transitions = split
        .paths()
        .iter()
        .filter(|path| {
            !path
                .facts()
                .iter()
                .any(|fact| pure_facts.directly_conflicts_with(fact.proposition()))
        })
        .map(|path| {
            let mut successor_facts = pure_facts.clone();
            let mut path_facts = Vec::new();
            for fact in path.facts() {
                let proposition = fact.proposition().clone();
                successor_facts = successor_facts.with_kernel_checked_fact(proposition.clone());
                path_facts.push(proposition);
            }
            reject_known_undefined_behavior(
                path.obligations(),
                |_| successor_facts.assumptions(),
                context_label,
            )?;
            for obligation in path.obligations() {
                if !crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision(
                    successor_facts.assumptions(),
                    obligation.proposition(),
                ) {
                    return Err(missing_condition_prerequisite_error(
                        context_label,
                        obligation,
                        state,
                    ));
                }
            }
            match path.outcome() {
                ConditionOutcome::Value(is_true) => Ok(CertifiedProofConditionTransition {
                    is_true: *is_true,
                    pure_facts: successor_facts,
                    path_facts,
                    theorem: path.theorem().clone(),
                }),
                ConditionOutcome::UndefinedBehavior(kind) => Err(ClickError::new(format!(
                    "{context_label} could not evaluate the C condition: {}{}{}",
                    crate::surface::diagnostics::describe_execution_safety_refusal(kind),
                    crate::surface::diagnostics::describe_undefined_behavior_site(
                        state,
                        branch_statement,
                        pure_facts.assumptions(),
                        kind,
                    ),
                    crate::surface::diagnostics::describe_execution_statement_site()
                ))
                .with_reported_assertion_goal(kind.required_goal().cloned())
                .with_kind(crate::surface::diagnostics::undefined_behavior_refusal_kind(kind))
                .with_proof_refusal(crate::surface::ProofRefusal::Tactic)),
                ConditionOutcome::RuntimeError(error) => Err(proof_condition_runtime_error(
                    context_label,
                    error,
                    state,
                    function,
                )),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((split, transitions))
}

pub(in crate::surface::proof) fn certified_condition_transitions(
    state: &ExecutionState,
    pure_facts: &PureFactList,
    condition: &ProgramExpression,
    context_label: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    context: Option<&PureFactContext>,
) -> Result<Vec<CertifiedConditionTransition>, ClickError> {
    // The list keeps its context, so consulting it here and on every path
    // below builds it at most once, and extends the one the list carried in.
    let pure_context = || pure_facts.context();
    let mut assumptions = match prerequisite_policy {
        StatementPrerequisitePolicy::Exact
        | StatementPrerequisitePolicy::Retained
        | StatementPrerequisitePolicy::Fast => context.cloned().unwrap_or_else(pure_context),
    };
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
        assumptions = assumptions.defer_non_exact_condition_reasoning();
    }
    let evaluation = prove_symbolic_program_condition_evaluation(
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
            "{context_label} stopped at {}",
            limit.describe()
        )));
    }
    evaluation
        .paths()
        .iter()
        // `exact_facts_directly_conflict` against every listed fact, decided
        // through the list's conjunct index.
        .filter(|path| {
            !path
                .facts()
                .iter()
                .any(|path_fact| pure_facts.directly_conflicts_with(path_fact.proposition()))
        })
        .map(|path| {
            // Cloned after the context is consulted above, so every
            // successor list starts from the built context.
            let mut successor_facts = pure_facts.clone();
            successor_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let prerequisite_assumptions = match context {
                // The checked step's presentation already extends the
                // incoming proof graph with this outcome's facts.
                _ if pure_facts.is_statement_view() => successor_facts.context(),
                // The successor facts beyond `pure_facts` are the path's.
                Some(context) => path
                    .facts()
                    .iter()
                    .map(|fact| fact.proposition())
                    .filter(|fact| !pure_facts.contains(fact))
                    .fold(context.clone(), |assumptions, fact| {
                        assumptions.assume_proposition(fact.clone())
                    }),
                // The successor facts extend `pure_facts` by the path's
                // facts, so their context extends the one it carried.
                None => successor_facts.context(),
            };
            reject_known_undefined_behavior(
                path.obligations(),
                |_| &prerequisite_assumptions,
                context_label,
            )?;
            for obligation in path.obligations() {
                match prerequisite_policy {
                    StatementPrerequisitePolicy::Exact => {
                        if exact_fact_is_available(obligation.proposition(), pure_facts)
                            || matches!(
                                normalize_proposition(obligation.proposition()),
                                NormalizedProposition::True
                            )
                        {
                        } else {
                            return Err(missing_condition_prerequisite_error(
                                context_label,
                                obligation,
                                state,
                            )
                            .with_kind(crate::surface::ClickErrorKind::Internal));
                        }
                    }
                    StatementPrerequisitePolicy::Retained | StatementPrerequisitePolicy::Fast => {
                        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Retained)
                            && source_backed_requirement_should_intercept(
                                obligation,
                                state.memory(),
                            )?
                        {
                            return Err(missing_condition_prerequisite_error(
                                context_label,
                                obligation,
                                state,
                            ));
                        }
                        if exact_fact_is_available(obligation.proposition(), pure_facts)
                            || prerequisite_assumptions
                                .states_required_goal(obligation.proposition())
                        {
                        } else {
                            refuse_or_probe(
                                prerequisite_policy,
                                missing_condition_prerequisite_error(
                                    context_label,
                                    obligation,
                                    state,
                                ),
                            )?;
                        }
                    }
                }
            }
            match path.theorem().execution_conclusion() {
                Proposition::ProgramConditionEvaluates {
                    outcome: ConditionOutcome::Value(is_true),
                    ..
                } => Ok(CertifiedConditionTransition {
                    is_true: *is_true,
                    context: assumptions.clone(),
                    pure_facts: successor_facts,
                    path_facts: path
                        .facts()
                        .iter()
                        .map(|fact| fact.proposition().clone())
                        .collect(),
                    theorem: path.theorem().clone(),
                }),
                Proposition::ProgramConditionEvaluates {
                    outcome: ConditionOutcome::UndefinedBehavior(kind),
                    ..
                } => Err(ClickError::new(format!(
                    "{context_label} refused while evaluating the condition: {}{}{}",
                    crate::surface::diagnostics::describe_execution_safety_refusal(kind),
                    crate::surface::diagnostics::describe_undefined_behavior_condition_site(
                        state,
                        condition,
                        &assumptions,
                        kind,
                    ),
                    crate::surface::diagnostics::describe_execution_statement_site()
                ))
                .with_reported_assertion_goal(kind.required_goal().cloned())
                .with_kind(crate::surface::diagnostics::undefined_behavior_refusal_kind(kind))
                .with_proof_refusal(crate::surface::ProofRefusal::Tactic)),
                Proposition::ProgramConditionEvaluates {
                    outcome: ConditionOutcome::RuntimeError(error),
                    ..
                } => Err(ClickError::new(format!(
                    "{context_label} could not verify the C condition: {}{}",
                    crate::surface::diagnostics::describe_runtime_error_over_locals(error, state),
                    crate::surface::diagnostics::describe_execution_statement_site(),
                ))
                .with_kind(crate::surface::diagnostics::runtime_refusal_kind(error))
                .with_proof_refusal(crate::surface::diagnostics::runtime_proof_refusal(error))),
                proposition => Err(ClickError::new(format!(
                    "{context_label} saw unexpected condition theorem `{}`",
                    crate::surface::proof_diagnostics::render::render_proposition(proposition),
                ))),
            }
        })
        .collect()
}

pub(in crate::surface) fn certified_statement_transitions(
    state: &ExecutionState,
    pure_facts: &PureFactList,
    input: impl Into<crate::kernel::StatementProofInput>,
    function_environment: &ExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
    execution_semantics: ExecutionSemantics,
    context_label: &str,
    next_opaque_call: &mut u64,
    next_kernel_variable: &mut u64,
    prerequisite_policy: StatementPrerequisitePolicy,
    context: Option<&PureFactContext>,
) -> Result<(Vec<CertifiedStatementTransition>, Option<VerifiedLoopRule>), ClickError> {
    let input = input.into();
    let statement = input.statement();
    // A statement executed in a proof context sees that context as the
    // kernel already keeps it: incrementally indexed, shared by clone. The
    // slice then carries only the statement-local delta bookkeeping.
    // Without one, the list's own context is extended by the facts it
    // gained since it was last consulted.
    let mut assumptions = context.cloned().unwrap_or_else(|| pure_facts.context());
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
        assumptions = assumptions.defer_non_exact_loadability_obligations();
        assumptions = assumptions.prefer_symbolic_external_loads();
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
        assumptions = assumptions.defer_non_exact_condition_reasoning();
    }
    if collecting_step_requirements() {
        assumptions = assumptions.retaining_required_obligations();
    }
    let mut budget = ExecutionBudget::continuing_from(*next_kernel_variable)
        .with_next_opaque_call(*next_opaque_call);
    let executed_under = assumptions.clone();
    let execute = || {
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            state.clone(),
            input.clone(),
            assumptions,
            function_environment.clone(),
            execution_semantics,
            &mut budget,
        )
    };
    let (execution, loop_rule) = execute();
    *next_opaque_call = budget.next_opaque_call();
    *next_kernel_variable = budget.next_kernel_variable();
    let (transitions, loop_rule) = certified_transitions_from_execution(
        execution,
        state,
        statement,
        loop_rule,
        pure_facts,
        function_environment,
        predicate_environment,
        context_label,
        prerequisite_policy,
        context,
        &executed_under,
    )?;
    Ok((transitions, loop_rule))
}

pub(in crate::surface::proof) fn certified_loop_exit_transitions_with_proven_phases(
    state: &ExecutionState,
    pure_facts: &PureFactList,
    input: impl Into<crate::kernel::StatementProofInput>,
    function_environment: &ExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
    context_label: &str,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: &[LoopFinalExitCandidate],
    early_exits: &[LoopEarlyExit],
    return_exits: &[LoopReturnExit],
    back_edges: &[crate::kernel::LoopBackEdges],
    otherwise: Option<&mut crate::kernel::LoopOtherwiseProof<'_>>,
    exit_fact_scope: Option<&crate::kernel::LoopExitFactScope<'_>>,
    next_opaque_call: &mut u64,
    next_kernel_variable: &mut u64,
) -> Result<(Vec<CertifiedStatementTransition>, Option<VerifiedLoopRule>), ClickError> {
    let input = input.into();
    let statement = input.statement();
    let assumptions = assumptions_from_propositions(pure_facts);
    let executed_under = assumptions.clone();
    let mut budget = ExecutionBudget::continuing_from(*next_kernel_variable)
        .with_next_opaque_call(*next_opaque_call);
    // Exit facts are retained behind shared slices, so these copies move one
    // handle per exit rather than cloning each exit's whole proposition list.
    crate::instrumentation::record_deterministic_work(
        final_exit_candidates.len() + early_exits.len() + return_exits.len(),
    );
    let (execution, loop_rule) = prove_symbolic_loop_exit_with_proven_phases_using_budget(
        state.clone(),
        input.clone(),
        assumptions,
        function_environment.clone(),
        initialization_proven,
        preservation_proven,
        final_exit_candidates.to_vec(),
        early_exits.to_vec(),
        return_exits.to_vec(),
        back_edges,
        otherwise,
        exit_fact_scope,
        &mut budget,
    );
    *next_opaque_call = budget.next_opaque_call();
    *next_kernel_variable = budget.next_kernel_variable();
    certified_transitions_from_execution(
        execution,
        state,
        statement,
        loop_rule,
        pure_facts,
        function_environment,
        predicate_environment,
        context_label,
        StatementPrerequisitePolicy::Fast,
        None,
        &executed_under,
    )
}

pub(in crate::surface::proof) fn statement_contains_call(statement: &ProgramStatement) -> bool {
    match statement {
        ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. } => true,
        ProgramStatement::Seq(statements) => statements
            .iter()
            .any(|statement| statement_contains_call(statement)),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => statement_contains_call(try_body) || statement_contains_call(handler),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => statement_contains_call(then_branch) || statement_contains_call(else_branch),
        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            statement_contains_call(body)
                || test
                    .as_ref()
                    .is_some_and(|test| statement_contains_call(&test.statement))
                || update
                    .as_ref()
                    .is_some_and(|update| statement_contains_call(update))
        }
        ProgramStatement::Switch { cases, .. } => {
            cases.iter().any(|case| statement_contains_call(&case.body))
        }
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::CreateClosure { .. }
        | ProgramStatement::BuiltinConstantP { .. }
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::Update { .. } => false,
        ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::EndAutomaticLifetimes { .. } => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn certified_transitions_from_execution(
    execution: SymbolicExecution,
    state: &ExecutionState,
    statement: &ProgramStatement,
    loop_rule: Option<VerifiedLoopRule>,
    pure_facts: &PureFactList,
    environment: &ExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
    context_label: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    context: Option<&PureFactContext>,
    executed_under: &PureFactContext,
) -> Result<(Vec<CertifiedStatementTransition>, Option<VerifiedLoopRule>), ClickError> {
    if let Some(limit) = execution.limit() {
        if matches!(limit, crate::kernel::ExecutionLimit::Deadline) {
            return Err(ClickError::new(format!(
                "verification budget exhausted inside {}",
                crate::instrumentation::deadline_context()
            )));
        }
        return Err(ClickError::new(format!(
            "{context_label} stopped at {}",
            limit.describe()
        )));
    }
    // `exact_facts_directly_conflict` against every listed fact, decided
    // through the list's conjunct index.
    let feasible = |path: &&crate::kernel::SymbolicExecutionPath| {
        !path
            .facts()
            .iter()
            .any(|path_fact| pure_facts.directly_conflicts_with(path_fact.proposition()))
    };
    let transitions = execution
        .paths()
        .iter()
        .enumerate()
        .filter(|(_, path)| feasible(path))
        .map(|(path_index, path)| {
            let loop_invariant_correspondence = loop_rule.as_ref()
                .map(|rule| rule.loop_invariant_correspondence(path_index).to_vec())
                .unwrap_or_default();
            let loop_iterations = loop_rule
                .as_ref()
                .and_then(|rule| rule.loop_iterations(path_index))
                .map(|term| crate::kernel::KernelTermImport::default().integer(&term.clone().into()));
            let mut successor_facts = pure_facts.clone();
            let statement_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let statement_fact_sources = statement_facts.clone();
            successor_facts.extend(statement_facts.iter().cloned());
            let execution_facts = path.execution_facts();
            let prerequisite_assumptions = match context {
                // The checked step's presentation already extends the
                // incoming proof graph with this outcome's facts.
                _ if pure_facts.is_statement_view() => successor_facts.context(),
                Some(context) => statement_facts
                    .iter()
                    .fold(context.clone(), |assumptions, fact| {
                        assumptions.assume_proposition(fact.clone())
                    }),
                // `successor_facts` is `pure_facts` followed by the
                // statement's facts, so its context extends the one
                // `pure_facts` carried.
                None => successor_facts.context(),
            };
            let mut prerequisite_derivations = Vec::new();
            // Stable-view recovery refuses a call whose checked path still
            // carries pending obligations (`PendingCallObligations`); other
            // contract boundaries refuse with `FunctionContract`.
            let rejected_contract_call = matches!(
                implication_body(path.theorem().proposition()),
                Proposition::ProgramStatementVerifies {
                    outcome: StatementOutcome::RuntimeError(
                        crate::kernel::RuntimeError::FunctionContract(_)
                            | crate::kernel::RuntimeError::UnsuppliedResourceValue(_)
                            | crate::kernel::RuntimeError::PendingCallObligations(_)
                    ),
                    ..
                }
            );
            // A precondition cannot cite a fact produced by the
            // transition whose validity depends on that precondition.
            let facts_for_obligation = |obligation: &ProofObligation| {
                if obligation.requires_statement_entry() {
                    executed_under
                } else {
                    &prerequisite_assumptions
                }
            };
            reject_known_undefined_behavior(path.obligations(), facts_for_obligation, context_label)?;
            for obligation in path.obligations() {
                let prerequisite_assumptions = facts_for_obligation(obligation);
                let proposition = obligation.proposition();
                let live_view_write = obligation.live_view_write_overlap();
                // The call can ask for a different descriptor for the same
                // physical byte spans. Check that entry fact before collecting
                // an internal prerequisite whose descriptor may not raise.
                // Keep collecting obligations already stated as written so
                // explicit step proofs keep their existing obligation list.
                if !rejected_contract_call
                    && obligation.call_requirement_site().is_some()
                    && live_view_write == Some(false)
                    && !executed_under.contains_assumed_exact(proposition)
                    && executed_under.states_prepared_memory_separation(proposition)
                {
                    continue;
                }
                // An allocation step can establish this exact separation
                // before the temporary has a Surface name. Its predecessor
                // fact is checked here, without opening a source proof.
                let established_temporary_separation =
                    matches!(proposition, Proposition::ResourceSeparate { left, .. }
                        if matches!(left.as_ref(), crate::kernel::Resource::Memory(range)
                            if matches!(&range.base().base,
                                crate::kernel::AddressBase::AutomaticLocal { binding, .. }
                                if binding.is_temporary())))
                    && executed_under.contains_assumed_exact(proposition);
                if collecting_step_requirements()
                    && !obligation.is_assumable()
                    && !established_temporary_separation
                {
                    let description = crate::surface::diagnostics::describe_proof_obligation_context(obligation);
                    let message = match description {
                        Some(description) if live_view_write == Some(true) => {
                            format!("{context_label} cannot proceed: {description}")
                        }
                        Some(description) => format!("{context_label} requires an explicit prerequisite proof ({description})"),
                        None => format!("{context_label} requires an explicit prerequisite proof"),
                    };
                    refuse_or_probe(prerequisite_policy, ClickError::new(format!(
                        "{message}{}",
                        crate::surface::diagnostics::describe_execution_statement_site()
                    )).with_unresolved_requirement(obligation)
                        .with_assertion_condition(
                            crate::surface::proof::fact_reasoning::asserted_condition(proposition, statement),
                        ))?;
                    continue;
                }
                let derivation = match prerequisite_policy {
                    StatementPrerequisitePolicy::Exact => {
                        // An exact conjunct is also the availability the
                        // polarity-aware check below accepts.
                        if pure_facts.has_exact_conjunct(proposition)
                            || exact_fact_is_available(proposition, pure_facts)
                            || if live_view_write.is_some() {
                                states_write_separation(proposition, executed_under)
                            } else {
                                directly_matching_separation_fact(proposition, pure_facts).is_some()
                            }
                            || directly_covering_loadability_fact(proposition, pure_facts).is_some()
                            || matches!(normalize_proposition(proposition), NormalizedProposition::True)
                        {
                            None
                        } else {
                            return Err(missing_prerequisite_error(
                                format!(
                                    "{context_label} is missing certified prerequisite{}: {}",
                                    crate::surface::diagnostics::describe_proof_obligation_context(obligation)
                                        .map(|context| format!(" ({context})"))
                                        .unwrap_or_default(),
                                    describe_statement_prerequisite_failure(
                                proposition,
                                pure_facts,
                                &statement_facts,
                                state,
                                statement,
                                environment,
                                predicate_environment,
                            ),
                                ),
                                obligation,
                            ).with_kind(crate::surface::ClickErrorKind::Internal));
                        }
                    }
                    StatementPrerequisitePolicy::Retained | StatementPrerequisitePolicy::Fast => {
                        // A refusal lists the facts this check consulted.
                        // Over a proof context `pure_facts` is only the
                        // statement-local delta, and the context itself
                        // (the contract's requirements, earlier path facts)
                        // is what was searched beside it; list both, so a
                        // loop guard held in the delta is not left out.
                        let consulted_facts = || match context {
                            _ if live_view_write.is_some() => Vec::new(),
                            Some(_) => {
                                let mut facts = prerequisite_assumptions.pure_facts();
                                facts.extend(pure_facts.iter().cloned());
                                facts
                            }
                            None => pure_facts.to_vec(),
                        };
                        // A retained checked derivation over the context, or
                        // the exact structural rules the explicit law used (a
                        // listed premise covering a loadability, a matching
                        // separation).
                        // The bare prover verdict is not one of them: a
                        // required verification condition the kernel emitted
                        // -- a call precondition, most of them -- is
                        // discharged by evidence this side can check, never
                        // by a search whose answer nothing records.
                        // Load names are not preserved across call-havoc and
                        // store edges by path assumptions (see
                        // `MemoryDerivation`). A prerequisite naming a cell
                        // whose load the assumption-free naming walk left
                        // symbolic is checked in the form this context
                        // decides: each such load is resolved along the
                        // recorded memory DAG, crossing edges only where the
                        // context proves the cell untouched.
                        let resolved =
                            crate::kernel::resolve_prerequisite_loads_along_memory_derivations(
                                proposition,
                                prerequisite_assumptions,
                            );
                        let proposition = resolved.as_ref().unwrap_or(proposition);
                        if matches!(
                            prerequisite_policy,
                            StatementPrerequisitePolicy::Retained
                        ) && source_backed_requirement_should_intercept(
                            obligation,
                            state.memory(),
                        )? {
                            return Err(missing_prerequisite_error(
                                format!(
                                    "{context_label} is missing prerequisite{}: {}",
                                    crate::surface::diagnostics::describe_proof_obligation_context(obligation)
                                        .map(|context| format!(" ({context})"))
                                        .unwrap_or_default(),
                                    describe_statement_prerequisite_failure(
                                        proposition,
                                        &consulted_facts(),
                                        &statement_facts,
                                        state,
                                        statement,
                                        environment,
                                        predicate_environment,
                                    ),
                                ),
                                obligation,
                            ));
                        }
                        if prerequisite_assumptions.states_required_goal(proposition)
                            || pure_facts.has_exact_conjunct(proposition)
                            || exact_fact_is_available(proposition, pure_facts)
                            // The same rule for a prerequisite the resolution
                            // above leaves symbolic: an earlier fact about the
                            // same cells, load atoms proven unchanged in
                            // context.
                            || crate::kernel::proof::fact_reasoning::condition_bridged_fact_is_available_among(
                                proposition,
                                pure_facts,
                                prerequisite_assumptions,
                            )
                            || if live_view_write.is_some() {
                                states_write_separation(proposition, prerequisite_assumptions)
                            } else {
                                directly_matching_separation_fact(proposition, pure_facts).is_some()
                            }
                            || directly_covering_loadability_fact(proposition, pure_facts).is_some()
                            // A rejected contract candidate must not erase its
                            // pending clause merely because that clause is
                            // trivially true. Preparation reports requirements
                            // separately from whether a successor was produced.
                            || (matches!(normalize_proposition(proposition), NormalizedProposition::True)
                                && !(matches!(prerequisite_policy, StatementPrerequisitePolicy::Fast)
                                    && obligation.call_requirement_site().is_some()
                                    && rejected_contract_call))

                        {
                            None
                        } else {
                            refuse_or_probe(
                                prerequisite_policy,
                                missing_prerequisite_error(
                                    format!(
                                        "{context_label} is missing prerequisite{}: {}",
                                        crate::surface::diagnostics::describe_proof_obligation_context(obligation)
                                            .map(|context| format!(" ({context})"))
                                            .unwrap_or_default(),
                                        describe_statement_prerequisite_failure(
                                            proposition,
                                            &consulted_facts(),
                                            &statement_facts,
                                            state,
                                            statement,
                                            environment,
                                            predicate_environment,
                                        ),
                                    ),
                                    obligation,
                                )
                                .with_assertion_condition(
                                    crate::surface::proof::fact_reasoning::asserted_condition(
                                        proposition,
                                        statement,
                                    ),
                                )
                                .with_reported_assertion_goal(
                                    crate::surface::proof::fact_reasoning::asserted_condition(
                                        proposition,
                                        statement,
                                    )
                                    .and_then(|condition| {
                                        crate::surface::proof::fact_reasoning::asserted_condition_goal(state, condition)
                                    }),
                                ),
                            )?;
                            None
                        }
                    }
                };
                if let Some(derivation) = derivation {
                    prerequisite_derivations.push(derivation);
                }
            }
            #[cfg(test)]
            let _publication = crate::kernel::search::FastOperationScope::enter(
                "statement result publication",
            );
            let introduced_facts = statement_facts.clone();
            let Proposition::ProgramStatementVerifies {
                state: _,
                outcome,
                ..
            } =
                implication_body(path.theorem().proposition())
            else {
                return Err(ClickError::new(format!(
                    "{context_label} saw an unexpected execution theorem"
                )));
            };
            if matches!(outcome, StatementOutcome::Normal(_) | StatementOutcome::Return { .. })
            {
                // Publish the producer's facts at their original states.
                // Extra current-state consequences belong to explicit proof or
                // expandable search, not automatic statement-exit discovery.
                let mut transported_facts = Vec::new();
                for execution_fact in &execution_facts {
                    let (Some(source), Some(theorem)) = (
                        execution_fact.transport_source(),
                        execution_fact.transport_theorem(),
                    ) else {
                        continue;
                    };
                    let Some((frame_premises, theorem_target)) =
                        crate::kernel::program_condition_fact_transport_parts(theorem, source)
                    else {
                        continue;
                    };
                    if theorem_target != execution_fact.proposition() {
                        continue;
                    }
                    let transport = CertifiedFactTransport {
                        source: source.clone(),
                        target: execution_fact.proposition().clone(),
                        theorem: theorem.clone(),
                        statement_local: false,
                        frame_premises: frame_premises.into_iter().cloned().collect(),
                    };
                    if !transported_facts.contains(&transport) {
                        transported_facts.push(transport);
                    }
                }
                let path_facts = path
                    .facts()
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .filter(|fact| statement_fact_sources.contains(fact))
                    .collect::<Vec<_>>();
                let generated_load_bindings =
                    generated_load_bindings_from_facts(&execution_facts);
                let generated_load_source_events =
                    generated_load_source_events_from_facts(&execution_facts);
                return Ok(CertifiedStatementTransition {
                    native_step: Arc::new(path.clone()),
                call_result: path.call_result().cloned().map(|value| RetainedProgramValue::from(value.into_value())),
                    theorem: path.theorem().clone(),
                    context: executed_under.clone(),
                    outcome: outcome.clone(),
                    execution_facts,
                    path_facts,
                    obligations: path.obligations().to_vec(),
                    pure_facts: successor_facts,
                    introduced_facts,
                    loop_invariant_correspondence,
                    loop_iterations: loop_iterations.clone(),
                    prerequisite_derivations,
                    planning_premises: Vec::new(),
                    fact_transports: transported_facts,
                    generated_load_bindings,
                    generated_load_source_events,
                    borrow_evidence: path.borrow_evidence().clone(),
                });
            }
            let generated_load_bindings = generated_load_bindings_from_facts(&execution_facts);
            let generated_load_source_events =
                generated_load_source_events_from_facts(&execution_facts);
            Ok(CertifiedStatementTransition {
                    native_step: Arc::new(path.clone()),
                call_result: path.call_result().cloned().map(|value| RetainedProgramValue::from(value.into_value())),
                theorem: path.theorem().clone(),
                context: executed_under.clone(),
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
                introduced_facts,
                loop_invariant_correspondence,
                loop_iterations,
                prerequisite_derivations,
                planning_premises: Vec::new(),
                fact_transports: Vec::new(),
                generated_load_bindings,
                generated_load_source_events,
                borrow_evidence: path.borrow_evidence().clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((transitions, loop_rule))
}

/// Retain only producer-issued load metadata, with a variable-level
/// tombstone when one checked path observes incompatible exact keys.  The
/// transition owns this small output-sized vector; no proof-state or memory
/// scan is involved.
fn generated_load_bindings_from_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Vec<crate::kernel::GeneratedLoadBinding> {
    let mut bindings =
        std::collections::BTreeMap::<Variable, crate::kernel::GeneratedLoadBinding>::new();
    for fact in facts.fact_iter() {
        let Some(binding) = fact.generated_load_binding() else {
            continue;
        };
        let variable = match binding {
            crate::kernel::GeneratedLoadBinding::Exact { variable, .. }
            | crate::kernel::GeneratedLoadBinding::Ambiguous { variable } => *variable,
        };
        let next = match bindings.get(&variable) {
            Some(crate::kernel::GeneratedLoadBinding::Ambiguous { .. }) => continue,
            Some(crate::kernel::GeneratedLoadBinding::Exact {
                retained_state,
                pointer,
                load,
                ..
            }) => match binding {
                crate::kernel::GeneratedLoadBinding::Exact {
                    retained_state: next_state,
                    pointer: next_pointer,
                    load: next_load,
                    ..
                } if retained_state == next_state
                    && pointer == next_pointer
                    && load == next_load =>
                {
                    continue;
                }
                _ => crate::kernel::GeneratedLoadBinding::Ambiguous { variable },
            },
            None => binding.clone(),
        };
        bindings.insert(variable, next);
    }
    bindings.into_values().collect()
}

fn generated_load_source_events_from_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Vec<crate::kernel::GeneratedLoadSourceEvent> {
    facts
        .fact_iter()
        .flat_map(ExecutionPureFact::generated_load_source_events)
        .cloned()
        .collect()
}

#[cfg(test)]
mod condition_transition_tests {
    use super::*;
    use crate::kernel::RuntimeError;

    #[test]
    fn condition_transition_still_checks_execution_obligations() {
        let state = ExecutionState::new().with_local(
            "p",
            ProgramValue::pointer(Address::new(
                "havoc:condition-obligation".into(),
                AddressOffset::constant(0),
            )),
        );
        let condition = crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        );

        let error = match certified_condition_transitions(
            &state,
            &PureFactList::default(),
            &condition,
            "condition obligation regression",
            StatementPrerequisitePolicy::Fast,
            None,
        ) {
            Ok(_) => panic!("a step accepted an unproved viewability obligation"),
            Err(error) => error,
        };

        assert!(
            error
                .message()
                .contains("missing condition prerequisite: `viewable(p[0..1])`"),
            "{error}"
        );
    }

    #[test]
    fn generated_load_binding_collection_tombstones_conflicting_keys() {
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let load = |pointer: Address| {
            OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&memory),
                Box::new(pointer),
                crate::kernel::LoadKind::Int32,
            )
        };
        let variable = Variable(0xfeed);
        let producer_fact = |pointer: Address| {
            let mut facts = crate::kernel::ExecutionFacts::new();
            crate::kernel::record_load_variable_defining_fact(variable, load(pointer), &mut facts);
            facts.pop().expect("producer emits defining fact")
        };
        let same = generated_load_bindings_from_facts(&[
            producer_fact(pointer.clone()),
            producer_fact(pointer),
        ]);
        assert!(matches!(
            same.as_slice(),
            [crate::kernel::GeneratedLoadBinding::Exact { .. }]
        ));

        let conflicting = generated_load_bindings_from_facts(&[
            producer_fact(Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::constant(0),
            )),
            producer_fact(Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::constant(4),
            )),
        ]);
        assert!(matches!(
            conflicting.as_slice(),
            [crate::kernel::GeneratedLoadBinding::Ambiguous {
                variable
            }] if *variable == Variable(0xfeed)
        ));
    }

    #[test]
    fn real_scalar_load_transition_retains_its_read_without_a_binding() {
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let parsed = crate::languages::c::syntax::parse_functions_for_source(
            r#"
            struct owner { int32 len; };
            int32 owner_len(struct owner* owner) {
                return owner->len;
            }
            "#,
            "owner_len.c",
        )
        .expect("field getter should parse with source identity");
        let statement = parsed[0].body_kernel_statement();
        let state = ExecutionState::new()
            .with_local(
                parsed[0].parameters()[0].binding_name(),
                ProgramValue::pointer(pointer.clone()),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new(
                    pointer.clone(),
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(1),
                )),
            ));
        let mut next_opaque_call = 0;
        let mut next_kernel_variable = 0;
        let (transitions, _) = certified_statement_transitions(
            &state,
            &PureFactList::default(),
            &statement,
            &ExecutionEnvironment::new(),
            None,
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            "real load transition test",
            &mut next_opaque_call,
            &mut next_kernel_variable,
            StatementPrerequisitePolicy::Fast,
            None,
        )
        .expect("a symbolic external load should produce a checked transition");
        let [transition] = transitions.as_slice() else {
            panic!("expected one load transition: {transitions:?}");
        };
        assert!(transition.generated_load_bindings.is_empty());
        assert!(transition.generated_load_source_events.is_empty());
        assert!(matches!(&transition.outcome,
            StatementOutcome::Return { value, .. }
                if matches!(value.native().as_ref(), ProgramValue::Int32(OldMachineTerm::MemoryLoad(_, at, crate::kernel::LoadKind::Int32)) if **at == pointer)));

        // Feed the producer-issued transition metadata through the same
        // persistent presentation store used by the execution cursor. This
        // keeps the test on the production path past transition planning,
        // rather than manufacturing a metadata-only fact.
        let mut execution = ExecutionProofState::at_entry(
            state,
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        );
        execution
            .presentation
            .record_generated_load_bindings(&transition.generated_load_bindings);
        execution
            .presentation
            .record_generated_load_source_events(&transition.generated_load_source_events);
        assert_eq!(execution.presentation.generated_load_bindings.len(), 0);
        assert_eq!(
            execution.presentation.generated_load_binding_events.len(),
            0
        );
        assert_eq!(
            execution
                .presentation
                .generated_load_source_resolutions
                .len(),
            0
        );
        assert_eq!(execution.presentation.generated_load_source_events.len(), 0);
    }

    #[test]
    fn parsed_compound_field_update_retains_its_structural_read() {
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let parsed = crate::languages::c::syntax::parse_functions_for_source(
            r#"
            struct counter { uint32 value; };
            void bump(struct counter* counter) {
                counter->value += 1u;
            }
            "#,
            "bump.c",
        )
        .expect("compound field update should parse with source identity");
        let statement = parsed[0].body_kernel_statement();
        let state = ExecutionState::new()
            .with_local(
                parsed[0].parameters()[0].binding_name(),
                ProgramValue::pointer(pointer.clone()),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new(
                    pointer.clone(),
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(1),
                )),
            ));
        let mut next_opaque_call = 0;
        let mut next_kernel_variable = 0;
        let (transitions, _) = certified_statement_transitions(
            &state,
            &PureFactList::default(),
            &statement,
            &ExecutionEnvironment::new(),
            None,
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            "compound field update source-event test",
            &mut next_opaque_call,
            &mut next_kernel_variable,
            StatementPrerequisitePolicy::Fast,
            None,
        )
        .expect("an owned unsigned field update should produce a checked transition");
        let [transition] = transitions.as_slice() else {
            panic!("expected one field-update transition: {transitions:?}");
        };
        assert!(transition.generated_load_source_events.is_empty());
        let after = match &transition.outcome {
            StatementOutcome::Normal(after) | StatementOutcome::Return { state: after, .. } => {
                after
            }
            other => panic!("completed update: {other:?}"),
        };
        let ExpressionOutcome::Value(ProgramValue::UInt32(value)) = after.memory().load(&pointer)
        else {
            panic!("unsigned field");
        };
        assert!(crate::kernel::proposition_mentions_scalar_read(
            &Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: crate::kernel::MachineIntegerType::UInt32,
                    relation: crate::kernel::CompareRelation::Equal,
                    left: Box::new(value),
                    right: Box::new(OldMachineTerm::constant(0))
                },
                true
            )
        ));
    }

    #[test]
    fn failed_typed_load_publishes_no_source_event() {
        let statement = ProgramStatement::Return(ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::Value(ProgramValue::Int32(
                OldMachineTerm::constant(7),
            ))),
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: crate::kernel::ExpressionLoadSource::new(crate::kernel::LoadSourceId {
                owner: crate::kernel::LoadSourceOwnerId {
                    source_unit: std::sync::Arc::from("bad.c"),
                    function: std::sync::Arc::from("bad"),
                },
                occurrence: 0,
                reference_access: None,
            }),
        });
        let mut next_opaque_call = 0;
        let mut next_kernel_variable = 0;
        let (transitions, _) = certified_statement_transitions(
            &ExecutionState::new(),
            &PureFactList::default(),
            &statement,
            &ExecutionEnvironment::new(),
            None,
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            "failed load source-event test",
            &mut next_opaque_call,
            &mut next_kernel_variable,
            StatementPrerequisitePolicy::Fast,
            None,
        )
        .expect("a runtime type error should remain an explicit transition outcome");
        let [transition] = transitions.as_slice() else {
            panic!("expected one failed load transition: {transitions:?}");
        };
        assert!(matches!(
            transition.outcome,
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
        ));
        assert!(transition.generated_load_source_events.is_empty());
    }

    #[test]
    fn typed_load_source_metadata_is_semantically_neutral() {
        use std::collections::HashSet;
        let pointer = ProgramExpression::Value(ProgramValue::pointer(Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::constant(8),
        )));
        let source = |occurrence| {
            crate::kernel::ExpressionLoadSource::new(crate::kernel::LoadSourceId {
                owner: crate::kernel::LoadSourceOwnerId {
                    source_unit: std::sync::Arc::from("f.c"),
                    function: std::sync::Arc::from("f"),
                },
                occurrence,
                reference_access: None,
            })
        };
        let first = ProgramExpression::TypedLoad {
            pointer: Box::new(pointer.clone()),
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: source(0),
        };
        let second = ProgramExpression::TypedLoad {
            pointer: Box::new(pointer),
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: source(1),
        };
        assert_eq!(first, second);
        let mut expressions = HashSet::new();
        expressions.insert(first);
        expressions.insert(second);
        assert_eq!(expressions.len(), 1);
    }
}
